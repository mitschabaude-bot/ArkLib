/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.ProofSystem.Whir.Errors

/-!
# WHIR decoding, named witness selection, and the retained-witness certificate goal

`initialExtractor` is total and selects an actual base-field message from an explicit decoder
list. `retainedExtractor` supplies identity backward maps for any annotation of the actual
opening tree by predicates on that original message. `OpeningCertificateGoal` records the
remaining certificate and acceptance-transfer requirements; it is a proposition, not a theorem
asserting that they hold.

Annex B bounds escape of an existential list relation. It does not prove preservation of each
chosen preimage under a fold. `affineRetention_badChallenge` exposes this distinction in the
smallest witness carrier: an arbitrary affine preimage can vanish at every fresh challenge
even though it was not the zero message. At a level transition, the complement of Annex B's
invariant also includes OOD collisions; `oodState` exhibits that additional witness carrier.
-/

@[expose] public section

open Interaction Interaction.Oracle Interaction.Oracle.Security

namespace Whir

/-- An explicit interleaved list-decoding algorithm, with correctness supplied separately. -/
structure ListDecoder {K E : Type} {vars : ℕ} (enc : Encoding K vars) (lanes : ℕ) where
  /-- Candidate messages are ordered, so selection is a named deterministic operation. -/
  decode : Word E lanes (2 ^ (vars + enc.rate)) → List (Table E (lanes + vars))

/-- Exact list coverage, no duplicates, and the real Johnson cardinality bound. -/
structure ListDecoder.Correct {K E : Type} [Semiring K] [Semiring E] [DecidableEq E]
    {vars lanes : ℕ} {enc : Encoding K vars} (decoder : ListDecoder (E := E) enc lanes)
    (ι : K →+* E) (γ L : ℝ) : Prop where
  /-- The decoder enumerates each candidate once. -/
  nodup : ∀ word, (decoder.decode word).Nodup
  /-- Membership is equivalent to column proximity to the message's encoding. -/
  mem_iff : ∀ word f, f ∈ decoder.decode word ↔ Close γ word (enc.interleave ι f)
  /-- The list length is bounded without an interleaving row factor. -/
  length_le : ∀ word, ((decoder.decode word).length : ℝ) ≤ L

/-- The opening relation has the original base-field multilinear as its witness. -/
def initialState {K E : Type} [Semiring K] [Semiring E] [DecidableEq K]
    {vars lanes : ℕ} (enc : Encoding K vars) (ι : K →+* E) (γ : ℝ)
    (word : Word K lanes (2 ^ (vars + enc.rate)))
    (claims : List (Claim E (lanes + vars))) : KnowledgeState where
  Witness := Table K (lanes + vars)
  holds f := Close γ word (enc.interleave (RingHom.id K) f) ∧
    ∀ c ∈ claims, c.Holds (fun u => ι (f u))

/-- Choose the first list member satisfying every input claim, and zero if there is none.
The zero result in the empty case carries no assertion of knowledge. -/
def initialExtractor {K E : Type} [Semiring K] [Semiring E] [DecidableEq E]
    {vars lanes : ℕ} {enc : Encoding K vars} (decoder : ListDecoder (E := K) enc lanes)
    (ι : K →+* E) (word : Word K lanes (2 ^ (vars + enc.rate)))
    (claims : List (Claim E (lanes + vars))) : Table K (lanes + vars) :=
  match (decoder.decode word).find? (fun f =>
    claims.all fun c => decide (c.Holds (fun u => ι (f u)))) with
  | some f => f
  | none => 0

/-- If the input opening relation holds, the named total choice returns a valid witness. -/
theorem initialExtractor_holds {K E : Type} [Semiring K] [Semiring E]
    [DecidableEq K] [DecidableEq E] {vars lanes : ℕ} {enc : Encoding K vars}
    (decoder : ListDecoder (E := K) enc lanes) (γ L : ℝ)
    (correct : decoder.Correct (RingHom.id K) γ L) (ι : K →+* E)
    (word : Word K lanes (2 ^ (vars + enc.rate)))
    (claims : List (Claim E (lanes + vars)))
    (exists_witness : ∃ f, (initialState enc ι γ word claims).holds f) :
    (initialState enc ι γ word claims).holds (initialExtractor decoder ι word claims) := by
  sorry

/-- At a round boundary, a decoded current message is close and satisfies the running claims. -/
def candidateState {K E : Type} [Semiring K] [Semiring E] [DecidableEq E]
    {vars lanes : ℕ} (enc : Encoding K vars) (ι : K →+* E) (γ : ℝ)
    (word : Word E lanes (2 ^ (vars + enc.rate)))
    (claims : List (Claim E (lanes + vars))) (active : Bool) : KnowledgeState where
  Witness := Table E (lanes + vars)
  holds f := active = true ∧ Close γ word (enc.interleave ι f) ∧
    ∀ c ∈ claims, c.Holds f

/-- The requested stronger state retains an original message and its explicit folded view. -/
def retainedState {K E : Type} [Semiring K] [Semiring E] [DecidableEq E]
    {original vars lanes : ℕ} (enc : Encoding K vars) (ι : K →+* E) (γ : ℝ)
    (word : Word E lanes (2 ^ (vars + enc.rate)))
    (claims : List (Claim E (lanes + vars))) (active : Bool)
    (view : Table K original → Table E (lanes + vars)) : KnowledgeState where
  Witness := Table K original
  holds f := (candidateState enc ι γ word claims active).holds (view f)

/-- The complement of Annex B's post-OOD invariant needs an old candidate or a collision pair.
The new list is fixed before `z`; the answer and queries have not yet been sent. -/
def oodState {E : Type} [CommRing E] {n : ℕ} (old : Table E n → Prop)
    (newList : List (Table E n)) (z : Fin n → E) (active : Bool) : KnowledgeState where
  Witness := Sum (Table E n) (Table E n × Table E n)
  holds w := active = true ∧ match w with
    | .inl f => old f
    | .inr (f, g) => f ∈ newList ∧ g ∈ newList ∧ f ≠ g ∧ mle f z = mle g z

/-- Predicates on the same witness carrier at every authored node of an oracle tree. -/
def RetainedStates (W : Type) : Oracle.TypeTree.{0} → Type
  | .done => W → Prop
  | .public Moves next => (W → Prop) × ((move : Moves) → RetainedStates W (next move))
  | .oracle Messages next => (W → Prop) ×
      ((message : Messages) → RetainedStates W (next PUnit.unit))

/-- The input predicate of a retained-witness annotation. -/
def RetainedStates.predicate {W : Type} : {tree : Oracle.TypeTree} →
    RetainedStates W tree → W → Prop
  | .done, states => states
  | .public _ _, states => states.1
  | .oracle _ _, states => states.1

/-- The input carrier is definitionally the original witness type. -/
def RetainedStates.input {W : Type} {tree : Oracle.TypeTree}
    (states : RetainedStates W tree) : KnowledgeState :=
  ⟨W, states.predicate⟩

/-- Named total backward maps retain the original witness through the entire actual tree. -/
def retainedExtractor {W : Type} : {tree : Oracle.TypeTree} →
    (states : RetainedStates W tree) → RoundExtractor tree states.input
  | .done, _ => PUnit.unit
  | .public _ _, states => fun move =>
      ⟨(states.2 move).input, id, retainedExtractor (states.2 move)⟩
  | .oracle _ _, states => fun message =>
      ⟨(states.2 message).input, id, retainedExtractor (states.2 message)⟩

/-- Put an original witness in the terminal carrier, independently of its knowledge predicate. -/
def retainedTerminalSeed {W : Type} : {tree : Oracle.TypeTree} →
    (states : RetainedStates W tree) → (path : tree.ExecutionPath) →
      W → ((retainedExtractor states).terminalState path).Witness
  | .done, _, _, witness => witness
  | .public _ _, states, path, witness => retainedTerminalSeed (states.2 path.1) path.2 witness
  | .oracle _ _, states, path, witness => retainedTerminalSeed (states.2 path.1) path.2 witness

/-- Backward extraction on the retained terminal carrier returns the supplied message. -/
theorem extract_retainedTerminalSeed {W : Type} {tree : Oracle.TypeTree}
    (states : RetainedStates W tree) (path : tree.ExecutionPath) (witness : W) :
    (retainedExtractor states).extractWitness path (retainedTerminalSeed states path witness) =
      witness := by
  sorry

/-- The base-field decoder for exactly the head encoding of the authored schedule. -/
def InitialDecoder {K : Type} : {n : ℕ} → Schedule K n → Type
  | _, .last lanes _ enc _ => ListDecoder (E := K) enc lanes
  | _, .more lanes enc _ _ => ListDecoder (E := K) enc lanes

/-- Input proximity and claims use the schedule's head encoding and its analysis radius. -/
def openingState {K E : Type} [Semiring K] [Semiring E] [DecidableEq K]
    (ι : K →+* E) {n : ℕ} (s : Schedule K n) (sec : SecurityParameters s)
    (word : oracleMessage K s) (claims : List (Claim E n)) : KnowledgeState where
  Witness := Table K n
  holds := match s, sec, word, claims with
    | .last _ _ enc _, sec, word, claims =>
        (initialState enc ι (radius enc sec) word claims).holds
    | .more _ enc _ _, sec, word, claims =>
        (initialState enc ι (radius enc sec.1) word claims).holds

/-- Run the named initial extractor for the actual schedule's head encoder. -/
def selectInitial {K E : Type} [Semiring K] [Semiring E] [DecidableEq E]
    (ι : K →+* E) : {n : ℕ} → (s : Schedule K n) → InitialDecoder s →
      oracleMessage K s → List (Claim E n) → Table K n
  | _, .last _ _ _ _, decoder, word, claims => initialExtractor decoder ι word claims
  | _, .more _ _ _ _, decoder, word, claims => initialExtractor decoder ι word claims

/-- The intended opening certificate and terminal acceptance transfer, explicitly left as a goal.
`states` must annotate the protocol with the specified proximity/claim states; an arbitrary
annotation satisfying this proposition is not a WHIR knowledge theorem. -/
def OpeningCertificateGoal {K E : Type} [Semiring K] [CommRing E]
    [DecidableEq K] [DecidableEq E] [Fintype E] [SampleableType E]
    (ι : K →+* E) {n : ℕ} (s : Schedule K n) (sec : SecurityParameters s)
    (word : oracleMessage K s) (claims : List (Claim E n)) (decoder : InitialDecoder s)
    (states : RetainedStates (Table K n) (opening E s).tree) : Prop :=
  states.input = openingState ι s sec word claims ∧
    ∃ certificate : KnowledgeCertificate (opening E s).tree (opening E s).roles states.input,
      certificate.extractor = retainedExtractor states ∧
      certificate.challenges = challenges (E := E) s sec claims.length ∧
      ∀ path, accepts ι s (fun x u => ι (word x u)) claims path = true →
        ((retainedExtractor states).terminalState path).holds
          (retainedTerminalSeed states path (selectInitial ι s decoder word claims))

/-- A test fold retaining every affine preimage, with zero as the only initially known message. -/
def affineRetentionExtractor (E : Type) [Semiring E] :
    RoundExtractor (.public E fun _ => .done)
      (⟨E × E, fun f => f = (0, 0)⟩ : KnowledgeState) :=
  fun r => ⟨⟨E × E, fun f => f.1 + r * f.2 = 0⟩, id, PUnit.unit⟩

/-- Every challenge admits a nonzero affine preimage of zero under identity retention.
The witness `(-r, 1)` depends on the fresh challenge inside the existential bad event. -/
theorem affineRetention_badChallenge {E : Type} [Ring E] [Nontrivial E] (r : E) :
    (affineRetentionExtractor E).badChallenge r := by
  sorry

/-- Unrestricted identity retention has bad-challenge probability one, rather than an MCA loss. -/
theorem prob_affineRetention_badChallenge {E : Type} [Ring E] [Nontrivial E] [SampleableType E] :
    Pr{let r ←$ᵗ E}[(affineRetentionExtractor E).badChallenge r] = 1 := by
  sorry

end Whir
