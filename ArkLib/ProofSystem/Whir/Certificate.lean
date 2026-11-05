/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.ProofSystem.Whir.LocalBounds
public import ArkLib.ProofSystem.Sumcheck.Interaction.Knowledge

/-!
# List-lifting WHIR opening knowledge certificate

Each encoded state concerns the current word. Batching and folding lift successor polynomials
through its proximity list, preferring preimages satisfying the old claims. At a level boundary,
the OOD state carries either an old polynomial or a colliding pair from the new list. After a
separating OOD point, the answer fixes the candidate before queries. The final plaintext is fixed
before queries and closing Sumcheck. Only the root map selects a base-field input polynomial.

With `q = |E|`, the local error schedule is:

| Message | Local error |
| --- | --- |
| Batching at level i | `(J_i - 1)L_i/q` |
| Each fold at level i | `2L_i/q + ε_i` |
| OOD entering level i ≥ 1 | `binom(L_i,2)n_i/q` |
| Queries at level i | `(1 - γ_i)^t_i` |
| Final batching | `t_last/q` |
| Each closing Sumcheck round | `2/q` |

`certificate` supplies concrete maps and the concrete uniform challenge schedule; its
prover-preservation and local probability obligations are statements only.

## Open obligations

- Dimension-one MCA requires a separate bound.
- CompPoly's strict `< r` domain hypothesis requires an adapter.
- The compressed wire format requires a protocol refinement.
-/

@[expose] public section

open Interaction Interaction.Oracle Interaction.Oracle.Security OracleComp OracleSpec

namespace Whir

/-- A fixed plaintext candidate satisfies the running claims and all preceding checks. -/
def plaintextState {E : Type} [Semiring E] {n : ℕ} (candidate : Table E n)
    (claims : List (Claim E n)) (active : Bool) : KnowledgeState where
  Witness := PUnit
  holds _ := active = true ∧ ∀ c ∈ claims, c.Holds candidate

/-- Closing Sumcheck restricts a fixed plaintext and weight; the terminal carrier is `PUnit`. -/
def closingExtractor {E : Type} [CommRing E] [DecidableEq E] :
    (count : ℕ) → (candidate : Table E count) → (claim : Claim E count) → (active : Bool) →
      RoundExtractor (scalarRounds E count .done).tree
        (plaintextState candidate [claim] active)
  | 0, _, _, _ => PUnit.unit
  | count + 1, candidate, claim, active => fun q =>
      let checked := active && decide (evalQuadratic q 0 + evalQuadratic q 1 = claim.value)
      ⟨plaintextState candidate [claim] checked, id, fun r =>
        ⟨plaintextState (foldMessageOne (vars := 0) candidate r)
          [⟨foldMessageOne (vars := 0) claim.weight r, evalQuadratic q r⟩] checked,
          id, closingExtractor count (foldMessageOne (vars := 0) candidate r)
            ⟨foldMessageOne (vars := 0) claim.weight r, evalQuadratic q r⟩ checked⟩⟩

/-- Final power batching has a fixed candidate, followed by its closing Sumcheck. -/
def finalBatchExtractor {E : Type} [CommRing E] [DecidableEq E] {n : ℕ}
    (candidate : Table E n) (claims : List (Claim E n)) (active : Bool) :
    RoundExtractor (.public E fun _ => (scalarRounds E n .done).tree)
      (plaintextState candidate claims active) :=
  fun r => ⟨plaintextState candidate [batch claims r] active, id,
    closingExtractor n candidate (batch claims r) active⟩

/-- Each fold lifts from the current folded list, preferring a claim-satisfying preimage. -/
noncomputable def foldExtractor {K E : Type} [Semiring K] [CommRing E] [DecidableEq E]
    [Fintype E] {vars : ℕ} (enc : Encoding K vars) (ι : K →+* E) (γ : ℝ)
    {rest : Protocol}
    (finish : (word : Word E 0 (2 ^ (vars + enc.rate))) →
      (claim : Claim E (0 + vars)) → (active : Bool) →
      RoundExtractor rest.tree (candidateState enc ι γ word [claim] active)) :
    (lanes : ℕ) → (word : Word E lanes (2 ^ (vars + enc.rate))) →
      (claim : Claim E (lanes + vars)) → (active : Bool) →
      RoundExtractor (scalarRounds E lanes rest).tree
        (candidateState enc ι γ word [claim] active)
  | 0, word, claim, active => finish word claim active
  | lanes + 1, word, claim, active => fun q =>
      let checked := active && decide (evalQuadratic q 0 + evalQuadratic q 1 = claim.value)
      ⟨candidateState enc ι γ word [claim] checked, id, fun r =>
        let word' := foldRowsOne word r
        let claim' : Claim E (lanes + vars) :=
          ⟨foldMessageOne claim.weight r, evalQuadratic q r⟩
        ⟨candidateState enc ι γ word' [claim'] checked,
          listLift ((nearbyDecoder enc ι γ (lanes + 1)).decode word)
            (fun f => foldMessageOne f r) claim.Holds,
          foldExtractor enc ι γ finish lanes word' claim' checked⟩⟩

/-- After a plaintext message, knowledge means that this fixed table was an old-list member. -/
def plaintextProximityState {K E : Type} [Semiring K] [Semiring E] [DecidableEq E]
    {tail : ℕ} (enc : Encoding K tail) (ι : K →+* E) (γ : ℝ)
    (word : Word E 0 (2 ^ (tail + enc.rate))) (claim : Claim E (0 + tail))
    (candidate : Table E tail) (active : Bool) : KnowledgeState where
  Witness := PUnit
  holds _ := (candidateState enc ι γ word [claim] active).holds
    (castTable (Nat.zero_add tail).symm candidate)

/-- The last-level message lifts the fixed plaintext; queries then test that one candidate. -/
noncomputable def lastExtractor {K E : Type} [Semiring K] [CommRing E] [DecidableEq E]
    [Fintype E] {tail : ℕ} (lanes queries : ℕ) (enc : Encoding K tail) (ι : K →+* E)
    (sec : LevelSecurity) (word : Word E 0 (2 ^ (tail + enc.rate)))
    (claim : Claim E (0 + tail)) (active : Bool) :
    RoundExtractor (transition E (.last lanes tail enc queries)).tree
      (candidateState enc ι (radius enc sec) word [claim] active) :=
  fun candidate =>
    ⟨plaintextProximityState enc ι (radius enc sec) word claim candidate active,
      (fun _ => listLift ((nearbyDecoder enc ι (radius enc sec) 0).decode word)
        (castTable (Nat.zero_add tail)) claim.Holds candidate), fun xs =>
      let claims : List (Claim E tail) :=
        ⟨castTable (Nat.zero_add tail) claim.weight, claim.value⟩ ::
          List.ofFn (fun q : Fin queries =>
            ⟨fun u => ι (enc.weight (xs q) u), word (xs q) Fin.elim0⟩)
      ⟨plaintextState candidate claims active, (fun _ => PUnit.unit),
        finalBatchExtractor candidate claims active⟩⟩

/-- The collision predicate uses only the new oracle and the OOD point, before its answer. -/
def OodCollision {E : Type} [CommRing E] {n : ℕ}
    (candidates : List (Table E n)) (z : Fin n → E) : Prop :=
  ∃ f ∈ candidates, ∃ g ∈ candidates, f ≠ g ∧ mle f z = mle g z

/-- The OOD answer fixes this candidate before the independent query vector is sampled. -/
noncomputable def oodCandidate {E : Type} [CommRing E] {n : ℕ}
    (candidates : List (Table E n)) (z : Fin n → E) (answer : E) : Table E n := by
  classical
  exact if exists_answer : ∃ f ∈ candidates, mle f z = answer then
    Classical.choose exists_answer
  else 0

/-- OOD backward failure is contained entirely in the new-list collision event. -/
theorem ood_lift_failure_subset {E : Type} [CommRing E] {n : ℕ}
    (old : Table E n → Prop) (candidates : List (Table E n))
    (z : Fin n → E) (active : Bool)
    (bad : ∃ witness, (oodState old candidates z active).holds witness ∧
      ¬ (active = true ∧ old (match witness with | .inl f => f | .inr _ => 0))) :
    OodCollision candidates z := by
  sorry

/-- Lift by polynomial equality when an old-list preimage exists; otherwise carry a collision.
The remaining case returns the image of the fixed zero default. -/
noncomputable def boundaryLift {E : Type} [CommRing E] {n m : ℕ}
    (oldList : List (Table E m)) (view : Table E m → Table E n)
    (valid : Table E m → Prop) (newList : List (Table E n)) (z : Fin n → E)
    (successor : Table E n) : Sum (Table E n) (Table E n × Table E n) := by
  classical
  exact if ∃ f ∈ oldList, view f = successor then
    .inl (view (listLift oldList view valid successor))
  else if collision : OodCollision newList z then
    let f := Classical.choose collision
    let g := Classical.choose (Classical.choose_spec collision).2
    .inr (f, g)
  else .inl (view 0)

/-- A level boundary returns the identical polynomial whenever the old list contains it. -/
theorem boundaryLift_of_preimage {E : Type} [CommRing E] {n m : ℕ}
    (oldList : List (Table E m)) (view : Table E m → Table E n)
    (valid : Table E m → Prop) (newList : List (Table E n)) (z : Fin n → E)
    (successor : Table E n) (preimage : ∃ f ∈ oldList, view f = successor) :
    boundaryLift oldList view valid newList z successor = .inl successor := by
  sorry

/-- A failed query lift is a far fixed candidate passing every sampled consistency check.
The candidate depends on the new list, OOD point and answer, but not on `xs`. -/
theorem boundary_query_failure_subset {K E : Type} [Semiring K] [CommRing E]
    [DecidableEq E] {tail queries : ℕ} (enc : Encoding K tail) (ι : K →+* E) (γ L : ℝ)
    (decoder : ListDecoder (E := E) enc 0) (correct : decoder.Correct ι γ L)
    (word : Word E 0 (2 ^ (tail + enc.rate))) (claim : Claim E (0 + tail))
    (candidates : List (Table E tail)) (z : Fin tail → E) (answer : E)
    (xs : Fin queries → enc.Columns) (active : Bool)
    (bad : ∃ f ∈ candidates, active = true ∧
      claim.Holds (castTable (Nat.zero_add tail).symm f) ∧ mle f z = answer ∧
      (∀ q, word (xs q) Fin.elim0 = enc.encode ι f (xs q)) ∧
      ¬ (oodState (fun g => (candidateState enc ι γ word [claim] active).holds
          (castTable (Nat.zero_add tail).symm g)) candidates z active).holds
        (boundaryLift (decoder.decode word) (castTable (Nat.zero_add tail))
          claim.Holds candidates z f)) :
    ¬ Close γ word (enc.interleave ι
      (castTable (Nat.zero_add tail).symm (oodCandidate candidates z answer))) ∧
    ∀ q, word (xs q) Fin.elim0 = enc.encode ι (oodCandidate candidates z answer) (xs q) := by
  sorry

/-- A new oracle preserves the old state; OOD introduces collisions and queries lift equality. -/
noncomputable def boundaryExtractor {K E : Type} [Semiring K] [CommRing E]
    [DecidableEq E] [Fintype E] {tail : ℕ} (lanes queries : ℕ) (enc : Encoding K tail)
    (ι : K →+* E) (sec : LevelSecurity) (rest : Schedule K tail)
    (nextSec : SecurityParameters rest)
    (suffixExtractor : (word : oracleMessage E rest) → (claims : List (Claim E tail)) →
      (active : Bool) → RoundExtractor (opening E rest).tree
        (levelState ι rest nextSec word claims active))
    (word : Word E 0 (2 ^ (tail + enc.rate))) (claim : Claim E (0 + tail))
    (active : Bool) :
    RoundExtractor (transition E (.more lanes enc queries rest)).tree
      (candidateState enc ι (radius enc sec) word [claim] active) :=
  fun nextWord =>
    let oldState := candidateState enc ι (radius enc sec) word [claim] active
    let old := fun f : Table E tail => oldState.holds (castTable (Nat.zero_add tail).symm f)
    let newList := levelList ι rest nextSec nextWord
    ⟨oldState, id, fun z =>
      let separatedState := oodState old newList z active
      ⟨separatedState, (fun w => match w with
        | .inl f => castTable (Nat.zero_add tail).symm f
        | .inr _ => (0 : Table E (0 + tail))), fun answer =>
        ⟨separatedState, id, fun xs =>
          let residual : Claim E tail :=
            ⟨castTable (Nat.zero_add tail) claim.weight, claim.value⟩
          let claims := nextClaims enc ι residual z answer xs (fun x => word x Fin.elim0)
          ⟨levelState ι rest nextSec nextWord claims active,
            boundaryLift ((nearbyDecoder enc ι (radius enc sec) 0).decode word)
              (castTable (Nat.zero_add tail)) claim.Holds newList z,
            suffixExtractor nextWord claims active⟩⟩⟩⟩

/-- The E-valued opening lifts the current witness through each batching and fold challenge. -/
noncomputable def levelExtractor {K E : Type} [Semiring K] [CommRing E]
    [DecidableEq E] [Fintype E] (ι : K →+* E) :
    {n : ℕ} → (s : Schedule K n) → (sec : SecurityParameters s) →
      (word : oracleMessage E s) → (claims : List (Claim E n)) → (active : Bool) →
      RoundExtractor (opening E s).tree (levelState ι s sec word claims active)
  | _, .last lanes tail enc queries, sec, word, claims, active => fun r =>
      ⟨candidateState enc ι (radius enc sec) word [batch claims r] active,
        listLift ((nearbyDecoder enc ι (radius enc sec) lanes).decode word) id
          (fun f => ∀ c ∈ claims, c.Holds f),
        foldExtractor enc ι (radius enc sec)
          (lastExtractor lanes queries enc ι sec) lanes word (batch claims r) active⟩
  | _, .more lanes enc queries rest, sec, word, claims, active => fun r =>
      ⟨candidateState enc ι (radius enc sec.1) word [batch claims r] active,
        listLift ((nearbyDecoder enc ι (radius enc sec.1) lanes).decode word) id
          (fun f => ∀ c ∈ claims, c.Holds f),
        foldExtractor enc ι (radius enc sec.1)
          (boundaryExtractor lanes queries enc ι sec.1 rest sec.2
            (levelExtractor ι rest sec.2)) lanes word (batch claims r) active⟩

/-- Replace only the first backward map by a fixed root selection, retaining the concrete suffix. -/
def rootSelection {Moves : Type} {next : Moves → Oracle.TypeTree} {state : KnowledgeState}
    (extractor : RoundExtractor (.public Moves next) state) (input : KnowledgeState)
    (selected : input.Witness) : RoundExtractor (.public Moves next) input :=
  fun move => ⟨(extractor move).1, (fun _ => selected), (extractor move).2.2⟩

/-- The opening's root map is the first satisfying decoded base-field message, else zero. -/
noncomputable def openingExtractor {K E : Type} [Semiring K] [CommRing E]
    [DecidableEq K] [DecidableEq E] [Fintype E] (ι : K →+* E) :
    {n : ℕ} → (s : Schedule K n) → (sec : SecurityParameters s) →
      (word : oracleMessage K s) → (claims : List (Claim E n)) → (decoder : InitialDecoder s) →
      RoundExtractor (opening E s).tree (openingState ι s sec word claims)
  | _, .last lanes tail enc queries, sec, word, claims, decoder =>
      rootSelection (levelExtractor ι (.last lanes tail enc queries) sec
        (fun x u => ι (word x u)) claims true)
        (openingState ι (.last lanes tail enc queries) sec word claims)
        (selectInitial ι (.last lanes tail enc queries) decoder word claims)
  | _, .more lanes enc queries rest, sec, word, claims, decoder =>
      rootSelection (levelExtractor ι (.more lanes enc queries rest) sec
        (fun x u => ι (word x u)) claims true)
        (openingState ι (.more lanes enc queries rest) sec word claims)
        (selectInitial ι (.more lanes enc queries rest) decoder word claims)

/-- WHIR's opening certificate with explicit list-lifting maps and Annex B's local errors. -/
noncomputable def certificate {K E : Type} [Field K] [Field E]
    [DecidableEq K] [DecidableEq E] [Fintype E] [SampleableType E]
    (ι : K →+* E) {n : ℕ} (s : Schedule K n) (sec : SecurityParameters s)
    (valid : s.Valid ι sec) (word : oracleMessage K s) (claims : List (Claim E n))
    (decoder : InitialDecoder s) (correct : InitialDecoder.Correct decoder sec) :
    KnowledgeCertificate (opening E s).tree (opening E s).roles
      (openingState ι s sec word claims) where
  extractor := openingExtractor ι s sec word claims decoder
  challenges := challenges (E := E) s sec claims.length
  prover_preserving := by sorry
  local_bound := by sorry

/-- Acceptance supplies terminal knowledge for the concrete certificate's terminal carrier. -/
theorem accepts_terminal {K E : Type} [Field K] [Field E]
    [DecidableEq K] [DecidableEq E] [Fintype E] [SampleableType E]
    (ι : K →+* E) {n : ℕ} (s : Schedule K n) (sec : SecurityParameters s)
    (valid : s.Valid ι sec) (word : oracleMessage K s) (claims : List (Claim E n))
    (decoder : InitialDecoder s) (correct : InitialDecoder.Correct decoder sec)
    (path : (opening E s).tree.ExecutionPath)
    (accepted : accepts ι s (fun x u => ι (word x u)) claims path = true) :
    ∃ witness, ((certificate ι s sec valid word claims decoder correct).extractor.terminalState
      path).holds witness := by
  sorry

end Whir
