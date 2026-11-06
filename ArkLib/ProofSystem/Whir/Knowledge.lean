/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.ProofSystem.Whir.Errors

/-!
# WHIR list witnesses and total backward choices

The witness at an encoded prefix is a polynomial for the current, possibly virtual, word.
`listLift` prefers a preimage satisfying the current claims, then any list preimage, then zero.
`nearbyDecoder` is a classical finite enumeration for analysis; `initialExtractor` uses the
supplied executable base-field decoder. Decoder efficiency is a separate obligation.

## Open obligations

- Dimension-one MCA requires a separate bound.
- CompPoly's strict `< r` domain hypothesis requires an adapter.
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
  obtain ⟨f, hf, hclaims⟩ := exists_witness
  unfold initialExtractor
  split
  · rename_i g hg
    exact ⟨(correct.mem_iff word g).mp (List.mem_of_find?_eq_some hg),
      by simpa only [List.all_eq_true, decide_eq_true_eq] using List.find?_some hg⟩
  · rename_i hn
    have absent := List.find?_eq_none.mp hn f ((correct.mem_iff word f).mpr hf)
    exact (absent (by simpa only [List.all_eq_true, decide_eq_true_eq] using hclaims)).elim

/-- At a round boundary, a decoded current message is close and satisfies the running claims. -/
def candidateState {K E : Type} [Semiring K] [Semiring E] [DecidableEq E]
    {vars lanes : ℕ} (enc : Encoding K vars) (ι : K →+* E) (γ : ℝ)
    (word : Word E lanes (2 ^ (vars + enc.rate)))
    (claims : List (Claim E (lanes + vars))) (active : Bool) : KnowledgeState where
  Witness := Table E (lanes + vars)
  holds f := active = true ∧ Close γ word (enc.interleave ι f) ∧
    ∀ c ∈ claims, c.Holds f

/-- The complement of Annex B's post-OOD invariant needs an old candidate or a collision pair.
The new list is fixed before `z`; the answer and queries have not yet been sent. -/
def oodState {E : Type} [CommRing E] {n : ℕ} (old : Table E n → Prop)
    (newList : List (Table E n)) (z : Fin n → E) (active : Bool) : KnowledgeState where
  Witness := Sum (Table E n) (Table E n × Table E n)
  holds w := active = true ∧ match w with
    | .inl f => old f
    | .inr (f, g) => f ∈ newList ∧ g ∈ newList ∧ f ≠ g ∧ mle f z = mle g z

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

/-- Exhaustive classical proximity enumeration; an efficient decoder can refine this list. -/
noncomputable def nearbyDecoder {K E : Type} [Semiring K] [Semiring E] [Fintype E]
    [DecidableEq E] {vars : ℕ} (enc : Encoding K vars) (ι : K →+* E) (γ : ℝ)
    (lanes : ℕ) : ListDecoder (E := E) enc lanes := by
  classical
  exact ⟨fun word => (Finset.univ.filter fun f => Close γ word (enc.interleave ι f)).toList⟩

/-- Prefer a valid list preimage, then any list preimage, then the fixed zero polynomial.
Classical choice supplies total backward maps without an efficiency assertion. -/
noncomputable def listLift {E : Type} [Zero E] {n m : ℕ}
    (candidates : List (Table E n)) (view : Table E n → Table E m)
    (valid : Table E n → Prop) (successor : Table E m) : Table E n := by
  classical
  exact if good : ∃ f ∈ candidates, view f = successor ∧ valid f then
    Classical.choose good
  else if preimage : ∃ f ∈ candidates, view f = successor then
    Classical.choose preimage
  else 0

/-- The knowledge predicate for the head encoded level, including accumulated verifier checks. -/
def levelState {K E : Type} [Semiring K] [Semiring E] [DecidableEq E]
    (ι : K →+* E) {n : ℕ} (s : Schedule K n) (sec : SecurityParameters s)
    (word : oracleMessage E s) (claims : List (Claim E n)) (active : Bool) :
    KnowledgeState where
  Witness := Table E n
  holds := match s, sec, word, claims with
    | .last _ _ enc _, sec, word, claims =>
        (candidateState enc ι (radius enc sec) word claims active).holds
    | .more _ enc _ _, sec, word, claims =>
        (candidateState enc ι (radius enc sec.1) word claims active).holds

/-- The exact head list of a schedule at its analysis radius. -/
noncomputable def levelList {K E : Type} [Semiring K] [Semiring E]
    [Fintype E] [DecidableEq E] (ι : K →+* E) :
    {n : ℕ} → (s : Schedule K n) → SecurityParameters s →
      oracleMessage E s → List (Table E n)
  | _, .last lanes _ enc _, sec, word =>
      (nearbyDecoder enc ι (radius enc sec) lanes).decode word
  | _, .more lanes enc _ _, sec, word =>
      (nearbyDecoder enc ι (radius enc sec.1) lanes).decode word

/-- The decoder correctness premise at the actual initial encoding and analysis radius. -/
def InitialDecoder.Correct {K : Type} [Semiring K] [DecidableEq K] :
    {n : ℕ} → {s : Schedule K n} → InitialDecoder s → SecurityParameters s → Prop
  | _, .last _ _ enc _, decoder, sec =>
      ListDecoder.Correct decoder (RingHom.id K) (radius enc sec) (listBound enc sec)
  | _, .more _ enc _ _, decoder, sec =>
      ListDecoder.Correct decoder (RingHom.id K) (radius enc sec.1) (listBound enc sec.1)

end Whir
