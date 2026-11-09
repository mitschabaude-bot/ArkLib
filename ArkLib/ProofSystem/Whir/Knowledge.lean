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
Every level uses a supplied executable decoder, including all intermediate fold row counts.
Proximity predicates are proof-only inputs; real-valued security data belongs to analysis.

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
  decode : MaskedWord E lanes (2 ^ (vars + enc.rate)) → List (Table E (lanes + vars))
  /-- Materialize candidate encodings before comparing their columns. -/
  encodeColumns : Table E (lanes + vars) → Vector (Cube lanes → E) (2 ^ (vars + enc.rate))

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
  /-- Every materialized column equals the mathematical interleaved encoding. -/
  encodeColumns_eq : ∀ f x, (decoder.encodeColumns f)[x.val] = enc.interleave ι f x

/-- Filter a zero-filled decoder's output using an executable absolute agreement cutoff. -/
def ListDecoder.ofZeroFill {K E : Type} [Semiring K] [Semiring E] [DecidableEq E]
    {vars lanes : ℕ} {enc : Encoding K vars} (ι : K →+* E) (cutoff : ℕ)
    (decode : Word E lanes (2 ^ (vars + enc.rate)) → List (Table E (lanes + vars))) :
    ListDecoder (E := E) enc lanes where
  encodeColumns f := Vector.ofFn (enc.interleave ι f)
  decode word := (decode (zeroFill word)).filter fun f =>
    decide (cutoff ≤ (agreement word (enc.interleave ι f)).card)

/-- Zero-fill decoding followed by masked filtering preserves the certified list contract. -/
theorem ListDecoder.ofZeroFill_correct {K E : Type} [Semiring K] [Semiring E] [DecidableEq E]
    {vars lanes : ℕ} {enc : Encoding K vars} (ι : K →+* E)
    (decode : Word E lanes (2 ^ (vars + enc.rate)) → List (Table E (lanes + vars)))
    (γ L : ℝ)
    (nodup : ∀ word, (decode word).Nodup)
    (mem : ∀ word f, f ∈ decode word ↔ Close γ (fullWord word) (enc.interleave ι f))
    (length : ∀ word, ((decode word).length : ℝ) ≤ L) :
    (ListDecoder.ofZeroFill ι ⌈(1 - γ) * (2 ^ (vars + enc.rate) : ℕ)⌉₊ decode).Correct ι γ L := by
  refine ⟨fun word => (nodup _).filter _, ?_, ?_, ?_⟩
  · intro word f
    simp only [ListDecoder.ofZeroFill, List.mem_filter, decide_eq_true_eq, mem, ← close_iff_cutoff]
    exact ⟨fun h => h.2, fun h => ⟨Close.zeroFill h, h⟩⟩
  · intro word
    have h : ((ListDecoder.ofZeroFill ι
        ⌈(1 - γ) * (2 ^ (vars + enc.rate) : ℕ)⌉₊ decode).decode word).length ≤
        (decode (zeroFill word)).length := List.length_filter_le _ _
    exact (Nat.cast_le.mpr h).trans (length (zeroFill word))
  · intro f x
    simp only [ListDecoder.ofZeroFill, Vector.getElem_ofFn]

/-- Hiding columns only shrinks every certified decoder list. -/
theorem ListDecoder.mem_mono {K E : Type} [Semiring K] [Semiring E] [DecidableEq E]
    {vars lanes : ℕ} {enc : Encoding K vars} (decoder : ListDecoder (E := E) enc lanes)
    (ι : K →+* E) (γ L : ℝ) (correct : decoder.Correct ι γ L)
    {small large : MaskedWord E lanes (2 ^ (vars + enc.rate))} (h : MaskLE small large)
    {f : Table E (lanes + vars)} (hf : f ∈ decoder.decode small) : f ∈ decoder.decode large :=
  (correct.mem_iff _ _).mpr (((correct.mem_iff _ _).mp hf).mono h)

/-- The opening relation has the original base-field multilinear as its witness. -/
def initialState {K E : Type} [Semiring K] [Semiring E] [DecidableEq K]
    {vars lanes : ℕ} (enc : Encoding K vars) (ι : K →+* E) (γ : ℝ)
    (word : MaskedWord K lanes (2 ^ (vars + enc.rate)))
    (claims : List (Claim E (lanes + vars))) : KnowledgeState where
  Witness := Table K (lanes + vars)
  holds f := Close γ word (enc.interleave (RingHom.id K) f) ∧
    ∀ c ∈ claims, c.Holds (fun u => ι (f u))

/-- Choose the first list member satisfying every input claim, and zero if there is none.
The zero result in the empty case carries no assertion of knowledge. -/
def initialExtractor {K E : Type} [Semiring K] [Semiring E] [DecidableEq E]
    {vars lanes : ℕ} {enc : Encoding K vars} (decoder : ListDecoder (E := K) enc lanes)
    (ι : K →+* E) (word : MaskedWord K lanes (2 ^ (vars + enc.rate)))
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
    (word : MaskedWord K lanes (2 ^ (vars + enc.rate)))
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
    (word : MaskedWord E lanes (2 ^ (vars + enc.rate)))
    (claims : List (Claim E (lanes + vars))) (active : Bool) : KnowledgeState where
  Witness := Table E (lanes + vars)
  holds f := active = true ∧ Close γ word (enc.interleave ι f) ∧
    ∀ c ∈ claims, c.Holds f

/-- A word-to-message relation with active checks and accumulated claims. -/
def relationState {E : Type} [Semiring E] {vars lanes columns : ℕ}
    (nearby : MaskedWord E lanes columns → Table E (lanes + vars) → Prop)
    (word : MaskedWord E lanes columns) (claims : List (Claim E (lanes + vars)))
    (active : Bool) : KnowledgeState where
  Witness := Table E (lanes + vars)
  holds f := active = true ∧ nearby word f ∧ ∀ c ∈ claims, c.Holds f

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

/-- Prefer the first valid list preimage, then the first preimage, then zero. -/
def listLift {E : Type} [Zero E] [DecidableEq E] {n m : ℕ}
    (candidates : List (Table E n)) (view : Table E n → Table E m)
    (valid : Table E n → Prop) [DecidablePred valid] (successor : Table E m) : Table E n :=
  match candidates.find? (fun f => decide (view f = successor ∧ valid f)) with
  | some f => f
  | none => (candidates.find? (fun f => decide (view f = successor))).getD 0

/-- Executable decoders for every level and every intermediate fold row count. -/
def DecoderFamily {K E : Type} : {n : ℕ} → Schedule K n → Type
  | _, .last _ _ enc _ => (lanes : ℕ) → ListDecoder (E := E) enc lanes
  | _, .more _ enc _ rest =>
      ((lanes : ℕ) → ListDecoder (E := E) enc lanes) × DecoderFamily (E := E) rest

/-- Proof-only proximity predicates indexed by level and intermediate row count. -/
abbrev ProximityFamily (K E : Type) := (level : ℕ) → {vars : ℕ} → (enc : Encoding K vars) →
  (lanes : ℕ) → MaskedWord E lanes (2 ^ (vars + enc.rate)) → Table E (lanes + vars) → Prop

/-- The security parameters at a level, with the final level used beyond the schedule. -/
def securityAt {K : Type} : {n : ℕ} → (s : Schedule K n) → SecurityParameters s →
    ℕ → LevelSecurity
  | _, .last _ _ _ _, sec, _ => sec
  | _, .more _ _ _ _, sec, 0 => sec.1
  | _, .more _ _ _ rest, sec, level + 1 => securityAt rest sec.2 level

/-- The analytical proximity family; real arithmetic occurs only inside predicates. -/
def proximityFamily {K E : Type} [Semiring K] [Semiring E] [DecidableEq E]
    (ι : K →+* E) {n : ℕ} (s : Schedule K n) (sec : SecurityParameters s) :
    ProximityFamily K E :=
  fun level _ enc _ word f => Close (radius enc (securityAt s sec level)) word (enc.interleave ι f)

/-- The head relation with activity and accumulated claims. -/
def relationLevelState {K E : Type} [Semiring E] {n : ℕ}
    (s : Schedule K n) (nearby : ProximityFamily K E) (word : oracleMessage E s)
    (claims : List (Claim E n)) (active : Bool) : KnowledgeState where
  Witness := Table E n
  holds := match s, word, claims with
    | .last lanes _ enc _, word, claims =>
        (relationState (nearby 0 enc lanes) word claims active).holds
    | .more lanes enc _ _, word, claims =>
        (relationState (nearby 0 enc lanes) word claims active).holds

/-- The analytical head relation with accumulated verifier checks. -/
abbrev levelState {K E : Type} [Semiring K] [Semiring E] [DecidableEq E]
    (ι : K →+* E) {n : ℕ} (s : Schedule K n) (sec : SecurityParameters s)
    (word : oracleMessage E s) (claims : List (Claim E n)) (active : Bool) : KnowledgeState :=
  relationLevelState s (proximityFamily ι s sec) word claims active

/-- Exact coverage and cardinality for each decoder at its level's analysis radius. -/
def DecoderFamily.Correct {K E : Type} [Semiring K] [Semiring E] [DecidableEq E]
    (ι : K →+* E) : {n : ℕ} → (s : Schedule K n) →
      DecoderFamily (E := E) s → SecurityParameters s → Prop
  | _, .last _ _ enc _, decoders, sec =>
      ∀ lanes, (decoders lanes).Correct ι (radius enc sec) (listBound enc sec)
  | _, .more _ enc _ rest, decoders, sec =>
      (∀ lanes, (decoders.1 lanes).Correct ι (radius enc sec.1) (listBound enc sec.1)) ∧
        DecoderFamily.Correct ι rest decoders.2 sec.2

/-- The supplied head decoder's ordered candidate list. -/
def levelList {K E : Type} : {n : ℕ} → (s : Schedule K n) →
    DecoderFamily (E := E) s → oracleMessage E s → List (Table E n)
  | _, .last lanes _ _ _, decoders, word => (decoders lanes).decode word
  | _, .more lanes _ _ _, decoders, word => (decoders.1 lanes).decode word

/-- The decoder correctness premise at the actual initial encoding and analysis radius. -/
def InitialDecoder.Correct {K : Type} [Semiring K] [DecidableEq K] :
    {n : ℕ} → {s : Schedule K n} → InitialDecoder s → SecurityParameters s → Prop
  | _, .last _ _ enc _, decoder, sec =>
      ListDecoder.Correct decoder (RingHom.id K) (radius enc sec) (listBound enc sec)
  | _, .more _ enc _ _, decoder, sec =>
      ListDecoder.Correct decoder (RingHom.id K) (radius enc sec.1) (listBound enc sec.1)

end Whir
