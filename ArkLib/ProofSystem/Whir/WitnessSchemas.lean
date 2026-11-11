/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.Interaction.Oracle.Security.WitnessRefinement
public import ArkLib.ProofSystem.Whir.Certificate

/-! # Executable local bad schemas for WHIR's authenticated masked prefixes -/

@[expose] public section

open Interaction Interaction.Oracle Interaction.Oracle.Security OracleComp OracleSpec
open Interaction.Oracle.Security.StandardBcs

namespace Whir

/-- Field enumeration is confined to analytical propositions and erased bounds. -/
noncomputable local instance {E : Type} [Finite E] : Fintype E := Fintype.ofFinite E

/-- Encoded batching reads a masked word and a public claim list of the scheduled length. -/
def batchSchema {K E : Type} [Field K] [Field E] [DecidableEq E]
    [Finite E] [SampleableType E] {vars lanes : ℕ} (enc : Encoding K vars)
    (ι : K →+* E) (sec : Erased LevelSecurity) (decoder : ListDecoder (E := E) enc lanes)
    (correct : decoder.Correct ι (radius enc sec.out) (listBound enc sec.out)) (count : ℕ) :
    BadSchema E where
  Input := MaskedWord E lanes (2 ^ (vars + enc.rate)) ×
    {claims : List (Claim E (lanes + vars)) // claims.length ≤ count} × Bool
  equality := inferInstance
  isQuery := false
  MaskLE small large := small.2.2 = true → large.2.2 = true ∧
    Whir.MaskLE small.1 large.1 ∧ small.2.1.val = large.2.1.val
  Bad input r := input.2.2 = true ∧ BadBatch ι (radius enc sec.out) input.1 input.2.1.val r
  check input r := input.2.2 && checkBadBatch decoder input.1 input.2.1.val r
  check_iff input r := by
    simp only [Bool.and_eq_true, checkBadBatch_iff ι _ _ decoder correct]
  monotone small large h _ r bad := by
    obtain ⟨active, mask, claims⟩ := h bad.1
    exact ⟨active, claims ▸ bad.2.mono mask⟩
  error := Erased.mk (batchError (E := E) enc sec.out count)
  bad_bound input := by
    simp only [Erased.out_mk]
    refine (prEvent_mono ($ᵗ E) _ _ (fun _ bad => bad.2)).trans ?_
    refine (prob_badBatch_le ι sec.out decoder correct input.1 input.2.1.val).trans ?_
    unfold batchError
    apply ENNReal.ofReal_le_ofReal
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply mul_le_mul_of_nonneg_right _
      ((Nat.cast_nonneg (decoder.decode input.1).length).trans (correct.length_le input.1))
    exact_mod_cast Nat.sub_le_sub_right input.2.1.property 1

/-- Encoded folds combine the maximal-agreement obstruction and the old-list root event. -/
def foldSchema {K E : Type} [Field K] [Field E] [DecidableEq E]
    [Finite E] [SampleableType E] {vars lanes : ℕ} (enc : Encoding K vars)
    (ι : K →+* E) (sec : Erased LevelSecurity) (contract : EncodingContract enc ι)
    (valid : sec.out.Valid enc) (decoders : (lanes : ℕ) → ListDecoder (E := E) enc lanes)
    (correct : ∀ lanes, (decoders lanes).Correct ι (radius enc sec.out) (listBound enc sec.out)) :
    BadSchema E where
  Input := MaskedWord E (lanes + 1) (2 ^ (vars + enc.rate)) ×
    (Claim E ((lanes + 1) + vars) × Quadratic E) × Bool
  equality := inferInstance
  isQuery := false
  MaskLE small large := small.2.2 = true → large.2.2 = true ∧
    Whir.MaskLE small.1 large.1 ∧ small.2.1 = large.2.1
  Bad input r := input.2.2 = true ∧
    BadFold ι (radius enc sec.out) input.1 input.2.1.1 input.2.1.2 r
  check input r := input.2.2 && checkBadFold (decoders (lanes + 1)) (decoders lanes)
    input.1 input.2.1.1 input.2.1.2 r
  check_iff input r := by
    simp only [Bool.and_eq_true, checkBadFold_iff ι _ _ _ _ (correct _) (correct _)]
  monotone small large h _ r bad := by
    obtain ⟨active, mask, data⟩ := h bad.1
    refine ⟨active, ?_⟩
    simpa only [← data] using bad.2.mono mask
  error := Erased.mk (foldError (E := E) enc sec.out)
  bad_bound input := by
    simp only [Erased.out_mk]
    exact (prEvent_mono ($ᵗ E) _ _ (fun _ bad => bad.2)).trans
      (prob_badFold_le ι contract sec.out valid (decoders _) (correct _)
        input.1 input.2.1.1 input.2.1.2)

/-- OOD separation reads only the newly committed masked word. -/
def oodSchema {K E : Type} [Field K] [Field E] [DecidableEq E]
    [Finite E] [SampleableType E] {vars lanes : ℕ} (enc : Encoding K vars)
    (ι : K →+* E) (sec : Erased LevelSecurity) (valid : sec.out.Valid enc)
    (decoder : ListDecoder (E := E) enc lanes)
    (correct : decoder.Correct ι (radius enc sec.out) (listBound enc sec.out)) :
    BadSchema (Fin (lanes + vars) → E) where
  Input := MaskedWord E lanes (2 ^ (vars + enc.rate))
  equality := inferInstance
  isQuery := false
  MaskLE := Whir.MaskLE
  Bad := BadOod ι (radius enc sec.out)
  check := checkBadOod decoder
  check_iff := checkBadOod_iff ι _ _ decoder correct
  monotone _ _ h _ _ bad := bad.mono h
  error := Erased.mk (oodError (E := E) enc sec.out (lanes + vars))
  bad_bound word := by
    simpa only [Erased.out_mk] using prob_badOod_le ι sec.out valid decoder correct word

/-- A masked word is complete when every column is revealed. -/
def fullMask {F : Type} {lanes columns : ℕ} (word : MaskedWord F lanes columns) : Bool :=
  (List.finRange columns).all fun x => (word x).isSome

/-- A complete word has no strictly larger masked extension. -/
theorem MaskLE.eq_of_fullMask {F : Type} {lanes columns : ℕ}
    {small large : MaskedWord F lanes columns} (masks : Whir.MaskLE small large)
    (full : fullMask small = true) : small = large := by
  funext x
  have known : (small x).isSome = true := List.all_eq_true.mp full x (List.mem_finRange x)
  obtain ⟨column, hx⟩ := Option.isSome_iff_exists.mp known
  rw [hx, masks x column hx]

/-- The data fixed before a last-level column query: the word, residual, plaintext and activity. -/
structure LastQueryInput (E : Type) (columns tail : ℕ) where
  /-- The last committed masked word. -/
  word : MaskedWord E 0 columns
  /-- The residual claim on that word. -/
  claim : Claim E (0 + tail)
  /-- The plaintext candidate sent before the queries. -/
  candidate : Table E tail
  /-- Every preceding check accepted. -/
  active : Bool

/-- The residual and sampled column equations a last-level plaintext must satisfy. -/
def lastQueryClaims {K E : Type} [Semiring K] [CommRing E] {tail queries : ℕ}
    (enc : Encoding K tail) (ι : K →+* E) (input : LastQueryInput E (2 ^ (tail + enc.rate)) tail)
    (xs : Fin queries → enc.Columns) : List (Claim E tail) :=
  ⟨castTable (Nat.zero_add tail) input.claim.weight, input.claim.value⟩ ::
    List.ofFn (fun q : Fin queries =>
      ⟨(enc.queryWeights ι xs).weight q, zeroFill input.word (xs q) Fin.elim0⟩)

/-- A fixed last-level plaintext fails its old relation yet passes every sampled column check. -/
def LastQueryBad {K E : Type} [Semiring K] [CommRing E] [DecidableEq E] {tail queries : ℕ}
    (enc : Encoding K tail) (ι : K →+* E) (γ : ℝ)
    (input : LastQueryInput E (2 ^ (tail + enc.rate)) tail) (xs : Fin queries → enc.Columns) :
    Prop :=
  ¬ (input.active = true ∧
      Close γ input.word (enc.interleave ι (castTable (Nat.zero_add tail).symm input.candidate)) ∧
      ∀ c ∈ [input.claim], c.Holds (castTable (Nat.zero_add tail).symm input.candidate)) ∧
    (input.active && queriesKnown input.word xs) = true ∧
      ∀ c ∈ lastQueryClaims enc ι input xs, c.Holds input.candidate

/-- Last-level column queries test one fixed plaintext against its committed word. -/
def lastQuerySchema {K E : Type} [Field K] [Field E] [DecidableEq E]
    [Finite E] [SampleableType E] {tail : ℕ} (queries : ℕ) (enc : Encoding K tail) (ι : K →+* E)
    (sec : Erased LevelSecurity) (valid : sec.out.Valid enc) (decoder : ListDecoder (E := E) enc 0)
    (correct : decoder.Correct ι (radius enc sec.out) (listBound enc sec.out)) :
    BadSchema (Fin queries → enc.Columns) where
  Input := LastQueryInput E (2 ^ (tail + enc.rate)) tail
  equality := inferInstance
  isQuery := true
  complete input := fullMask input.word
  MaskLE small large := small.active = true → large.active = true ∧
    Whir.MaskLE small.word large.word ∧ small.claim = large.claim ∧
      small.candidate = large.candidate
  Bad := LastQueryBad enc ι (radius enc sec.out)
  check input xs :=
    let f := castTable (Nat.zero_add tail).symm input.candidate
    !(input.active && decide (f ∈ decoder.decode input.word) && decide (input.claim.Holds f)) &&
      (input.active && queriesKnown input.word xs) &&
      decide (∀ c ∈ lastQueryClaims enc ι input xs, c.Holds input.candidate)
  check_iff input xs := by
    have close := correct.mem_iff input.word (castTable (Nat.zero_add tail).symm input.candidate)
    simp only [LastQueryBad, List.forall_mem_singleton, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not, ← close]
    constructor
    · rintro ⟨⟨old, known⟩, claims⟩
      refine ⟨?_, known, claims⟩
      rintro ⟨active, member, claim⟩
      rcases old with (inactive | absent) | false
      · rw [active] at inactive
        exact Bool.noConfusion inactive
      · exact absent member
      · exact false claim
    · rintro ⟨old, known, claims⟩
      refine ⟨⟨?_, known⟩, claims⟩
      by_cases active : input.active = true
      · by_cases member : castTable (Nat.zero_add tail).symm input.candidate ∈
            decoder.decode input.word
        · exact Or.inr (fun claim => old ⟨active, member, claim⟩)
        · exact Or.inl (Or.inr member)
      · exact Or.inl (Or.inl (Bool.eq_false_iff.mpr active))
  monotone small large h complete xs bad := by
    obtain ⟨live, masks, claim, candidate⟩ := h (Bool.and_eq_true_iff.mp bad.2.1).1
    have word := MaskLE.eq_of_fullMask masks (complete rfl)
    rcases small with ⟨w, c, f, a⟩
    rcases large with ⟨w', c', f', a'⟩
    dsimp only at word claim candidate live bad ⊢
    subst word claim candidate
    have activeTrue := (Bool.and_eq_true_iff.mp bad.2.1).1
    subst activeTrue
    subst live
    exact bad
  error := Erased.mk (queryError enc sec.out queries)
  bad_bound input := by
    simp only [Erased.out_mk]
    refine (prEvent_mono ($ᵗ (Fin queries → enc.Columns)) _ _ ?_).trans
      (last_query_local_bound 0 queries enc ι sec.out decoder valid input.word input.claim
        input.candidate input.active)
    intro xs bad
    exact ⟨PUnit.unit, bad⟩

/-- The data fixed before a boundary column query: both words, the OOD exchange and activity. -/
structure BoundaryQueryInput {K : Type} (E : Type) {tail : ℕ} (columns : ℕ)
    (rest : Schedule K tail) where
  /-- The current level's committed masked word. -/
  word : MaskedWord E 0 columns
  /-- The residual claim on that word. -/
  claim : Claim E (0 + tail)
  /-- The next level's committed masked word. -/
  nextWord : oracleMessage E rest
  /-- The OOD point. -/
  z : Fin tail → E
  /-- The OOD answer. -/
  answer : E
  /-- Every preceding check accepted. -/
  active : Bool

/-- The boundary query lift fails for some next-level candidate passing every new claim. -/
def BoundaryQueryBad {K E : Type} [Field K] [Field E] [DecidableEq E] {tail queries : ℕ}
    (enc : Encoding K tail) (ι : K →+* E) (sec : LevelSecurity)
    (decoder : ListDecoder (E := E) enc 0) (rest : Schedule K tail)
    (nextSec : SecurityParameters rest) (decoders : DecoderFamily (E := E) rest)
    (input : BoundaryQueryInput E (2 ^ (tail + enc.rate)) rest)
    (xs : Fin queries → enc.Columns) : Prop :=
  ∃ f, ¬ (oodState (fun g => (candidateState enc ι (radius enc sec) input.word [input.claim]
        input.active).holds (castTable (Nat.zero_add tail).symm g))
        (levelList rest decoders input.nextWord) input.z input.active).holds
      (boundaryLift (decoder.decode input.word) (castTable (Nat.zero_add tail))
        input.claim.Holds (levelList rest decoders input.nextWord) input.z f) ∧
    (levelState ι rest nextSec input.nextWord
      (nextClaims enc ι ⟨castTable (Nat.zero_add tail) input.claim.weight, input.claim.value⟩
        input.z input.answer xs (fun x => zeroFill input.word x Fin.elim0))
      (input.active && queriesKnown input.word xs)).holds f

/-- Decide the post-OOD state through the certified current-level decoder. -/
def checkOodState {K E : Type} [Field K] [Field E] [DecidableEq E] {tail : ℕ}
    (enc : Encoding K tail) (decoder : ListDecoder (E := E) enc 0)
    (word : MaskedWord E 0 (2 ^ (tail + enc.rate))) (claim : Claim E (0 + tail))
    (newList : List (Table E tail)) (z : Fin tail → E) (active : Bool) :
    Sum (Table E tail) (Table E tail × Table E tail) → Bool
  | .inl f => active && decide (castTable (Nat.zero_add tail).symm f ∈ decoder.decode word) &&
      decide (claim.Holds (castTable (Nat.zero_add tail).symm f))
  | .inr (f, g) => active && decide (f ∈ newList ∧ g ∈ newList ∧ f ≠ g ∧ mle f z = mle g z)

/-- The decoder-based post-OOD check decides the analytical state. -/
theorem checkOodState_iff {K E : Type} [Field K] [Field E] [DecidableEq E] {tail : ℕ}
    (enc : Encoding K tail) (ι : K →+* E) (γ L : ℝ) (decoder : ListDecoder (E := E) enc 0)
    (correct : decoder.Correct ι γ L)
    (word : MaskedWord E 0 (2 ^ (tail + enc.rate))) (claim : Claim E (0 + tail))
    (newList : List (Table E tail)) (z : Fin tail → E) (active : Bool)
    (w : Sum (Table E tail) (Table E tail × Table E tail)) :
    checkOodState enc decoder word claim newList z active w = true ↔
      (oodState (fun g => (candidateState enc ι γ word [claim] active).holds
        (castTable (Nat.zero_add tail).symm g)) newList z active).holds w := by
  rcases w with f | ⟨f, g⟩
  · simp only [checkOodState, oodState, candidateState, Bool.and_eq_true, decide_eq_true_eq,
      correct.mem_iff, List.forall_mem_singleton]
    constructor
    · rintro ⟨⟨active, close⟩, claim⟩
      exact ⟨active, active, close, claim⟩
    · rintro ⟨active, -, close, claim⟩
      exact ⟨⟨active, close⟩, claim⟩
  · simp only [checkOodState, oodState, Bool.and_eq_true, decide_eq_true_eq]

/-- Boundary column queries test the candidate fixed by the OOD answer. -/
def boundaryQuerySchema {K E : Type} [Field K] [Field E] [DecidableEq E]
    [Finite E] [SampleableType E] {tail : ℕ} (queries : ℕ) (enc : Encoding K tail) (ι : K →+* E)
    (sec : Erased LevelSecurity) (valid : sec.out.Valid enc) (decoder : ListDecoder (E := E) enc 0)
    (correct : decoder.Correct ι (radius enc sec.out) (listBound enc sec.out))
    (rest : Schedule K tail) (nextSec : Erased (SecurityParameters rest))
    (decoders : DecoderFamily (E := E) rest)
    (nextCorrect : DecoderFamily.Correct ι rest decoders nextSec.out) :
    BadSchema (Fin queries → enc.Columns) where
  Input := BoundaryQueryInput E (2 ^ (tail + enc.rate)) rest
  equality := inferInstance
  isQuery := true
  complete input := fullMask input.word && fullMask input.nextWord
  MaskLE small large := small.active = true → large.active = true ∧
    Whir.MaskLE small.word large.word ∧ Whir.MaskLE small.nextWord large.nextWord ∧
      small.claim = large.claim ∧ small.z = large.z ∧ small.answer = large.answer
  Bad := BoundaryQueryBad enc ι sec.out decoder rest nextSec.out decoders
  check input xs :=
    let newList := levelList rest decoders input.nextWord
    let claims := nextClaims enc ι
      ⟨castTable (Nat.zero_add tail) input.claim.weight, input.claim.value⟩
      input.z input.answer xs (fun x => zeroFill input.word x Fin.elim0)
    (input.active && queriesKnown input.word xs) && newList.any fun f =>
      decide (∀ c ∈ claims, c.Holds f) &&
        !checkOodState enc decoder input.word input.claim newList input.z input.active
          (boundaryLift (decoder.decode input.word) (castTable (Nat.zero_add tail))
            input.claim.Holds newList input.z f)
  check_iff input xs := by
    simp only [BoundaryQueryBad, levelState_holds_iff ι rest nextSec.out decoders nextCorrect,
      Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      ← Bool.not_eq_true, checkOodState_iff enc ι _ _ decoder correct]
    constructor
    · rintro ⟨active, f, member, claims, bad⟩
      exact ⟨f, bad, active, member, claims⟩
    · rintro ⟨f, bad, active, member, claims⟩
      exact ⟨active, f, member, claims, bad⟩
  monotone small large h complete xs bad := by
    have good := bad.choose_spec.2
    rw [levelState_holds_iff ι rest nextSec.out decoders nextCorrect] at good
    obtain ⟨live, masks, nextMasks, claim, z, answer⟩ :=
      h (Bool.and_eq_true_iff.mp good.1).1
    obtain ⟨wordFull, nextFull⟩ := Bool.and_eq_true_iff.mp (complete rfl)
    have word := MaskLE.eq_of_fullMask masks wordFull
    have nextWord := MaskLE.eq_of_fullMask nextMasks nextFull
    have activeTrue := (Bool.and_eq_true_iff.mp good.1).1
    rcases small with ⟨w, c, n, z₀, a₀, act⟩
    rcases large with ⟨w', c', n', z₁, a₁, act'⟩
    dsimp only at word nextWord claim z answer live activeTrue bad ⊢
    subst word nextWord claim z answer activeTrue live
    exact bad
  error := Erased.mk (queryError enc sec.out queries)
  bad_bound input := by
    simp only [Erased.out_mk]
    exact (prEvent_mono _ _ _ fun _ bad => bad).trans
      (boundary_query_local_bound enc ι sec.out valid decoder correct rest nextSec.out decoders
        nextCorrect input.nextWord input.word input.claim input.z input.answer input.active)

/-- Final batching retains earlier query activity and authenticates the current masked equations. -/
def finalBatchSchema {E : Type} [Field E] [DecidableEq E]
    [Finite E] [SampleableType E] (n columns queries : ℕ) : BadSchema E where
  Input := {pre : PlaintextPrefix E n columns queries // pre.publicData.residual.length = 1} × Bool
  equality := inferInstance
  isQuery := false
  MaskLE small large := small.2 = true → large.2 = true ∧ small.1.val.MaskLE large.1.val
  Bad input r := input.2 = true ∧ PrefixBadFinalBatch input.1.val r
  check input r := input.2 && checkPrefixBadFinalBatch input.1.val r
  check_iff input r := by simp only [Bool.and_eq_true, checkPrefixBadFinalBatch_iff]
  monotone _ _ h _ _ bad := by
    obtain ⟨active, masks⟩ := h bad.1
    exact ⟨active, BadFinalBatch.mask_mono masks bad.2⟩
  error := Erased.mk ((queries : ENNReal) / Fintype.card E)
  bad_bound input := by
    simp only [Erased.out_mk]
    refine (prEvent_mono ($ᵗ E) _ _ (fun _ bad => bad.2.2)).trans ?_
    have len : input.1.val.claims.length - 1 = queries := by
      simp only [PlaintextPrefix.claims, List.length_append, List.length_ofFn, input.1.property]
      omega
    simpa only [len] using prob_badFinalBatch_le input.1.val.publicData.candidate input.1.val.claims

/-- Closing data retains the original guarded prefix and its public scalar-history transform. -/
structure ClosingInput (E : Type) (n columns queries count : ℕ) where
  /-- The original plaintext prefix with its authenticated query source. -/
  pre : PlaintextPrefix E n columns queries
  /-- Public scalar history acts on the candidate and all sampled equations. -/
  history : Table E n → List (Claim E n) → Table E (count + 1) × Claim E (count + 1)
  /-- The current compressed quadratic message. -/
  quadratic : Quadratic E
  /-- Activity retains all preceding query-availability and scalar-acceptance checks. -/
  active : Bool

/-- Closing checks a guarded root event after applying only public scalar history. -/
def closingSchema {E : Type} [Field E] [DecidableEq E]
    [Finite E] [SampleableType E] (n columns queries count : ℕ) : BadSchema E where
  Input := ClosingInput E n columns queries count
  equality := inferInstance
  isQuery := false
  MaskLE small large := small.active = true → large.active = true ∧
    small.pre.MaskLE large.pre ∧ small.history = large.history ∧ small.quadratic = large.quadratic
  Bad input r := input.active = true ∧ PrefixBadClosing input.history input.pre input.quadratic r
  check input r := input.active && checkPrefixBadClosing input.history input.pre input.quadratic r
  check_iff input r := by simp only [Bool.and_eq_true, checkPrefixBadClosing_iff]
  monotone small large h _ r bad := by
    rcases small with ⟨pre, history, q, active⟩
    rcases large with ⟨pre', history', q', active'⟩
    obtain ⟨live, masks, rfl, rfl⟩ := h bad.1
    exact ⟨live, BadClosing.mask_mono history masks bad.2⟩
  error := Erased.mk ((2 : ENNReal) / Fintype.card E)
  bad_bound input := by
    simp only [Erased.out_mk]
    exact (prEvent_mono ($ᵗ E) _ _ (fun _ bad => bad.2.2)).trans
      (prob_badClosing_le _ _ _)

/-- The closing block classifies every scalar round as a guarded quadratic root event. -/
def closingSchemas {E : Type} [Field E] [DecidableEq E]
    [Finite E] [SampleableType E] (n columns queries : ℕ) : (count : ℕ) →
    BadSchemas (scalarRoundsPublicCoin (E := E) count .done)
  | 0 => PUnit.unit
  | count + 1 => fun _ => ⟨closingSchema n columns queries count,
      closingSchemas n columns queries count⟩

/-- Fold schemas precede a fixed suffix and use the exact encoded fold error. -/
def foldSchemas {K E : Type} [Field K] [Field E] [DecidableEq E]
    [Finite E] [SampleableType E] {vars : ℕ} (enc : Encoding K vars) (ι : K →+* E)
    (sec : Erased LevelSecurity) (contract : EncodingContract enc ι) (valid : sec.out.Valid enc)
    (decoders : (lanes : ℕ) → ListDecoder (E := E) enc lanes)
    (correct : ∀ lanes, (decoders lanes).Correct ι (radius enc sec.out) (listBound enc sec.out))
    {rest : Protocol} (coin : PublicCoin rest) (suffix : BadSchemas coin) : (lanes : ℕ) →
    BadSchemas (scalarRoundsPublicCoin (E := E) lanes coin)
  | 0 => suffix
  | lanes + 1 => fun _ => ⟨foldSchema (lanes := lanes) enc ι sec contract valid decoders correct,
      foldSchemas enc ι sec contract valid decoders correct coin suffix lanes⟩

/-- The new level's OOD schema uses its certified head decoder. -/
def enteringOodSchema {K E : Type} [Field K] [Field E] [DecidableEq E]
    [Finite E] [SampleableType E] (ι : K →+* E) {n : ℕ} (s : Schedule K n)
    (sec : Erased (SecurityParameters s)) (decoders : DecoderFamily (E := E) s)
    (correct : DecoderFamily.Correct ι s decoders sec.out) (valid : s.Valid ι sec.out) :
    BadSchema (Fin n → E) :=
  match s with
  | .last lanes _ enc _ => oodSchema enc ι sec valid.2.1 (decoders lanes) (correct lanes)
  | .more lanes enc _ _ =>
      oodSchema enc ι (Erased.mk sec.out.1)
        (by simpa only [Erased.out_mk] using valid.2.1) (decoders.1 lanes)
        (by simpa only [Erased.out_mk] using correct.1 lanes)

/-- The newly extracted oracle is the masked input to the head OOD schema. -/
def enteringOodInput {K E : Type} [Field K] [Field E] [DecidableEq E]
    [Finite E] [SampleableType E] (ι : K →+* E) {n : ℕ} (s : Schedule K n)
    (sec : Erased (SecurityParameters s)) (decoders : DecoderFamily (E := E) s)
    (correct : DecoderFamily.Correct ι s decoders sec.out) (valid : s.Valid ι sec.out)
    (word : oracleMessage E s) : (enteringOodSchema ι s sec decoders correct valid).Input := by
  cases s <;> exact word

/-- WHIR's local classifier follows its opening syntax, with only column challenges marked query. -/
def openingSchemas {K E : Type} [Field K] [Field E] [DecidableEq E]
    [Finite E] [SampleableType E] (ι : K →+* E) : {n : ℕ} → (s : Schedule K n) →
    (sec : Erased (SecurityParameters s)) → (decoders : DecoderFamily (E := E) s) →
    DecoderFamily.Correct ι s decoders sec.out → s.Valid ι sec.out → ℕ →
    BadSchemas (openingPublicCoin (E := E) s)
  | _, .last lanes tail enc queries, sec, decoders, correct, valid, count =>
      ⟨batchSchema enc ι sec (decoders lanes) (correct lanes) count,
        foldSchemas enc ι sec valid.2.2.2 valid.2.1 decoders correct
          (rest := transition E (.last lanes tail enc queries))
          (.sender fun _ => .challenge (.challenge (scalarRoundsPublicCoin tail .done)))
          (fun _ => ⟨lastQuerySchema queries enc ι sec valid.2.1 (decoders 0) (correct 0),
            ⟨finalBatchSchema tail (2 ^ (tail + enc.rate)) queries,
              closingSchemas tail (2 ^ (tail + enc.rate)) queries tail⟩⟩) lanes⟩
  | _, .more lanes enc queries rest, sec, decoders, correct, valid, count =>
      ⟨batchSchema enc ι (Erased.mk sec.out.1) (decoders.1 lanes)
          (by simpa only [Erased.out_mk] using correct.1 lanes) count,
        foldSchemas enc ι (Erased.mk sec.out.1) valid.2.2.2.1
          (by simpa only [Erased.out_mk] using valid.2.1) decoders.1
          (by simpa only [Erased.out_mk] using correct.1)
          (rest := transition E (.more lanes enc queries rest))
          (.oracle (.challenge (.sender fun _ => .challenge (openingPublicCoin rest))))
          ⟨enteringOodSchema ι rest (Erased.mk sec.out.2) decoders.2
              (by simpa only [Erased.out_mk] using correct.2)
              (by simpa only [Erased.out_mk] using valid.2.2.2.2),
            fun _ => ⟨boundaryQuerySchema queries enc ι (Erased.mk sec.out.1)
                (by simpa only [Erased.out_mk] using valid.2.1) (decoders.1 0)
                (by simpa only [Erased.out_mk] using correct.1 0) rest (Erased.mk sec.out.2)
                decoders.2 (by simpa only [Erased.out_mk] using correct.2),
              openingSchemas ι rest (Erased.mk sec.out.2) decoders.2
              (by simpa only [Erased.out_mk] using correct.2)
              (by simpa only [Erased.out_mk] using valid.2.2.2.2) (queries + 2)⟩⟩ lanes⟩

end Whir
