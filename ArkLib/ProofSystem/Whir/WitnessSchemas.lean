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

/-- Encoded batching reads a masked word and a public claim list of the scheduled length. -/
noncomputable def batchSchema {K E : Type} [Field K] [Field E] [DecidableEq E]
    [Fintype E] [SampleableType E] {vars lanes : ℕ} (enc : Encoding K vars)
    (ι : K →+* E) (sec : LevelSecurity) (decoder : ListDecoder (E := E) enc lanes)
    (correct : decoder.Correct ι (radius enc sec) (listBound enc sec)) (count : ℕ) :
    BadSchema E where
  Input := MaskedWord E lanes (2 ^ (vars + enc.rate)) ×
    {claims : List (Claim E (lanes + vars)) // claims.length = count} × Bool
  equality := inferInstance
  isQuery := false
  MaskLE small large := small.2.2 = true → large.2.2 = true ∧
    Whir.MaskLE small.1 large.1 ∧ small.2.1.val = large.2.1.val
  Bad input r := input.2.2 = true ∧ BadBatch ι (radius enc sec) input.1 input.2.1.val r
  check input r := input.2.2 && checkBadBatch decoder input.1 input.2.1.val r
  check_iff input r := by
    simp only [Bool.and_eq_true, checkBadBatch_iff ι _ _ decoder correct]
  monotone small large h r bad := by
    obtain ⟨active, mask, claims⟩ := h bad.1
    exact ⟨active, claims ▸ bad.2.mono mask⟩
  error := batchError (E := E) enc sec count
  bad_bound input _ := by
    refine (prEvent_mono ($ᵗ E) _ _ (fun _ bad => bad.2)).trans ?_
    simpa only [input.2.1.property] using
      prob_badBatch_le ι sec decoder correct input.1 input.2.1.val

/-- Encoded folds combine the maximal-agreement obstruction and the old-list root event. -/
noncomputable def foldSchema {K E : Type} [Field K] [Field E] [DecidableEq E]
    [Fintype E] [SampleableType E] {vars lanes : ℕ} (enc : Encoding K vars)
    (ι : K →+* E) (sec : LevelSecurity) (contract : EncodingContract enc ι)
    (valid : sec.Valid enc) (decoders : (lanes : ℕ) → ListDecoder (E := E) enc lanes)
    (correct : ∀ lanes, (decoders lanes).Correct ι (radius enc sec) (listBound enc sec)) :
    BadSchema E where
  Input := MaskedWord E (lanes + 1) (2 ^ (vars + enc.rate)) ×
    (Claim E ((lanes + 1) + vars) × Quadratic E) × Bool
  equality := inferInstance
  isQuery := false
  MaskLE small large := small.2.2 = true → large.2.2 = true ∧
    Whir.MaskLE small.1 large.1 ∧ small.2.1 = large.2.1
  Bad input r := input.2.2 = true ∧
    BadFold ι (radius enc sec) input.1 input.2.1.1 input.2.1.2 r
  check input r := input.2.2 && checkBadFold ι (decoders (lanes + 1)) (decoders lanes)
    input.1 input.2.1.1 input.2.1.2 r
  check_iff input r := by
    simp only [Bool.and_eq_true, checkBadFold_iff ι _ _ _ _ (correct _) (correct _)]
  monotone small large h r bad := by
    obtain ⟨active, mask, data⟩ := h bad.1
    refine ⟨active, ?_⟩
    simpa only [← data] using bad.2.mono mask
  error := foldError (E := E) enc sec
  bad_bound input _ :=
    (prEvent_mono ($ᵗ E) _ _ (fun _ bad => bad.2)).trans
      (prob_badFold_le ι contract sec valid (decoders _) (correct _)
        input.1 input.2.1.1 input.2.1.2)

/-- OOD separation reads only the newly committed masked word. -/
noncomputable def oodSchema {K E : Type} [Field K] [Field E] [DecidableEq E]
    [Fintype E] [SampleableType E] {vars lanes : ℕ} (enc : Encoding K vars)
    (ι : K →+* E) (sec : LevelSecurity) (valid : sec.Valid enc)
    (decoder : ListDecoder (E := E) enc lanes)
    (correct : decoder.Correct ι (radius enc sec) (listBound enc sec)) :
    BadSchema (Fin (lanes + vars) → E) where
  Input := MaskedWord E lanes (2 ^ (vars + enc.rate))
  equality := inferInstance
  isQuery := false
  MaskLE := Whir.MaskLE
  Bad := BadOod ι (radius enc sec)
  check := checkBadOod decoder
  check_iff := checkBadOod_iff ι _ _ decoder correct
  monotone _ _ h _ bad := bad.mono h
  error := oodError (E := E) enc sec (lanes + vars)
  bad_bound word _ := prob_badOod_le ι sec valid decoder correct word

/-- Query challenges retain their extractor-relative event in the decomposition. -/
def querySchema (Challenge : Type) [SampleableType Challenge] [DecidableEq Challenge] :
    BadSchema Challenge where
  Input := PUnit
  equality := inferInstance
  isQuery := true
  MaskLE _ _ := True
  Bad _ _ := False
  check _ _ := false
  check_iff _ _ := by simp only [Bool.false_eq_true]
  monotone _ _ _ _ bad := bad.elim
  error := 0
  bad_bound _ impossible := Bool.noConfusion impossible

/-- Final batching authenticates the masked prefix from which the sampled claims are read. -/
noncomputable def finalBatchSchema {E : Type} [Field E] [DecidableEq E]
    [Fintype E] [SampleableType E] (n columns queries : ℕ) : BadSchema E where
  Input := {pre : PlaintextPrefix E n columns queries // pre.publicData.residual.length = 1}
  equality := inferInstance
  isQuery := false
  MaskLE small large := small.val.MaskLE large.val
  Bad input := PrefixBadFinalBatch input.val
  check input := checkPrefixBadFinalBatch input.val
  check_iff input := checkPrefixBadFinalBatch_iff input.val
  monotone _ _ h _ bad := BadFinalBatch.mask_mono h bad
  error := (queries : ENNReal) / Fintype.card E
  bad_bound input _ := by
    refine (prEvent_mono ($ᵗ E) _ _ (fun _ bad => bad.2)).trans ?_
    have len : input.val.claims.length - 1 = queries := by
      simp only [PlaintextPrefix.claims, List.length_append, List.length_ofFn, input.property]
      omega
    simpa only [len] using prob_badFinalBatch_le input.val.publicData.candidate input.val.claims

/-- Closing data retains the original guarded prefix and its public scalar-history transform. -/
structure ClosingInput (E : Type) (n columns queries count : ℕ) where
  /-- The original plaintext prefix with its authenticated query source. -/
  pre : PlaintextPrefix E n columns queries
  /-- Public scalar history acts on the candidate and all sampled equations. -/
  history : Table E n → List (Claim E n) → Table E (count + 1) × Claim E (count + 1)
  /-- The current compressed quadratic message. -/
  quadratic : Quadratic E

/-- Closing checks a guarded root event after applying only public scalar history. -/
noncomputable def closingSchema {E : Type} [Field E] [DecidableEq E]
    [Fintype E] [SampleableType E] (n columns queries count : ℕ) : BadSchema E where
  Input := ClosingInput E n columns queries count
  equality := inferInstance
  isQuery := false
  MaskLE small large := small.pre.MaskLE large.pre ∧ small.history = large.history ∧
    small.quadratic = large.quadratic
  Bad input := PrefixBadClosing input.history input.pre input.quadratic
  check input := checkPrefixBadClosing input.history input.pre input.quadratic
  check_iff input := checkPrefixBadClosing_iff input.history input.pre input.quadratic
  monotone small large h r bad := by
    rcases small with ⟨pre, history, q⟩
    rcases large with ⟨pre', history', q'⟩
    obtain ⟨masks, rfl, rfl⟩ := h
    exact BadClosing.mask_mono history masks bad
  error := (2 : ENNReal) / Fintype.card E
  bad_bound input _ :=
    (prEvent_mono ($ᵗ E) _ _ (fun _ bad => bad.2)).trans
      (prob_badClosing_le _ _ _)

/-- The closing block classifies every scalar round as a guarded quadratic root event. -/
noncomputable def closingSchemas {E : Type} [Field E] [DecidableEq E]
    [Fintype E] [SampleableType E] (n columns queries : ℕ) : (count : ℕ) →
    BadSchemas (scalarRoundsPublicCoin (E := E) count .done)
  | 0 => PUnit.unit
  | count + 1 => fun _ => ⟨closingSchema n columns queries count,
      closingSchemas n columns queries count⟩

/-- Fold schemas precede a fixed suffix and use the exact encoded fold error. -/
noncomputable def foldSchemas {K E : Type} [Field K] [Field E] [DecidableEq E]
    [Fintype E] [SampleableType E] {vars : ℕ} (enc : Encoding K vars) (ι : K →+* E)
    (sec : LevelSecurity) (contract : EncodingContract enc ι) (valid : sec.Valid enc)
    (decoders : (lanes : ℕ) → ListDecoder (E := E) enc lanes)
    (correct : ∀ lanes, (decoders lanes).Correct ι (radius enc sec) (listBound enc sec))
    {rest : Protocol} (coin : PublicCoin rest) (suffix : BadSchemas coin) : (lanes : ℕ) →
    BadSchemas (scalarRoundsPublicCoin (E := E) lanes coin)
  | 0 => suffix
  | lanes + 1 => fun _ => ⟨foldSchema (lanes := lanes) enc ι sec contract valid decoders correct,
      foldSchemas enc ι sec contract valid decoders correct coin suffix lanes⟩

/-- The new level's OOD schema uses its certified head decoder. -/
noncomputable def enteringOodSchema {K E : Type} [Field K] [Field E] [DecidableEq E]
    [Fintype E] [SampleableType E] (ι : K →+* E) {n : ℕ} (s : Schedule K n)
    (sec : SecurityParameters s) (decoders : DecoderFamily (E := E) s)
    (correct : DecoderFamily.Correct ι s decoders sec) (valid : s.Valid ι sec) :
    BadSchema (Fin n → E) :=
  match s with
  | .last lanes _ enc _ => oodSchema enc ι sec valid.2.1 (decoders lanes) (correct lanes)
  | .more lanes enc _ _ => oodSchema enc ι sec.1 valid.2.1 (decoders.1 lanes) (correct.1 lanes)

/-- The newly extracted oracle is the masked input to the head OOD schema. -/
noncomputable def enteringOodInput {K E : Type} [Field K] [Field E] [DecidableEq E]
    [Fintype E] [SampleableType E] (ι : K →+* E) {n : ℕ} (s : Schedule K n)
    (sec : SecurityParameters s) (decoders : DecoderFamily (E := E) s)
    (correct : DecoderFamily.Correct ι s decoders sec) (valid : s.Valid ι sec)
    (word : oracleMessage E s) : (enteringOodSchema ι s sec decoders correct valid).Input := by
  cases s <;> exact word

/-- WHIR's local classifier follows its opening syntax, with only column challenges marked query. -/
noncomputable def openingSchemas {K E : Type} [Field K] [Field E] [DecidableEq E]
    [Fintype E] [SampleableType E] (ι : K →+* E) : {n : ℕ} → (s : Schedule K n) →
    (sec : SecurityParameters s) → (decoders : DecoderFamily (E := E) s) →
    DecoderFamily.Correct ι s decoders sec → s.Valid ι sec → ℕ →
    BadSchemas (openingPublicCoin (E := E) s)
  | _, .last lanes tail enc queries, sec, decoders, correct, valid, count =>
      ⟨batchSchema enc ι sec (decoders lanes) (correct lanes) count,
        foldSchemas enc ι sec valid.2.2.2 valid.2.1 decoders correct
          (rest := transition E (.last lanes tail enc queries))
          (.sender fun _ => .challenge (.challenge (scalarRoundsPublicCoin tail .done)))
          (fun _ => ⟨querySchema (Fin queries → enc.Columns),
            ⟨finalBatchSchema tail (2 ^ (tail + enc.rate)) queries,
              closingSchemas tail (2 ^ (tail + enc.rate)) queries tail⟩⟩) lanes⟩
  | _, .more lanes enc queries rest, sec, decoders, correct, valid, count =>
      ⟨batchSchema enc ι sec.1 (decoders.1 lanes) (correct.1 lanes) count,
        foldSchemas enc ι sec.1 valid.2.2.2.1 valid.2.1 decoders.1 correct.1
          (rest := transition E (.more lanes enc queries rest))
          (.oracle (.challenge (.sender fun _ => .challenge (openingPublicCoin rest))))
          ⟨enteringOodSchema ι rest sec.2 decoders.2 correct.2 valid.2.2.2.2,
            fun _ => ⟨querySchema (Fin queries → enc.Columns),
              openingSchemas ι rest sec.2 decoders.2 correct.2 valid.2.2.2.2 (queries + 2)⟩⟩ lanes⟩

end Whir
