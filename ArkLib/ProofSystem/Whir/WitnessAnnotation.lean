/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.ProofSystem.Whir.WitnessSchemas

/-! # Same-prefix escape containment for WHIR's concrete extractor -/

@[expose] public section

open Interaction Interaction.Oracle Interaction.Oracle.Security OracleComp OracleSpec
open Interaction.Oracle.Security.StandardBcs

namespace Whir

/-- Closing annotations retain the original masked prefix through every public scalar fold. -/
noncomputable def closingAnnotation {E : Type} [Field E] [DecidableEq E]
    [Fintype E] [SampleableType E] {n columns queries : ℕ}
    (pre : PlaintextPrefix E n columns queries) : (count : ℕ) →
    (history : Table E n → List (Claim E n) → Table E count × Claim E count) →
    (active : Bool) → (active = true → pre.known = true) →
    BadAnnotation (scalarRoundsPublicCoin (E := E) count .done)
      (closingSchemas n columns queries count)
      (closingExtractor count (history pre.publicData.candidate pre.claims).1
        (history pre.publicData.candidate pre.claims).2 active)
  | 0, _, _, _ => PUnit.unit
  | count + 1, history, active, known => fun q =>
      ⟨⟨pre, history, q⟩, ⟨fun r _ escape =>
        ⟨known (Bool.and_eq_true_iff.mp escape.choose_spec.2.1).1,
          closing_escape_subset_bad _ _ q active r escape⟩,
        fun r => closingAnnotation pre count (fun candidate claims =>
          let data := history candidate claims
          (foldMessageOne (vars := 0) data.1 r,
            ⟨foldMessageOne (vars := 0) data.2.weight r,
              evalQuadratic data.2.value q r⟩))
          (active && (Sumcheck.compressedOps 1).accept
            (history pre.publicData.candidate pre.claims).2.value q)
          (fun h => known (Bool.and_eq_true_iff.mp h).1)⟩⟩

/-- The last query fixes a guarded masked prefix before final batching and closing. -/
noncomputable def lastAnnotation {K E : Type} [Field K] [Field E] [DecidableEq E]
    [Fintype E] [SampleableType E] {tail : ℕ} (lanes queries : ℕ)
    (enc : Encoding K tail) (ι : K →+* E) (sec : LevelSecurity)
    (decoder : ListDecoder (E := E) enc 0)
    (word : MaskedWord E 0 (2 ^ (tail + enc.rate))) (claim : Claim E (0 + tail))
    (active : Bool) :
    BadAnnotation (protocol := transition E (.last lanes tail enc queries))
      (.sender fun _ => .challenge
      (.challenge (scalarRoundsPublicCoin (E := E) tail .done)))
      (fun _ => (querySchema (Fin queries → enc.Columns),
        (finalBatchSchema tail (2 ^ (tail + enc.rate)) queries,
          closingSchemas tail (2 ^ (tail + enc.rate)) queries tail)))
      (lastExtractor lanes queries enc ι
        (fun w f => Close (radius enc sec) w (enc.interleave ι f)) decoder word claim active) :=
  fun candidate => ⟨PUnit.unit, ⟨fun _ impossible _ => Bool.noConfusion impossible, fun xs =>
    let pre : PlaintextPrefix E tail (2 ^ (tail + enc.rate)) queries :=
      ⟨⟨candidate, [⟨castTable (Nat.zero_add tail) claim.weight, claim.value⟩],
        (fun q u => ι (enc.weight (xs q) u)), xs⟩, word⟩
    ⟨⟨pre, rfl⟩, ⟨fun r _ escape =>
      ⟨(Bool.and_eq_true_iff.mp escape.choose_spec.2.1).2,
        finalBatch_escape_subset_bad candidate pre.claims (active && pre.known) r escape⟩,
      fun r => closingAnnotation pre tail (fun candidate claims => (candidate, batch claims r))
        (active && pre.known) (fun h => (Bool.and_eq_true_iff.mp h).2)⟩⟩⟩⟩

/-- Fold annotations expose the maximal-agreement event for each concrete list-lifting map. -/
noncomputable def foldAnnotation {K E : Type} [Field K] [Field E] [DecidableEq E]
    [Fintype E] [SampleableType E] {vars : ℕ} (enc : Encoding K vars) (ι : K →+* E)
    (sec : LevelSecurity) (contract : EncodingContract enc ι) (valid : sec.Valid enc)
    (decoders : (lanes : ℕ) → ListDecoder (E := E) enc lanes)
    (correct : ∀ lanes, (decoders lanes).Correct ι (radius enc sec) (listBound enc sec))
    {rest : Protocol} (coin : PublicCoin rest) (schemas : BadSchemas coin)
    (finish : (word : MaskedWord E 0 (2 ^ (vars + enc.rate))) →
      (claim : Claim E (0 + vars)) → (active : Bool) →
      RoundExtractor rest.tree
        (candidateState enc ι (radius enc sec) word [claim] active))
    (suffix : ∀ word claim active, BadAnnotation coin schemas (finish word claim active)) :
    (lanes : ℕ) → (word : MaskedWord E lanes (2 ^ (vars + enc.rate))) →
    (claim : Claim E (lanes + vars)) → (active : Bool) →
    BadAnnotation (scalarRoundsPublicCoin (E := E) lanes coin)
      (foldSchemas enc ι sec contract valid decoders correct coin schemas lanes)
      (foldExtractor enc (fun _ w f => Close (radius enc sec) w (enc.interleave ι f))
        decoders finish lanes word claim active)
  | 0, word, claim, active => suffix word claim active
  | lanes + 1, word, claim, active => fun q =>
      ⟨⟨word, (claim, q), active && (Sumcheck.compressedOps 1).accept claim.value q⟩,
        ⟨fun r _ escape => ⟨escape.choose_spec.2.1,
        fold_escape_subset_bad ι contract sec valid (decoders _) (decoders _)
          (correct _) (correct _) word claim q
          (active && (Sumcheck.compressedOps 1).accept claim.value q) r
          ⟨escape.choose, escape.choose_spec.2, escape.choose_spec.1⟩⟩,
        fun r => foldAnnotation enc ι sec contract valid decoders correct coin schemas
          finish suffix lanes (foldMaskedRowsOne word r)
          ⟨foldMessageOne claim.weight r, evalQuadratic claim.value q r⟩
          (active && (Sumcheck.compressedOps 1).accept claim.value q)⟩⟩

/-- A collision in the newly extracted list is precisely the entering masked OOD event. -/
theorem enteringOod_collision {K E : Type} [Field K] [Field E] [DecidableEq E]
    [Fintype E] [SampleableType E] (ι : K →+* E) {n : ℕ} (s : Schedule K n)
    (sec : SecurityParameters s) (decoders : DecoderFamily (E := E) s)
    (correct : DecoderFamily.Correct ι s decoders sec) (valid : s.Valid ι sec)
    (word : oracleMessage E s) (z : Fin n → E)
    (collision : OodCollision (levelList s decoders word) z) :
    (enteringOodSchema ι s sec decoders correct valid).Bad
      (enteringOodInput ι s sec decoders correct valid word) z := by
  obtain ⟨f, hf, g, hg, rest⟩ := collision
  cases s with
  | last lanes tail enc queries =>
      exact ⟨f, g, ((correct lanes).mem_iff _ _).mp hf,
        ((correct lanes).mem_iff _ _).mp hg, rest⟩
  | more lanes enc queries rest' =>
      exact ⟨f, g, ((correct.1 lanes).mem_iff _ _).mp hf,
        ((correct.1 lanes).mem_iff _ _).mp hg, rest⟩

/-- Boundary annotations read the new oracle before OOD and classify only the column query. -/
noncomputable def boundaryAnnotation {K E : Type} [Field K] [Field E] [DecidableEq E]
    [Fintype E] [SampleableType E] {tail : ℕ} (lanes queries : ℕ)
    (enc : Encoding K tail) (ι : K →+* E) (sec : LevelSecurity)
    (decoder : ListDecoder (E := E) enc 0)
    (rest : Schedule K tail) (nextSec : SecurityParameters rest)
    (decoders : DecoderFamily (E := E) rest)
    (correct : DecoderFamily.Correct ι rest decoders nextSec) (valid : rest.Valid ι nextSec)
    (suffix : ∀ word claims active, claims.length = queries + 2 →
      BadAnnotation (openingPublicCoin rest)
        (openingSchemas ι rest nextSec decoders correct valid (queries + 2))
        (levelExtractor ι rest (proximityFamily ι rest nextSec) decoders word claims active))
    (word : MaskedWord E 0 (2 ^ (tail + enc.rate))) (claim : Claim E (0 + tail))
    (active : Bool) :
    BadAnnotation (protocol := transition E (.more lanes enc queries rest))
      (.oracle (.challenge (.sender fun _ => .challenge (openingPublicCoin rest))))
      (enteringOodSchema ι rest nextSec decoders correct valid,
        fun _ => (querySchema (Fin queries → enc.Columns),
          openingSchemas ι rest nextSec decoders correct valid (queries + 2)))
      (boundaryExtractor lanes queries enc ι
        (fun w f => Close (radius enc sec) w (enc.interleave ι f))
        rest (proximityFamily ι rest nextSec) decoder decoders
        (levelExtractor ι rest (proximityFamily ι rest nextSec) decoders) word claim active) :=
  fun nextWord => ⟨enteringOodInput ι rest nextSec decoders correct valid nextWord,
    ⟨fun z _ escape => by
      apply enteringOod_collision ι rest nextSec decoders correct valid nextWord z
      obtain ⟨witness, bad, good⟩ := escape
      cases witness with
      | inl f => exact (bad good.2).elim
      | inr pair => exact ⟨pair.1, good.2.1, pair.2, good.2.2.1, good.2.2.2⟩,
    fun z answer => ⟨PUnit.unit, ⟨fun _ impossible _ => Bool.noConfusion impossible, fun xs =>
      suffix nextWord
        (nextClaims enc ι ⟨castTable (Nat.zero_add tail) claim.weight, claim.value⟩
          z answer xs (fun x => zeroFill word x Fin.elim0))
        (active && queriesKnown word xs) (by
          simp only [nextClaims, List.length_cons, List.length_ofFn])⟩⟩⟩⟩

/-- Every level of the actual list-lifting extractor has its masked bad-event annotation. -/
noncomputable def levelAnnotation {K E : Type} [Field K] [Field E] [DecidableEq E]
    [Fintype E] [SampleableType E] (ι : K →+* E) : {n : ℕ} → (s : Schedule K n) →
    (sec : SecurityParameters s) → (decoders : DecoderFamily (E := E) s) →
    (correct : DecoderFamily.Correct ι s decoders sec) → (valid : s.Valid ι sec) →
    (word : oracleMessage E s) → (claims : List (Claim E n)) → (active : Bool) →
    BadAnnotation (openingPublicCoin s)
      (openingSchemas ι s sec decoders correct valid claims.length)
      (levelExtractor ι s (proximityFamily ι s sec) decoders word claims active)
  | _, .last lanes tail enc queries, sec, decoders, correct, valid, word, claims, active =>
      ⟨⟨word, ⟨claims, rfl⟩, active⟩, ⟨fun r _ escape => ⟨escape.choose_spec.2.1,
        batch_escape_subset_bad ι _ _ _ (correct lanes) word claims active r
          ⟨escape.choose, escape.choose_spec.2, escape.choose_spec.1⟩⟩,
        fun r => foldAnnotation enc ι sec valid.2.2.2 valid.2.1 decoders correct _ _
          (lastExtractor lanes queries enc ι
            (fun w f => Close (radius enc sec) w (enc.interleave ι f)) (decoders 0))
          (lastAnnotation lanes queries enc ι sec (decoders 0)) lanes word (batch claims r)
          active⟩⟩
  | _, .more lanes enc queries rest, sec, decoders, correct, valid, word, claims, active =>
      ⟨⟨word, ⟨claims, rfl⟩, active⟩, ⟨fun r _ escape => ⟨escape.choose_spec.2.1,
        batch_escape_subset_bad ι _ _ _ (correct.1 lanes) word claims active r
          ⟨escape.choose, escape.choose_spec.2, escape.choose_spec.1⟩⟩,
        fun r => foldAnnotation enc ι sec.1 valid.2.2.2.1 valid.2.1 decoders.1 correct.1 _ _
          (boundaryExtractor lanes queries enc ι
            (fun w f => Close (radius enc sec.1) w (enc.interleave ι f))
            rest (proximityFamily ι rest sec.2) (decoders.1 0) decoders.2
            (levelExtractor ι rest (proximityFamily ι rest sec.2) decoders.2))
          (boundaryAnnotation lanes queries enc ι sec.1 (decoders.1 0) rest sec.2 decoders.2
            correct.2 valid.2.2.2.2 (fun word claims active length => by
              simpa only [length] using
                levelAnnotation ι rest sec.2 decoders.2 correct.2 valid.2.2.2.2 word claims active))
          lanes word (batch claims r) active⟩⟩

end Whir
