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

/-- Field enumeration belongs only to the analytical claims of the annotation. -/
noncomputable local instance {E : Type} [Finite E] : Fintype E := Fintype.ofFinite E

/-- Closing annotations retain the original masked prefix through every public scalar fold. -/
def closingAnnotation {E : Type} [Field E] [DecidableEq E]
    [Finite E] [SampleableType E] {n columns queries : ℕ}
    (pre : PlaintextPrefix E n columns queries) : (count : ℕ) →
    (history : Table E n → List (Claim E n) → Table E count × Claim E count) →
    (active : Bool) → (active = true → pre.known = true) →
    BadAnnotation (scalarRoundsPublicCoin (E := E) count .done)
      (closingSchemas n columns queries count)
      (closingExtractor count (history pre.publicData.candidate pre.claims).1
        (history pre.publicData.candidate pre.claims).2 active)
  | 0, _, _, _ => PUnit.unit
  | count + 1, history, active, known => fun q =>
      ⟨⟨pre, history, q, active⟩, ⟨fun r escape =>
        ⟨(Bool.and_eq_true_iff.mp escape.choose_spec.2.1).1,
          known (Bool.and_eq_true_iff.mp escape.choose_spec.2.1).1,
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
def lastAnnotation {K E : Type} [Field K] [Field E] [DecidableEq E]
    [Finite E] [SampleableType E] {tail : ℕ} (lanes queries : ℕ)
    (enc : Encoding K tail) (ι : K →+* E) (sec : Erased LevelSecurity) (valid : sec.out.Valid enc)
    (decoder : ListDecoder (E := E) enc 0)
    (correct : decoder.Correct ι (radius enc sec.out) (listBound enc sec.out))
    (word : MaskedWord E 0 (2 ^ (tail + enc.rate))) (claim : Claim E (0 + tail))
    (active : Bool) :
    BadAnnotation (protocol := transition E (.last lanes tail enc queries))
      (.sender fun _ => .challenge
      (.challenge (scalarRoundsPublicCoin (E := E) tail .done)))
      (fun _ => (lastQuerySchema queries enc ι sec valid decoder correct,
        (finalBatchSchema tail (2 ^ (tail + enc.rate)) queries,
          closingSchemas tail (2 ^ (tail + enc.rate)) queries tail)))
      (lastExtractor lanes queries enc ι
        (fun w f => Close (radius enc sec.out) w (enc.interleave ι f)) decoder word claim active) :=
  fun candidate => ⟨⟨word, claim, candidate, active⟩, ⟨fun _ escape => by
    obtain ⟨_, old, new⟩ := escape
    exact ⟨old, new⟩, fun xs =>
    let weights := enc.queryWeights ι xs
    let pre : PlaintextPrefix E tail (2 ^ (tail + enc.rate)) queries :=
      ⟨⟨candidate, [⟨castTable (Nat.zero_add tail) claim.weight, claim.value⟩],
        (fun q => weights.weight q), xs⟩, word⟩
    ⟨(⟨pre, rfl⟩, active), ⟨fun r escape =>
      ⟨(Bool.and_eq_true_iff.mp escape.choose_spec.2.1).1,
        (Bool.and_eq_true_iff.mp escape.choose_spec.2.1).2,
        finalBatch_escape_subset_bad candidate pre.claims (active && pre.known) r escape⟩,
      fun r => closingAnnotation pre tail (fun candidate claims => (candidate, batch claims r))
        (active && pre.known) (fun h => (Bool.and_eq_true_iff.mp h).2)⟩⟩⟩⟩

/-- Fold annotations expose the maximal-agreement event for each concrete list-lifting map. -/
def foldAnnotation {K E : Type} [Field K] [Field E] [DecidableEq E]
    [Finite E] [SampleableType E] {vars : ℕ} (enc : Encoding K vars) (ι : K →+* E)
    (sec : Erased LevelSecurity) (contract : EncodingContract enc ι) (valid : sec.out.Valid enc)
    (decoders : (lanes : ℕ) → ListDecoder (E := E) enc lanes)
    (correct : ∀ lanes, (decoders lanes).Correct ι (radius enc sec.out) (listBound enc sec.out))
    {rest : Protocol} (coin : PublicCoin rest) (schemas : BadSchemas coin)
    (finish : (word : MaskedWord E 0 (2 ^ (vars + enc.rate))) →
      (claim : Claim E (0 + vars)) → (active : Bool) →
      RoundExtractor rest.tree
        (candidateState enc ι (radius enc sec.out) word [claim] active))
    (suffix : ∀ word claim active, BadAnnotation coin schemas (finish word claim active)) :
    (lanes : ℕ) → (word : MaskedWord E lanes (2 ^ (vars + enc.rate))) →
    (claim : Claim E (lanes + vars)) → (active : Bool) →
    BadAnnotation (scalarRoundsPublicCoin (E := E) lanes coin)
      (foldSchemas enc ι sec contract valid decoders correct coin schemas lanes)
      (foldExtractor enc (fun _ w f => Close (radius enc sec.out) w (enc.interleave ι f))
        decoders finish lanes word claim active)
  | 0, word, claim, active => suffix word claim active
  | lanes + 1, word, claim, active => fun q =>
      ⟨⟨word, (claim, q), active && (Sumcheck.compressedOps 1).accept claim.value q⟩,
        ⟨fun r escape => ⟨escape.choose_spec.2.1,
        fold_escape_subset_bad ι contract sec.out valid (decoders _) (decoders _)
          (correct _) (correct _) word claim q
          (active && (Sumcheck.compressedOps 1).accept claim.value q) r
          ⟨escape.choose, escape.choose_spec.2, escape.choose_spec.1⟩⟩,
        fun r => foldAnnotation enc ι sec contract valid decoders correct coin schemas
          finish suffix lanes (foldMaskedRowsOne word r)
          ⟨foldMessageOne claim.weight r, evalQuadratic claim.value q r⟩
          (active && (Sumcheck.compressedOps 1).accept claim.value q)⟩⟩

/-- A collision in the newly extracted list is precisely the entering masked OOD event. -/
theorem enteringOod_collision {K E : Type} [Field K] [Field E] [DecidableEq E]
    [Finite E] [SampleableType E] (ι : K →+* E) {n : ℕ} (s : Schedule K n)
    (sec : Erased (SecurityParameters s)) (decoders : DecoderFamily (E := E) s)
    (correct : DecoderFamily.Correct ι s decoders sec.out) (valid : s.Valid ι sec.out)
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
      change BadOod ι (radius enc (Erased.mk sec.out.1).out) word z
      simpa only [Erased.out_mk] using
        (show BadOod ι (radius enc sec.out.1) word z from
          ⟨f, g, ((correct.1 lanes).mem_iff _ _).mp hf,
            ((correct.1 lanes).mem_iff _ _).mp hg, rest⟩)

/-- Boundary annotations read the new oracle before OOD and fix the query input after the answer. -/
def boundaryAnnotation {K E : Type} [Field K] [Field E] [DecidableEq E]
    [Finite E] [SampleableType E] {tail : ℕ} (lanes queries : ℕ)
    (enc : Encoding K tail) (ι : K →+* E) (sec : Erased LevelSecurity) (levelValid : sec.out.Valid enc)
    (decoder : ListDecoder (E := E) enc 0)
    (decoderCorrect : decoder.Correct ι (radius enc sec.out) (listBound enc sec.out))
    (rest : Schedule K tail) (nextSec : Erased (SecurityParameters rest))
    (decoders : DecoderFamily (E := E) rest)
    (correct : DecoderFamily.Correct ι rest decoders nextSec.out) (valid : rest.Valid ι nextSec.out)
    (suffix : ∀ word claims active, claims.length = queries + 2 →
      BadAnnotation (openingPublicCoin rest)
        (openingSchemas ι rest nextSec decoders correct valid (queries + 2))
        (levelExtractor ι rest (proximityFamily ι rest nextSec.out) decoders word claims active))
    (word : MaskedWord E 0 (2 ^ (tail + enc.rate))) (claim : Claim E (0 + tail))
    (active : Bool) :
    BadAnnotation (protocol := transition E (.more lanes enc queries rest))
      (.oracle (.challenge (.sender fun _ => .challenge (openingPublicCoin rest))))
      (enteringOodSchema ι rest nextSec decoders correct valid,
        fun _ => (boundaryQuerySchema queries enc ι sec levelValid decoder decoderCorrect rest nextSec
            decoders correct,
          openingSchemas ι rest nextSec decoders correct valid (queries + 2)))
      (boundaryExtractor lanes queries enc ι
        (fun w f => Close (radius enc sec.out) w (enc.interleave ι f))
        rest (proximityFamily ι rest nextSec.out) decoder decoders
        (levelExtractor ι rest (proximityFamily ι rest nextSec.out) decoders) word claim active) :=
  fun nextWord => ⟨enteringOodInput ι rest nextSec decoders correct valid nextWord,
    ⟨fun z escape => by
      apply enteringOod_collision ι rest nextSec decoders correct valid nextWord z
      obtain ⟨witness, bad, good⟩ := escape
      cases witness with
      | inl f => exact (bad good.2).elim
      | inr pair => exact ⟨pair.1, good.2.1, pair.2, good.2.2.1, good.2.2.2⟩,
    fun z answer => ⟨⟨word, claim, nextWord, z, answer, active⟩, ⟨fun _ escape => escape, fun xs =>
      suffix nextWord
        (nextClaims enc ι ⟨castTable (Nat.zero_add tail) claim.weight, claim.value⟩
          z answer xs (fun x => zeroFill word x Fin.elim0))
        (active && queriesKnown word xs) (by
          simp only [nextClaims, List.length_cons, List.length_ofFn])⟩⟩⟩⟩

/-- The first proximity relation reads the head security parameters. -/
theorem proximityFamily_more_head {K E : Type} [Semiring K] [Semiring E] [DecidableEq E]
    (ι : K →+* E) {n lanes : ℕ} (enc : Encoding K n) (queries : ℕ)
    (rest : Schedule K n) (sec : SecurityParameters (.more lanes enc queries rest)) :
    proximityFamily ι (.more lanes enc queries rest) sec 0 enc =
      (fun _ word f => Close (radius enc sec.1) word (enc.interleave ι f)) := rfl

/-- Advancing an encoded level reads exactly the suffix security parameters. -/
theorem proximityFamily_more_tail {K E : Type} [Semiring K] [Semiring E] [DecidableEq E]
    (ι : K →+* E) {n lanes : ℕ} (enc : Encoding K n) (queries : ℕ)
    (rest : Schedule K n) (sec : SecurityParameters (.more lanes enc queries rest)) :
    (fun level {vars} =>
      proximityFamily ι (.more lanes enc queries rest) sec (level + 1) (vars := vars)) =
      proximityFamily ι rest sec.2 := rfl

/-- Every level of the actual list-lifting extractor has its masked bad-event annotation. -/
def levelAnnotation {K E : Type} [Field K] [Field E] [DecidableEq E]
    [Finite E] [SampleableType E] (ι : K →+* E) : {n : ℕ} → (s : Schedule K n) →
    (sec : Erased (SecurityParameters s)) → (decoders : DecoderFamily (E := E) s) →
    (correct : DecoderFamily.Correct ι s decoders sec.out) → (valid : s.Valid ι sec.out) →
    (word : oracleMessage E s) → (claims : List (Claim E n)) → (active : Bool) →
    (count : ℕ) → claims.length ≤ count → BadAnnotation (openingPublicCoin s)
      (openingSchemas ι s sec decoders correct valid count)
      (levelExtractor ι s (proximityFamily ι s sec.out) decoders word claims active)
  | _, .last lanes tail enc queries, sec, decoders, correct, valid, word, claims, active,
      count, length =>
      ⟨⟨word, ⟨claims, length⟩, active⟩, ⟨fun r escape => ⟨escape.choose_spec.2.1,
        batch_escape_subset_bad ι _ _ _ (correct lanes) word claims active r
          ⟨escape.choose, escape.choose_spec.2, escape.choose_spec.1⟩⟩,
        fun r => foldAnnotation enc ι sec valid.2.2.2 valid.2.1 decoders correct _ _
          (lastExtractor lanes queries enc ι
            (fun w f => Close (radius enc sec.out) w (enc.interleave ι f)) (decoders 0))
          (lastAnnotation lanes queries enc ι sec valid.2.1 (decoders 0) (correct 0)) lanes word
            (batch claims r)
          active⟩⟩
  | _, .more lanes enc queries rest, sec, decoders, correct, valid, word, claims, active,
      count, length =>
      ⟨⟨word, ⟨claims, length⟩, active⟩, ⟨fun r escape => ⟨escape.choose_spec.2.1,
        by simpa only [Erased.out_mk] using
          batch_escape_subset_bad ι _ _ _ (correct.1 lanes) word claims active r
            ⟨escape.choose, escape.choose_spec.2, escape.choose_spec.1⟩⟩,
        fun r => by
          simp only [levelExtractor, openingSchemas]
          rw [proximityFamily_more_head, proximityFamily_more_tail]
          convert foldAnnotation enc ι (Erased.mk sec.out.1) valid.2.2.2.1
              (by simpa only [Erased.out_mk] using valid.2.1) decoders.1
              (by simpa only [Erased.out_mk] using correct.1) _ _
              (boundaryExtractor lanes queries enc ι
                (fun w f => Close (radius enc (Erased.mk sec.out.1).out) w (enc.interleave ι f))
                rest (proximityFamily ι rest (Erased.mk sec.out.2).out) (decoders.1 0) decoders.2
                (levelExtractor ι rest (proximityFamily ι rest (Erased.mk sec.out.2).out)
                  decoders.2))
              (boundaryAnnotation lanes queries enc ι (Erased.mk sec.out.1)
                (by simpa only [Erased.out_mk] using valid.2.1) (decoders.1 0)
                (by simpa only [Erased.out_mk] using correct.1 0) rest (Erased.mk sec.out.2) decoders.2
                (by simpa only [Erased.out_mk] using correct.2)
                (by simpa only [Erased.out_mk] using valid.2.2.2.2)
                (fun word claims active length =>
                  levelAnnotation ι rest (Erased.mk sec.out.2) decoders.2
                      (by simpa only [Erased.out_mk] using correct.2)
                      (by simpa only [Erased.out_mk] using valid.2.2.2.2) word claims active
                      (queries + 2) (Nat.le_of_eq length)))
              lanes word (batch claims r) active using 1
          congr 3 <;> rw [Erased.out_mk]⟩⟩

end Whir
