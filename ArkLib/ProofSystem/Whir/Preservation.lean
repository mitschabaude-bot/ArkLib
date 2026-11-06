/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.ProofSystem.Whir.Extractor

/-!
# Prover preservation for WHIR list lifting

Prover messages retain accumulated checks. A fixed plaintext message lifts through its known
old-list preimage. Oracle messages and OOD answers retain their preceding knowledge state.
-/

@[expose] public section

open Interaction Interaction.Oracle Interaction.Oracle.Security

namespace Whir

/-- Closing prover checks only strengthen the fixed-plaintext knowledge predicate. -/
theorem closingExtractor_preserving {E : Type} [CommRing E] [DecidableEq E]
    (count : ℕ) (candidate : Table E count) (claim : Claim E count) (active : Bool) :
    (closingExtractor count candidate claim active).IsProverPreserving
      (scalarRounds E count .done).roles := by
  induction count generalizing active with
  | zero => trivial
  | succ count ih =>
      refine ⟨?_, fun q => ⟨?_, fun r => ih _ _ _⟩⟩
      · intro q _ witness good
        exact ⟨(Bool.and_eq_true_iff.mp good.1).1, good.2⟩
      · intro r impossible
        cases impossible

/-- Final batching is a verifier message, and closing prover messages preserve knowledge. -/
theorem finalBatchExtractor_preserving {E : Type} [CommRing E] [DecidableEq E] {n : ℕ}
    (candidate : Table E n) (claims : List (Claim E n)) (active : Bool) :
    (finalBatchExtractor candidate claims active).IsProverPreserving
      (Protocol.public .receiver E fun _ => scalarRounds E n .done).roles := by
  exact ⟨(fun _ impossible => by cases impossible),
    fun _ => closingExtractor_preserving _ _ _ _⟩

/-- Fold prover checks strengthen the state; the supplied suffix preserves knowledge. -/
theorem foldExtractor_preserving {K E : Type} [Semiring K] [CommRing E] [DecidableEq E]
    {vars : ℕ} (enc : Encoding K vars) (ι : K →+* E) (γ : ℝ)
    (decoders : (lanes : ℕ) → ListDecoder (E := E) enc lanes)
    {rest : Protocol}
    (finish : (word : Word E 0 (2 ^ (vars + enc.rate))) →
      (claim : Claim E (0 + vars)) → (active : Bool) →
      RoundExtractor rest.tree (candidateState enc ι γ word [claim] active))
    (preserving : ∀ word claim active, (finish word claim active).IsProverPreserving rest.roles)
    (lanes : ℕ) (word : Word E lanes (2 ^ (vars + enc.rate)))
    (claim : Claim E (lanes + vars)) (active : Bool) :
    (foldExtractor enc (fun _ w f => Close γ w (enc.interleave ι f)) decoders finish lanes word
      claim active).IsProverPreserving
      (scalarRounds E lanes rest).roles := by
  induction lanes generalizing active with
  | zero => exact preserving _ _ _
  | succ lanes ih =>
      refine ⟨?_, fun q => ⟨?_, fun r => ih _ _ _⟩⟩
      · intro q _ witness good
        exact ⟨(Bool.and_eq_true_iff.mp good.1).1, good.2⟩
      · intro r impossible
        cases impossible

/-- A plaintext's proximity state gives a valid list preimage for its prover backward map. -/
theorem lastExtractor_preserving {K E : Type} [Field K] [Field E] [DecidableEq E]
    {tail : ℕ} (lanes queries : ℕ) (enc : Encoding K tail) (ι : K →+* E)
    (sec : LevelSecurity) (decoder : ListDecoder (E := E) enc 0)
    (correct : decoder.Correct ι (radius enc sec) (listBound enc sec))
    (word : Word E 0 (2 ^ (tail + enc.rate))) (claim : Claim E (0 + tail)) (active : Bool) :
    (lastExtractor lanes queries enc ι
      (fun w f => Close (radius enc sec) w (enc.interleave ι f)) decoder word claim
        active).IsProverPreserving
      (transition E (.last lanes tail enc queries)).roles := by
  refine ⟨?_, fun candidate => ⟨?_, fun xs => finalBatchExtractor_preserving _ _ _⟩⟩
  · intro candidate _ witness good
    change (candidateState enc ι (radius enc sec) word [claim] active).holds
      (listLift (decoder.decode word)
        (castTable (Nat.zero_add tail)) claim.Holds candidate)
    have hclaim := good.2.2 claim (List.mem_singleton_self _)
    have lift := listLift_of_valid_preimage
      (decoder.decode word)
      (castTable (Nat.zero_add tail)) claim.Holds candidate
      ⟨_, (correct.mem_iff _ _).mpr good.2.1, castTable_inverse _ _, hclaim⟩
    exact ⟨good.1, (correct.mem_iff _ _).mp lift.1,
      by simpa only [List.mem_singleton, forall_eq] using lift.2.2⟩
  · intro xs impossible
    cases impossible

/-- New oracle messages and OOD answers retain the old knowledge predicate. -/
theorem boundaryExtractor_preserving {K E : Type} [Semiring K] [CommRing E]
    [DecidableEq E] {tail : ℕ} (lanes queries : ℕ) (enc : Encoding K tail)
    (ι : K →+* E) (sec : LevelSecurity) (rest : Schedule K tail)
    (nextSec : SecurityParameters rest)
    (decoder : ListDecoder (E := E) enc 0) (decoders : DecoderFamily (E := E) rest)
    (suffix : (word : oracleMessage E rest) → (claims : List (Claim E tail)) →
      (active : Bool) → RoundExtractor (opening E rest).tree
        (levelState ι rest nextSec word claims active))
    (preserving : ∀ word claims active,
      (suffix word claims active).IsProverPreserving (opening E rest).roles)
    (word : Word E 0 (2 ^ (tail + enc.rate))) (claim : Claim E (0 + tail)) (active : Bool) :
    (boundaryExtractor lanes queries enc ι
      (fun w f => Close (radius enc sec) w (enc.interleave ι f))
      rest (proximityFamily ι rest nextSec) decoder decoders suffix
      word claim active).IsProverPreserving
      (transition E (.more lanes enc queries rest)).roles := by
  refine ⟨fun _ _ good => good, fun _ => ⟨?_, fun _ => ⟨?_, fun _ => ⟨?_, ?_⟩⟩⟩⟩
  · intro _ impossible
    cases impossible
  · intro _ _ _ good
    exact good
  · intro _ impossible
    cases impossible
  · exact fun _ => preserving _ _ _

/-- All prover messages of an extension-field opening preserve its concrete list witness. -/
theorem levelExtractor_preserving {K E : Type} [Field K] [Field E]
    [DecidableEq E] (ι : K →+* E) {n : ℕ} (s : Schedule K n)
    (sec : SecurityParameters s) (decoders : DecoderFamily (E := E) s)
    (correct : decoders.Correct ι s sec)
    (word : oracleMessage E s) (claims : List (Claim E n)) (active : Bool) :
    (levelExtractor ι s (proximityFamily ι s sec) decoders word claims active).IsProverPreserving
      (opening E s).roles := by
  induction s generalizing active with
  | last lanes tail enc queries =>
      exact ⟨(fun _ impossible => by cases impossible), fun _ =>
        foldExtractor_preserving enc ι _ decoders _
          (lastExtractor_preserving lanes queries enc ι sec (decoders 0) (correct 0)) _ _ _ _⟩
  | more lanes enc queries rest ih =>
      exact ⟨(fun _ impossible => by cases impossible), fun _ =>
        foldExtractor_preserving enc ι _ decoders.1 _
          (boundaryExtractor_preserving lanes queries enc ι sec.1 rest sec.2 (decoders.1 0)
            decoders.2 _
            (ih sec.2 decoders.2 correct.2)) _ _ _ _⟩

/-- Replacing the verifier root map leaves every prover-preservation obligation unchanged. -/
theorem openingExtractor_preserving {K E : Type} [Field K] [Field E]
    [DecidableEq K] [DecidableEq E] (ι : K →+* E) {n : ℕ}
    (s : Schedule K n) (sec : SecurityParameters s) (decoders : DecoderFamily (E := E) s)
    (correct : decoders.Correct ι s sec)
    (word : oracleMessage K s) (claims : List (Claim E n)) (decoder : InitialDecoder s) :
    (openingExtractor ι s (proximityFamily ι s sec)
      (openingState ι s sec word claims).holds decoders word claims decoder).IsProverPreserving
        (opening E s).roles := by
  cases s <;>
    exact ⟨(fun _ impossible => by cases impossible),
      (levelExtractor_preserving ι _ sec decoders correct (fun x u => ι (word x u)) claims true).2⟩

end Whir
