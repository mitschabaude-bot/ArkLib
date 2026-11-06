/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.ProofSystem.Whir.Preservation

/-!
# Local knowledge bounds for WHIR extractors

Each verifier message has its own fixed-prefix event bound. Recursive assembly follows the
protocol tree and retains the exact Annex B errors.
-/

@[expose] public section

open Interaction Interaction.Oracle Interaction.Oracle.Security OracleComp OracleSpec
open scoped ProbabilityTheory

namespace Whir

/-- A bound on the existential bad event is the bound required by the local game interface. -/
theorem localGame_bounded {Moves : Type} {next : Moves → Oracle.TypeTree}
    {state : KnowledgeState} (extractor : RoundExtractor (.public Moves next) state)
    (sample : ProbComp Moves) (error : ENNReal)
    (bound : Pr{let move ← sample}[extractor.badChallenge move] ≤ error) :
    (extractor.localGame sample).IsBounded (fun _ => error) := by
  rw [_root_.RoundByRound.GameFamily.isBounded_iff]
  exact fun _ _ => bound

/-- Closing's local bad event is a degree-two collision for its fixed plaintext. -/
theorem closing_local_bound {E : Type} [Field E]
    [Fintype E] [SampleableType E] {n : ℕ} (candidate : Table E (n + 1))
    (claim : Claim E (n + 1)) (active : Bool) (q : Quadratic E) :
    Pr{let r ←$ᵗ E}[∃ _ : PUnit.{1},
      ¬ (plaintextState candidate [claim]
        (active && (Sumcheck.compressedOps 1).accept claim.value q)).holds
          (PUnit.unit : PUnit.{1}) ∧
      (plaintextState (foldMessageOne (vars := 0) candidate r)
        [⟨foldMessageOne (vars := 0) claim.weight r, evalQuadratic claim.value q r⟩]
        (active && (Sumcheck.compressedOps 1).accept claim.value q)).holds
          (PUnit.unit : PUnit.{1})] ≤
      (2 : ENNReal) / Fintype.card E := by
  classical
  by_cases lost : ¬ claim.Holds candidate
  · exact (prEvent_mono ($ᵗ E) _ _ (fun r ⟨_, _, good⟩ =>
      good.2 _ (List.mem_singleton_self _))).trans
      (prob_closing_escape_le candidate claim q lost)
  · exact (prEvent_eq_zero_of_forall_not ($ᵗ E) _ (by
      rintro r ⟨_, bad, good⟩
      exact bad ⟨good.1, by
        simpa only [List.mem_singleton, forall_eq] using not_not.mp lost⟩)).le.trans zero_le

/-- Every closing receiver challenge has the fixed-plaintext Sumcheck error. -/
theorem closingExtractor_bounded {E : Type} [Field E] [DecidableEq E]
    [Fintype E] [SampleableType E] (count : ℕ) (candidate : Table E count)
    (claim : Claim E count) (active : Bool) :
    (closingExtractor count candidate claim active).IsLocallyBounded
      (scalarRounds E count .done).roles
      (scalarChallenges ((2 : ENNReal) / Fintype.card E) (rest := .done) PUnit.unit count) := by
  induction count generalizing active with
  | zero => trivial
  | succ count ih =>
      intro q
      refine ⟨localGame_bounded _ _ _ ?_, fun r => ih _ _ _⟩
      refine (prEvent_mono ($ᵗ E) _ _ ?_).trans (closing_local_bound candidate claim active q)
      rintro r ⟨witness, bad, good⟩
      exact ⟨PUnit.unit, bad, good⟩

/-- Final batching's fixed candidate incurs the power-batching error, without a list factor. -/
theorem final_batch_local_bound {E : Type} [Field E] [DecidableEq E]
    [Fintype E] [SampleableType E] {n : ℕ}
    (candidate : Table E n) (claims : List (Claim E n)) (active : Bool) :
    Pr{let r ←$ᵗ E}[(finalBatchExtractor candidate claims active).badChallenge r] ≤
      ((claims.length - 1 : ℕ) : ENNReal) / Fintype.card E := by
  classical
  by_cases lost : ∃ c ∈ claims, ¬ c.Holds candidate
  · exact (prEvent_mono ($ᵗ E) _ _ (fun r ⟨_, _, good⟩ =>
      good.2 _ (List.mem_singleton_self _))).trans
        (prob_final_batch_escape_le claims candidate lost)
  · exact (prEvent_eq_zero_of_forall_not ($ᵗ E) _ (by
      rintro r ⟨_, bad, good⟩
      exact bad ⟨good.1, by simpa only [not_exists, not_and, not_not] using lost⟩)).le.trans zero_le

/-- Final batching and its entire closing block satisfy their concrete challenge schedule. -/
theorem finalBatchExtractor_bounded {E : Type} [Field E] [DecidableEq E]
    [Fintype E] [SampleableType E] {n : ℕ}
    (candidate : Table E n) (claims : List (Claim E n)) (active : Bool) :
    (finalBatchExtractor candidate claims active).IsLocallyBounded
      (Protocol.public .receiver E fun _ => scalarRounds E n .done).roles
      ⟨⟨$ᵗ E, ((claims.length - 1 : ℕ) : ENNReal) / Fintype.card E⟩,
        fun _ => scalarChallenges ((2 : ENNReal) / Fintype.card E)
          (rest := .done) PUnit.unit n⟩ := by
  exact ⟨localGame_bounded _ _ _ (final_batch_local_bound candidate claims active),
    fun _ => closingExtractor_bounded _ _ _ _⟩

/-- At an encoded fold, a failed checked lift pays only list MCA plus false-claim roots. -/
theorem fold_local_bound {K E : Type} [Field K] [Field E] [DecidableEq E]
    [Fintype E] [SampleableType E] {vars lanes : ℕ} (enc : Encoding K vars) (ι : K →+* E)
    (sec : LevelSecurity)
    (decoders : (lanes : ℕ) → ListDecoder (E := E) enc lanes)
    (correct : ∀ lanes, (decoders lanes).Correct ι (radius enc sec) (listBound enc sec))
    (valid : sec.Valid enc) (contract : EncodingContract enc ι)
    (word : Word E (lanes + 1) (2 ^ (vars + enc.rate)))
    (claim : Claim E ((lanes + 1) + vars)) (active : Bool) (q : Quadratic E) :
    Pr{let r ←$ᵗ E}[∃ f,
      ¬ (candidateState enc ι (radius enc sec) word [claim]
        (active && (Sumcheck.compressedOps 1).accept claim.value q)).holds
          (listLift ((decoders (lanes + 1)).decode word)
            (fun g => foldMessageOne g r) claim.Holds f) ∧
      (candidateState enc ι (radius enc sec) (foldRowsOne word r)
        [⟨foldMessageOne claim.weight r, evalQuadratic claim.value q r⟩]
        (active && (Sumcheck.compressedOps 1).accept claim.value q)).holds f] ≤
      foldError (E := E) enc sec := by
  classical
  have bound := prob_fold_lift_failure_le ι contract sec valid _ _
    (correct (lanes + 1))
    (correct lanes) word claim q
    (active && (Sumcheck.compressedOps 1).accept claim.value q)
  exact (prEvent_mono ($ᵗ E) _ _ (fun _ ⟨f, bad, good⟩ => ⟨f, good, bad⟩)).trans bound

/-- Encoded folds assemble the same local bound at every authored prefix of a round block. -/
theorem foldExtractor_bounded {K E : Type} [Field K] [Field E] [DecidableEq E]
    [Fintype E] [SampleableType E] {vars : ℕ} (enc : Encoding K vars) (ι : K →+* E)
    (sec : LevelSecurity)
    (decoders : (lanes : ℕ) → ListDecoder (E := E) enc lanes)
    (correct : ∀ lanes, (decoders lanes).Correct ι (radius enc sec) (listBound enc sec))
    (valid : sec.Valid enc) (contract : EncodingContract enc ι)
    {rest : Protocol}
    (finish : (word : Word E 0 (2 ^ (vars + enc.rate))) →
      (claim : Claim E (0 + vars)) → (active : Bool) →
      RoundExtractor rest.tree (candidateState enc ι (radius enc sec) word [claim] active))
    (schedule : RoundExtractor.ChallengeSchedule rest.tree rest.roles)
    (bounded : ∀ word claim active,
      (finish word claim active).IsLocallyBounded rest.roles schedule)
    (lanes : ℕ) (word : Word E lanes (2 ^ (vars + enc.rate)))
    (claim : Claim E (lanes + vars)) (active : Bool) :
    (foldExtractor enc (fun _ w f => Close (radius enc sec) w (enc.interleave ι f)) decoders
      finish lanes word claim active).IsLocallyBounded
      (scalarRounds E lanes rest).roles
      (scalarChallenges (foldError (E := E) enc sec) schedule lanes) := by
  induction lanes generalizing active with
  | zero => exact bounded _ _ _
  | succ lanes ih =>
      intro q
      exact ⟨localGame_bounded _ _ _
        (fold_local_bound enc ι sec decoders correct valid contract word claim active q),
        fun r => ih _ _ _⟩

end Whir
