/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.ProofSystem.Whir.LocalSecurity

/-! # Algebraic bad events for the public plaintext suffix -/

@[expose] public section

open Interaction Interaction.Oracle.Security OracleComp OracleSpec

namespace Whir

/-- A false fixed-plaintext claim list becomes true after power batching. -/
def BadFinalBatch {E : Type} [CommRing E] {n : ℕ}
    (candidate : Table E n) (claims : List (Claim E n)) (r : E) : Prop :=
  (∃ c ∈ claims, ¬ c.Holds candidate) ∧ (batch claims r).Holds candidate

/-- The public-plaintext batching event has a direct executable checker. -/
def checkBadFinalBatch {E : Type} [CommRing E] [DecidableEq E] {n : ℕ}
    (candidate : Table E n) (claims : List (Claim E n)) (r : E) : Bool :=
  claims.any (fun c => !decide (c.Holds candidate)) && decide ((batch claims r).Holds candidate)

/-- The final batching checker decides the false-claim root event. -/
theorem checkBadFinalBatch_iff {E : Type} [CommRing E] [DecidableEq E] {n : ℕ}
    (candidate : Table E n) (claims : List (Claim E n)) (r : E) :
    checkBadFinalBatch candidate claims r = true ↔ BadFinalBatch candidate claims r := by
  simp only [checkBadFinalBatch, Bool.and_eq_true, List.any_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_eq, BadFinalBatch]

/-- Final batching escape lies in the fixed-plaintext root event. -/
theorem finalBatch_escape_subset_bad {E : Type} [CommRing E] [DecidableEq E] {n : ℕ}
    (candidate : Table E n) (claims : List (Claim E n)) (active : Bool) (r : E)
    (escape : (finalBatchExtractor candidate claims active).badChallenge r) :
    BadFinalBatch candidate claims r := by
  obtain ⟨_, bad, good⟩ := escape
  refine ⟨?_, good.2 _ (List.mem_singleton_self _)⟩
  by_contra h
  apply bad
  exact ⟨good.1, by simpa only [not_exists, not_and, not_not] using h⟩

/-- The public plaintext singleton and its fixed claims are independent of hiding oracle columns. -/
theorem BadFinalBatch.mask_mono {E : Type} [CommRing E] {n lanes columns : ℕ}
    {small large : MaskedWord E lanes columns} (_h : MaskLE small large)
    {candidate : Table E n} {claims : List (Claim E n)} {r : E}
    (bad : BadFinalBatch candidate claims r) : BadFinalBatch candidate claims r := bad

/-- Final batching keeps the original fixed-candidate bound without a Johnson list factor. -/
theorem prob_badFinalBatch_le {E : Type} [Field E] [Fintype E] [SampleableType E] {n : ℕ}
    (candidate : Table E n) (claims : List (Claim E n)) :
    Pr{let r ←$ᵗ E}[BadFinalBatch candidate claims r] ≤
      ((claims.length - 1 : ℕ) : ENNReal) / Fintype.card E := by
  classical
  by_cases lost : ∃ c ∈ claims, ¬ c.Holds candidate
  · exact (prEvent_mono ($ᵗ E) _ _ (fun _ h => h.2)).trans
      (prob_final_batch_escape_le claims candidate lost)
  · exact (prEvent_eq_zero_of_forall_not ($ᵗ E) _ (fun _ h => lost h.1)).le.trans zero_le

/-- A false fixed-plaintext claim becomes true after a quadratic closing fold. -/
def BadClosing {E : Type} [CommRing E] {n : ℕ}
    (candidate : Table E (n + 1)) (claim : Claim E (n + 1)) (q : Quadratic E) (r : E) : Prop :=
  ¬ claim.Holds candidate ∧
    (⟨foldMessageOne (vars := 0) claim.weight r, evalQuadratic claim.value q r⟩ :
      Claim E n).Holds (foldMessageOne (vars := 0) candidate r)

/-- The closing checker evaluates only fixed public data and the scalar challenge. -/
def checkBadClosing {E : Type} [CommRing E] [DecidableEq E] {n : ℕ}
    (candidate : Table E (n + 1)) (claim : Claim E (n + 1)) (q : Quadratic E) (r : E) : Bool :=
  decide (¬ claim.Holds candidate ∧
    (⟨foldMessageOne (vars := 0) claim.weight r, evalQuadratic claim.value q r⟩ :
      Claim E n).Holds (foldMessageOne (vars := 0) candidate r))

/-- The closing checker decides the quadratic root event. -/
theorem checkBadClosing_iff {E : Type} [CommRing E] [DecidableEq E] {n : ℕ}
    (candidate : Table E (n + 1)) (claim : Claim E (n + 1)) (q : Quadratic E) (r : E) :
    checkBadClosing candidate claim q r = true ↔ BadClosing candidate claim q r := by
  simp only [checkBadClosing, decide_eq_true_eq, BadClosing]

/-- A closing challenge escape is a false plaintext claim becoming true. -/
theorem closing_escape_subset_bad {E : Type} [CommRing E] [DecidableEq E] {n : ℕ}
    (candidate : Table E (n + 1)) (claim : Claim E (n + 1)) (q : Quadratic E)
    (active : Bool) (r : E)
    (escape : ((closingExtractor (n + 1) candidate claim active q).2.2).badChallenge r) :
    BadClosing candidate claim q r := by
  obtain ⟨_, bad, good⟩ := escape
  refine ⟨?_, good.2 _ (List.mem_singleton_self _)⟩
  intro hc
  exact bad ⟨good.1, by simpa only [List.mem_singleton, forall_eq] using hc⟩

/-- Closing's fixed public plaintext and claim are independent of oracle hiding. -/
theorem BadClosing.mask_mono {E : Type} [CommRing E] {n lanes columns : ℕ}
    {small large : MaskedWord E lanes columns} (_h : MaskLE small large)
    {candidate : Table E (n + 1)} {claim : Claim E (n + 1)} {q : Quadratic E} {r : E}
    (bad : BadClosing candidate claim q r) : BadClosing candidate claim q r := bad

/-- Closing retains its original degree-two root bound. -/
theorem prob_badClosing_le {E : Type} [Field E] [Fintype E] [SampleableType E] {n : ℕ}
    (candidate : Table E (n + 1)) (claim : Claim E (n + 1)) (q : Quadratic E) :
    Pr{let r ←$ᵗ E}[BadClosing candidate claim q r] ≤ (2 : ENNReal) / Fintype.card E := by
  classical
  by_cases lost : ¬ claim.Holds candidate
  · exact (prEvent_mono ($ᵗ E) _ _ (fun _ h => h.2)).trans
      (prob_closing_escape_le candidate claim q lost)
  · exact (prEvent_eq_zero_of_forall_not ($ᵗ E) _ (fun _ h => lost h.1)).le.trans zero_le

end Whir
