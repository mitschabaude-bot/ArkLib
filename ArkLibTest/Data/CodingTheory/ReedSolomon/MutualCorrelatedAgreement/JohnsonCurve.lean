/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.CurveProbability
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fin.VecNotation

/-! # Acceptance cases for Johnson power-curve agreement -/

open Polynomial CoreDefinitions ReedSolomon ReedSolomon.HiddenDerivative

/-- At length `4`, degree `1` and slack `1/4`, the Johnson agreement fraction is `3/4`. -/
private theorem johnsonAgreement_four_one : johnsonAgreement 4 1 (1 / 4) = 3 / 4 := by
  have hsqrt : √((1 : ℝ) / 4) = 1 / 2 := by
    rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  simp only [johnsonAgreement, johnsonRhoMinus, Nat.cast_one, Nat.cast_ofNat, hsqrt]
  norm_num

private def natDomain (n : ℕ) : Fin n ↪ ℚ := ⟨fun i ↦ (i : ℚ), fun i j h ↦ by
  apply Fin.ext
  change (i.val : ℚ) = (j.val : ℚ) at h
  exact_mod_cast h⟩

/-- On the zero quadratic curve, at threshold `3 = (3/4) * 4`, some challenge outside at most
`2 E₀` exceptional challenges recovers the zero candidate with exact power agreement. -/
example : ∃ exceptional : Finset ℚ,
    (exceptional.card : ℝ) ≤ 2 * johnsonExceptionCount 4 1 3 (1 / 4) ∧
    ∃ z ∉ exceptional, HasExactPowerAgreement (natDomain 4) (0 : Fin 3 → Fin 4 → ℚ)
      (RingHom.id ℚ) 2 z 0 := by
  obtain ⟨exceptional, hcard, hgood⟩ := exists_johnson_curve_exactPowerAgreement_line_mul
    (n := 4) (D := 1) (A := 3) (ℓ := 2) (eta := 1 / 4) (natDomain 4) 0 le_rfl (by norm_num)
    (by norm_num) (by norm_num) (by rw [johnsonAgreement_four_one]; norm_num) (by norm_num)
  obtain ⟨z, hz⟩ := Finset.exists_notMem exceptional
  refine ⟨exceptional, by exact_mod_cast hcard, z, hz, ?_⟩
  convert hgood z hz 0 (by rw [degree_zero]; exact WithBot.bot_lt_coe _) ?_
  simp [polynomialAgreementSet, powerBatchedWord]

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def johnsonFiniteDomain : Fin 4 ↪ ZMod 5 := ⟨![0, 1, 2, 3], by decide⟩

/-- Over `ZMod 5` at length `4`, degree `1` and slack `1/4`, the MCA error of the cubic powers
generator at radius `1/4` is at most `min 1 (3 E₀ / 5)` with threshold `3`. -/
example : mcaError (univariatePowersGenerator (ZMod 5) 3) (code johnsonFiniteDomain 2)
    (1 / 4 : ℝ) ≤ min 1 (ENNReal.ofReal (3 * johnsonExceptionCount 4 1 3 (1 / 4) / 5)) := by
  have h := mcaError_univariatePowers_johnson_le (ℓ := 3) (D := 1) (eta := 1 / 4)
    johnsonFiniteDomain le_rfl (by simp) (by norm_num) (by norm_num)
    (by rw [Fintype.card_fin, johnsonAgreement_four_one]; norm_num)
  rw [Fintype.card_fin, johnsonAgreement_four_one,
    show ⌈(3 / 4 : ℝ) * ((4 : ℕ) : ℝ)⌉₊ = 3 by norm_num, ZMod.card] at h
  norm_num at h ⊢
  exact h
