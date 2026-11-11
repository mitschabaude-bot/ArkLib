/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.ProofSystem.Whir.Errors

/-!
# Johnson parameter arithmetic for WHIR

The reduced rate determines the radius, the list budget and the scalar MCA theorem's slack.
-/

@[expose] public section

namespace Whir

/-- A positive message-variable count gives a positive reduced rate. -/
theorem reducedRate_pos {K : Type} {vars : ℕ} (enc : Encoding K vars) (h : 0 < vars) :
    0 < reducedRate enc := by
  unfold reducedRate
  have : 1 < 2 ^ vars := one_lt_pow₀ (by decide : 1 < (2 : ℕ)) (Nat.ne_of_gt h)
  have : (0 : ℝ) < ((2 ^ vars - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 ^ vars - 1)
  positivity

/-- The analysis radius is positive. -/
theorem radius_pos {K : Type} {vars : ℕ} {enc : Encoding K vars}
    {sec : LevelSecurity} (valid : sec.Valid enc) : 0 < radius enc sec := by
  unfold radius
  linarith [valid.2.2.2.2]

/-- Every analysis radius is below one. -/
theorem radius_lt_one {K : Type} {vars : ℕ} {enc : Encoding K vars}
    {sec : LevelSecurity} (valid : sec.Valid enc) : radius enc sec < 1 := by
  unfold radius
  have := Real.sqrt_nonneg (reducedRate enc)
  linarith [valid.2.2.2.1]

/-- The real Johnson list budget is positive. -/
theorem listBound_pos {K : Type} {vars : ℕ} {enc : Encoding K vars}
    {sec : LevelSecurity} (valid : sec.Valid enc) : 0 < listBound enc sec := by
  unfold listBound
  exact one_div_pos.mpr (mul_pos (mul_pos (by norm_num) valid.2.2.2.1)
    (Real.sqrt_pos.mpr (reducedRate_pos enc valid.1)))

/-- The Johnson list budget contains at least one codeword. -/
theorem one_le_listBound {K : Type} {vars : ℕ} {enc : Encoding K vars}
    {sec : LevelSecurity} (valid : sec.Valid enc) : 1 ≤ listBound enc sec := by
  have hsp := Real.sqrt_pos.mpr (reducedRate_pos enc valid.1)
  have hden : 0 < 2 * sec.slack * Real.sqrt (reducedRate enc) :=
    mul_pos (mul_pos (by norm_num) valid.2.2.2.1) hsp
  unfold listBound
  apply (le_div_iff₀ hden).mpr
  nlinarith [valid.2.2.2.2, valid.2.2.2.1, sq_nonneg (Real.sqrt (reducedRate enc) - 1 / 2)]

/-- The code dimension is strictly smaller than its number of columns. -/
theorem dimension_lt_columns {K : Type} {vars : ℕ} {enc : Encoding K vars}
    {sec : LevelSecurity} (valid : sec.Valid enc) : 2 ^ vars < 2 ^ (vars + enc.rate) := by
  exact pow_lt_pow_right₀ (by decide) (Nat.lt_add_of_pos_right valid.2.1)

/-- Positive message-variable count excludes the dimension-one MCA edge. -/
theorem dimension_one_lt {K : Type} {vars : ℕ} {enc : Encoding K vars}
    {sec : LevelSecurity} (valid : sec.Valid enc) : 1 < 2 ^ vars := by
  exact one_lt_pow₀ (by decide : 1 < (2 : ℕ)) (Nat.ne_of_gt valid.1)

/-- The agreement threshold exceeds the code dimension: `√ρ⁻ · 2^(vars + rate) ≥ 2^vars`. -/
theorem dimension_lt_agreement {K : Type} {vars : ℕ} {enc : Encoding K vars}
    {sec : LevelSecurity} (valid : sec.Valid enc) :
    (2 ^ vars : ℝ) < (1 - radius enc sec) * 2 ^ (vars + enc.rate) := by
  have hN : (0 : ℝ) < 2 ^ (vars + enc.rate) := by positivity
  have hone := dimension_one_lt valid
  have hnat : 2 ^ vars * 2 ^ vars ≤ (2 ^ vars - 1) * 2 ^ (vars + enc.rate) := by
    have h2 : 2 * 2 ^ vars ≤ 2 ^ (vars + enc.rate) := by
      rw [pow_add]
      have : 2 ≤ 2 ^ enc.rate := by
        simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 2) valid.2.1
      nlinarith
    have : 2 ^ vars ≤ 2 * (2 ^ vars - 1) := by omega
    calc 2 ^ vars * 2 ^ vars ≤ 2 * (2 ^ vars - 1) * 2 ^ vars := Nat.mul_le_mul_right _ this
      _ = (2 ^ vars - 1) * (2 * 2 ^ vars) := by ring
      _ ≤ (2 ^ vars - 1) * 2 ^ (vars + enc.rate) := Nat.mul_le_mul_left _ h2
  have hsq : (2 ^ vars : ℝ) ≤ Real.sqrt (reducedRate enc) * 2 ^ (vars + enc.rate) := by
    rw [← Real.sqrt_sq hN.le, ← Real.sqrt_mul (reducedRate_pos enc valid.1).le]
    apply Real.le_sqrt_of_sq_le
    have hcast : ((2 ^ vars * 2 ^ vars : ℕ) : ℝ) ≤
        (((2 ^ vars - 1) * 2 ^ (vars + enc.rate) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    unfold reducedRate
    rw [div_mul_eq_mul_div, le_div_iff₀ hN]
    push_cast at hcast ⊢
    nlinarith
  have hgap : 0 < sec.slack * 2 ^ (vars + enc.rate) := mul_pos valid.2.2.2.1 hN
  have : 1 - radius enc sec = Real.sqrt (reducedRate enc) + sec.slack := by
    unfold radius; ring
  rw [this, add_mul]
  linarith

/-- Scalar Johnson MCA on the encoder's arbitrary injective evaluation domain. -/
theorem mcaError_additive_le {K E : Type} [Field K] [Field E] [Fintype E]
    [SampleableType E] {vars : ℕ} (enc : Encoding K vars) (ι : K →+* E)
    (sec : LevelSecurity) (valid : sec.Valid enc) :
    CoreDefinitions.mcaError (CoreDefinitions.AffineLineGenerator E)
      (ReedSolomon.code (enc.extendedDomain ι) (2 ^ vars)) (radius enc sec) ≤
        mcaError (E := E) enc sec := by
  let n := 2 ^ (vars + enc.rate)
  let D := 2 ^ vars - 1
  let η := sec.slack
  have hD : 1 ≤ D := by dsimp [D]; have := dimension_one_lt valid; omega
  have hDn : D ≤ n - 2 := by dsimp [D, n]; have := dimension_lt_columns valid; omega
  have hη : 0 < η := valid.2.2.2.1
  have hrho : ReedSolomon.HiddenDerivative.johnsonRhoMinus n D = reducedRate enc := by
    simp only [ReedSolomon.HiddenDerivative.johnsonRhoMinus, reducedRate, n, D,
      Nat.cast_pow, Nat.cast_ofNat]
  have hA : ReedSolomon.HiddenDerivative.johnsonAgreement n D η = 1 - radius enc sec := by
    rw [ReedSolomon.HiddenDerivative.johnsonAgreement, hrho]
    dsimp [η, radius]
    ring
  have ha : ReedSolomon.HiddenDerivative.johnsonAgreement n D η ≤ 1 := by
    rw [hA]
    linarith [radius_pos valid]
  have hb := ReedSolomon.mcaError_affineLine_johnson_le
    (enc.extendedDomain ι) hD hDn hη ha
  rw [hA, sub_sub_cancel] at hb
  have hcount := ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate
    hD hDn hη ha (Nat.le_ceil _)
  have hdim : D + 1 = 2 ^ vars := by dsimp [D]; have := dimension_one_lt valid; omega
  rw [hdim] at hb
  refine (hb.trans (min_le_right _ _)).trans ?_
  apply ENNReal.ofReal_le_ofReal
  rw [hA] at hcount
  refine (div_le_div_of_nonneg_right hcount
    (show (0 : ℝ) ≤ Fintype.card E by positivity)).trans_eq ?_
  unfold mcaNumerator
  dsimp [ReedSolomon.HiddenDerivative.johnsonComparisonEstimate,
    ReedSolomon.HiddenDerivative.johnsonComparisonShift,
    ReedSolomon.HiddenDerivative.johnsonComparisonMultiplicity,
    ReedSolomon.HiddenDerivative.johnsonGamma]
  rw [hA]
  simp only [sub_sub_cancel, Nat.cast_max, Nat.cast_ofNat, hrho]
  simp only [η, n, Nat.cast_pow, Nat.cast_ofNat]

end Whir
