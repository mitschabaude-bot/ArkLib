/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.ProofSystem.Whir.Errors

/-!
# Johnson parameter arithmetic for WHIR

The dimension rate determines the radius and list budget. The scalar MCA theorem uses the
strictly smaller reduced rate, at the same radius.
-/

@[expose] public section

namespace Whir

/-- Every encoded level has a positive dimension rate. -/
theorem dimensionRate_pos {K : Type} {vars : ℕ} (enc : Encoding K vars) :
    0 < dimensionRate enc := by
  unfold dimensionRate
  positivity

/-- Positive inverse-rate exponent places the dimension rate strictly below one. -/
theorem dimensionRate_lt_one {K : Type} {vars : ℕ} (enc : Encoding K vars)
    (h : 0 < enc.rate) : dimensionRate enc < 1 := by
  unfold dimensionRate
  apply (div_lt_one (by positivity)).mpr
  exact_mod_cast pow_lt_pow_right₀ (by decide : 1 < 2) (Nat.lt_add_of_pos_right h)

/-- The Johnson regime has positive analysis radius. -/
theorem radius_pos {K : Type} {vars : ℕ} {enc : Encoding K vars}
    {sec : LevelSecurity} (valid : sec.Valid enc) : 0 < radius enc sec := by
  exact sub_pos.mpr valid.2.2.2.2

/-- Every analysis radius is below one. -/
theorem radius_lt_one {K : Type} {vars : ℕ} {enc : Encoding K vars}
    {sec : LevelSecurity} (valid : sec.Valid enc) : radius enc sec < 1 := by
  unfold radius
  have := Real.sqrt_nonneg (dimensionRate enc)
  linarith [valid.2.2.2.1]

/-- The real Johnson list budget is positive. -/
theorem listBound_pos {K : Type} {vars : ℕ} {enc : Encoding K vars}
    {sec : LevelSecurity} (valid : sec.Valid enc) : 0 < listBound enc sec := by
  unfold listBound
  exact one_div_pos.mpr (mul_pos (mul_pos (by norm_num) valid.2.2.2.1)
    (Real.sqrt_pos.mpr (dimensionRate_pos enc)))

/-- The Johnson list budget contains at least one codeword. -/
theorem one_le_listBound {K : Type} {vars : ℕ} {enc : Encoding K vars}
    {sec : LevelSecurity} (valid : sec.Valid enc) : 1 ≤ listBound enc sec := by
  have hs := Real.sqrt_nonneg (dimensionRate enc)
  have hsp := Real.sqrt_pos.mpr (dimensionRate_pos enc)
  have hden : 0 < 2 * sec.slack * Real.sqrt (dimensionRate enc) :=
    mul_pos (mul_pos (by norm_num) valid.2.2.2.1) hsp
  unfold listBound
  apply (le_div_iff₀ hden).mpr
  nlinarith [valid.2.2.2.2, sq_nonneg (Real.sqrt (dimensionRate enc) - 1 / 2)]

/-- The reduced rate is bounded above by the dimension rate. -/
theorem reducedRate_le_dimensionRate {K : Type} {vars : ℕ} (enc : Encoding K vars) :
    reducedRate enc ≤ dimensionRate enc := by
  unfold reducedRate dimensionRate
  gcongr
  exact_mod_cast Nat.sub_le (2 ^ vars) 1

/-- The analysis radius lies strictly inside the reduced-rate Johnson regime. -/
theorem radius_lt_reduced_johnson {K : Type} {vars : ℕ} {enc : Encoding K vars}
    {sec : LevelSecurity} (valid : sec.Valid enc) :
    radius enc sec < 1 - Real.sqrt (reducedRate enc) := by
  have hs := Real.sqrt_le_sqrt (reducedRate_le_dimensionRate enc)
  unfold radius
  linarith [valid.2.2.2.1]

/-- The code dimension is strictly smaller than its number of columns. -/
theorem dimension_lt_columns {K : Type} {vars : ℕ} {enc : Encoding K vars}
    {sec : LevelSecurity} (valid : sec.Valid enc) : 2 ^ vars < 2 ^ (vars + enc.rate) := by
  exact pow_lt_pow_right₀ (by decide) (Nat.lt_add_of_pos_right valid.2.1)

/-- Positive message-variable count excludes the dimension-one MCA edge. -/
theorem dimension_one_lt {K : Type} {vars : ℕ} {enc : Encoding K vars}
    {sec : LevelSecurity} (valid : sec.Valid enc) : 1 < 2 ^ vars := by
  exact one_lt_pow₀ (by decide : 1 < (2 : ℕ)) (Nat.ne_of_gt valid.1)

/-- The agreement threshold exceeds the code dimension. -/
theorem dimension_lt_agreement {K : Type} {vars : ℕ} {enc : Encoding K vars}
    {sec : LevelSecurity} (valid : sec.Valid enc) :
    (2 ^ vars : ℝ) < (1 - radius enc sec) * 2 ^ (vars + enc.rate) := by
  have hR := dimensionRate_pos enc
  have hR1 := dimensionRate_lt_one enc valid.2.1
  have hs := Real.sqrt_nonneg (dimensionRate enc)
  have hs1 : Real.sqrt (dimensionRate enc) < 1 := by
    nlinarith [Real.sq_sqrt hR.le]
  have hs2 := Real.sq_sqrt hR.le
  have hle : dimensionRate enc ≤ Real.sqrt (dimensionRate enc) := by nlinarith
  have hN : (0 : ℝ) < 2 ^ (vars + enc.rate) := by positivity
  have h := mul_lt_mul_of_pos_right
    (show dimensionRate enc < Real.sqrt (dimensionRate enc) + sec.slack by
      linarith [valid.2.2.2.1]) hN
  dsimp [dimensionRate] at h
  rw [div_mul_cancel₀ _ hN.ne'] at h
  convert h using 1
  dsimp [radius, dimensionRate]
  ring

/-- Scalar Johnson MCA on the encoder's arbitrary injective evaluation domain. -/
theorem mcaError_additive_le {K E : Type} [Field K] [Field E] [Fintype E]
    [SampleableType E] {vars : ℕ} (enc : Encoding K vars) (ι : K →+* E)
    (sec : LevelSecurity) (valid : sec.Valid enc) :
    CoreDefinitions.mcaError (CoreDefinitions.AffineLineGenerator E)
      (ReedSolomon.code (enc.extendedDomain ι) (2 ^ vars)) (radius enc sec) ≤
        mcaError (E := E) enc sec := by
  let n := 2 ^ (vars + enc.rate)
  let D := 2 ^ vars - 1
  let η := 1 - Real.sqrt (reducedRate enc) - radius enc sec
  have hD : 1 ≤ D := by dsimp [D]; have := dimension_one_lt valid; omega
  have hDn : D ≤ n - 2 := by dsimp [D, n]; have := dimension_lt_columns valid; omega
  have hη : 0 < η := sub_pos.mpr (radius_lt_reduced_johnson valid)
  have hrho : ReedSolomon.HiddenDerivative.johnsonRhoMinus n D = reducedRate enc := by
    simp only [ReedSolomon.HiddenDerivative.johnsonRhoMinus, reducedRate, n, D,
      Nat.cast_pow, Nat.cast_ofNat]
  have hA : ReedSolomon.HiddenDerivative.johnsonAgreement n D η = 1 - radius enc sec := by
    rw [ReedSolomon.HiddenDerivative.johnsonAgreement, hrho]
    dsimp [η]
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
