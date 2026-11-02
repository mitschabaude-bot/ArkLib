/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Aleph
-/
module

public import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds.UniqueDecoding.Curves
public import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-!
# Reed--Solomon CA in the unique-decoding range

This module proves the BCHKS25 correlated-agreement bound for lines below the finite-length
half-distance boundary, as the case `M = 1` of the bound for curves
(`UniqueDecoding.card_goodCoeffs_le`, `UniqueDecoding/Curves.lean`).

## Main result

- `rs_epsCa_le_in_unique_decoding_range` is [BCHKS25, Theorem 1.3].

## References

- [BCHKS25] Theorem 1.3.
-/

@[expose] public section

namespace CodingTheory

open scoped NNReal
open CoreDefinitions ProximityGap

section ReedSolomon

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [SampleableType F] [DecidableEq F]

open scoped NNReal ProbabilityTheory in
omit [DecidableEq ι] in
private theorem rs_fold_probability_le_bound_of_not_joint_proximity
    (domain : ι ↪ F) (k : ℕ) (δ_fld δ_int : ℝ≥0)
    (h_ud : (δ_fld : ℝ) ≤
      (1 - (k : ℝ) / Fintype.card ι) / 2 - 1 / Fintype.card ι)
    (h_pos : 0 < δ_fld) (h_lt : δ_fld < δ_int)
    (u : Fin 2 → ι → F)
    (hjoint : ¬ Code.jointProximity
      (C := (ReedSolomon.code domain k : Set (ι → F))) (u := u) δ_int) :
    Pr{let z ← $ᵗ F}[
      δᵣ(u 0 + z • u 1, ReedSolomon.code domain k) ≤ δ_fld] ≤
      ENNReal.ofReal
        (max
          ((1 - (k : ℝ) / Fintype.card ι - (δ_fld : ℝ)) /
            ((δ_fld : ℝ) *
              (1 - (k : ℝ) / Fintype.card ι - 2 * (δ_fld : ℝ)) *
              Fintype.card F))
          ((δ_int : ℝ) /
            (((δ_int : ℝ) - (δ_fld : ℝ)) * Fintype.card F))) := by
  classical
  let good := UniqueDecoding.goodCoeffs domain k u δ_fld
  let T₁ : ℝ :=
    (1 - (k : ℝ) / Fintype.card ι - (δ_fld : ℝ)) /
      ((δ_fld : ℝ) *
        (1 - (k : ℝ) / Fintype.card ι - 2 * (δ_fld : ℝ)))
  let T₂ : ℝ := (δ_int : ℝ) / ((δ_int : ℝ) - (δ_fld : ℝ))
  have hcard : (good.card : ℝ) ≤ max T₁ T₂ := by
    have := UniqueDecoding.card_goodCoeffs_le domain k 1 u δ_fld δ_int h_ud h_pos h_lt hjoint
    rwa [Nat.cast_one, one_mul] at this
  have hline : ∀ z : F, Curve.polynomialCurveEval u z = u 0 + z • u 1 := fun z => by
    simp only [Curve.polynomialCurveEval, Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero,
      pow_one, one_smul]
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  rw [SampleableType.prEvent_uniformSample_eq_ofReal]
  apply ENNReal.ofReal_le_ofReal
  have hfilt : (Finset.univ.filter fun z : F =>
      δᵣ(u 0 + z • u 1, (ReedSolomon.code domain k : Set (ι → F))) ≤ δ_fld) = good := by
    simp only [good, UniqueDecoding.goodCoeffs, hline]
  rw [hfilt]
  change (good.card : ℝ) / Fintype.card F ≤
    max
      ((1 - (k : ℝ) / Fintype.card ι - (δ_fld : ℝ)) /
        ((δ_fld : ℝ) *
          (1 - (k : ℝ) / Fintype.card ι - 2 * (δ_fld : ℝ)) *
          Fintype.card F))
      ((δ_int : ℝ) /
        (((δ_int : ℝ) - (δ_fld : ℝ)) * Fintype.card F))
  calc
    (good.card : ℝ) / Fintype.card F ≤
        max T₁ T₂ / Fintype.card F :=
      div_le_div_of_nonneg_right hcard hq.le
    _ = max (T₁ / Fintype.card F) (T₂ / Fintype.card F) := by
      symm
      exact max_div_div_right hq.le T₁ T₂
    _ = max
        ((1 - (k : ℝ) / Fintype.card ι - (δ_fld : ℝ)) /
          ((δ_fld : ℝ) *
            (1 - (k : ℝ) / Fintype.card ι - 2 * (δ_fld : ℝ)) *
            Fintype.card F))
        ((δ_int : ℝ) /
          (((δ_int : ℝ) - (δ_fld : ℝ)) * Fintype.card F)) := by
      apply congrArg₂ max
      · simp only [T₁]
        rw [div_div]
      · simp only [T₂]
        rw [div_div]

open scoped NNReal in
open scoped ProbabilityTheory in
omit [DecidableEq ι] in
/-- Bounds Reed--Solomon CA error when `δ_fld` lies in the finite-length unique-decoding range
`0 < δ_fld ≤ (1 - ρ) / 2 - 1 / n`, and `δ_fld < δ_int`. -/
theorem rs_epsCa_le_in_unique_decoding_range
    (domain : ι ↪ F) (k : ℕ) (δ_fld δ_int : ℝ≥0)
    (_h_ud : (δ_fld : ℝ) ≤ (1 - (k : ℝ) / Fintype.card ι) / 2 - 1 / Fintype.card ι)
    (_h_pos : 0 < δ_fld) (_h_lt : δ_fld < δ_int) :
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / n
    let bound : ℝ :=
      max ((1 - ρ - δ_fld) / (δ_fld * (1 - ρ - 2 * δ_fld) * Fintype.card F))
          ((δ_int : ℝ) / ((δ_int - δ_fld) * Fintype.card F))
    epsCa (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F))) δ_fld δ_int ≤
      ENNReal.ofReal bound := by
  classical
  dsimp
  simp only [epsCa_eq]
  refine iSup_le fun u => ?_
  by_cases hj : Code.jointProximity
      (C := (ReedSolomon.code domain k : Set (ι → F))) (u := u) δ_int
  · rw [ite_eq_left hj]
    exact zero_le
  · rw [ite_eq_right hj]
    exact rs_fold_probability_le_bound_of_not_joint_proximity
      domain k δ_fld δ_int _h_ud _h_pos _h_lt u hj

end ReedSolomon

end CodingTheory
