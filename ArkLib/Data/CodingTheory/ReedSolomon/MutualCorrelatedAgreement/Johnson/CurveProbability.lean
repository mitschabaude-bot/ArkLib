/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Curve
public import ArkLib.Data.CodingTheory.ProximityGenerator.AffineGenerator
public import ArkLib.Data.CodingTheory.ProximityGenerator.Interleaving

/-!
# Johnson mutual correlated agreement error for power curves

Over a finite field, the Johnson exceptional-set bound for power curves at the threshold
`⌈a n⌉₊`, with `a = √(D / n) + η`, bounds the mutual correlated agreement error of the univariate
powers generator `z ↦ (1, z, …, z ^ ℓ)` at radius `1 - a` by `min 1 (ℓ E₀ / |F|)`, where
`E₀ = johnsonExceptionCount n D ⌈a n⌉₊ η` is the affine-line count. The evaluation domain is an
arbitrary finite index type, and no characteristic hypothesis is needed. The same bound holds for
every row-wise interleaving of the code.

## Main statements

* `ReedSolomon.UniformExactPowerAgreement.of_equiv`: uniform exact power agreement is invariant
  under reindexing the evaluation points.
* `ReedSolomon.mcaError_univariatePowers_le_of_uniformExactPowerAgreement`: a uniform exact power
  agreement bound with count `e` bounds the powers MCA error by `e / |F|`.
* `ReedSolomon.mcaError_univariatePowers_johnson_le`: the Johnson powers MCA error bound.
* `ReedSolomon.mcaError_univariatePowers_johnson_le_closed`: its closed form
  `ℓ · (8/3) n t³ / (ρ₋ |F|)`.
* `ReedSolomon.mcaError_univariatePowers_johnson_le_comparisonEstimate`: the bound with the
  constant of [BCHKS25] Theorem 4.6, `ℓ · johnsonComparisonEstimate n D η / |F|`.
* `ReedSolomon.mcaError_univariatePowers_interleaved_johnson_le`: the same bound for the
  interleaved code `code domain (D + 1) ^⋈ κ`.
* `ReedSolomon.mcaError_univariatePowers_zero`, `ReedSolomon.mcaError_univariatePowers_code_one_le`:
  the degree-`0` generator has MCA error `0`, and the constant code has powers MCA error at most
  `ℓ n² / |F|`.

## References

* [BCHKS25]
* [DKT26]
* [Jo26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial HiddenDerivative CoreDefinitions LinearCode

/-- `johnsonExceptionCount` is nonnegative. -/
theorem johnsonExceptionCount_nonneg (n D A : ℕ) (eta : ℝ) :
    0 ≤ johnsonExceptionCount n D A eta := by
  unfold johnsonExceptionCount johnsonTheta
  positivity

section Reindex

variable {F : Type*} [Field F] [DecidableEq F] {ι ι' : Type*} [Fintype ι] [Fintype ι'] {ℓ : ℕ}

/-- **Reindexing uniform exact power agreement.** Uniform exact power agreement on the
evaluation points `domain ∘ σ`, for the reindexed words `w t ∘ σ`, gives uniform exact power
agreement on `domain` for `w` with the same degree bound, threshold and count. -/
theorem UniformExactPowerAgreement.of_equiv (σ : ι' ≃ ι) (domain : ι ↪ F)
    (w : Fin (ℓ + 1) → ι → F) {k L e : ℕ}
    (h : UniformExactPowerAgreement (σ.toEmbedding.trans domain) (fun t ↦ w t ∘ σ) k L e) :
    UniformExactPowerAgreement domain w k L e := by
  obtain ⟨bad, hcard, hgood⟩ := h
  have hset (z : F) (Q : F[X]) :
      polynomialAgreementSet (σ.toEmbedding.trans domain) (powerBatchedWord (fun t ↦ w t ∘ σ) z)
        Q = (polynomialAgreementSet domain (powerBatchedWord w z) Q).map σ.symm.toEmbedding := by
    ext i
    rw [Finset.mem_map_equiv, mem_polynomialAgreementSet, mem_polynomialAgreementSet]
    simp [powerBatchedWord]
  refine ⟨bad, hcard, fun z hz Q hQ hL ↦ ?_⟩
  have hL' : L ≤ (polynomialAgreementSet (σ.toEmbedding.trans domain)
      (powerBatchedWord (fun t ↦ w t ∘ σ) z) Q).card := by
    rwa [hset, Finset.card_map]
  obtain ⟨P, hP, hQP, hagree⟩ :=
    (hasExactPowerAgreement_id_iff _ _ _ _ _).mp (hgood z hz Q hQ hL')
  refine (hasExactPowerAgreement_id_iff _ _ _ _ _).mpr ⟨P, hP, hQP, ?_⟩
  ext i
  have hi := congrArg (σ.symm i ∈ ·) hagree
  simp only [eq_iff_iff, mem_polynomialAgreementSet, mem_commonCurveAgreementSet,
    Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Equiv.apply_symm_apply,
    Function.comp_apply] at hi
  rw [mem_polynomialAgreementSet, mem_commonCurveAgreementSet]
  simpa [powerBatchedWord] using hi

/-- Reindexing the evaluation points by `Fintype.equivFin` transports the Johnson power bound to
an arbitrary finite index type. -/
theorem uniformExactPowerAgreement_johnson_of_fintype {D A : ℕ} {eta : ℝ} (domain : ι ↪ F)
    (w : Fin (ℓ + 1) → ι → F)
    (hD : 1 ≤ D) (hDn : D ≤ Fintype.card ι - 2) (heta : 0 < eta) (hℓ : 0 < ℓ)
    (hthreshold : johnsonAgreement (Fintype.card ι) D eta * Fintype.card ι ≤ A)
    (hAn : A ≤ Fintype.card ι) :
    UniformExactPowerAgreement domain w (D + 1) A
      ⌊(ℓ : ℝ) * johnsonExceptionCount (Fintype.card ι) D A eta⌋₊ :=
  UniformExactPowerAgreement.of_equiv (Fintype.equivFin ι).symm domain w
    (uniformExactPowerAgreement_johnson _ _ hD hDn heta hℓ hthreshold hAn)

end Reindex

section Probability

variable {F : Type} [Field F] [Fintype F] [SampleableType F] {ι : Type} [Fintype ι] {ℓ : ℕ}

open Classical in
/-- **Powers MCA error from uniform exact power agreement.** If every tuple of received words has
uniform exact power agreement for degree-`< k` candidates at threshold `A` with at most `e`
exceptional challenges, then the MCA error of the univariate powers generator of degree `ℓ` for
`code domain k` at every radius whose integer threshold `⌈|ι| (1 - δ)⌉₊` is at least `A` is at
most `e / |F|`. -/
theorem mcaError_univariatePowers_le_of_uniformExactPowerAgreement [DecidableEq F]
    (domain : ι ↪ F)
    {k A e : ℕ} (h : ∀ w : Fin (ℓ + 1) → ι → F, UniformExactPowerAgreement domain w k A e)
    (δ : ℝ) (hthreshold : A ≤ ⌈(Fintype.card ι : ℝ) * (1 - δ)⌉₊) :
    mcaError (univariatePowersGenerator F ℓ) (code domain k) δ ≤
      ENNReal.ofReal (e / (Fintype.card F : ℝ)) := by
  refine mcaError_le_ofReal_of_forall_card_le _ _ _ fun U ↦ ?_
  have hpb := Code.encard_setOf_isProjectionBad_le_of_uniformExactAgreement
    ((uniformExactPowerAgreement_iff_uniformExactAgreement domain U).mp (h U))
  have hsub : ((Finset.univ.filter fun z : F ↦
      IsMCA (univariatePowersGenerator F ℓ) (code domain k) z U δ : Finset F) : Set F) ⊆
      {z | Code.IsProjectionBad (univariatePowersGenerator F ℓ) (code domain k) A z U} := by
    intro z hz
    obtain ⟨T, hT, hmem⟩ := (isMCA_iff_isProjectionBad _ _ _ _ _).mp
      (Finset.mem_filter.mp hz).2
    exact ⟨T, hthreshold.trans hT, hmem⟩
  have hcard : ((Finset.univ.filter fun z : F ↦
      IsMCA (univariatePowersGenerator F ℓ) (code domain k) z U δ).card : ℕ∞) ≤ e := by
    rw [← Set.encard_coe_eq_coe_finsetCard]
    exact (Set.encard_le_encard hsub).trans hpb
  exact_mod_cast hcard

/-- **Johnson powers MCA error.** For a Reed–Solomon code of dimension `D + 1` on any `n`
evaluation points over a finite field, `ℓ ≥ 1` and `a = √(D / n) + η ≤ 1`, the MCA error of the
univariate powers generator `z ↦ (1, z, …, z ^ ℓ)` at radius `1 - a` is at most
`min 1 (ℓ · johnsonExceptionCount n D ⌈a n⌉₊ η / |F|)`. -/
theorem mcaError_univariatePowers_johnson_le {D : ℕ} {eta : ℝ} (domain : ι ↪ F)
    (hD : 1 ≤ D) (hDn : D ≤ Fintype.card ι - 2) (heta : 0 < eta) (hℓ : 0 < ℓ)
    (ha : johnsonAgreement (Fintype.card ι) D eta ≤ 1) :
    mcaError (univariatePowersGenerator F ℓ) (code domain (D + 1))
        (1 - johnsonAgreement (Fintype.card ι) D eta) ≤
      min 1 (ENNReal.ofReal (ℓ * johnsonExceptionCount (Fintype.card ι) D
        ⌈johnsonAgreement (Fintype.card ι) D eta * Fintype.card ι⌉₊ eta /
          (Fintype.card F : ℝ))) := by
  classical
  set n := Fintype.card ι
  set A := ⌈johnsonAgreement n D eta * n⌉₊
  have hAn : A ≤ n := Nat.ceil_le.mpr (by nlinarith [Nat.cast_nonneg n (α := ℝ)])
  refine le_min (mcaError_le_one _ _ _) ?_
  refine (mcaError_univariatePowers_le_of_uniformExactPowerAgreement domain
    (fun w ↦ uniformExactPowerAgreement_johnson_of_fintype domain w hD hDn heta hℓ
      (Nat.le_ceil _) hAn) _ ?_).trans ?_
  · rw [show (n : ℝ) * (1 - (1 - johnsonAgreement n D eta)) = johnsonAgreement n D eta * n by
      ring]
  · apply ENNReal.ofReal_le_ofReal
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) (johnsonExceptionCount_nonneg _ _ _ _))

/-- **Johnson powers MCA error, closed form.** Under the hypotheses of
`mcaError_univariatePowers_johnson_le`, the MCA error of the univariate powers generator of degree
`ℓ` at radius `1 - a` is at most `ℓ · (8/3) n t³ / (ρ₋ |F|)`, with `t = johnsonT n D η` and
`ρ₋ = D / n`. -/
theorem mcaError_univariatePowers_johnson_le_closed {D : ℕ} {eta : ℝ} (domain : ι ↪ F)
    (hD : 1 ≤ D) (hDn : D ≤ Fintype.card ι - 2) (heta : 0 < eta) (hℓ : 0 < ℓ)
    (ha : johnsonAgreement (Fintype.card ι) D eta ≤ 1) :
    mcaError (univariatePowersGenerator F ℓ) (code domain (D + 1))
        (1 - johnsonAgreement (Fintype.card ι) D eta) ≤
      ENNReal.ofReal (ℓ * ((8 / 3 : ℝ) * Fintype.card ι * johnsonT (Fintype.card ι) D eta ^ 3 /
        johnsonRhoMinus (Fintype.card ι) D) / (Fintype.card F : ℝ)) := by
  refine (mcaError_univariatePowers_johnson_le domain hD hDn heta hℓ ha).trans
    ((min_le_right _ _).trans (ENNReal.ofReal_le_ofReal ?_))
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_left (johnsonExceptionCount_lt_closed hD hDn heta
    (Nat.le_ceil _)).le (Nat.cast_nonneg _)

/-- **Johnson powers MCA error with the [BCHKS25] constant.** Under the hypotheses of
`mcaError_univariatePowers_johnson_le`, the MCA error of the univariate powers generator of degree
`ℓ` at radius `1 - a` is at most `ℓ` times the Johnson exception estimate
`johnsonComparisonEstimate n D η / |F|`, the constant of [BCHKS25] Theorem 4.6 at curve
degree `ℓ`. -/
theorem mcaError_univariatePowers_johnson_le_comparisonEstimate {D : ℕ} {eta : ℝ}
    (domain : ι ↪ F)
    (hD : 1 ≤ D) (hDn : D ≤ Fintype.card ι - 2) (heta : 0 < eta) (hℓ : 0 < ℓ)
    (ha : johnsonAgreement (Fintype.card ι) D eta ≤ 1) :
    mcaError (univariatePowersGenerator F ℓ) (code domain (D + 1))
        (1 - johnsonAgreement (Fintype.card ι) D eta) ≤
      ENNReal.ofReal (ℓ * johnsonComparisonEstimate (Fintype.card ι) D eta /
        (Fintype.card F : ℝ)) := by
  refine (mcaError_univariatePowers_johnson_le domain hD hDn heta hℓ ha).trans
    ((min_le_right _ _).trans (ENNReal.ofReal_le_ofReal ?_))
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_left (johnsonExceptionCount_le_comparisonEstimate hD hDn heta ha
    (Nat.le_ceil _)) (Nat.cast_nonneg _)

/-- **Johnson powers MCA error for interleaved codes.** The bound of
`mcaError_univariatePowers_johnson_le` holds for the row-wise interleaving
`code domain (D + 1) ^⋈ κ` with any finite row type `κ`: the seed space of the powers generator
is the field, so interleaving does not increase the MCA error. -/
theorem mcaError_univariatePowers_interleaved_johnson_le {κ : Type} [Finite κ] {D : ℕ}
    {eta : ℝ} (domain : ι ↪ F)
    (hD : 1 ≤ D) (hDn : D ≤ Fintype.card ι - 2) (heta : 0 < eta) (hℓ : 0 < ℓ)
    (ha : johnsonAgreement (Fintype.card ι) D eta ≤ 1) :
    mcaError (univariatePowersGenerator F ℓ)
        ((code domain (D + 1) : ModuleCode ι F F)^⋈κ)
        (1 - johnsonAgreement (Fintype.card ι) D eta) ≤
      min 1 (ENNReal.ofReal (ℓ * johnsonExceptionCount (Fintype.card ι) D
        ⌈johnsonAgreement (Fintype.card ι) D eta * Fintype.card ι⌉₊ eta /
          (Fintype.card F : ℝ))) :=
  (mcaError_moduleInterleavedCode_le_of_card_le _ _ _ le_rfl).trans
    (mcaError_univariatePowers_johnson_le domain hD hDn heta hℓ ha)

omit [SampleableType F] in
/-- A family is never MCA-bad for the univariate powers generator of degree `0`: the generated
word is the only word of the family. -/
theorem not_isMCA_univariatePowers_zero {A : Type} [AddCommMonoid A] [Module F A]
    (MC : ModuleCode ι F A) (z : F) (U : Fin 1 → ι → A) (δ : ℝ) :
    ¬ IsMCA (univariatePowersGenerator F 0) MC z U δ := by
  have : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
  rintro ⟨T, -, hmem, j, hj⟩
  apply hj
  have hvec : (fun i ↦ ∑ j', univariatePowersGenerator F 0 z j' • U j' i) = U j := by
    funext i
    rw [Fintype.sum_subsingleton _ j]
    simp [univariatePowersGenerator]
  rwa [hvec] at hmem

/-- The MCA error of the univariate powers generator of degree `0` is `0`. -/
theorem mcaError_univariatePowers_zero {A : Type} [AddCommMonoid A] [Module F A]
    (MC : ModuleCode ι F A) (δ : ℝ) :
    mcaError (univariatePowersGenerator F 0) MC δ = 0 := by
  classical
  refine le_antisymm ((mcaError_le_ofReal_of_forall_card_le _ _ _ (B := 0) fun U ↦ ?_).trans
    (by simp)) bot_le
  rw [Finset.filter_false_of_mem fun z _ ↦ not_isMCA_univariatePowers_zero MC z U δ]
  simp

open Classical in
/-- **Powers MCA error of the constant code.** For the Reed–Solomon code of message length `1`
(the constant words) on `n` evaluation points, the MCA error of the univariate powers generator of
degree `ℓ` is at most `ℓ n² / |F|` at every radius. A bad challenge makes the batched word
constant on a set where some word `U t` takes two values `U t i ≠ U t i'`, so it is a root of the
nonzero polynomial `∑ s, (U s i - U s i') Z ^ s` of degree at most `ℓ`. -/
theorem mcaError_univariatePowers_code_one_le (domain : ι ↪ F) (δ : ℝ) :
    mcaError (univariatePowersGenerator F ℓ) (code domain 1) δ ≤
      ENNReal.ofReal (ℓ * Fintype.card ι ^ 2 / (Fintype.card F : ℝ)) := by
  refine mcaError_le_ofReal_of_forall_card_le _ _ _ fun U ↦ ?_
  let p : ι × ι → F[X] := fun ii ↦ powerBatchedCoordinate fun t ↦ U t ii.1 - U t ii.2
  let bad : Finset F := Finset.univ.biUnion fun ii ↦ (p ii).roots.toFinset
  have hbad : (bad.card : ℝ) ≤ ℓ * Fintype.card ι ^ 2 := by
    have hcard : bad.card ≤ ∑ ii : ι × ι, ℓ :=
      Finset.card_biUnion_le.trans (Finset.sum_le_sum fun ii _ ↦
        (Multiset.toFinset_card_le _).trans ((card_roots' _).trans
          (powerBatchedCoordinate_natDegree_le _)))
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, smul_eq_mul] at hcard
    have : (bad.card : ℝ) ≤ ((Fintype.card ι * Fintype.card ι * ℓ : ℕ) : ℝ) := by
      exact_mod_cast hcard
    push_cast at this
    nlinarith
  refine le_trans (Nat.cast_le.mpr (Finset.card_le_card fun z hz ↦ ?_)) hbad
  obtain ⟨T, -, hmem, j, hj⟩ := (Finset.mem_filter.mp hz).2
  obtain ⟨c, hc, hcT⟩ := (mem_projectedCodeSubmod_iff _ T _).mp hmem
  obtain ⟨P, hP, hPc⟩ := mem_code_iff_eval.mp hc
  have hP0 : P.degree ≤ 0 := Nat.WithBot.lt_one_iff_le_zero.mp (by exact_mod_cast hP)
  have hconst : ∀ i, c i = P.coeff 0 := by
    intro i
    rw [← hPc i, eq_C_of_degree_le_zero hP0, eval_C, coeff_C_zero]
  have hv : ∀ i ∈ T, ∑ t : Fin (ℓ + 1), z ^ (t : ℕ) * U t i = P.coeff 0 := by
    intro i hi
    have := congrFun hcT ⟨i, hi⟩
    simp only [projectedWord, Set.domRestrict, univariatePowersGenerator, smul_eq_mul] at this
    rw [this, hconst]
  obtain ⟨i, hi, i', hi', hne⟩ : ∃ i ∈ T, ∃ i' ∈ T, U j i ≠ U j i' := by
    by_contra hall
    push Not at hall
    apply hj
    rw [mem_projectedCodeSubmod_iff]
    by_cases hT : T.Nonempty
    · obtain ⟨i₀, hi₀⟩ := hT
      refine ⟨fun _ ↦ U j i₀, mem_code_iff_eval.mpr ⟨C (U j i₀), ?_, fun _ ↦ eval_C⟩, ?_⟩
      · exact (degree_C_le).trans_lt (by norm_num)
      · funext ⟨i, hi⟩
        exact hall i hi i₀ hi₀
    · refine ⟨0, Submodule.zero_mem _, funext fun ⟨i, hi⟩ ↦ absurd ⟨i, hi⟩ hT⟩
  have hp : p (i, i') ≠ 0 := by
    intro h0
    apply hne
    have := congrArg (fun q ↦ q.coeff j) h0
    simp only [p, powerBatchedCoordinate_coeff, coeff_zero] at this
    exact sub_eq_zero.mp this
  refine Finset.mem_biUnion.mpr ⟨(i, i'), Finset.mem_univ _, ?_⟩
  rw [Multiset.mem_toFinset, mem_roots hp, IsRoot.def, powerBatchedCoordinate_eval]
  simp only [mul_sub, Finset.sum_sub_distrib, hv i hi, hv i' hi', sub_self]

end Probability

end ReedSolomon
