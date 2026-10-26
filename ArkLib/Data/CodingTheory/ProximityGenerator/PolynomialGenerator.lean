/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon
public import ArkLib.Data.CodingTheory.ProximityGenerator.MDSGenerator
public import ArkLib.Data.CodingTheory.ProximityGenerator.TensorGenerator
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.CurveProbability
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.FullCode

/-!
# Mutual correlated agreement for polynomial generators

A polynomial generator sends a seed `(x₁, …, xₛ)`, drawn from a product of subsets of a field,
to the evaluations of a fixed linearly independent family of multivariate polynomials at that
seed. This file proves that polynomial generators have mutual correlated agreement (MCA), by
factoring each one through an iterated tensor product of univariate powers generators followed
by right multiplication with a coefficient matrix that has a left inverse.

## Main results

- `PolynomialGenIsMCA.powersMCAError`: the MCA error function of a univariate powers generator.
- `PolynomialGenIsMCA.isMCAGenerator_tensorGeneratorPi` and
  `PolynomialGenIsMCA.isMCAGenerator_tensorGeneratorPi_tight`: iterated tensor products of MCA
  generators have MCA with the factors' errors adding; the `tight` variant is proved, from a
  factor hypothesis quantified over a class of module codes closed under interleaving.
- `PolynomialGenIsMCA.isMCAGenerator_of_isPolynomialGeneratorOf`: a polynomial generator over
  restricted seed sets has MCA for every linear code. Its only unproved input is
  `isMCAGenerator_of_isMDSGenerator`.
- `RSCode.reedSolomonMCAError`: the MCA error function for Reed-Solomon codes.
- `RSCode.isMCAGenerator_univariatePowersGenerator`: the univariate powers generator has MCA for
  Reed-Solomon codes up to the Johnson bound, from the Johnson power-curve bound
  `ReedSolomon.mcaError_univariatePowers_le_of_uniformExactPowerAgreement` of [DKT26].
- `RSCode.isMCAGenerator_of_isPolynomialGeneratorOfFull`: a full-field polynomial generator has
  MCA for Reed-Solomon codes up to the Johnson bound.

These results formalize §8 and §9 of [BCGM25] (Definitions 8.1 and 9.1, Theorem 8.2, Lemma 9.3,
Theorem 9.2); the per-declaration correspondence is catalogued in
`docs/kb/audits/bcgm25-mca-generators.md`.

## References

* [Bordage, S., Chiesa, A., Guan, Z., Manzur, I., *All Polynomial Generators Preserve Distance
  with Mutual Correlated Agreement*][BCGM25]. https://eprint.iacr.org/2025/2051
* [DKT26]
-/

@[expose] public section

namespace PolynomialGenIsMCA

open unitInterval NNReal Probability CoreDefinitions LinearTransformations

variable {F : Type} [Field F]
         {ι : Type} [Fintype ι] [Nonempty ι]

/-- A function assigning the maximum degree in the `i`-th variable of the collection of
polynomials `P`. -/
noncomputable def maxDegreeOf {s : ℕ} {ℓ : Type} [Fintype ℓ] (P : ℓ → MvPolynomial (Fin s) F) :
    Fin s → ℕ := fun i => Finset.sup Finset.univ (fun j => (P j).degreeOf i)

/-- The MCA error function of the univariate powers generator of degree `d` with `m` seeds,
for a linear code `LC`, at slack parameter `η`. As a function of the proximity parameter `γ` it
is a step function with three regimes: a unique-decoding bound `(⌊n·γ⌋ + 1)·d / m` below
`δ_C / (d + 2)`, a list-decoding bound up to `1 - (ρ_C + η) ^ (1 / (d + 2))`, and the trivial
bound `1` beyond. The unique-decoding regime is `mdsMCAError`'s, which corrects the paper's
`max{n·γ, 1}` to `⌊n·γ⌋ + 1`; see `ArkLib.Data.CodingTheory.ProximityGenerator.MDSGenerator`.

The slack hypothesis `0 < η < 1` is not needed to define the function, so it is omitted here
and required only by the statements that consume it. Valued in `ℝ≥0` to match `IsMCAGenerator`,
clamping the underlying real expression at `0` via `Real.toNNReal`; the clamp is not lossy in
the intended parameter range. -/
noncomputable def powersMCAError [DecidableEq F] (LC : LinearCode ι F) (d m : ℕ) (η : ℝ) :
  I → ℝ≥0 :=
  letI n : ℝ := Fintype.card ι
  letI δ_C : ℝ := (Code.minRelHammingDistCode (LC.carrier) : ℝ)
  letI ρ_C : ℝ := 1 - δ_C
  letI γ_d : ℝ := 1 - (ρ_C + η) ^ (1 / (d + 1) : ℝ)
  fun γ =>
    Real.toNNReal <|
      if γ < (δ_C / (d + 2) : ℝ) then
        letI m' : ℝ := ⌊n * γ⌋₊ + 1
        m' * (d / m : ℝ)
      else
        if γ ≤ 1 - (ρ_C + η) ^ (1 / (d + 2) : ℝ) then
            (n * γ_d / η) * (d / m) +
            max (2 * d /
                  (η * ((ρ_C + η) ^ (1 / (d + 2) : ℝ) - (ρ_C + η) ^ (1 / (d + 1) : ℝ)) * m))
                ((d + 1) * (d + 2) / (η * m) : ℝ)
        else
        1

/-- The MDS error bound `mdsMCAError` for output size `d + 1` (the univariate powers generator of
degree `d`, whose code has dimension `d + 1`) coincides with the univariate-powers error
`powersMCAError` of degree `d`. -/
lemma mdsMCAError_eq_powersMCAError [DecidableEq F] (LC : LinearCode ι F) (d m : ℕ) (η : ℝ) :
    mdsMCAError LC (d + 1) m η = powersMCAError LC d m η := by
  funext γ
  simp only [mdsMCAError, powersMCAError, Nat.cast_add, Nat.cast_one]
  rw [show (↑d + 1 + 1 : ℝ) = ↑d + 2 from by ring,
    show (↑d + 1 - 1 : ℝ) = ↑d from by ring]

/-- The iterated tensor product of a finite family of generators `Gᵢ : αᵢ → 𝔽^{ℓᵢ}`, over the
product seed space `∏ᵢ αᵢ`: `(x₁, ..., xₛ) ↦ ⊗ᵢ Gᵢ(xᵢ)`.  Both the full-field tensor
`RSCode.tensorGeneratorPiUnivariate` and the subset tensor `tensorGeneratorPiUnivariateOn` are
instances of this construction. -/
def tensorGeneratorPi {s : ℕ} {α : Fin s → Type} {ℓ : Fin s → Type}
    (G : ∀ i, Generator (α i) (ℓ i) F) : Generator (∀ i, α i) (∀ i, ℓ i) F :=
  fun x j => ∏ i, G i (x i) (j i)

omit [Nonempty ι] in
/-- The iterated tensor product of a family of MCA generators has MCA for any module code `MC`,
with error the sum `∑ᵢ εᵢ` of the factors' errors. The inductive step is the open
`isMCAGenerator_tensorGenerator_tight`, which this lemma therefore inherits; see
`isMCAGenerator_tensorGeneratorPi_tight` for the proved variant with a stronger factor
hypothesis.

The seeds and generator entries stay over `F` — it is only the code alphabet that is a general
`F`-module, which is all the induction needs: both `isMCAGenerator_tensorGenerator_tight` and
`isMCAGenerator_reindex` are already stated at that generality. At `A := F` this is the
linear-code statement, since `LinearCode ι F` and `ModuleCode ι F F` are the same type. -/
lemma isMCAGenerator_tensorGeneratorPi {A : Type} [AddCommMonoid A] [Module F A]
    (MC : ModuleCode ι F A) :
    ∀ {s : ℕ} {α : Fin s → Type} {ℓ : Fin s → Type}
      [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)] [∀ i, SampleableType (α i)]
      [SampleableType (∀ i, α i)]
      [∀ i, Fintype (ℓ i)]
      (G : ∀ i, Generator (α i) (ℓ i) F) (ε : Fin s → I → ℝ≥0),
      (∀ i, IsMCAGenerator (G i) (ε i) MC) →
      IsMCAGenerator (tensorGeneratorPi G) (fun γ => ∑ i, ε i γ) MC := by
  intro s
  induction s with
  | zero =>
    intro α ℓ _ _ _ _ _ G ε _ γ
    classical
    refine iSup_le fun U => ?_
    have hfalse : ∀ x : (∀ i : Fin 0, α i), ¬ IsMCA (tensorGeneratorPi G) MC x U (γ : ℝ) := by
      rintro x ⟨T, hT, hmem, j, hj⟩
      apply hj
      have hvec : (fun k => ∑ j', tensorGeneratorPi G x j' • U j' k) = U j := by
        funext w
        rw [Fintype.sum_subsingleton _ j]
        simp [tensorGeneratorPi]
      rwa [hvec] at hmem
    simpa using le_of_eq (prEvent_eq_zero_of_forall_not ($ᵗ _) _ hfalse)
  | succ s ih =>
    intro α ℓ _ _ hα _ _ G ε hmca
    let : ∀ i : Fin s, Fintype (Fin.tail α i) := fun i => inferInstanceAs (Fintype (α i.succ))
    let : ∀ i : Fin s, SampleableType (Fin.tail α i) := fun i => hα i.succ
    let : SampleableType (∀ i : Fin s, Fin.tail α i) := SampleableType.piOfFintype _
    let : ∀ i : Fin s, Fintype (Fin.tail ℓ i) := fun i => inferInstanceAs (Fintype (ℓ i.succ))
    set eS : (∀ i : Fin (s + 1), α i) ≃ (α 0 × (∀ i : Fin s, Fin.tail α i)) :=
      (Fin.consEquiv α).symm with heS
    set eL : (ℓ 0 × (∀ i : Fin s, Fin.tail ℓ i)) ≃ (∀ i : Fin (s + 1), ℓ i) :=
      Fin.consEquiv ℓ with heL
    have hBin := isMCAGenerator_tensorGenerator_tight MC
      (G 0) (ε 0) (hmca 0)
      (tensorGeneratorPi (α := Fin.tail α) (ℓ := Fin.tail ℓ) (Fin.tail G))
      (fun γ => ∑ i, Fin.tail ε i γ)
      (ih (α := Fin.tail α) (ℓ := Fin.tail ℓ) (Fin.tail G) (Fin.tail ε)
        (fun i => hmca (Fin.succ i)))
    have hR := isMCAGenerator_reindex MC
      (TensorGenerator_Explicit (G 0)
        (tensorGeneratorPi (α := Fin.tail α) (ℓ := Fin.tail ℓ) (Fin.tail G)))
      _ hBin eS eL
    have hgen : (fun (x' : ∀ i : Fin (s + 1), α i) (j' : ∀ i : Fin (s + 1), ℓ i) =>
        TensorGenerator_Explicit (G 0)
          (tensorGeneratorPi (α := Fin.tail α) (ℓ := Fin.tail ℓ) (Fin.tail G)) (eS x') (eL.symm j'))
        = tensorGeneratorPi G := by
      funext x' j'
      rw [heS, heL]
      simp only [TensorGenerator_Explicit, tensorGeneratorPi, Fin.tail, Fin.prod_univ_succ]
      simp_all only [eS, eL]
      rfl
    have herr : ((ε 0) + fun γ => ∑ i, Fin.tail ε i γ) = (fun γ => ∑ i, ε i γ) := by
      funext γ
      simp only [Pi.add_apply, Fin.sum_univ_succ]
      rfl
    rw [hgen, herr] at hR
    exact hR

omit [Nonempty ι] in
/-- Proved variant of `isMCAGenerator_tensorGeneratorPi`, with the factor hypothesis anchored on
a class `Good` of module codes over `ι` that is closed under row-wise interleaving by nonempty
finite row types: each factor must have MCA, with its fixed error `ε i`, for *every* code in the
class, over every alphabet.

Closure under interleaving makes the hypothesis available at the interleavings the induction
steps through, so the inductive step can use the proved
`TensorMCA.isMCAGenerator_tensorGenerator_of_moduleInterleavedCode` instead of the open
`isMCAGenerator_tensorGenerator_tight`. Two classes supply it: the codes of a fixed relative
distance (`Code.minRelHammingDistCode_moduleInterleavedCode`), for generators whose MCA error
reads the code only through its block length and relative distance, such as
`isMCAGenerator_of_isMDSGenerator`; and the codes whose MCA error is at most that of a fixed code
(`mcaError_moduleInterleavedCode_le_of_card_le`), for generators with at most `|F|` seeds. -/
lemma isMCAGenerator_tensorGeneratorPi_tight
    (Good : ∀ (A : Type) [AddCommMonoid A] [Module F A] [DecidableEq A], ModuleCode ι F A → Prop)
    (hGood : ∀ (A : Type) [AddCommMonoid A] [Module F A] [DecidableEq A] (κ : Type) [Fintype κ]
      [Nonempty κ] (MC : ModuleCode ι F A),
      Good A MC → Good _ (Code.ModuleCode.moduleInterleavedCode F A κ ι MC)) :
    ∀ {s : ℕ} {α : Fin s → Type} {ℓ : Fin s → Type}
      [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)] [∀ i, SampleableType (α i)]
      [SampleableType (∀ i, α i)]
      [∀ i, Fintype (ℓ i)] [∀ i, Nonempty (ℓ i)]
      (G : ∀ i, Generator (α i) (ℓ i) F) (ε : Fin s → I → ℝ≥0),
      (∀ i, ∀ {A : Type} [AddCommMonoid A] [Module F A] [DecidableEq A]
        (MC : ModuleCode ι F A), Good A MC → IsMCAGenerator (G i) (ε i) MC) →
      ∀ {A : Type} [AddCommMonoid A] [Module F A] [DecidableEq A]
        (MC : ModuleCode ι F A), Good A MC →
        IsMCAGenerator (tensorGeneratorPi G) (fun γ => ∑ i, ε i γ) MC := by
  intro s
  induction s with
  | zero =>
    intro α ℓ _ _ _ _ _ _ G ε _ A _ _ _ MC _ γ
    classical
    refine iSup_le fun U => ?_
    have hfalse : ∀ x : (∀ i : Fin 0, α i), ¬ IsMCA (tensorGeneratorPi G) MC x U (γ : ℝ) := by
      rintro x ⟨T, hT, hmem, j, hj⟩
      apply hj
      have hvec : (fun k => ∑ j', tensorGeneratorPi G x j' • U j' k) = U j := by
        funext w
        rw [Fintype.sum_subsingleton _ j]
        simp [tensorGeneratorPi]
      rwa [hvec] at hmem
    simpa using le_of_eq (prEvent_eq_zero_of_forall_not ($ᵗ _) _ hfalse)
  | succ s ih =>
    intro α ℓ _ _ hα _ _ _ G ε hmca A _ _ _ MC hδ
    let : ∀ i : Fin s, Fintype (Fin.tail α i) := fun i => inferInstanceAs (Fintype (α i.succ))
    let : ∀ i : Fin s, SampleableType (Fin.tail α i) := fun i => hα i.succ
    let : SampleableType (∀ i : Fin s, Fin.tail α i) := SampleableType.piOfFintype _
    let : ∀ i : Fin s, Fintype (Fin.tail ℓ i) := fun i => inferInstanceAs (Fintype (ℓ i.succ))
    let : ∀ i : Fin s, Nonempty (Fin.tail ℓ i) := fun i => inferInstanceAs (Nonempty (ℓ i.succ))
    set eS : (∀ i : Fin (s + 1), α i) ≃ (α 0 × (∀ i : Fin s, Fin.tail α i)) :=
      (Fin.consEquiv α).symm with heS
    set eL : (ℓ 0 × (∀ i : Fin s, Fin.tail ℓ i)) ≃ (∀ i : Fin (s + 1), ℓ i) :=
      Fin.consEquiv ℓ with heL
    -- the (ℓ 0)-fold interleaving stays in the class, so the anchored hypotheses apply there
    have hδI := hGood A (ℓ 0) MC hδ
    have hTail := ih (α := Fin.tail α) (ℓ := Fin.tail ℓ) (Fin.tail G) (Fin.tail ε)
      (fun i {A'} _ _ _ MC' hMC' => hmca i.succ MC' hMC')
      (Code.ModuleCode.moduleInterleavedCode F A (ℓ 0) ι MC) hδI
    have hBin := TensorMCA.isMCAGenerator_tensorGenerator_of_moduleInterleavedCode
      (G 0) (tensorGeneratorPi (α := Fin.tail α) (ℓ := Fin.tail ℓ) (Fin.tail G))
      (ε 0) (fun γ => ∑ i, Fin.tail ε i γ) MC
      (hmca 0 MC hδ) hTail
    have hR := isMCAGenerator_reindex MC
      (TensorGenerator_Explicit (G 0)
        (tensorGeneratorPi (α := Fin.tail α) (ℓ := Fin.tail ℓ) (Fin.tail G)))
      _ hBin eS eL
    have hgen : (fun (x' : ∀ i : Fin (s + 1), α i) (j' : ∀ i : Fin (s + 1), ℓ i) =>
        TensorGenerator_Explicit (G 0)
          (tensorGeneratorPi (α := Fin.tail α) (ℓ := Fin.tail ℓ) (Fin.tail G)) (eS x') (eL.symm j'))
        = tensorGeneratorPi G := by
      funext x' j'
      rw [heS, heL]
      simp only [TensorGenerator_Explicit, tensorGeneratorPi, Fin.tail, Fin.prod_univ_succ]
      simp_all only [eS, eL]
      rfl
    have herr : ((ε 0) + fun γ => ∑ i, Fin.tail ε i γ) = (fun γ => ∑ i, ε i γ) := by
      funext γ
      simp only [Pi.add_apply, Fin.sum_univ_succ]
      rfl
    rw [hgen, herr] at hR
    exact hR

end PolynomialGenIsMCA

namespace RSCode

open unitInterval NNReal CoreDefinitions PolynomialGenIsMCA LinearTransformations MvPolynomial
  Matrix

variable {F : Type} [Field F]
         {ι : Type} [Fintype ι]
         (k : ℕ) -- degree of the polynomials
         (D : ι ↪ F) -- the domain of evaluation


/-- The MCA error function for the Reed-Solomon code of degree `k` over the domain `D`, for the
univariate powers generator of degree `d`, at sharpness parameter `m`: up to the Johnson-type
radius `1 - (1 + 1/(2m))√ρ` the error is `(d n²/|F|) · (m + 1/2)⁷ / (3 ρ^{3/2})`, and beyond it
the trivial bound `1`. Valued in `ℝ≥0`, clamping the underlying real expression at `0` via
`Real.toNNReal`. -/
noncomputable def reedSolomonMCAError [Fintype F] [NeZero k] (d m : ℕ) : I → ℝ≥0 :=
  letI n : ℝ := Fintype.card ι
  let ρ_sqrt := ReedSolomon.sqrtRate k D
  fun γ =>
    Real.toNNReal <|
      if γ ≤ 1 - (1 + (1 / (2 * m : ℝ))) * ρ_sqrt then
        (Fintype.card F : ℝ)⁻¹  *  (m + 1 / 2) ^ 7  * (3 * (ρ_sqrt) ^ 3)⁻¹.toReal * d * n ^ 2
      else
        1

/-- The Johnson multiplicity at slack `η = √ρ / (2m)` is at most `m` when `√ρ₋ ≤ √ρ` and
`m ≥ 3`. -/
private lemma johnsonM_le_of_slack {n deg m : ℕ} {s : ℝ} (hs : 0 < s)
    (hsqrt : √(ReedSolomon.HiddenDerivative.johnsonRhoMinus n deg) ≤ s) (hm : 3 ≤ m) :
    ReedSolomon.HiddenDerivative.johnsonM n deg (s / (2 * (m : ℝ))) ≤ m := by
  unfold ReedSolomon.HiddenDerivative.johnsonM
  refine max_le (Nat.ceil_le.mpr ?_) hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  rw [div_le_iff₀ (by positivity)]
  calc √(ReedSolomon.HiddenDerivative.johnsonRhoMinus n deg) ≤ s := hsqrt
    _ = (m : ℝ) * (2 * (s / (2 * (m : ℝ)))) := by field_simp

/-- The closed Johnson count `(8/3) n t³ / ρ₋`, with `t ≤ m + 1/2`, is at most the
[BCIKS20]-shape coefficient `(m + 1/2)⁷ n² / (3 ρ^{3/2})` of `reedSolomonMCAError`, where
`ρ₋ = deg / n` and `ρ = (deg + 1) / n = s²`. -/
private lemma johnsonClosed_le_reedSolomonCoefficient {n deg m : ℕ} {s t : ℝ}
    (hdeg : 1 ≤ deg) (hs0 : 0 < s) (hs2 : s ^ 2 = ((deg + 1 : ℕ) : ℝ) / n) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (htT : t ≤ m + 1 / 2) (hm : 3 ≤ m) (hn : 0 < n) :
    (8 / 3 : ℝ) * n * t ^ 3 / ((deg : ℝ) / n) ≤ ((m : ℝ) + 1 / 2) ^ 7 * (3 * s ^ 3)⁻¹ * n ^ 2 := by
  set T : ℝ := (m : ℝ) + 1 / 2
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdegR : (1 : ℝ) ≤ deg := by exact_mod_cast hdeg
  have hT : (7 / 2 : ℝ) ≤ T := by
    have : (3 : ℝ) ≤ m := by exact_mod_cast hm
    simp only [T]; linarith
  have hT0 : 0 < T := by linarith
  have hs3 : s ^ 3 ≤ ((deg + 1 : ℕ) : ℝ) / n := by
    rw [← hs2, pow_succ]
    exact mul_le_of_le_one_right (by positivity) hs1
  have hinv : (n : ℝ) / (3 * ((deg + 1 : ℕ) : ℝ)) ≤ (3 * s ^ 3)⁻¹ := by
    have h3 : 3 * s ^ 3 ≤ 3 * (((deg + 1 : ℕ) : ℝ) / n) := by linarith
    calc (n : ℝ) / (3 * ((deg + 1 : ℕ) : ℝ)) = (3 * (((deg + 1 : ℕ) : ℝ) / n))⁻¹ := by
          field_simp
      _ ≤ (3 * s ^ 3)⁻¹ := inv_anti₀ (by positivity) h3
  have ht3 : t ^ 3 ≤ T ^ 3 := pow_le_pow_left₀ ht0 htT 3
  have hT4 : (16 : ℝ) ≤ T ^ 4 := by nlinarith [pow_le_pow_left₀ (by norm_num) hT 4]
  have hnum : 8 * (((deg + 1 : ℕ) : ℝ)) ≤ T ^ 4 * n * deg := by
    push_cast
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [mul_le_mul hT4 hn1 (by norm_num) (by positivity)]
  calc (8 / 3 : ℝ) * n * t ^ 3 / ((deg : ℝ) / n) ≤ (8 / 3 : ℝ) * n * T ^ 3 / ((deg : ℝ) / n) := by
        gcongr
    _ = T ^ 3 * n ^ 2 * (8 / (3 * deg)) := by field_simp
    _ ≤ T ^ 3 * n ^ 2 * (T ^ 4 * n / (3 * ((deg + 1 : ℕ) : ℝ))) := by
        have hfrac : 8 / (3 * (deg : ℝ)) ≤ T ^ 4 * n / (3 * ((deg + 1 : ℕ) : ℝ)) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        exact mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ = T ^ 7 * ((n : ℝ) / (3 * ((deg + 1 : ℕ) : ℝ))) * n ^ 2 := by ring
    _ ≤ T ^ 7 * (3 * s ^ 3)⁻¹ * n ^ 2 := by gcongr

/-- The univariate powers generator of degree `d` has MCA for the Reed-Solomon code of degree
`k` over the domain `D`, with error `reedSolomonMCAError k D d m`, for every `m ≥ 3`, over every
finite field and every evaluation domain.

The main case `2 ≤ k < |ι|`, `d ≥ 1` is the Johnson power-curve bound
`ReedSolomon.mcaError_univariatePowers_le_of_uniformExactPowerAgreement` at slack
`η = √ρ / (2m)`, whose count `d · johnsonExceptionCount` is below `d · (8/3) n t³ / ρ₋` with
`t ≤ m + 1/2`, which is at most the [BCIKS20]-shape error. The remaining cases are the full code
(`k ≥ |ι|`, error `0`), degree `d = 0` (error `0`) and the constant code `k = 1` (error at most
`d n² / |F|`). -/
lemma isMCAGenerator_univariatePowersGenerator [Fintype F] [SampleableType F] [NeZero k]
    (d m : ℕ) (hm : 3 ≤ m) :
    IsMCAGenerator (univariatePowersGenerator F d) (reedSolomonMCAError k D d m)
      (ReedSolomon.code D k) := by
  classical
  intro γ
  have hγ0 : (0 : ℝ) ≤ γ := γ.2.1
  have hγ1 : (γ : ℝ) ≤ 1 := γ.2.2
  have hk0 : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  simp only [reedSolomonMCAError]
  split_ifs with hthr
  swap
  · simpa using mcaError_le_one (univariatePowersGenerator F d) (ReedSolomon.code D k) γ
  change _ ≤ ENNReal.ofReal _
  set n := Fintype.card ι with hn_def
  rcases le_or_gt n k with hkn | hkn
  · rw [ReedSolomon.mcaError_eq_zero_of_card_le _ D hkn]
    exact bot_le
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [ReedSolomon.mcaError_univariatePowers_zero]
    exact bot_le
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  set s : ℝ := (ReedSolomon.sqrtRate k D : ℝ) with hs_def
  have hs2 : s ^ 2 = (k : ℝ) / n := by
    rw [hs_def, ReedSolomon.sqrtRate_sq, ← hn_def,
      min_eq_left (by exact_mod_cast hkn.le : (k : ℝ) ≤ n)]
  have hs0 : 0 < s := by
    have : 0 < s ^ 2 := by rw [hs2]; positivity
    rcases (ReedSolomon.sqrtRate_nonneg k D).lt_or_eq with h | h
    · exact h
    · rw [hs_def, ← h] at this; simp at this
  have hs1 : s ≤ 1 := by
    have : s ^ 2 ≤ 1 := by
      rw [hs2, div_le_one hnR]; exact_mod_cast hkn.le
    nlinarith
  have hcoe : (((3 * ReedSolomon.sqrtRate k D ^ 3)⁻¹ : ℝ≥0) : ℝ) = (3 * s ^ 3)⁻¹ := by
    simp only [NNReal.coe_inv, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_ofNat]
    rfl
  rw [hcoe]
  have hTpos : (0 : ℝ) < (m : ℝ) + 1 / 2 := by positivity
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  · -- the constant code
    have hk : k = 1 := by omega
    subst hk
    refine (ReedSolomon.mcaError_univariatePowers_code_one_le D γ).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have hs3 : s ^ 3 ≤ 1 := pow_le_one₀ hs0.le hs1
    have hK : 1 ≤ ((m : ℝ) + 1 / 2) ^ 7 * (3 * s ^ 3)⁻¹ := by
      have hT : (7 / 2 : ℝ) ≤ (m : ℝ) + 1 / 2 := by
        have : (3 : ℝ) ≤ m := by exact_mod_cast hm
        linarith
      have h7 : (3 : ℝ) ≤ ((m : ℝ) + 1 / 2) ^ 7 := by
        nlinarith [pow_le_pow_left₀ (by norm_num) hT 7]
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      nlinarith
    calc (d : ℝ) * n ^ 2 / (Fintype.card F : ℝ) =
          (Fintype.card F : ℝ)⁻¹ * 1 * (d * n ^ 2) := by ring
      _ ≤ (Fintype.card F : ℝ)⁻¹ * (((m : ℝ) + 1 / 2) ^ 7 * (3 * s ^ 3)⁻¹) * (d * n ^ 2) := by
          gcongr
      _ = _ := by ring
  -- the main case `2 ≤ k < n`
  obtain ⟨deg, rfl⟩ : ∃ deg, k = deg + 1 := ⟨k - 1, by omega⟩
  have hdeg : 1 ≤ deg := by omega
  have hDn : deg ≤ n - 2 := by omega
  set eta : ℝ := s / (2 * (m : ℝ)) with heta_def
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have heta : 0 < eta := by positivity
  have hsqrt : √(ReedSolomon.HiddenDerivative.johnsonRhoMinus n deg) ≤ s := by
    have hs' : s = √((((deg + 1 : ℕ) : ℝ)) / n) := by
      rw [← hs2, Real.sqrt_sq hs0.le]
    rw [hs']
    apply Real.sqrt_le_sqrt
    unfold ReedSolomon.HiddenDerivative.johnsonRhoMinus
    gcongr
    linarith
  set A := ⌈(n : ℝ) * (1 - γ)⌉₊ with hA_def
  have hthreshold : ReedSolomon.HiddenDerivative.johnsonAgreement n deg eta * n ≤ A := by
    refine le_trans ?_ (Nat.le_ceil _)
    unfold ReedSolomon.HiddenDerivative.johnsonAgreement
    have hle : √(ReedSolomon.HiddenDerivative.johnsonRhoMinus n deg) + eta ≤ 1 - γ := by
      have : eta = 1 / (2 * m) * s := by rw [heta_def]; ring
      rw [this]
      linarith
    nlinarith
  have hAn : A ≤ n := Nat.ceil_le.mpr (by nlinarith)
  refine (ReedSolomon.mcaError_univariatePowers_le_of_uniformExactPowerAgreement D
    (fun w ↦ ReedSolomon.uniformExactPowerAgreement_johnson_of_fintype D w hdeg hDn heta hd
      hthreshold hAn) γ le_rfl).trans (ENNReal.ofReal_le_ofReal ?_)
  have hE := ReedSolomon.HiddenDerivative.johnsonExceptionCount_lt_closed hdeg hDn heta hthreshold
  have hM : ReedSolomon.HiddenDerivative.johnsonM n deg eta ≤ m :=
    johnsonM_le_of_slack hs0 hsqrt hm
  have htT : ReedSolomon.HiddenDerivative.johnsonT n deg eta ≤ m + 1 / 2 := by
    unfold ReedSolomon.HiddenDerivative.johnsonT
    have : (ReedSolomon.HiddenDerivative.johnsonM n deg eta : ℝ) ≤ m := by exact_mod_cast hM
    linarith
  have hkey := johnsonClosed_le_reedSolomonCoefficient hdeg hs0 hs2 hs1
    (by unfold ReedSolomon.HiddenDerivative.johnsonT; positivity) htT hm hn
  have hfloor : (⌊(d : ℝ) * ReedSolomon.HiddenDerivative.johnsonExceptionCount n deg A eta⌋₊ : ℝ)
      ≤ d * (((m : ℝ) + 1 / 2) ^ 7 * (3 * s ^ 3)⁻¹ * n ^ 2) := by
    refine (Nat.floor_le (mul_nonneg (Nat.cast_nonneg _)
      (ReedSolomon.johnsonExceptionCount_nonneg _ _ _ _))).trans ?_
    gcongr
    exact hE.le.trans hkey
  rw [div_le_iff₀ hq]
  calc _ ≤ _ := hfloor
    _ = _ := by field_simp

/-- The multi-index (as a finitely supported function) associated to a bounded exponent vector. -/
noncomputable def exponentFinsupp {s : ℕ} {d : Fin s → ℕ} (e : (i : Fin s) → Fin (d i + 1)) :
    Fin s →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => (e i : ℕ))

/-- Distinct bounded exponent vectors give distinct monomials.  This lets a sum over the monomials
in the box `d` be rewritten as a sum over the finite index type `(i : Fin s) → Fin (d i + 1)`,
via `Finset.sum_image`. -/
lemma exponentFinsupp_injective {s : ℕ} {d : Fin s → ℕ} :
    Function.Injective (exponentFinsupp (d := d)) := by
  intro e₁ e₂ h
  funext i
  have := congrArg (fun f => (f i : ℕ)) h
  simpa using Fin.val_injective (by simpa [exponentFinsupp] using this)

/-- Conversely, every monomial lying inside the box `d` is `exponentFinsupp` of some bounded
exponent vector. Together with `exponentFinsupp_injective` this identifies the box index type with
the set of monomials of individual degree at most `d`. -/
lemma exists_exponentFinsupp_eq {s : ℕ} {d : Fin s → ℕ} {mo : Fin s →₀ ℕ} (h : ∀ i, mo i ≤ d i) :
    ∃ e, exponentFinsupp (d := d) e = mo :=
  ⟨fun i => ⟨mo i, Nat.lt_succ_of_le (h i)⟩, by ext i; simp [exponentFinsupp]⟩

/-- The `s`-fold tensor product of univariate powers generators, over the seed space `Fˢ`:
`(x₁, …, xₛ) ↦ ⊗ᵢ (1, xᵢ, …, xᵢ^{dᵢ})`. -/
def tensorGeneratorPiUnivariate {s : ℕ} (d : Fin s → ℕ) :
    Generator (Fin s → F) ((i : Fin s) → Fin (d i + 1)) F :=
  fun x j => ∏ i, x i ^ (j i : ℕ)

/-- The `s`-fold tensor product of univariate powers generators has MCA for any module code
`MC`, with error the sum `∑ i, ε (d i)` of the factors' errors, provided each univariate powers
generator has MCA for `MC` with error `ε e`. Proved through
`isMCAGenerator_tensorGeneratorPi_tight` with the class of module codes whose powers MCA errors
are at most those of `MC`: the seed space of a univariate powers generator is `F`, so
interleaving does not increase its MCA error (`mcaError_moduleInterleavedCode_le_of_card_le`).

Only the code alphabet is generalised: the generator `x ↦ (1, x, …, x^e)` is still over `F`.
At `A := F` this is the linear-code statement. -/
lemma isMCAGenerator_tensorGeneratorPiUnivariate [Fintype F] [SampleableType F]
    {A : Type} [AddCommMonoid A] [Module F A] (MC : ModuleCode ι F A)
    (ε : ℕ → I → ℝ≥0)
    (huniv : ∀ e : ℕ, IsMCAGenerator (univariatePowersGenerator F e) (ε e) MC) :
    ∀ {s : ℕ} [SampleableType (Fin s → F)] (d : Fin s → ℕ),
      IsMCAGenerator (tensorGeneratorPiUnivariate d) (fun γ => ∑ i, ε (d i) γ) MC := by
  classical
  intro s _ d
  exact isMCAGenerator_tensorGeneratorPi_tight
    (fun _ _ _ _ MC' => ∀ e (δ : ℝ), mcaError (univariatePowersGenerator F e) MC' δ ≤
      mcaError (univariatePowersGenerator F e) MC δ)
    (fun _ _ _ _ _ _ _ MC' hMC' e δ =>
      (mcaError_moduleInterleavedCode_le_of_card_le _ MC' δ le_rfl).trans (hMC' e δ))
    (fun i => univariatePowersGenerator F (d i)) (fun i => ε (d i))
    (fun i _ _ _ _ MC' hMC' γ => (hMC' (d i) γ).trans (huniv (d i) γ)) MC
    (fun _ _ => le_rfl)

/-- The coefficient matrix expressing the polynomial generator `G` as a right multiplication of
the tensor generator of powers: the entry at `(e, j)` is the coefficient of the monomial
`exponentFinsupp e` in the polynomial `P j` (see `generatorByRightMul_coeffMatrix`). -/
noncomputable def coeffMatrix {s : ℕ} {ℓ : Type} [Fintype ℓ] (P : ℓ → MvPolynomial (Fin s) F)
    (d : Fin s → ℕ) : Matrix ((i : Fin s) → Fin (d i + 1)) ℓ F :=
  fun e j => (P j).coeff (exponentFinsupp e)

/-- A generator that evaluates the polynomials `P` is the right multiplication of the tensor
generator of powers by the coefficient matrix of `P`. -/
lemma generatorByRightMul_coeffMatrix {s : ℕ} {ℓ : Type} [Fintype ℓ]
    (P : ℓ → MvPolynomial (Fin s) F) (d : Fin s → ℕ)
    (hdeg : ∀ (j : ℓ) (i : Fin s), (P j).degreeOf i ≤ d i)
    (G : Generator (Fin s → F) ℓ F) (hG : ∀ x, G x = MvPolynomial.eval x ∘ P) :
    generatorByRightMul (tensorGeneratorPiUnivariate d) (coeffMatrix P d) = G := by
  funext x j
  rw [hG]
  simp only [Function.comp_apply, generatorByRightMul, Matrix.vecMul, dotProduct,
    tensorGeneratorPiUnivariate, coeffMatrix]
  have hsub : (P j).support ⊆ Finset.univ.image (exponentFinsupp (d := d)) := by
    intro mo hmo
    obtain ⟨e, he⟩ :=
      exists_exponentFinsupp_eq fun i => le_trans (monomial_le_degreeOf i hmo) (hdeg j i)
    exact Finset.mem_image.mpr ⟨e, Finset.mem_univ _, he⟩
  rw [eval_eq', Finset.sum_subset hsub
      (fun mo _ hmo => by simp [MvPolynomial.notMem_support_iff.mp hmo]),
    Finset.sum_image (fun a _ b _ h => exponentFinsupp_injective h)]
  exact Finset.sum_congr rfl fun e _ => by simp [mul_comm, exponentFinsupp]

/-- The coefficient matrix of a linearly independent family of polynomials whose individual
degrees are bounded by the box `d` has a left inverse. -/
lemma hasLeftPseudoInverse_coeffMatrix {s : ℕ} {ℓ : Type} [Fintype ℓ] [DecidableEq ℓ]
    (P : ℓ → MvPolynomial (Fin s) F) (d : Fin s → ℕ)
    (hdeg : ∀ (j : ℓ) (i : Fin s), (P j).degreeOf i ≤ d i) (hP : LinearIndependent F P) :
    HasLeftPseudoInverse (coeffMatrix P d) := by
  set A := coeffMatrix P d with hA
  have hinj : LinearMap.ker A.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    set Q : MvPolynomial (Fin s) F := ∑ j, v j • P j with hQ
    have hcoeff : ∀ e : (i : Fin s) → Fin (d i + 1), Q.coeff (exponentFinsupp e) = 0 := by
      intro e
      have hve := congrFun hv e
      simpa [hA, coeffMatrix, Matrix.mulVecLin, Matrix.mulVec, dotProduct, hQ,
        MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, mul_comm] using hve
    have hQ0 : Q = 0 := by
      ext mo
      rw [AddMonoidAlgebra.coeff_zero]
      by_cases hmem : ∀ i, mo i ≤ d i
      · obtain ⟨e, he⟩ := exists_exponentFinsupp_eq hmem
        exact he ▸ hcoeff e
      · simp only [not_forall, not_le] at hmem
        obtain ⟨i, hi⟩ := hmem
        apply MvPolynomial.notMem_support_iff.mp
        intro hmo
        rw [hQ] at hmo
        obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hmo)
        have hj' : mo ∈ (P j).support := MvPolynomial.support_smul hj
        exact absurd (le_trans (monomial_le_degreeOf i hj') (hdeg j i)) (by omega)
    exact funext fun j => Fintype.linearIndependent_iff.mp hP v (hQ.symm.trans hQ0) j
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective A.mulVecLin hinj
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have hcomp : LinearMap.toMatrix' (g.comp A.mulVecLin) = LinearMap.toMatrix' g * A := by
    rw [LinearMap.toMatrix'_comp]
    congr 1
    rw [← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
  rw [hg, LinearMap.toMatrix'_id] at hcomp
  exact hcomp.symm

/-- A full-field polynomial generator has MCA for the Reed-Solomon code of degree `k` over the
domain `D`, with error `∑ i, reedSolomonMCAError k D (maxDegreeOf P i) m`, for every `m ≥ 3`.

The proof factors the generator through `tensorGeneratorPiUnivariate` via `coeffMatrix`, with
`isMCAGenerator_univariatePowersGenerator` for each factor and
`isMCAGenerator_tensorGeneratorPiUnivariate` for the tensor stage. -/
lemma isMCAGenerator_of_isPolynomialGeneratorOfFull [Fintype F] [SampleableType F] [NeZero k]
    (m : ℕ) (hm : 3 ≤ m)
    {ℓ : Type} [Fintype ℓ] {s : ℕ} [SampleableType (Fin s → F)]
    {P : ℓ → MvPolynomial (Fin s) F}
    (G : Generator ((Fin s) → F) ℓ F) (hG : IsPolynomialGeneratorOfFull G P) :
    letI ε := ∑ i : Fin s, reedSolomonMCAError k D (maxDegreeOf P i) m
    IsMCAGenerator G ε (ReedSolomon.code D k) := by
  classical
  have hdeg : ∀ (j : ℓ) (i : Fin s), (P j).degreeOf i ≤ maxDegreeOf P i := by
    intro j i
    simpa [maxDegreeOf] using
      Finset.le_sup (f := fun j => (P j).degreeOf i) (Finset.mem_univ j)
  have htensor := isMCAGenerator_tensorGeneratorPiUnivariate (ReedSolomon.code D k)
    (fun e => reedSolomonMCAError k D e m)
    (fun e => isMCAGenerator_univariatePowersGenerator k D e m hm) (maxDegreeOf P)
  have hmul := pseudoinverseGen (tensorGeneratorPiUnivariate (maxDegreeOf P))
    (fun γ => ∑ i, reedSolomonMCAError k D (maxDegreeOf P i) m γ) (ReedSolomon.code D k) htensor
    (coeffMatrix P (maxDegreeOf P))
    (hasLeftPseudoInverse_coeffMatrix P (maxDegreeOf P) hdeg hG.1)
  rw [generatorByRightMul_coeffMatrix P (maxDegreeOf P) hdeg G hG.2] at hmul
  rwa [_root_.funext fun γ => (Finset.sum_apply γ Finset.univ _).symm] at hmul

end RSCode

namespace PolynomialGenIsMCA

open CoreDefinitions LinearTransformations LinearCode RSCode ReedSolomon
open unitInterval NNReal Probability

variable {F : Type} [Field F]

/-- The univariate powers generator of degree `d` with its seed space restricted to a subset
`s ⊆ F`: `x ↦ (1, x, …, x^d)`. -/
def univariatePowersGeneratorOn (s : Set F) (d : ℕ) : Generator s (Fin (d + 1)) F :=
  fun x j => (x : F) ^ (j : ℕ)

/-- The code `C_G` of the restricted univariate powers generator is the Reed–Solomon code of
degree less than `d + 1` over `s`: its `M_G` matrix is the non-square Vandermonde matrix. -/
lemma univariatePowersGeneratorOn_code_eq_reedSolomon (s : Set F) [Fintype s] [Nonempty s] (d : ℕ) :
    fromColGenMat (M_G (univariatePowersGeneratorOn s d))
      = ReedSolomon.code (Function.Embedding.subtype (· ∈ s)) (d + 1) := by
  have hMG : M_G (univariatePowersGeneratorOn s d)
      = Vandermonde.nonsquare (d + 1) ((Function.Embedding.subtype (· ∈ s)) : s → F) := by
    ext x j
    simp [M_G, univariatePowersGeneratorOn, Vandermonde.nonsquare]
  rw [hMG, genMatIsVandermonde]

/-- The restricted univariate powers generator is an MDS generator (its code is Reed–Solomon,
hence MDS). Note that this holds for every degree `d`, with no bound relating `d` to `#s`. -/
lemma isMDSGenerator_univariatePowersGeneratorOn [DecidableEq F] (s : Set F) [Fintype s]
    [Inhabited s] (d : ℕ) : IsMDSGenerator (univariatePowersGeneratorOn s d) := by
  unfold IsMDSGenerator
  rw [univariatePowersGeneratorOn_code_eq_reedSolomon]
  exact ReedSolomon.isMDS_code

/-- The restricted univariate powers generator has MCA, with error `powersMCAError LC`, for
every module code over `ι` whose relative distance equals that of `LC` — in particular for `LC`
itself (`MC := LC`, `hδ := rfl`) and for every iterated interleaving of `LC`.

For `d ≥ 1` this is `isMCAGenerator_of_isMDSGenerator` (sorried) together with the
identifications `mdsMCAError_congr` (as `mdsMCAError` reads the code only through `δᵣ`) and
`mdsMCAError_eq_powersMCAError`; for `d = 0` the MCA event is vacuous at any alphabet, so the
error `0 ≤ powersMCAError` suffices. -/
lemma isMCAGenerator_univariatePowersGeneratorOn {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq F]
    (s : Set F) [Fintype s] [Inhabited s] [SampleableType s]
    (LC : LinearCode ι F) (d : ℕ) (η : ℝ) (hη : 0 < η ∧ η < 1)
    (h : d + 1 ≤ Fintype.card ↥s)
    {A : Type} [AddCommMonoid A] [Module F A] [DecidableEq A] (MC : ModuleCode ι F A)
    (hδ : Code.minRelHammingDistCode MC.carrier = Code.minRelHammingDistCode LC.carrier) :
    IsMCAGenerator (univariatePowersGeneratorOn s d)
      (powersMCAError LC d (Fintype.card ↥s) η) MC := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    classical
    have : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
    intro γ
    refine iSup_le fun U => ?_
    have hfalse : ∀ x : ↥s, ¬ IsMCA (univariatePowersGeneratorOn s 0) MC x U (γ : ℝ) := by
      rintro x ⟨T, hT, hmem, j, hj⟩
      apply hj
      have hvec : (fun k => ∑ j', univariatePowersGeneratorOn s 0 x j' • U j' k) = U j := by
        funext w
        rw [Fintype.sum_subsingleton _ j]
        simp [univariatePowersGeneratorOn]
      rwa [hvec] at hmem
    rw [SampleableType.prEvent_uniformSample_eq_ofReal,
      Finset.filter_false_of_mem fun x _ => hfalse x]
    simp
  · have hℓ : 2 ≤ Fintype.card (Fin (d + 1)) := by rw [Fintype.card_fin]; omega
    have hdim : LinearCode.dim (fromColGenMat (M_G (univariatePowersGeneratorOn s d)))
        = Fintype.card (Fin (d + 1)) := by
      rw [univariatePowersGeneratorOn_code_eq_reedSolomon, ReedSolomon.dim_eq_deg_of_le h,
        Fintype.card_fin]
    have hmca := isMCAGenerator_of_isMDSGenerator (univariatePowersGeneratorOn s d)
      (isMDSGenerator_univariatePowersGeneratorOn s d) hdim η hη hℓ MC
    rwa [Fintype.card_fin, mdsMCAError_congr LC MC (d + 1) (Fintype.card ↥s) η hδ,
      mdsMCAError_eq_powersMCAError] at hmca

/-- The `s`-fold tensor product of restricted univariate powers generators, over the product seed
space `∏ᵢ Sᵢ`: `(x₁, …, xₛ) ↦ ⊗ᵢ (1, xᵢ, …, xᵢ^{dᵢ})`. -/
def tensorGeneratorPiUnivariateOn {s : ℕ} (S : Fin s → Set F) (d : Fin s → ℕ) :
    Generator (∀ i, (S i)) ((i : Fin s) → Fin (d i + 1)) F :=
  fun x j => ∏ i, ((x i) : F) ^ (j i : ℕ)

/-- The tensor product of the restricted univariate powers generators has MCA for any linear
code `LC`, with error the sum `∑ᵢ powersMCAError LC dᵢ` of the factors' errors. Proved through
`isMCAGenerator_tensorGeneratorPi_tight`: `isMCAGenerator_univariatePowersGeneratorOn` supplies
each factor's MCA at every module code of relative distance `δᵣ LC`, which covers the iterated
interleavings the induction routes through, so the open `isMCAGenerator_tensorGenerator_tight`
is not needed. -/
lemma isMCAGenerator_tensorGeneratorPiUnivariateOn {ι : Type} [Fintype ι] [Nonempty ι]
    [DecidableEq F] (LC : LinearCode ι F) (η : ℝ) (hη : 0 < η ∧ η < 1)
    {s : ℕ} (S : Fin s → Set F) [∀ i, Fintype ↥(S i)] [∀ i, Inhabited ↥(S i)]
    [∀ i, SampleableType ↥(S i)]
    [SampleableType ((i : Fin s) → ↥(S i))]
    (d : Fin s → ℕ) (hcard : ∀ i, d i + 1 ≤ Fintype.card ↥(S i)) :
    IsMCAGenerator (tensorGeneratorPiUnivariateOn S d)
      (fun γ => ∑ i, powersMCAError LC (d i) (Fintype.card ↥(S i)) η γ) LC :=
  isMCAGenerator_tensorGeneratorPi_tight
    (fun _ _ _ _ MC =>
      Code.minRelHammingDistCode MC.carrier = Code.minRelHammingDistCode LC.carrier)
    (fun _ _ _ _ _ _ _ MC hMC => (Code.minRelHammingDistCode_moduleInterleavedCode MC).trans hMC)
    (fun i => univariatePowersGeneratorOn (S i) (d i))
    (fun i => powersMCAError LC (d i) (Fintype.card ↥(S i)) η)
    (fun i {_A} _ _ _ MC hMC =>
      isMCAGenerator_univariatePowersGeneratorOn (S i) LC (d i) η hη (hcard i) MC hMC)
    LC rfl

/-- A generator that evaluates the polynomials `P` on restricted seed sets is the right
multiplication of the restricted tensor generator of powers by the coefficient matrix of `P`. -/
lemma generatorByRightMul_coeffMatrix_on {s : ℕ} {ℓ : Type} [Fintype ℓ]
    (S : Fin s → Set F) (P : ℓ → MvPolynomial (Fin s) F) (d : Fin s → ℕ)
    (hdeg : ∀ (j : ℓ) (i : Fin s), (P j).degreeOf i ≤ d i)
    (G : Generator (∀ i, ↥(S i)) ℓ F)
    (hG : ∀ x, G x = MvPolynomial.eval (fun i => (↑(x i) : F)) ∘ P) :
    generatorByRightMul (tensorGeneratorPiUnivariateOn S d) (coeffMatrix P d) = G := by
  funext x
  set xc : Fin s → F := fun i => (↑(x i) : F) with hxc
  have hsub : tensorGeneratorPiUnivariateOn S d x = tensorGeneratorPiUnivariate d xc := by
    funext e; simp [tensorGeneratorPiUnivariateOn, tensorGeneratorPiUnivariate, hxc]
  have hgbm := generatorByRightMul_coeffMatrix P d hdeg
    (fun y => MvPolynomial.eval y ∘ P) (fun _ => rfl)
  calc generatorByRightMul (tensorGeneratorPiUnivariateOn S d) (coeffMatrix P d) x
      = Matrix.vecMul (tensorGeneratorPiUnivariateOn S d x) (coeffMatrix P d) := rfl
    _ = Matrix.vecMul (tensorGeneratorPiUnivariate d xc) (coeffMatrix P d) := by rw [hsub]
    _ = generatorByRightMul (tensorGeneratorPiUnivariate d) (coeffMatrix P d) xc := rfl
    _ = (MvPolynomial.eval xc ∘ P) := congrFun hgbm _
    _ = G x := (hG x).symm

/-- A polynomial generator over restricted seed sets `Sᵢ` with `|Sᵢ| ≥ dᵢ + 1` has MCA for
every linear code `LC`, with error `∑ᵢ powersMCAError LC dᵢ |Sᵢ| η`, for every `0 < η < 1`.

Its only unproved input is `isMCAGenerator_of_isMDSGenerator`: the tensor stage is
`isMCAGenerator_tensorGeneratorPi_tight`, which reaches the unscaled error sum through the
proved interleaved-hypothesis lemma rather than the open
`isMCAGenerator_tensorGenerator_tight`. -/
theorem isMCAGenerator_of_isPolynomialGeneratorOf {ι : Type} [Fintype ι] [Nonempty ι]
    [DecidableEq F] {ℓ : Type} [Fintype ℓ] (LC : LinearCode ι F)
    (η : ℝ) (hη : 0 < η ∧ η < 1)
    {s : ℕ} (S : Fin s → Set F) [∀ i, Fintype (S i)] [∀ i, Inhabited (S i)]
    [∀ i, SampleableType (S i)]
    [SampleableType ((i : Fin s) → S i)]
    (G : Generator (∀ i, S i) ℓ F)
    (P : ℓ → MvPolynomial (Fin s) F) (hG : IsPolynomialGeneratorOf S G P)
    (hS : ∀ i : Fin s, (maxDegreeOf P i + 1) ≤ (Set.ncard (S i))) :
    letI ε : I → ℝ≥0 := ∑ i : Fin s, (powersMCAError LC (maxDegreeOf P i) (Set.ncard (S i)) η)
    IsMCAGenerator G ε LC := by
  classical
  have hcard : ∀ i : Fin s, Set.ncard (S i) = Fintype.card (S i) := by
    intro i
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
  have hdeg : ∀ (j : ℓ) (i : Fin s), (P j).degreeOf i ≤ maxDegreeOf P i := by
    intro j i
    simpa [maxDegreeOf] using
      Finset.le_sup (f := fun j => (P j).degreeOf i) (Finset.mem_univ j)
  have hcard_deg : ∀ i : Fin s, maxDegreeOf P i + 1 ≤ Fintype.card (S i) := by
    intro i
    rw [← hcard i]
    exact hS i
  have htensor := isMCAGenerator_tensorGeneratorPiUnivariateOn LC η hη S (maxDegreeOf P) hcard_deg
  have hmul := pseudoinverseGen (tensorGeneratorPiUnivariateOn S (maxDegreeOf P))
    (fun γ => ∑ i, powersMCAError LC (maxDegreeOf P i) (Fintype.card ↥(S i)) η γ) LC htensor
    (coeffMatrix P (maxDegreeOf P))
    (hasLeftPseudoInverse_coeffMatrix P (maxDegreeOf P) hdeg hG.1)
  rw [generatorByRightMul_coeffMatrix_on S P (maxDegreeOf P) hdeg G hG.2] at hmul
  have herr : (∑ i : Fin s, powersMCAError LC (maxDegreeOf P i) (Set.ncard (S i)) η)
      = (fun γ => ∑ i, powersMCAError LC (maxDegreeOf P i) (Fintype.card ↥(S i)) η γ) := by
    funext γ
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl (fun i _ => by rw [hcard i])
  rwa [herr]

end PolynomialGenIsMCA
