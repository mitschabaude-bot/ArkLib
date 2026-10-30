/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.ProofSystem.Fri.QuerySoundness

/-!
# Folds with an injected word

Plonky3's FRI over inputs of several heights rolls the input of the folded domain's height into
the folded word: a fold by `2 ^ k` at `α` may add `α ^ 2 ^ k · g` for a word `g` on the folded
domain. Such a fold combines the `2 ^ k` coefficient words of the fold and `g` by the powers of
`α`, so its bad event (`LossyInjectFailure`) is contained in the lossy MCA event of the powers
generator of `2 ^ k + 1` words (`isLossyMCA_of_lossyInjectFailure`), and has probability at most
its lossy MCA error (`lossyInjectFailure_prob_le`). Without an injected word, the fold's bad
event is ArkLib's `LossyFoldingAgreementFailure`.

`Agrees` states that a word agrees with a Reed–Solomon codeword on a set of at least a given
density, the relation FRI tests its inputs for.
-/

@[expose] public section

namespace Fri.Interaction

open Polynomial Domain ProximityGap ReedSolomon LinearCode CoreDefinitions Fri
open OracleComp
open scoped BigOperators ProbabilityTheory

variable {F : Type} [Field F]

/-- A word agrees with a codeword of `code domain d` on a set of at least `ρ` of the domain. -/
def Agrees {m : ℕ} (domain : Fin (2 ^ m) ↪ F) (d : ℕ) (ρ : ℝ) (w : Fin (2 ^ m) → F) : Prop :=
  ∃ T : Finset (Fin (2 ^ m)), ρ * 2 ^ m ≤ T.card ∧ ∃ v ∈ code domain d, ∀ x ∈ T, v x = w x

/-- Agreement at a density gives agreement at every smaller density. -/
theorem Agrees.mono {m : ℕ} {domain : Fin (2 ^ m) ↪ F} {d : ℕ} {ρ ρ' : ℝ} (h : ρ' ≤ ρ)
    {w : Fin (2 ^ m) → F} (hw : Agrees domain d ρ w) : Agrees domain d ρ' w := by
  obtain ⟨T, hT, hv⟩ := hw
  exact ⟨T, le_trans (mul_le_mul_of_nonneg_right h (by positivity)) hT, hv⟩

variable [DecidableEq F]

/-- An injected fold is lossily bad if some large set admits a codeword of the folded word plus
`α ^ 2 ^ k g`, but on no subset of it missing at most `loss · |L'|` points do both the word before
folding lift to a codeword above it and `g` agree with a codeword on it. -/
def LossyInjectFailure {n : ℕ} (domain : SmoothCosetFftDomain n F) (f : Fin (2 ^ n) → F)
    (k d : ℕ) (g : Fin (2 ^ (n - k)) → F) (θ loss : ℝ) (α : F) : Prop :=
  ∃ T : Finset (Fin (2 ^ (n - k))),
    (Fintype.card (Fin (2 ^ (n - k))) : ℝ) * (1 - θ) ≤ T.card ∧
    projectedWord (fun x ↦ foldWord domain f k α x + α ^ 2 ^ k * g x) T ∈
      projectedCodeSubmod (code (domain.subdomain k) d) T ∧
    ∀ T' ⊆ T, (T'.card : ℝ) ≥ T.card - loss * Fintype.card (Fin (2 ^ (n - k))) →
      ¬ ((∃ u ∈ code domain (2 ^ k * d),
          ∀ i x, x ∈ T' → domain i ^ (2 ^ k) = domain.subdomain k x → u i = f i) ∧
        projectedWord g T' ∈ projectedCodeSubmod (code (domain.subdomain k) d) T')

/-- The words an injected fold combines by the powers of `α`: the fold's coefficient words, then
`g`. -/
noncomputable def injectWords {n : ℕ} (domain : SmoothCosetFftDomain n F) (f : Fin (2 ^ n) → F)
    (k : ℕ) (g : Fin (2 ^ (n - k)) → F) : Fin (2 ^ k + 1) → Fin (2 ^ (n - k)) → F :=
  Fin.lastCases g fun j x ↦ foldWordAuxCoeff domain f k j (domain.subdomain k x)

/-- The powers of `α` combine the injected fold's words into the folded word plus `α ^ 2 ^ k g`. -/
theorem sum_injectWords {n : ℕ} (domain : SmoothCosetFftDomain n F) (f : Fin (2 ^ n) → F)
    (k : ℕ) (g : Fin (2 ^ (n - k)) → F) (α : F) (x : Fin (2 ^ (n - k))) :
    ∑ j, univariatePowersGenerator F (2 ^ k) α j • injectWords domain f k g j x =
      foldWord domain f k α x + α ^ 2 ^ k * g x := by
  rw [Fin.sum_univ_castSucc]
  simp only [injectWords, Fin.lastCases_castSucc, Fin.lastCases_last,
    smul_eq_mul, foldWord, foldValue_eq_sum_of_foldAuxCoeff_mul_pow_alpha]
  congr 1
  exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _

/-- The injected fold's bad event is contained in the lossy MCA event of its words. -/
theorem isLossyMCA_of_lossyInjectFailure [Fintype F] {n k d : ℕ}
    (domain : SmoothCosetFftDomain n F) (f : Fin (2 ^ n) → F) (g : Fin (2 ^ (n - k)) → F)
    (hd : 0 < d) (θ loss : ℝ) (α : F) (h : LossyInjectFailure domain f k d g θ loss α) :
    IsLossyMCA (univariatePowersGenerator F (2 ^ k)) (code (domain.subdomain k) d) α
      (injectWords domain f k g) θ loss := by
  classical
  obtain ⟨T, hT, hfold, hbad⟩ := h
  refine ⟨T, hT, ?_, fun T' hT' hcard ↦ ?_⟩
  · convert hfold using 2
    exact funext fun x ↦ sum_injectWords domain f k g α x
  · by_contra! hall
    refine hbad T' hT' hcard ⟨exists_codeword_agree_of_coefficients domain f hd T' fun j ↦ ?_, ?_⟩
    · have := hall j.castSucc
      simpa only [injectWords, Fin.lastCases_castSucc] using this
    · have := hall (Fin.last _)
      simpa only [injectWords, Fin.lastCases_last] using this

/-- An injected fold is lossily bad with probability at most the lossy MCA error of the powers
generator of `2 ^ k + 1` words, uniformly over the words. -/
theorem lossyInjectFailure_prob_le [Fintype F] [SampleableType F] {n k d : ℕ}
    (domain : SmoothCosetFftDomain n F) (f : Fin (2 ^ n) → F) (g : Fin (2 ^ (n - k)) → F)
    (hd : 0 < d) (θ loss : ℝ) :
    Pr{let α ←$ᵗ F}[LossyInjectFailure domain f k d g θ loss α] ≤
      lossyMcaError (univariatePowersGenerator F (2 ^ k))
        (code (domain.subdomain k : Fin (2 ^ (n - k)) ↪ F) d) θ loss := by
  apply le_trans (prEvent_mono _ _ _
    (isLossyMCA_of_lossyInjectFailure domain f g hd θ loss))
  exact le_iSup (fun U ↦ Pr{let α ←$ᵗ F}[
    IsLossyMCA (univariatePowersGenerator F (2 ^ k))
      (code (domain.subdomain k : Fin (2 ^ (n - k)) ↪ F) d) α U θ loss]) _

end Fri.Interaction
