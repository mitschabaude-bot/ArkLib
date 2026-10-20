/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import ArkLib.ProofSystem.Fri.QuerySoundness

/-!
# Agreement lifting along the executable FRI query projections

The executable specification indexes every domain from the original domain. This module
applies the single-fold agreement theorem to positions projected through an arbitrary
prefix of folding rounds, keeping the original query set fixed. Under lossy safety, the lifted
agreement holds on a subset of the original queries missing at most a `loss` fraction of the
original domain.
-/

@[expose] public section

namespace Fri

open Domain ProximityGap ReedSolomon LinearCode Polynomial
open CosetFftDomainClass (sqFoldMapGen)

variable {F : Type} [Field F] [DecidableEq F] {n a k d : ℕ}

/-- Lift a polynomial agreement certificate through a lossily safe fold, on the projected
positions of a large set `S` of original queries. The lifted certificate holds on a subset of
`S` missing at most `loss · 2 ^ n` positions. This reconciles absolute and nested domain
indexing. -/
theorem exists_polynomial_agree_on_projection
    (domain : SmoothCosetFftDomain n F) (hak : a + k ≤ n) (hd : 0 < d)
    (f : Fin (2 ^ (n - a)) → F) (α : F) (θ loss : ℝ)
    (hsafe : ¬ LossyFoldingAgreementFailure (domain.subdomain a) f k d θ loss α)
    (S : Finset (Fin (2 ^ n))) (hlarge : (2 ^ n : ℝ) * (1 - θ) ≤ S.card)
    (p : F[X]) (hp : p.natDegree < d)
    (hcheck : ∀ z ∈ S,
      foldValue (domain.subdomain a) f k α ((domain z ^ (2 ^ a)) ^ (2 ^ k)) =
        p.eval ((domain z ^ (2 ^ a)) ^ (2 ^ k))) :
    ∃ q : F[X], q.natDegree < 2 ^ k * d ∧ ∃ S' ⊆ S, (S.card : ℝ) ≤ S'.card + loss * 2 ^ n ∧
      ∀ z ∈ S', q.eval (domain z ^ (2 ^ a)) = f (sqFoldMapGen (i := a) z) := by
  classical
  let proj : Fin (2 ^ n) → Fin (2 ^ (n - a - k)) := fun z ↦
    sqFoldMapGen (i := k) (sqFoldMapGen (i := a) z)
  have hproj (R : Finset (Fin (2 ^ n))) :
      (R.card : ℝ) ≤ 2 ^ a * (2 ^ k * ((R.image (sqFoldMapGen (i := a))).image
        (sqFoldMapGen (i := k))).card) := by
    have h₁ : (R.card : ℝ) ≤
        2 ^ a * ((R.image (sqFoldMapGen (i := a))).card : ℝ) := by
      exact_mod_cast card_le_mul_card_sqFoldMapGen_image domain a R
    have h₂ : ((R.image (sqFoldMapGen (i := a))).card : ℝ) ≤
        2 ^ k * (((R.image (sqFoldMapGen (i := a))).image (sqFoldMapGen (i := k))).card : ℝ) := by
      exact_mod_cast card_le_mul_card_sqFoldMapGen_image (domain.subdomain a) k
        (R.image (sqFoldMapGen (i := a)))
    exact h₁.trans (mul_le_mul_of_nonneg_left h₂ (by positivity))
  have hn : (2 : ℝ) ^ n = 2 ^ a * (2 ^ k * 2 ^ (n - a - k)) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have hproduct : (0 : ℝ) < 2 ^ a * 2 ^ k := by positivity
  let T := (S.image (sqFoldMapGen (i := a))).image (sqFoldMapGen (i := k))
  have hTlarge : (2 ^ (n - a - k) : ℝ) * (1 - θ) ≤ T.card := by
    have h := hproj S
    rw [hn] at hlarge
    nlinarith
  have hpow (z : Fin (2 ^ n)) :
      (domain.subdomain a).subdomain k (proj z) = (domain z ^ (2 ^ a)) ^ (2 ^ k) := by
    rw [CosetFftDomainClass.pow_eq_subdomain_sqFoldMapGen,
      CosetFftDomainClass.pow_eq_subdomain_sqFoldMapGen]
  have hfold : projectedWord (foldWord (domain.subdomain a) f k α) T ∈
      projectedCodeSubmod (code ((domain.subdomain a).subdomain k) d) T := by
    rw [mem_projectedCodeSubmod_iff]
    refine ⟨evalOnPoints _ p, evalOnPoints_mem_code_of_natDegree_lt hp, ?_⟩
    funext x
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp x.property
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    change foldValue _ f k α (((domain.subdomain a).subdomain k) x.val) =
      p.eval (((domain.subdomain a).subdomain k) x.val)
    rw [← hxy, hpow]
    exact hcheck z hz
  obtain ⟨T', hT', hT'card, u, hu, hagree⟩ : ∃ T' ⊆ T,
      (T'.card : ℝ) ≥ T.card - loss * Fintype.card (Fin (2 ^ (n - a - k))) ∧
      ∃ u ∈ code (domain.subdomain a) (2 ^ k * d),
        ∀ i x, x ∈ T' → domain.subdomain a i ^ (2 ^ k) =
          (domain.subdomain a).subdomain k x → u i = f i := by
    by_contra h
    exact hsafe ⟨T, by simpa using hTlarge, hfold, fun T' hT' hc hex ↦ h ⟨T', hT', hc, hex⟩⟩
  simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] at hT'card
  let : NeZero (2 ^ k * d) := ⟨by positivity⟩
  obtain ⟨q, hq, rfl⟩ := mem_code_iff_exists_polynomial_of_ne_zero.mp hu
  refine ⟨q, hq, S.filter fun z ↦ proj z ∈ T', Finset.filter_subset _ _, ?_, fun z hz ↦ ?_⟩
  · let R := S.filter fun z ↦ ¬ proj z ∈ T'
    have hR : (R.image (sqFoldMapGen (i := a))).image (sqFoldMapGen (i := k)) ⊆ T \ T' := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨hzS, hzT⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hzS), hzT⟩
    have hsdiff : ((T \ T').card : ℝ) = T.card - T'.card := by
      rw [Finset.card_sdiff_of_subset hT']
      exact Nat.cast_sub (Finset.card_le_card hT')
    have hRcard : (R.card : ℝ) ≤ 2 ^ a * (2 ^ k * (T.card - T'.card)) := by
      rw [← hsdiff]
      refine (hproj R).trans ?_
      gcongr
    have hsplit : (S.card : ℝ) = (S.filter fun z ↦ proj z ∈ T').card + R.card := by
      exact_mod_cast (Finset.card_filter_add_card_filter_not
        (s := S) (fun z ↦ proj z ∈ T')).symm
    have hloss : 2 ^ a * (2 ^ k * ((T.card : ℝ) - T'.card)) ≤
        2 ^ a * (2 ^ k * (loss * 2 ^ (n - a - k))) := by
      gcongr
      linarith
    rw [hn]
    linarith
  · have h := hagree (sqFoldMapGen (i := a) z) (proj z) (Finset.mem_filter.mp hz).2
      (CosetFftDomainClass.pow_eq_subdomain_sqFoldMapGen (ω := domain.subdomain a) _).symm
    change q.eval (domain.subdomain a (sqFoldMapGen (i := a) z)) = _ at h
    rwa [CosetFftDomainClass.pow_eq_subdomain_sqFoldMapGen] at h

end Fri
