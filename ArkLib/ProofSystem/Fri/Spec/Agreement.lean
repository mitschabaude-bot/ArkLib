/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import ArkLib.ProofSystem.Fri.Projection
public import ArkLib.ProofSystem.Fri.Spec.SingleRound

/-!
# Agreement certificates for the indexed FRI specification

The specification records all domains relative to the original domain, rather than as
nested subdomains. We lift a certificate backwards along that precise folding schedule.
Each lossily safe fold drops at most `loss · 2 ^ n` original queries from the agreement set, so
after the `k + 1` folds the certificate holds off at most `(k + 1) · loss · 2 ^ n` of them; the
agreement set must start `k · loss · 2 ^ n` above the threshold for the outermost fold to apply.
-/

@[expose] public section

namespace Fri.Spec

open Domain Polynomial ProximityGap Finset
open CosetFftDomainClass (sqFoldMapGen)

variable {F : Type} [Field F] [DecidableEq F] {n k : ℕ}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+)

/-- Total folding exponent before a stage, including the terminal stage. -/
def foldingPrefix (i : Fin (k + 2)) : ℕ :=
  ∑ j ∈ finRangeTo (k + 1) i.val, (s j).val

/-- Degree bound at a stage of the existing folding schedule. -/
def foldingDegree (i : Fin (k + 2)) : ℕ :=
  2 ^ ((∑ j, (s j).val) - foldingPrefix s i) * d.val

@[simp] theorem foldingPrefix_zero : foldingPrefix s 0 = 0 := by
  simp [foldingPrefix, finRangeTo]

@[simp] theorem foldingPrefix_last : foldingPrefix s (Fin.last (k + 1)) = ∑ j, (s j).val := by
  simp only [foldingPrefix, Fin.val_last, finRangeTo]
  rw [List.take_of_length_le (by simp)]
  simp

theorem foldingPrefix_succ (i : Fin (k + 1)) :
    foldingPrefix s i.succ = foldingPrefix s i.castSucc + (s i).val := by
  exact sum_finRangeTo_add_one

theorem foldingPrefix_le (i : Fin (k + 2)) : foldingPrefix s i ≤ ∑ j, (s j).val :=
  Finset.sum_le_sum_of_subset (by simp)

theorem foldingDegree_pos (i : Fin (k + 2)) : 0 < foldingDegree s d i := by
  unfold foldingDegree
  positivity

theorem foldingDegree_castSucc (i : Fin (k + 1)) :
    foldingDegree s d i.castSucc = 2 ^ (s i).val * foldingDegree s d i.succ := by
  have h := foldingPrefix_le s i.succ
  rw [foldingPrefix_succ] at h
  unfold foldingDegree
  rw [foldingPrefix_succ, ← mul_assoc, ← pow_add]
  congr 2
  omega

@[simp] theorem foldingDegree_last : foldingDegree s d (Fin.last (k + 1)) = d.val := by
  simp [foldingDegree]

/-- Agreement with a terminal polynomial lifts to every preceding word, provided no folding
challenge is lossily bad. At stage `i` it holds on the projections of a subset of the original
queries `S` missing at most `(k + 1 - i) · loss · 2 ^ n` of them. -/
theorem exists_polynomial_agree_on_schedule
    (domain : SmoothCosetFftDomain n F) (hs : (∑ j, (s j).val) ≤ n)
    (w : Fin (k + 2) → F → F) (α : Fin (k + 1) → F) (θ loss : ℝ) (hloss : 0 ≤ loss)
    (hsafe : ∀ i : Fin (k + 1), ¬ LossyFoldingAgreementFailure
      (domain.subdomain (foldingPrefix s i.castSucc))
      (fun z ↦ w i.castSucc (domain.subdomain (foldingPrefix s i.castSucc) z))
      (s i).val (foldingDegree s d i.succ) θ loss (α i))
    (S : Finset (Fin (2 ^ n)))
    (hlarge : (2 ^ n : ℝ) * (1 - θ) + k * loss * 2 ^ n ≤ S.card)
    (p : F[X]) (hp : p.natDegree < d.val)
    (hfinal : ∀ z ∈ S, p.eval (domain z ^ (2 ^ foldingPrefix s (Fin.last (k + 1)))) =
      w (Fin.last (k + 1)) (domain z ^ (2 ^ foldingPrefix s (Fin.last (k + 1)))))
    (hcheck : ∀ z ∈ S, ∀ i : Fin (k + 1),
      foldValue (domain.subdomain (foldingPrefix s i.castSucc))
        (fun y ↦ w i.castSucc (domain.subdomain (foldingPrefix s i.castSucc) y))
        (s i).val (α i) (domain z ^ (2 ^ foldingPrefix s i.succ)) =
      w i.succ (domain z ^ (2 ^ foldingPrefix s i.succ))) :
    ∀ i : Fin (k + 2), ∃ q : F[X], q.natDegree < foldingDegree s d i ∧
      ∃ S' ⊆ S, (S.card : ℝ) ≤ S'.card + ((k : ℝ) + 1 - i) * loss * 2 ^ n ∧
        ∀ z ∈ S', q.eval (domain z ^ (2 ^ foldingPrefix s i)) =
          w i (domain z ^ (2 ^ foldingPrefix s i)) := by
  intro i
  induction i using Fin.reverseInduction with
  | last => exact ⟨p, by simpa using hp, S, subset_rfl, by simp, hfinal⟩
  | @cast i ih =>
    obtain ⟨p', hp', S₁, hS₁, hS₁card, hagree⟩ := ih
    have hi : foldingPrefix s i.castSucc + (s i).val ≤ n := by
      rw [← foldingPrefix_succ]
      exact (foldingPrefix_le s i.succ).trans hs
    have hpow (z : Fin (2 ^ n)) :
        (domain z ^ (2 ^ foldingPrefix s i.castSucc)) ^ (2 ^ (s i).val) =
          domain z ^ (2 ^ foldingPrefix s i.succ) := by
      rw [foldingPrefix_succ, pow_add, pow_mul]
    simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one, Fin.val_castSucc] at hS₁card ⊢
    have hik : (i : ℝ) ≤ k := by exact_mod_cast Nat.lt_succ_iff.mp i.isLt
    have hS₁large : (2 ^ n : ℝ) * (1 - θ) ≤ S₁.card := by
      have : 0 ≤ (i : ℝ) * loss * 2 ^ n := by positivity
      linarith
    obtain ⟨q, hq, S₂, hS₂, hS₂card, hqagree⟩ := exists_polynomial_agree_on_projection domain hi
      (foldingDegree_pos s d i.succ) _ (α i) θ loss (hsafe i) S₁ hS₁large p' hp'
      (fun z hz ↦ by rw [hpow]; exact (hcheck z (hS₁ hz) i).trans (hagree z hz).symm)
    refine ⟨q, by rwa [foldingDegree_castSucc], S₂, hS₂.trans hS₁, by linarith, fun z hz ↦ ?_⟩
    simpa only [CosetFftDomainClass.pow_eq_subdomain_sqFoldMapGen] using hqagree z hz

end Fri.Spec
