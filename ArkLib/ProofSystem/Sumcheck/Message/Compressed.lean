/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.ProofSystem.Sumcheck.Message.Quadratic

/-!
# Compressed Boolean Sumcheck messages of arbitrary positive degree

A degree-`d + 1` message sends its constant coefficient and its `d` coefficients of
degrees two through `d + 1`. The running claim determines the linear coefficient.
The reconstruction uses no division and applies in characteristic two.
-/

@[expose] public section

namespace Sumcheck

open Polynomial

/-- The constant coefficient and the coefficients of degrees two through `d + 1`. -/
abbrev CompressedMessage (R : Type) (d : ℕ) := R × (Fin d → R)

/-- Encode all coefficients except the linear coefficient of a bounded polynomial. -/
def compress {R : Type} [Semiring R] {d : ℕ} (p : R⦃≤ d + 1⦄[X]) : CompressedMessage R d :=
  (p.val.coeff 0, fun j => p.val.coeff (j.val + 2))

/-- A bounded polynomial splits into its constant, linear, and higher coefficients. -/
theorem bounded_decomposition {R : Type} [Semiring R] {d : ℕ} (p : R⦃≤ d + 1⦄[X]) :
    p.val = C (p.val.coeff 0) + C (p.val.coeff 1) * X +
      ∑ j : Fin d, C (p.val.coeff (j.val + 2)) * X ^ (j.val + 2) := by
  have hdeg := Polynomial.natDegree_le_iff_degree_le.mpr
    (Polynomial.mem_degreeLE.mp p.property)
  change p.val.natDegree ≤ d + 1 at hdeg
  have h := p.val.as_sum_range_C_mul_X_pow' (n := d + 2) (by omega)
  rw [← Fin.sum_univ_eq_sum_range, Fin.sum_univ_succ, Fin.sum_univ_succ] at h
  simpa only [Fin.val_zero, Fin.val_succ, pow_zero, mul_one, zero_add, pow_one,
    Nat.add_assoc, add_assoc] using h

variable {R : Type} [CommRing R] {d : ℕ}

/-- Reconstruct the linear coefficient from the Boolean sum and transmitted coefficients. -/
noncomputable def compressed (c : R) (m : CompressedMessage R d) : R⦃≤ d + 1⦄[X] :=
  ⟨C m.1 + C (c - 2 * m.1 - ∑ j, m.2 j) * X +
    ∑ j : Fin d, C (m.2 j) * X ^ (j.val + 2), by
    apply Polynomial.mem_degreeLE.mpr
    apply degree_add_le_of_degree_le
    · apply degree_add_le_of_degree_le
      · exact degree_C_le.trans (by exact_mod_cast Nat.zero_le (d + 1))
      · simpa only [pow_one] using
          (degree_C_mul_X_pow_le 1 (c - 2 * m.1 - ∑ j, m.2 j)).trans
            (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le d))
    · apply Polynomial.natDegree_le_iff_degree_le.mp
      change (∑ j : Fin d, C (m.2 j) * X ^ (j.val + 2)).natDegree ≤ d + 1
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro j _
      exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)⟩

/-- Evaluate a compressed message directly; reconstruction enforces the Boolean sum. -/
def compressedOps (d : ℕ) : MessageOps R (CompressedMessage R d) where
  evaluate c m r := m.1 + (c - 2 * m.1 - ∑ j, m.2 j) * r +
    ∑ j : Fin d, m.2 j * r ^ (j.val + 2)
  accept _ _ := true

/-- Runtime evaluation agrees with the reconstructed degree-bounded polynomial. -/
theorem compressed_evaluate_eq (c : R) (m : CompressedMessage R d) (r : R) :
    (compressedOps d).evaluate c m r = (compressed c m).val.eval r := by
  simp only [compressedOps, compressed, eval_add, eval_mul, eval_C, eval_X,
    eval_finsetSum, eval_pow]

/-- The reconstructed polynomial has the prescribed sum on zero and one. -/
theorem compressed_boolean_sum (c : R) (m : CompressedMessage R d) :
    (compressed c m).val.eval 0 + (compressed c m).val.eval 1 = c := by
  rw [← compressed_evaluate_eq, ← compressed_evaluate_eq]
  simp only [compressedOps, pow_succ, mul_zero, add_zero, Finset.sum_const_zero, one_pow, mul_one]
  ring

/-- The arbitrary-degree compressed encoding satisfies the neutral message contract. -/
noncomputable def compressedModel [DecidableEq R] [Nontrivial R] (d : ℕ) :
    MessageModel ({0, 1} : Finset R) (compressedOps d) (d + 1) where
  interpret := compressed
  evaluate_eq := compressed_evaluate_eq
  accept_iff c m := by
    simpa only [compressedOps, Finset.sum_pair (zero_ne_one : (0 : R) ≠ 1),
      true_iff] using compressed_boolean_sum c m

/-- The Boolean sum determines the omitted linear coefficient. -/
theorem linear_coeff_eq (c : R) (p : R⦃≤ d + 1⦄[X])
    (hsum : p.val.eval 0 + p.val.eval 1 = c) :
    c - 2 * p.val.coeff 0 - ∑ j : Fin d, p.val.coeff (j.val + 2) = p.val.coeff 1 := by
  have h := congrArg (fun q : R[X] => q.eval 1) (bounded_decomposition p)
  simp only [eval_add, eval_mul, eval_C, eval_X, one_pow, mul_one, eval_finsetSum,
    eval_pow] at h
  rw [← coeff_zero_eq_eval_zero, h] at hsum
  rw [← hsum]
  ring

/-- Decoding an encoded polynomial recovers it when its Boolean sum is the running claim. -/
theorem compressed_compress (c : R) (p : R⦃≤ d + 1⦄[X])
    (hsum : p.val.eval 0 + p.val.eval 1 = c) : compressed c (compress p) = p := by
  apply Subtype.ext
  change C (p.val.coeff 0) +
    C (c - 2 * p.val.coeff 0 - ∑ j : Fin d, p.val.coeff (j.val + 2)) * X +
      ∑ j : Fin d, C (p.val.coeff (j.val + 2)) * X ^ (j.val + 2) = p.val
  rw [linear_coeff_eq c p hsum]
  exact (bounded_decomposition p).symm

/-- Transmitted coefficients survive reconstruction at every running claim. -/
theorem compress_compressed (c : R) (m : CompressedMessage R d) :
    compress (compressed c m) = m := by
  apply Prod.ext
  · simp [compress, compressed, finsetSum_coeff]
  · funext j
    simp only [compress, compressed, coeff_add, finsetSum_coeff, coeff_C_mul_X,
      coeff_C_mul_X_pow, coeff_C, show j.val + 2 ≠ 0 by omega,
      show j.val + 2 ≠ 1 by omega, ite_false, zero_add]
    rw [Finset.sum_eq_single j]
    · simp only [ite_true]
    · intro k _ hkj
      apply ite_eq_right_iff.mpr
      intro h
      exact (hkj (Fin.ext (by omega))).elim
    · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

/-- Degree two specializes to the constant-and-quadratic encoding. -/
theorem compressed_eq_quadratic (c : R) (m : R × R) :
    compressed c (m.1, fun _ : Fin 1 => m.2) = quadratic c m := by
  apply Subtype.ext
  simp only [compressed, quadratic, Fin.sum_univ_one, Fin.val_zero, zero_add]

end Sumcheck
