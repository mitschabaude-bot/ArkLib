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

variable {R : Type} [CommRing R] {d : ℕ}

/-- Reconstruct the linear coefficient from the Boolean sum and transmitted coefficients. -/
noncomputable def compressed (c : R) (m : CompressedMessage R d) : R⦃≤ d + 1⦄[X] :=
  ⟨C m.1 + C (c - 2 * m.1 - ∑ j, m.2 j) * X +
    ∑ j : Fin d, C (m.2 j) * X ^ (j.val + 2), by sorry⟩

/-- Evaluate a compressed message directly; reconstruction enforces the Boolean sum. -/
def compressedOps (d : ℕ) : MessageOps R (CompressedMessage R d) where
  evaluate c m r := m.1 + (c - 2 * m.1 - ∑ j, m.2 j) * r +
    ∑ j : Fin d, m.2 j * r ^ (j.val + 2)
  accept _ _ := true

/-- Runtime evaluation agrees with the reconstructed degree-bounded polynomial. -/
theorem compressed_evaluate_eq (c : R) (m : CompressedMessage R d) (r : R) :
    (compressedOps d).evaluate c m r = (compressed c m).val.eval r := by
  sorry

/-- The reconstructed polynomial has the prescribed sum on zero and one. -/
theorem compressed_boolean_sum (c : R) (m : CompressedMessage R d) :
    (compressed c m).val.eval 0 + (compressed c m).val.eval 1 = c := by
  sorry

/-- The arbitrary-degree compressed encoding satisfies the neutral message contract. -/
noncomputable def compressedModel [DecidableEq R] [Nontrivial R] (d : ℕ) :
    MessageModel ({0, 1} : Finset R) (compressedOps d) (d + 1) where
  interpret := compressed
  evaluate_eq := by sorry
  accept_iff := by sorry

/-- Decoding an encoded polynomial recovers it when its Boolean sum is the running claim. -/
theorem compressed_compress (c : R) (p : R⦃≤ d + 1⦄[X])
    (hsum : p.val.eval 0 + p.val.eval 1 = c) : compressed c (compress p) = p := by
  sorry

/-- Transmitted coefficients survive reconstruction at every running claim. -/
theorem compress_compressed (c : R) (m : CompressedMessage R d) :
    compress (compressed c m) = m := by
  sorry

/-- Degree two specializes to the constant-and-quadratic encoding. -/
theorem compressed_eq_quadratic (c : R) (m : R × R) :
    compressed c (m.1, fun _ : Fin 1 => m.2) = quadratic c m := by
  sorry

end Sumcheck
