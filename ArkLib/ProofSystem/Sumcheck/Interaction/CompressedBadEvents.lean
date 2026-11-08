/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.ProofSystem.Sumcheck.Interaction.BadEvents
public import ArkLib.ProofSystem.Sumcheck.Message.Compressed

/-! # Executable coefficient instances for compressed Sumcheck root events -/

@[expose] public section

open Interaction Interaction.Oracle.Security

namespace Sumcheck.Interaction.Knowledge

/-- The omitted linear coefficient is reconstructed from the running Boolean sum. -/
def compressedCoefficients {F : Type} [CommRing F] {d : ℕ}
    (current : F) (message : CompressedMessage F d) : Coefficients F (d + 1) :=
  fun j => if h0 : j.val = 0 then message.1
    else if h1 : j.val = 1 then current - 2 * message.1 - ∑ i, message.2 i
    else message.2 ⟨j.val - 2, by omega⟩

/-- Runtime compressed coefficients agree with the interpreted polynomial at every bounded index. -/
theorem compressedCoefficients_coeff {F : Type} [CommRing F] {d : ℕ}
    (current : F) (message : CompressedMessage F d) (j : Fin (d + 2)) :
    compressedCoefficients current message j = (compressed current message).val.coeff j.val := by
  classical
  by_cases h0 : j.val = 0
  · simp [compressedCoefficients, compressed, h0]
  by_cases h1 : j.val = 1
  · simp [compressedCoefficients, compressed, h1]
  simp only [compressedCoefficients, h0, h1, dite_false, compressed, Polynomial.coeff_add,
    Polynomial.finsetSum_coeff]
  rw [Polynomial.coeff_C, ite_eq_right h0, Polynomial.coeff_C_mul_X,
    ite_eq_right h1, zero_add, zero_add]
  rw [Finset.sum_eq_single ⟨j.val - 2, by omega⟩]
  · simp only [Polynomial.coeff_C_mul_X_pow]
    rw [ite_eq_left (by omega)]
  · intro i _ hne
    rw [Polynomial.coeff_C_mul_X_pow, ite_eq_right]
    intro eq
    apply hne
    apply Fin.ext
    change i.val = j.val - 2
    omega
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

/-- A concrete Boolean-domain embedding gives the compressed protocol its polynomial model. -/
noncomputable def compressedRoundModel {F : Type} [CommRing F] [DecidableEq F] [Nontrivial F]
    {d : ℕ} (D : Fin 2 ↪ F) (domain : Finset.univ.map D = {0, 1}) :
    MessageModel (Finset.univ.map D) (compressedOps d) (d + 1) where
  interpret := compressed
  evaluate_eq := compressed_evaluate_eq
  accept_iff current message := by
    rw [domain]
    exact (compressedModel d).accept_iff current message

/-- The compressed round instance discharges both coefficient premises of generic containment. -/
theorem compressed_badChallenge_subset_badSummand {F W : Type} [CommRing F]
    [DecidableEq F] [Nontrivial F] {n d : ℕ} (D : Fin 2 ↪ F)
    (domain : Finset.univ.map D = {0, 1})
    (valid : W → Prop) (summand : W → Spec.OracleStatement F n (d + 1) ())
    (p : Spec.OracleStatement F n (d + 1) ()) (binding : BindsSummand valid summand p)
    (count start : ℕ) (finish : start + (count + 1) = n)
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) (active : Bool)
    (q : CompressedMessage F d) (r : F)
    (escape : RoundExtractor.badChallenge
      ((roundExtractor (compressedOps d) (claimPredicate D valid summand)
        (count + 1) start finish stmt active q).2.2) (some r)) :
    BadSummand [(fun j : Fin (d + 2) =>
      (Spec.SingleRound.projectedRoundPolynomial F n (d + 1) D ⟨start, by omega⟩
        stmt.challenges p).val.coeff j.val)] (compressedCoefficients stmt.target q) r :=
  badChallenge_subset_badSummand (compressedOps d) D (compressedRoundModel D domain)
    valid summand p binding count start finish stmt active q _ _
    (compressedCoefficients_coeff stmt.target q) (fun _ => rfl) r escape

end Sumcheck.Interaction.Knowledge
