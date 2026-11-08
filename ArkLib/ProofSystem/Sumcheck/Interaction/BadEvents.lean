/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.ProofSystem.Sumcheck.Interaction.Knowledge

/-! # Executable list-candidate root events for generic Sumcheck -/

@[expose] public section

open Interaction Interaction.Oracle Interaction.Oracle.Security OracleComp OracleSpec

namespace Sumcheck.Interaction.Knowledge

/-- A degree-bounded polynomial's executable coefficient vector. -/
abbrev Coefficients (F : Type) (deg : ℕ) := Fin (deg + 1) → F

/-- Evaluate a bounded coefficient vector using only field operations. -/
def evalCoefficients {F : Type} [Semiring F] {deg : ℕ} (a : Coefficients F deg) (r : F) : F :=
  ∑ j, a j * r ^ j.val

/-- A transmitted polynomial differs from a candidate's true message but agrees at the challenge. -/
def BadSummand {F : Type} [Semiring F] {deg : ℕ}
    (candidates : List (Coefficients F deg)) (message : Coefficients F deg) (r : F) : Prop :=
  ∃ actual ∈ candidates, message ≠ actual ∧ evalCoefficients message r = evalCoefficients actual r

/-- The Sumcheck root checker enumerates only the certified candidate list. -/
def checkBadSummand {F : Type} [Semiring F] [DecidableEq F] {deg : ℕ}
    (candidates : List (Coefficients F deg)) (message : Coefficients F deg) (r : F) : Bool :=
  candidates.any fun actual => decide
    (message ≠ actual ∧ evalCoefficients message r = evalCoefficients actual r)

/-- The coefficient checker decides the mathematical Sumcheck bad event. -/
theorem checkBadSummand_iff {F : Type} [Semiring F] [DecidableEq F] {deg : ℕ}
    (candidates : List (Coefficients F deg)) (message : Coefficients F deg) (r : F) :
    checkBadSummand candidates message r = true ↔ BadSummand candidates message r := by
  simp only [checkBadSummand, List.any_eq_true, decide_eq_true_eq, BadSummand]

/-- Hiding columns only removes decoded candidates and therefore cannot create a root event. -/
theorem BadSummand.mono {F : Type} [Semiring F] {deg : ℕ}
    {small large : List (Coefficients F deg)} (h : small ⊆ large)
    {message : Coefficients F deg} {r : F} (bad : BadSummand small message r) :
    BadSummand large message r := by
  obtain ⟨actual, ha, rest⟩ := bad
  exact ⟨actual, h ha, rest⟩

/-- A zero-filled candidate list bounds every masked list at the original degree and list size. -/
theorem prob_badSummand_le {F : Type} [Field F] [Fintype F] [SampleableType F] {deg : ℕ}
    (masked completed : List (Coefficients F deg)) (subset : masked ⊆ completed)
    (message : Coefficients F deg) :
    Pr{let r ←$ᵗ F}[BadSummand masked message r] ≤
      (completed.length : ENNReal) * ((deg : ENNReal) / Fintype.card F) := by
  sorry

/-- A bound summand uses a singleton true-message list and keeps the original round error. -/
theorem prob_badSummand_singleton_le {F : Type} [Field F] [Fintype F] [SampleableType F]
    {deg : ℕ} (actual message : Coefficients F deg) :
    Pr{let r ←$ᵗ F}[BadSummand [actual] message r] ≤ (deg : ENNReal) / Fintype.card F := by
  simpa only [List.length_singleton, Nat.cast_one, one_mul] using
    prob_badSummand_le [actual] [actual] (List.Subset.refl _) message

/-- Binding places a generic retained-witness escape inside the singleton candidate root event. -/
theorem badChallenge_subset_badSummand {F W M : Type} [CommRing F]
    {n deg m : ℕ} (ops : MessageOps F M) (D : Fin m ↪ F)
    (model : MessageModel (Finset.univ.map D) ops deg)
    (valid : W → Prop) (summand : W → Spec.OracleStatement F n deg ())
    (p : Spec.OracleStatement F n deg ()) (binding : BindsSummand valid summand p)
    (count start : ℕ) (finish : start + (count + 1) = n)
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) (active : Bool) (q : M)
    (message actual : Coefficients F deg)
    (message_coeff : ∀ j, message j = (model.interpret stmt.target q).val.coeff j.val)
    (actual_coeff : ∀ j, actual j =
      (Spec.SingleRound.projectedRoundPolynomial F n deg D ⟨start, by omega⟩
        stmt.challenges p).val.coeff j.val)
    (r : F)
    (escape : RoundExtractor.badChallenge
      ((roundExtractor ops (claimPredicate D valid summand) (count + 1) start finish stmt active
        q).2.2) (some r)) : BadSummand [actual] message r := by
  sorry

end Sumcheck.Interaction.Knowledge
