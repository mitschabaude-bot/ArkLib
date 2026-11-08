/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.ProofSystem.Sumcheck.Interaction.Knowledge
public import Mathlib.Algebra.Polynomial.OfFn

/-! # Executable list-candidate root events for generic Sumcheck -/

@[expose] public section

open Interaction Interaction.Oracle Interaction.Oracle.Security OracleComp OracleSpec

namespace Sumcheck.Interaction.Knowledge

open SingleRound MultivariateRound
/-- A degree-bounded polynomial's executable coefficient vector. -/
abbrev Coefficients (F : Type) (deg : ℕ) := Fin (deg + 1) → F
/-- Evaluate a bounded coefficient vector using only field operations. -/
def evalCoefficients {F : Type} [Semiring F] {deg : ℕ} (a : Coefficients F deg) (r : F) : F :=
  ∑ j, a j * r ^ j.val
/-- Coefficient-vector evaluation agrees with evaluation of its bounded polynomial. -/
theorem evalCoefficients_eq_eval {F : Type} [Semiring F] {deg : ℕ}
    (a : Coefficients F deg) (p : Polynomial.degreeLE F deg)
    (coeff : ∀ j, a j = p.val.coeff j.val) (r : F) :
    evalCoefficients a r = p.val.eval r := by
  rw [p.val.eval_eq_sum_range' (n := deg + 1)
    (by have h := Polynomial.natDegree_le_of_degree_le
          (Polynomial.mem_degreeLE.mp p.property); omega)]
  simp only [evalCoefficients, coeff]
  exact (Finset.sum_range (fun i => p.val.coeff i * r ^ i)).symm
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
  classical
  let event := fun actual r => message ≠ actual ∧
    evalCoefficients message r = evalCoefficients actual r
  have per (actual : Coefficients F deg) (_ha : actual ∈ completed) :
      Pr{let r ←$ᵗ F}[event actual r] ≤ (deg : ENNReal) / Fintype.card F := by
    by_cases different : message = actual
    · exact (prEvent_eq_zero_of_forall_not ($ᵗ F) _
        (fun _ h => h.1 different)).le.trans zero_le
    · have ev (a : Coefficients F deg) (r : F) :
          (Polynomial.ofFn (deg + 1) a).eval r = evalCoefficients a r := by
        simp only [Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum,
          Polynomial.eval_monomial, evalCoefficients]
      exact (prEvent_mono ($ᵗ F) _ _ (fun r h => by simpa only [ev] using h.2)).trans
        (Probability.prob_polynomial_eval_eq_le
          (fun h => different (Polynomial.injective_ofFn _ h))
          (Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) message))
          (Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) actual)))
  refine (prEvent_mono ($ᵗ F) _ _
    (fun r bad => BadSummand.mono subset bad)).trans ?_
  change Pr{let r ←$ᵗ F}[∃ actual ∈ completed, event actual r] ≤ _
  clear subset masked
  induction completed with
  | nil =>
      simp only [List.not_mem_nil, false_and, exists_false, prEvent_false,
        List.length_nil, Nat.cast_zero, zero_mul]
      exact le_rfl
  | cons a rest ih =>
      simp only [List.mem_cons, exists_eq_or_imp]
      refine (prEvent_or_le _ _ _).trans ?_
      have hp := per a List.mem_cons_self
      have hr := ih (fun x hx => per x (List.mem_cons_of_mem _ hx))
      simpa only [List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul,
        add_comm] using add_le_add hp hr

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
  obtain ⟨falseClaim, accepted, r', same, good⟩ := badChallenge_implies_successor ops D
    model valid summand p binding count start finish stmt active q (some r) escape
  cases Option.some.inj same
  refine ⟨actual, List.mem_singleton_self _, ?_, ?_⟩
  · intro eq
    apply falseClaim
    apply (projected_sum_iff_closedRelation F n deg D ⟨start, by omega⟩ stmt p).mp
    have sameEval (x : F) :
        (Spec.SingleRound.projectedRoundPolynomial F n deg D ⟨start, by omega⟩
          stmt.challenges p).val.eval x = (model.interpret stmt.target q).val.eval x := by
      rw [← evalCoefficients_eq_eval actual _ actual_coeff,
        ← evalCoefficients_eq_eval message _ message_coeff, eq]
    simp only [sameEval]
    rw [Finset.sum_map_toList]
    exact (model.accept_iff _ _).mp accepted
  · rw [evalCoefficients_eq_eval message _ message_coeff,
      evalCoefficients_eq_eval actual _ actual_coeff]
    exact ((acceptedRun_closedRelation_iff F n deg D ⟨start, by omega⟩ stmt p
      (model.interpret stmt.target q) r).mp good).symm
end Sumcheck.Interaction.Knowledge
