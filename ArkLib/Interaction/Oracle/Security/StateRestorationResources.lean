/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.KnowledgeResources
public import ArkLib.Interaction.Oracle.Security.StateRestorationOracle

/-!
# State restoration with measured knowledge certificates

`MeasuredKnowledgeCertificate.stateRestoration_oracle_knowledge_soundness` packages the
closed-oracle knowledge bound `Q * max_j error_j + sum_j error_j` with a uniform stage budget for
the same certificate's named extractor. The certificate's challenge schedule must equal the
error schedule, and its stage budgets must satisfy the stated bound on the selected inputs.

The scope caveats in `KnowledgeResources` still apply: every map has a zero-budget
`OracleComp.BudgetedProgram.ofFun`, so only a named program with a stated instruction set is
evidence. Stage budgets charge only those instructions, not views, handlers, witness
identifications, stage composition, or knowledge predicates.
-/

@[expose] public section

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec
open Interaction.Oracle.TypeTree
open Interaction.Oracle.Security.StateRestoration

namespace Interaction.Oracle.Security

/-- The actual closed-oracle game has knowledge error at most `Q * max + sum`, together with the
uniform stage budget of the same measured certificate's named extractor. Budgets count declared
stage instructions under the accounting of `OracleComp.MeasuredProgram`. -/
theorem MeasuredKnowledgeCertificate.stateRestoration_oracle_knowledge_soundness
    {ω Input Salt : Type} [AddCommMonoid ω] [Preorder ω] {protocol : Input → Protocol} {W : Type}
    [DecidableEq Input] [DecidableEq Salt] (coin : (z : Input) → PublicCoin (protocol z))
    (state : Input → KnowledgeState.{0})
    (certificate : (z : Input) →
      MeasuredKnowledgeCertificate ω (protocol z).tree (protocol z).roles (state z))
    (Z : Set Input) (errors : (z : Input) → Errors (coin z))
    (schedule : ∀ z ∈ Z, (certificate z).challenges = errorSchedule (coin z) (errors z))
    (bound : ω) (hbudget : ∀ z ∈ Z, (certificate z).stages.BudgetAtMost bound)
    (initial : PFunctor) (impl : Input → QueryImpl (ofPFunctor initial) Id)
    (Stmt : (z : Input) → (protocol z).tree.BranchPath → Type)
    {Idx : (z : Input) → (protocol z).tree.BranchPath → Type}
    {Realization : (z : Input) → (p : (protocol z).tree.BranchPath) → Idx z p → Type}
    (family : (z : Input) → (p : (protocol z).tree.BranchPath) →
      OracleFamily (Idx z p) (Realization z p))
    (terminal : (z : Input) → (p : (protocol z).tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter (protocol z).tree
        (protocol z).oracles initial p)) (OracleOutput initial Stmt family z p))
    (Rin : (z : Input) → (state z).Witness → Prop)
    (Rout : (z : Input) → (p : (protocol z).tree.BranchPath) →
      ClosedClaim (Stmt z p) (family z p) → W → Prop)
    (terminalWitness : (z : Input) → (path : (protocol z).tree.ExecutionPath) →
      W ≃ (((certificate z).extractor).terminalState path).Witness)
    (inputLaw : ∀ z witness, (state z).holds witness ↔ Rin z witness)
    (outputLaw : ∀ z path witness,
      (((certificate z).extractor).terminalState path).holds (terminalWitness z path witness) ↔
        ∃ claim, closedTerminalObservation initial impl Stmt family terminal z path = some claim ∧
          Rout z path.toBranchPath claim witness)
    (adversary : OracleComp (oracleSpec Input Salt coin) (Selection Input Salt W coin))
    (Q : ℕ) (queryBound : IsTotalQueryBound adversary Q) :
    Pr{let result ← (simulateQ randomOracle
        (closedVerificationGame coin initial impl Stmt family terminal adversary)).run' ∅}[
      result.1 ∈ Z ∧
      (∃ claim, result.2.2.1 = some claim ∧
        Rout result.1 result.2.1.toBranchPath claim result.2.2.2) ∧
      ¬ Rin result.1 (extractInputWitness state (fun z => (certificate z).extractor) terminalWitness
        result.1 result.2.1 result.2.2.2)] ≤ Q * maxError errors + sumError errors ∧
      ∀ z ∈ Z, (certificate z).stages.BudgetAtMost bound := by
  refine ⟨?_, hbudget⟩
  exact StateRestoration.stateRestoration_oracle_knowledge_soundness coin state
    (fun z => (certificate z).extractor) Z errors
    (fun z _ => (certificate z).prover_preserving)
    (fun z hz => by rw [← schedule z hz]; exact (certificate z).local_bound)
    initial impl Stmt family terminal Rin Rout terminalWitness inputLaw outputLaw
    adversary Q queryBound

end Interaction.Oracle.Security
