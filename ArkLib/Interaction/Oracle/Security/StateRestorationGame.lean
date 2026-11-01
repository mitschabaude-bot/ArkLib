/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.StateRestorationReplay

/-!
# State-restoration knowledge soundness

The actual restoration game lets an adversary choose the input, all messages and salts, and an
output witness after adaptive cached-oracle queries. Completion uses the same oracle. The
verifier then runs on those completed challenges and queries its actual accumulated source access.
Its execution equation is proved from the runner, without a table available to the game.

The principal theorem converts all-authored-prefix round-by-round knowledge errors into the
relation-level `Q * maxError errors + sumError errors` bound. A named terminal witness
equivalence and endpoint iff laws identify the supplied output witness and the extracted input
witness. Extraction cost and private random coins are separate statements; the adversary here is
a total oracle program.
-/

@[expose] public section

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec
open Interaction.Oracle.TypeTree

namespace Interaction.Oracle.Security.StateRestoration

universe w

variable {Input Salt W : Type} {protocol : Input → Protocol}

/-- The verifier's actual terminal observation of the closed input and oracle messages. -/
def terminalObservation (initial : PFunctor)
    (impl : Input → QueryImpl (ofPFunctor initial) Id)
    (Out : (z : Input) → (protocol z).tree.BranchPath → Type)
    (terminal : (z : Input) → (p : (protocol z).tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter (protocol z).tree
        (protocol z).oracles initial p)) (Out z p))
    (z : Input) (path : (protocol z).tree.ExecutionPath) : Out z path.toBranchPath :=
  evalWithAnswerFn (path.closingImpl (protocol z).oracles initial (impl z))
    (terminal z path.toBranchPath)

/-- The actual restoration game: complete with the same oracle, then execute the
prover/verifier on the completed challenges. Replay sees only the completed path, not a table. -/
noncomputable def verificationGame (coin : (z : Input) → PublicCoin (protocol z)) (initial :
    PFunctor)
    (impl : Input → QueryImpl (ofPFunctor initial) Id)
    (Out : (z : Input) → (protocol z).tree.BranchPath → Type)
    (terminal : (z : Input) → (p : (protocol z).tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter (protocol z).tree
        (protocol z).oracles initial p)) (Out z p))
    (adversary : OracleComp (oracleSpec Input Salt coin) (Selection Input Salt W coin)) :
    OracleComp (oracleSpec Input Salt coin)
      ((z : Input) × (path : (protocol z).tree.ExecutionPath) ×
        Out z path.toBranchPath × W) := do
  let ⟨z, messages, witness⟩ ← adversary
  let path ← complete coin z messages
  let result ← executeStrategies (oracleSpec Input Salt coin) (protocol z).tree
    (protocol z).roles (protocol z).oracles initial (impl z)
    (pathProver (oracleSpec Input Salt coin) (coin z) path)
    (challengeVerifier (oracleSpec Input Salt coin) (coin z) initial
      (pathPrograms (oracleSpec Input Salt coin) (coin z) path) (Out z) (terminal z))
  pure ⟨z, result.1, result.2.2, witness⟩

/-- Actual verification is exactly the observation of the completed path. -/
theorem verificationGame_eq (coin : (z : Input) → PublicCoin (protocol z)) (initial : PFunctor)
    (impl : Input → QueryImpl (ofPFunctor initial) Id)
    (Out : (z : Input) → (protocol z).tree.BranchPath → Type)
    (terminal : (z : Input) → (p : (protocol z).tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter (protocol z).tree
        (protocol z).oracles initial p)) (Out z p))
    (adversary : OracleComp (oracleSpec Input Salt coin) (Selection Input Salt W coin)) :
    verificationGame coin initial impl Out terminal adversary =
      (fun result => (⟨result.1, result.2.1,
        terminalObservation initial impl Out terminal result.1 result.2.1, result.2.2⟩ :
        (z : Input) × (path : (protocol z).tree.ExecutionPath) ×
          Out z path.toBranchPath × W)) <$>
      restoredExecution coin adversary := by
  simp only [verificationGame, restoredExecution, map_eq_pure_bind, bind_assoc]
  apply bind_congr
  rintro ⟨z, messages, witness⟩
  apply bind_congr
  intro path
  rw [execute_pathReplay]
  rfl

/-- The supplied output witness is transported by a named equivalence and extracted backwards
through the actual completed path. No valid intermediate witness is selected. -/
def extractInputWitness (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol z).tree (state z))
    (terminalWitness : (z : Input) → (path : (protocol z).tree.ExecutionPath) →
      W ≃ ((extractor z).terminalState path).Witness)
    (z : Input) (path : (protocol z).tree.ExecutionPath) (witness : W) :
    (state z).Witness :=
  (extractor z).extractWitness path (terminalWitness z path witness)

/-- Round-by-round knowledge bounds imply state-restoration knowledge soundness for the actual
verifier. The adversary chooses the input adaptively and supplies the terminal witness;
the named backwards extractor fails on a valid output with probability at most
`Q * maxError errors + sumError errors`. -/
theorem stateRestoration_knowledge_soundness
    [DecidableEq Input] [DecidableEq Salt] (coin : (z : Input) → PublicCoin (protocol z))
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol z).tree (state z))
    (Z : Set Input) (errors : (z : Input) → Errors (coin z))
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol z).roles)
    (bounded : ∀ z ∈ Z, RoundExtractor.IsLocallyBounded (extractor z) (protocol z).roles
      (errorSchedule (coin z) (errors z)))
    (initial : PFunctor) (impl : Input → QueryImpl (ofPFunctor initial) Id)
    (Out : (z : Input) → (protocol z).tree.BranchPath → Type)
    (terminal : (z : Input) → (p : (protocol z).tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter (protocol z).tree
        (protocol z).oracles initial p)) (Out z p))
    (Rin : (z : Input) → (state z).Witness → Prop)
    (Rout : (z : Input) → (p : (protocol z).tree.BranchPath) → Out z p → W → Prop)
    (terminalWitness : (z : Input) → (path : (protocol z).tree.ExecutionPath) →
      W ≃ ((extractor z).terminalState path).Witness)
    (inputLaw : ∀ z witness, (state z).holds witness ↔ Rin z witness)
    (outputLaw : ∀ z path witness,
      ((extractor z).terminalState path).holds (terminalWitness z path witness) ↔
        Rout z path.toBranchPath (terminalObservation initial impl Out terminal z path) witness)
    (adversary : OracleComp (oracleSpec Input Salt coin) (Selection Input Salt W coin))
    (Q : ℕ) (queryBound : IsTotalQueryBound adversary Q) :
    Pr{let result ← (simulateQ randomOracle
        (verificationGame coin initial impl Out terminal adversary)).run' ∅}[
      result.1 ∈ Z ∧ Rout result.1 result.2.1.toBranchPath result.2.2.1 result.2.2.2 ∧
      ¬ Rin result.1 (extractInputWitness state extractor terminalWitness
        result.1 result.2.1 result.2.2.2)] ≤ Q * maxError errors + sumError errors := by
  rw [verificationGame_eq, simulateQ_map]
  simp only [StateT.run'_map', prEvent_map]
  simp only [extractInputWitness, ← inputLaw, ← outputLaw]
  exact (prEvent_mono _ _ _ fun result h => ⟨h.1, _, h.2⟩).trans
    (restored_extraction_bound state extractor Z errors preserving bounded adversary Q queryBound)

end Interaction.Oracle.Security.StateRestoration
