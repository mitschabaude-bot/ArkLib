/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.StateRestorationGame

/-!
# State-restoration knowledge soundness for oracle outputs

The verifier returns an optional open oracle claim. After actual execution, the relation
observes its closed behavior under that same path's accumulated input/message handler. The
verifier never receives concrete oracle realizations or that closing handler as authoring data.
Rejection remains unsuccessful. The resulting extraction bound applies to arbitrary output
relations on closed behavior, including virtual outputs with arbitrarily many possible queries.
-/

@[expose] public section

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec
open Interaction.Oracle.TypeTree

namespace Interaction.Oracle.Security.StateRestoration

universe w

variable {Input Salt W : Type} {protocol : Input → Protocol}

/-- The terminal program may reject or return an open claim over declared source access. -/
abbrev OracleOutput (initial : PFunctor)
    (Stmt : (z : Input) → (protocol z).tree.BranchPath → Type)
    {Idx : (z : Input) → (protocol z).tree.BranchPath → Type}
    {Realization : (z : Input) → (p : (protocol z).tree.BranchPath) → Idx z p → Type}
    (family : (z : Input) → (p : (protocol z).tree.BranchPath) →
      OracleFamily (Idx z p) (Realization z p))
    (z : Input) (p : (protocol z).tree.BranchPath) :=
  Option (OpenClaim
    (ofPFunctor (accessAfter (protocol z).tree (protocol z).oracles initial p))
    (Stmt z p) (family z p))

/-- Close the actual verifier's returned virtual output under that same run's handler.
Closing interprets the relation and grants no concrete payload access to verifier authoring. -/
noncomputable def closedVerificationGame (coin : (z : Input) → PublicCoin (protocol z))
    (initial : PFunctor)
    (impl : Input → QueryImpl (ofPFunctor initial) Id)
    (Stmt : (z : Input) → (protocol z).tree.BranchPath → Type)
    {Idx : (z : Input) → (protocol z).tree.BranchPath → Type}
    {Realization : (z : Input) → (p : (protocol z).tree.BranchPath) → Idx z p → Type}
    (family : (z : Input) → (p : (protocol z).tree.BranchPath) →
      OracleFamily (Idx z p) (Realization z p))
    (terminal : (z : Input) → (p : (protocol z).tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter (protocol z).tree
        (protocol z).oracles initial p)) (OracleOutput initial Stmt family z p))
    (adversary : OracleComp (oracleSpec Input Salt coin) (Selection Input Salt W coin)) :
    OracleComp (oracleSpec Input Salt coin)
      ((z : Input) × (path : (protocol z).tree.ExecutionPath) ×
        Option (ClosedClaim (Stmt z path.toBranchPath) (family z path.toBranchPath)) × W) :=
  (fun result => ⟨result.1, result.2.1,
    result.2.2.1.map (fun claim => claim.closeWith
      (result.2.1.closingImpl (protocol result.1).oracles initial (impl result.1))),
    result.2.2.2⟩) <$>
    verificationGame coin initial impl (OracleOutput initial Stmt family) terminal adversary

/-- Observe the output oracle behavior using the accumulated handler of the completed path. -/
def closedTerminalObservation (initial : PFunctor)
    (impl : Input → QueryImpl (ofPFunctor initial) Id)
    (Stmt : (z : Input) → (protocol z).tree.BranchPath → Type)
    {Idx : (z : Input) → (protocol z).tree.BranchPath → Type}
    {Realization : (z : Input) → (p : (protocol z).tree.BranchPath) → Idx z p → Type}
    (family : (z : Input) → (p : (protocol z).tree.BranchPath) →
      OracleFamily (Idx z p) (Realization z p))
    (terminal : (z : Input) → (p : (protocol z).tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter (protocol z).tree
        (protocol z).oracles initial p)) (OracleOutput initial Stmt family z p))
    (z : Input) (path : (protocol z).tree.ExecutionPath) :
    Option (ClosedClaim (Stmt z path.toBranchPath) (family z path.toBranchPath)) :=
  (terminalObservation initial impl (OracleOutput initial Stmt family) terminal z path).map
    (fun claim => claim.closeWith
      (path.closingImpl (protocol z).oracles initial (impl z)))

/-- Exact actual-execution equation, including the verifier's virtual output interpretation. -/
theorem closedVerificationGame_eq (coin : (z : Input) → PublicCoin (protocol z))
    (initial : PFunctor)
    (impl : Input → QueryImpl (ofPFunctor initial) Id)
    (Stmt : (z : Input) → (protocol z).tree.BranchPath → Type)
    {Idx : (z : Input) → (protocol z).tree.BranchPath → Type}
    {Realization : (z : Input) → (p : (protocol z).tree.BranchPath) → Idx z p → Type}
    (family : (z : Input) → (p : (protocol z).tree.BranchPath) →
      OracleFamily (Idx z p) (Realization z p))
    (terminal : (z : Input) → (p : (protocol z).tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter (protocol z).tree
        (protocol z).oracles initial p)) (OracleOutput initial Stmt family z p))
    (adversary : OracleComp (oracleSpec Input Salt coin) (Selection Input Salt W coin)) :
    closedVerificationGame coin initial impl Stmt family terminal adversary =
      (fun result => (⟨result.1, result.2.1,
        closedTerminalObservation initial impl Stmt family terminal result.1 result.2.1,
        result.2.2⟩ : (z : Input) × (path : (protocol z).tree.ExecutionPath) ×
          Option (ClosedClaim (Stmt z path.toBranchPath) (family z path.toBranchPath)) × W)) <$>
        restoredExecution coin adversary := by
  rw [closedVerificationGame, verificationGame_eq, Functor.map_map]
  rfl

/-- Round-by-round knowledge bounds imply state-restoration knowledge soundness for oracle
output relations, with error `Q * maxError errors + sumError errors` for an arbitrary adaptive
`Q`-query adversary. The relation sees the actual closed output behavior, never open query code or
unobserved concrete realizations. Rejection is never a valid output. The named terminal-witness
equivalence and exact input/output relation laws link the extractor to the actual source-only
terminal program. No finite input or salt domain is required. -/
theorem stateRestoration_oracle_knowledge_soundness
    [DecidableEq Input] [DecidableEq Salt] (coin : (z : Input) → PublicCoin (protocol z))
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol z).tree (state z))
    (Z : Set Input) (errors : (z : Input) → Errors (coin z))
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol z).roles)
    (bounded : ∀ z ∈ Z, RoundExtractor.IsLocallyBounded (extractor z) (protocol z).roles
      (errorSchedule (coin z) (errors z)))
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
      W ≃ ((extractor z).terminalState path).Witness)
    (inputLaw : ∀ z witness, (state z).holds witness ↔ Rin z witness)
    (outputLaw : ∀ z path witness,
      ((extractor z).terminalState path).holds (terminalWitness z path witness) ↔
        ∃ claim, closedTerminalObservation initial impl Stmt family terminal z path = some claim ∧
          Rout z path.toBranchPath claim witness)
    (adversary : OracleComp (oracleSpec Input Salt coin) (Selection Input Salt W coin))
    (Q : ℕ) (queryBound : IsTotalQueryBound adversary Q) :
    Pr{let result ← (simulateQ randomOracle
        (closedVerificationGame coin initial impl Stmt family terminal adversary)).run' ∅}[
      result.1 ∈ Z ∧
      (∃ claim, result.2.2.1 = some claim ∧
        Rout result.1 result.2.1.toBranchPath claim result.2.2.2) ∧
      ¬ Rin result.1 (extractInputWitness state extractor terminalWitness
        result.1 result.2.1 result.2.2.2)] ≤ Q * maxError errors + sumError errors := by
  rw [closedVerificationGame_eq, simulateQ_map]
  simp only [StateT.run'_map', prEvent_map]
  simp only [extractInputWitness, ← inputLaw, ← outputLaw]
  exact (prEvent_mono _ _ _ fun result h => ⟨h.1, _, h.2⟩).trans
    (restored_extraction_bound state extractor Z errors preserving bounded adversary Q queryBound)

/-- **State-restoration extraction from knowledge certificates.** If every input's certificate
samples its challenges uniformly, the restoration game, with any terminal program, completes a
path that has a valid terminal witness whose backward extraction fails with probability at most
`Q * maxError + sumError` of the certificates' node errors (`supErrors`), for an adversary making
at most `Q` queries. The terminal witness is any witness of the completed path. -/
theorem KnowledgeCertificate.stateRestoration_extraction_le
    [DecidableEq Input] [DecidableEq Salt] (coin : (z : Input) → PublicCoin (protocol z))
    (state : Input → KnowledgeState.{w})
    (certificate : (z : Input) → KnowledgeCertificate (protocol z).tree (protocol z).roles
      (state z))
    (uniform : ∀ z, UniformChallenges (coin z) (certificate z).challenges)
    (initial : PFunctor) (impl : Input → QueryImpl (ofPFunctor initial) Id)
    (Out : (z : Input) → (protocol z).tree.BranchPath → Type)
    (terminal : (z : Input) → (p : (protocol z).tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter (protocol z).tree
        (protocol z).oracles initial p)) (Out z p))
    (adversary : OracleComp (oracleSpec Input Salt coin) (Selection Input Salt W coin))
    (Q : ℕ) (queryBound : IsTotalQueryBound adversary Q) :
    Pr{let result ← (simulateQ randomOracle
        (verificationGame coin initial impl Out terminal adversary)).run' ∅}[
      ∃ witness, ((certificate result.1).extractor.terminalState result.2.1).holds witness ∧
        ¬ (state result.1).holds
          ((certificate result.1).extractor.extractWitness result.2.1 witness)] ≤
      Q * maxError (fun z => supErrors (coin z) (certificate z).challenges) +
        sumError (fun z => supErrors (coin z) (certificate z).challenges) := by
  rw [verificationGame_eq, simulateQ_map]
  simp only [StateT.run'_map', prEvent_map]
  exact (prEvent_mono _ _ _ fun result h => ⟨Set.mem_univ _, h⟩).trans
    (restored_extraction_bound state (fun z => (certificate z).extractor) Set.univ
      (fun z => supErrors (coin z) (certificate z).challenges)
      (fun z _ => (certificate z).prover_preserving)
      (fun z _ => isLocallyBounded_errorSchedule (coin z) _ _ (uniform z)
        (certificate z).local_bound _ fun _ => le_rfl) adversary Q queryBound)

/-- **State-restoration knowledge soundness of a public-coin protocol from its knowledge
certificates.** If every input's certificate samples its challenges uniformly, the closed oracle
game has knowledge error `Q * maxError + sumError` of the certificates' node errors: `Q` times
the largest error at any challenge node, plus the largest sum of errors along a path, where a
node's error is the certificate's largest error there over the erased earlier challenges. -/
theorem KnowledgeCertificate.stateRestoration_oracle_knowledge_soundness
    [DecidableEq Input] [DecidableEq Salt] (coin : (z : Input) → PublicCoin (protocol z))
    (state : Input → KnowledgeState.{w})
    (certificate : (z : Input) → KnowledgeCertificate (protocol z).tree (protocol z).roles (state
        z))
    (uniform : ∀ z, UniformChallenges (coin z) (certificate z).challenges)
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
      (∃ claim, result.2.2.1 = some claim ∧
        Rout result.1 result.2.1.toBranchPath claim result.2.2.2) ∧
      ¬ Rin result.1 (extractInputWitness state (fun z => (certificate z).extractor)
        terminalWitness result.1 result.2.1 result.2.2.2)] ≤
      Q * maxError (fun z => supErrors (coin z) (certificate z).challenges) +
        sumError (fun z => supErrors (coin z) (certificate z).challenges) := by
  have h := StateRestoration.stateRestoration_oracle_knowledge_soundness coin state
    (fun z => (certificate z).extractor) Set.univ
    (fun z => supErrors (coin z) (certificate z).challenges)
    (fun z _ => (certificate z).prover_preserving)
    (fun z _ => isLocallyBounded_errorSchedule (coin z) _ _ (uniform z) (certificate z).local_bound
      _ fun _ => le_rfl)
    initial impl Stmt family terminal Rin Rout terminalWitness inputLaw outputLaw adversary Q
    queryBound
  simpa only [Set.mem_univ, true_and] using h

end Interaction.Oracle.Security.StateRestoration
