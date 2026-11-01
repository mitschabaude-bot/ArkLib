/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.StateRestorationBudget
public import ArkLib.Interaction.Oracle.Security.KnowledgeComposition
public import PolyFun.Interaction.TwoParty.Strategy

/-!
# Verifier replay for state restoration

A scripted prover sends the prover moves and oracle payloads of a path. The restricted verifier
runs declared challenge programs and a terminal program that can read only its accumulated input
and message access. The existing executor interprets that terminal program with the closing
handler of the same concrete execution path.

Path-based replay reads the challenges from the path itself, so it makes no additional oracle
queries and requires no global response table (`execute_pathReplay`). The ordinary
uniform-program verifier samples every challenge as the uniform error schedule
(`uniformVerifier_fresh`). This covers source-only terminal programs; arbitrary terminal ambient
effects are outside this supported presentation.
-/

@[expose] public section

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec
open Interaction.Oracle.TypeTree

namespace Interaction.Oracle.Security.StateRestoration

/-- Actual ambient challenge programs at the challenge nodes, each followed by its
public-response-dependent continuation. Oracle payloads are not available to them. This is
verifier authoring data; execution uses the existing interpreter. -/
@[reducible] def ChallengePrograms {ι : Type} (ambient : OracleSpec ι) {protocol : Protocol}
    (coin : PublicCoin protocol) : Type :=
  PublicCoin.rec (motive := fun _ _ => Type) PUnit
    (fun {Moves} _ _ _ programs => (move : Moves) → programs move)
    (fun _ programs => programs)
    (@fun Challenge _ _ _ _ _ programs => OracleComp ambient Challenge × (Challenge → programs))
    coin

/-- Forward ambient challenge queries into the ambient side of the restricted signature. -/
def ambientQueries {ι : Type} (ambient : OracleSpec ι) (access : PFunctor) :
    QueryImpl ambient (OracleComp (ambient + ofPFunctor access)) :=
  fun q => liftM ((ambient + ofPFunctor access).query (Sum.inl q))

/-- Forward source-only terminal queries into the accumulated input/message access. -/
def sourceQueries {ι : Type} (ambient : OracleSpec ι) (access : PFunctor) :
    QueryImpl (ofPFunctor access) (OracleComp (ambient + ofPFunctor access)) :=
  fun q => liftM ((ambient + ofPFunctor access).query (Sum.inr q))

/-- Restricted verifier: prover moves and oracle receives are pure; each public challenge is
the supplied ambient program. No concrete oracle payload is available to authoring. -/
def challengeFragment {ι : Type} (ambient : OracleSpec ι) : {protocol : Protocol} →
    (coin : PublicCoin protocol) → (initial : PFunctor) → ChallengePrograms ambient coin →
    Verifier.Fragment ambient protocol.tree protocol.roles protocol.oracles initial (fun _ => Unit)
  | _, .done, _, _ => ()
  | _, @PublicCoin.sender _ _ _ next, initial, programs =>
      fun move => pure (challengeFragment ambient (next move) initial (programs move))
  | _, @PublicCoin.oracle _ _ interface _ next, initial, programs =>
      pure (challengeFragment ambient next (Access.extend initial interface) programs)
  | _, @PublicCoin.challenge _ _ _ _ _ next, initial, programs => do
      let challenge ← simulateQ (ambientQueries ambient initial) programs.1
      pure ⟨challenge, challengeFragment ambient next initial (programs.2 challenge)⟩

/-- Complete the fragment with a deterministic source-only terminal program. It can
query accumulated inputs/messages; ambient randomness is confined to challenge programs. -/
def challengeVerifier {ι : Type} (ambient : OracleSpec ι) {protocol : Protocol}
    (coin : PublicCoin protocol) (initial : PFunctor) (programs : ChallengePrograms ambient coin)
    (Out : protocol.tree.BranchPath → Type)
    (terminal : (p : protocol.tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter protocol.tree protocol.oracles initial p)) (Out p)) :
    Verifier.Strategy ambient protocol.tree protocol.roles protocol.oracles initial Out :=
  Verifier.Fragment.mapOutput ambient (fun p _ =>
    simulateQ (sourceQueries ambient (accessAfter protocol.tree protocol.oracles initial p))
      (terminal p))
    (challengeFragment ambient coin initial programs)

/-- The prover sending the moves and oracle payloads of a path, whatever the challenges. -/
def pathProver {ι : Type} (ambient : OracleSpec ι) : {protocol : Protocol} →
    (coin : PublicCoin protocol) → protocol.tree.ExecutionPath →
    Prover.Strategy ambient protocol.tree protocol.roles (fun _ => Unit)
  | _, .done, _ => ()
  | _, @PublicCoin.sender _ _ _ next, path =>
      pure ⟨path.1, pathProver ambient (next path.1) path.2⟩
  | _, @PublicCoin.oracle _ _ _ _ next, path => pure ⟨path.1, pathProver ambient next path.2⟩
  | _, @PublicCoin.challenge _ _ _ _ _ next, path =>
      fun _ => pure (pathProver ambient next path.2)

/-- Programs returning arbitrary challenges, for the moves a replayed path does not take. -/
noncomputable def arbitraryPrograms {ι : Type} (ambient : OracleSpec ι) :
    {protocol : Protocol} → (coin : PublicCoin protocol) → ChallengePrograms ambient coin
  | _, .done => PUnit.unit
  | _, @PublicCoin.sender _ _ _ next => fun move => arbitraryPrograms ambient (next move)
  | _, @PublicCoin.oracle _ _ _ _ next => arbitraryPrograms ambient next
  | _, @PublicCoin.challenge _ _ _ _ _ next =>
      ⟨pure (Classical.arbitrary _), fun _ => arbitraryPrograms ambient next⟩

/-- Replay programs read the challenges of the path already obtained by completion. -/
noncomputable def pathPrograms {ι : Type} (ambient : OracleSpec ι) :
    {protocol : Protocol} → (coin : PublicCoin protocol) → protocol.tree.ExecutionPath →
    ChallengePrograms ambient coin
  | _, .done, _ => PUnit.unit
  | _, @PublicCoin.sender Moves decEq _ next, path => fun move =>
      @dite _ (path.1 = move) (decEq path.1 move)
        (fun h => h ▸ pathPrograms ambient (next path.1) path.2)
        (fun _ => arbitraryPrograms ambient (next move))
  | _, @PublicCoin.oracle _ _ _ _ next, path => pathPrograms ambient next path.2
  | _, @PublicCoin.challenge _ _ _ _ _ next, path =>
      ⟨pure path.1, fun _ => pathPrograms ambient next path.2⟩

/-- Ordinary fresh uniform challenge programs. -/
def uniformPrograms : {protocol : Protocol} → (coin : PublicCoin protocol) →
    ChallengePrograms unifSpec coin
  | _, .done => PUnit.unit
  | _, @PublicCoin.sender _ _ _ next => fun move => uniformPrograms (next move)
  | _, @PublicCoin.oracle _ _ _ _ next => uniformPrograms next
  | _, @PublicCoin.challenge Challenge _ _ _ _ next =>
      ⟨$ᵗ Challenge, fun _ => uniformPrograms next⟩

theorem simulate_ambientQueries {ι : Type} (ambient : OracleSpec ι) (access : PFunctor)
    (impl : QueryImpl (ofPFunctor access) Id) {α : Type} (program : OracleComp ambient α) :
    simulateQ (Verifier.liftAccessImpl ambient access impl)
      (simulateQ (ambientQueries ambient access) program) = program := by
  rw [← QueryImpl.simulateQ_compose]
  have h : QueryImpl.compose (Verifier.liftAccessImpl ambient access impl)
      (ambientQueries ambient access) = QueryImpl.id' ambient := by
    funext q
    simp [QueryImpl.compose, ambientQueries]
  rw [h, simulateQ_id']

theorem simulate_sourceQueries {ι : Type} (ambient : OracleSpec ι) (access : PFunctor)
    (impl : QueryImpl (ofPFunctor access) Id) {α : Type}
    (program : OracleComp (ofPFunctor access) α) :
    simulateQ (Verifier.liftAccessImpl ambient access impl)
      (simulateQ (sourceQueries ambient access) program) =
      pure (evalWithAnswerFn impl program) := by
  rw [← QueryImpl.simulateQ_compose]
  have h : QueryImpl.compose (Verifier.liftAccessImpl ambient access impl)
      (sourceQueries ambient access) = impl.liftTarget (OracleComp ambient) := by
    funext q
    simp [QueryImpl.compose, sourceQueries, QueryImpl.liftTarget]
    rfl
  rw [h, simulateQ_liftTarget]
  rfl

/-- The actual terminal observation uses exactly the run's accumulated closing handler. -/
theorem execute_sourceTerminal {ι : Type} (ambient : OracleSpec ι)
    {protocol : Protocol} (coin : PublicCoin protocol) (initial : PFunctor)
    (impl : QueryImpl (ofPFunctor initial) Id) (programs : ChallengePrograms ambient coin)
    (OutP : protocol.tree.ExecutionPath → Type)
    (prover : Prover.Strategy ambient protocol.tree protocol.roles OutP)
    (Out : protocol.tree.BranchPath → Type)
    (terminal : (p : protocol.tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter protocol.tree
        protocol.oracles initial p)) (Out p)) :
    executeStrategies ambient protocol.tree protocol.roles
      protocol.oracles initial impl prover
      (challengeVerifier ambient coin initial programs Out terminal) =
    (fun result => let path := ExecutionPath.ofTypeTreePath result.1
      ⟨path, result.2.1, evalWithAnswerFn
        (path.closingImpl protocol.oracles initial impl)
        (terminal path.toBranchPath)⟩) <$>
      TwoParty.run protocol.tree.toTypeTree
        (RoleDecoration.toTypeTreeRoles protocol.tree protocol.roles)
        prover (Verifier.toCounterpartValue ambient protocol.tree protocol.roles
          protocol.oracles initial impl (fun _ => Unit)
          (challengeFragment ambient coin initial programs)) := by
  have interpreted : Verifier.toCounterpart ambient protocol.tree protocol.roles
      protocol.oracles initial impl Out
      (challengeVerifier ambient coin initial programs Out terminal) =
    StrategyOver.TwoParty.Counterpart.mapOutput (fun path _ =>
      pure (evalWithAnswerFn ((ExecutionPath.ofTypeTreePath path).closingImpl
        protocol.oracles initial impl)
        (terminal (ExecutionPath.ofTypeTreePath path).toBranchPath)))
      (Verifier.toCounterpartValue ambient protocol.tree protocol.roles
        protocol.oracles initial impl (fun _ => Unit)
        (challengeFragment ambient coin initial programs)) := by
    unfold Verifier.toCounterpart challengeVerifier
    rw [Verifier.toCounterpartWith_mapOutput]
    simp only [simulate_sourceQueries]
    exact Verifier.toCounterpartWith_finish_eq_mapOutput ambient protocol.tree
      protocol.roles protocol.oracles initial impl (fun _ => Unit)
      (fun p => OracleComp ambient (Out p))
      (fun path actual _ => pure (evalWithAnswerFn actual (terminal path)))
      (challengeFragment ambient coin initial programs)
  rw [executeStrategies_eq_run, interpreted, run_counterpart_mapOutput]
  simp only [map_eq_pure_bind, bind_assoc]
  apply bind_congr
  intro result
  rfl

/-- Exact path-based replay in the actual executor. The real game has only this completed
path; its verifier never inspects a global response table or makes additional oracle queries. -/
theorem execute_pathReplay {ι : Type} (ambient : OracleSpec ι) {protocol : Protocol}
    (coin : PublicCoin protocol) (initial : PFunctor)
    (impl : QueryImpl (ofPFunctor initial) Id) (path : protocol.tree.ExecutionPath)
    (Out : protocol.tree.BranchPath → Type)
    (terminal : (p : protocol.tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter protocol.tree protocol.oracles initial p)) (Out p)) :
    executeStrategies ambient protocol.tree protocol.roles protocol.oracles initial impl
      (pathProver ambient coin path)
      (challengeVerifier ambient coin initial (pathPrograms ambient coin path) Out terminal) =
    pure ⟨path, (), evalWithAnswerFn (path.closingImpl protocol.oracles initial impl)
      (terminal path.toBranchPath)⟩ := by
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- The ordinary verifier actually samples every challenge according to the uniform error
schedule, for all authored prover moves and oracle messages and every supported continuation. -/
theorem uniformFragment_fresh {protocol : Protocol} (coin : PublicCoin protocol)
    (errors : Errors coin) (initial : PFunctor) (impl : QueryImpl (ofPFunctor initial) Id) :
    SamplesChallenges unifSpec (QueryImpl.id' unifSpec) protocol.tree protocol.roles
      protocol.oracles initial impl (fun _ => Unit)
      (challengeFragment unifSpec coin initial (uniformPrograms coin))
      (errorSchedule coin errors) := by
  sorry

/-- Source-only terminal authoring preserves actual uniform challenge freshness. -/
theorem uniformVerifier_fresh {protocol : Protocol} (coin : PublicCoin protocol)
    (errors : Errors coin) (initial : PFunctor) (impl : QueryImpl (ofPFunctor initial) Id)
    (Out : protocol.tree.BranchPath → Type)
    (terminal : (p : protocol.tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter protocol.tree protocol.oracles initial p)) (Out p)) :
    SamplesChallenges unifSpec (QueryImpl.id' unifSpec) protocol.tree protocol.roles
      protocol.oracles initial impl _
      (challengeVerifier unifSpec coin initial (uniformPrograms coin) Out terminal)
      (errorSchedule coin errors) := by
  unfold challengeVerifier
  exact samplesChallenges_mapOutput _ _ _ _ _ _ _ _ _ _ _ _
    (uniformFragment_fresh coin errors initial impl)

end Interaction.Oracle.Security.StateRestoration
