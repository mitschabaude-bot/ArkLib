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
the supplied ambient program, and the leaf runs a deterministic source-only terminal program. No
concrete oracle payload is available to authoring; ambient randomness is confined to challenge
programs. -/
def challengeVerifier {ι : Type} (ambient : OracleSpec ι) : {protocol : Protocol} →
    (coin : PublicCoin protocol) → (initial : PFunctor) → ChallengePrograms ambient coin →
    (Out : protocol.tree.BranchPath → Type) →
    (terminal : (p : protocol.tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter protocol.tree protocol.oracles initial p)) (Out p)) →
    Verifier.Strategy ambient protocol.tree protocol.roles protocol.oracles initial Out
  | _, .done, initial, _, _, terminal =>
      simulateQ (sourceQueries ambient initial) (terminal PUnit.unit)
  | _, @PublicCoin.sender _ _ _ next, initial, programs, Out, terminal => fun move =>
      pure (challengeVerifier ambient (next move) initial (programs move)
        (fun p => Out ⟨move, p⟩) fun p => terminal ⟨move, p⟩)
  | _, @PublicCoin.oracle _ _ interface _ next, initial, programs, Out, terminal =>
      pure (challengeVerifier ambient next (Access.extend initial interface) programs
        (fun p => Out ⟨PUnit.unit, p⟩) fun p => terminal ⟨PUnit.unit, p⟩)
  | _, @PublicCoin.challenge _ _ _ _ _ next, initial, programs, Out, terminal => do
      let challenge ← simulateQ (ambientQueries ambient initial) programs.1
      pure ⟨challenge, challengeVerifier ambient next initial (programs.2 challenge)
        (fun p => Out ⟨challenge, p⟩) fun p => terminal ⟨challenge, p⟩⟩

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
  induction coin generalizing initial with
  | done =>
      refine (executeStrategies_done ambient initial impl _ _).trans ?_
      have h := simulate_sourceQueries ambient initial impl (terminal PUnit.unit)
      simp only [challengeVerifier]
      erw [h, pure_bind]
      rfl
  | @sender Moves _ rest next ih =>
      refine (executeStrategies_public_sender ambient (rest := fun move => (rest move).tree)
        (fun move => (rest move).roles) _ initial impl _ _).trans ?_
      simp only [pathProver, pure_bind, challengeVerifier, pathPrograms, ↓reduceDIte]
      have h := ih path.1 initial impl path.2 (fun p => Out ⟨path.1, p⟩)
        (fun p => terminal ⟨path.1, p⟩)
      erw [simulateQ_pure, pure_bind, h, pure_bind]
      rfl
  | @oracle Messages _ interface rest next ih =>
      refine (executeStrategies_oracle ambient (rest := fun _ => rest.tree) _ _ initial impl _ _).trans
        ?_
      simp only [pathProver, challengeVerifier, pathPrograms]
      have h := ih (Access.extend initial interface)
        (Access.extendImpl initial interface impl path.1) path.2 (fun p => Out ⟨PUnit.unit, p⟩)
        (fun p => terminal ⟨PUnit.unit, p⟩)
      erw [pure_bind, simulateQ_pure, pure_bind, h, pure_bind]
      rfl
  | @challenge Challenge _ _ _ rest next ih =>
      refine (executeStrategies_public_receiver ambient (rest := fun _ => rest.tree)
        (fun _ => rest.roles) _ initial impl _ _).trans ?_
      simp only [pathProver, challengeVerifier, pathPrograms]
      have h := ih initial impl path.2 (fun p => Out ⟨path.1, p⟩) (fun p => terminal ⟨path.1, p⟩)
      erw [pure_bind, pure_bind, h, pure_bind]
      rfl

/-- The ordinary uniform-program verifier samples every challenge according to the uniform error
schedule, for all authored prover moves and oracle messages and every supported continuation. -/
theorem uniformVerifier_fresh {protocol : Protocol} (coin : PublicCoin protocol)
    (errors : Errors coin) (initial : PFunctor) (impl : QueryImpl (ofPFunctor initial) Id)
    (Out : protocol.tree.BranchPath → Type)
    (terminal : (p : protocol.tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter protocol.tree protocol.oracles initial p)) (Out p)) :
    SamplesChallenges unifSpec (QueryImpl.id' unifSpec) protocol.tree protocol.roles
      protocol.oracles initial impl _
      (challengeVerifier unifSpec coin initial (uniformPrograms coin) Out terminal)
      (errorSchedule coin errors) := by
  induction coin generalizing initial with
  | done => trivial
  | sender next ih =>
      intro move after supported
      rw [simulateQ_id'] at supported
      simp only [challengeVerifier] at supported
      have same := OracleComp.eq_of_mem_support_pure _ supported
      subst after
      exact ih move _ _ _ _ _
  | oracle next ih =>
      intro message after supported
      rw [simulateQ_id'] at supported
      simp only [challengeVerifier] at supported
      have same := OracleComp.eq_of_mem_support_pure _ supported
      subst after
      exact ih _ _ _ _ _
  | challenge next ih =>
      simp only [challengeVerifier, uniformPrograms, errorSchedule, ← map_eq_pure_bind]
      constructor
      · intro event
        erw [simulateQ_id', simulateQ_map, simulate_ambientQueries, prEvent_map]
      · intro chosen supported
        erw [simulateQ_id', simulateQ_map, simulate_ambientQueries] at supported
        obtain ⟨challenge, _, rfl⟩ := OracleComp.mem_support_map_peel _ _ supported
        exact ih _ _ _ _ _

end Interaction.Oracle.Security.StateRestoration
