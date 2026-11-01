/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.FiatShamir.PublicStopped

/-! # Equation between the public native executor and stopped completion -/

@[expose] public section

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec

namespace Interaction.Oracle.FiatShamir

open Security.StateRestoration

set_option backward.isDefEq.respectTransparency false in
/-- The real public strategy executor is extensionally the guarded full-prefix completion. -/
theorem publicStoppedVerifyWith_eq_mapped {Input : Type} {allProtocol : Input → Protocol}
    {allCoin : (z : Input) → PublicCoin (allProtocol z)} {protocol : Protocol}
    (coin : PublicCoin protocol) (guards : GuardSchedule PUnit coin)
    (messages : Messages PUnit coin)
    (embed : Prefix PUnit coin → Key Input PUnit allCoin)
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) :
    publicStoppedVerifyWith coin guards messages embed preserve =
      mappedStoppedComplete coin guards messages embed preserve := by
  induction coin with
  | done =>
      unfold publicStoppedVerifyWith
      simp only [guardedPublicProtocol, Protocol.done_tree, Protocol.done_roles,
        Protocol.done_oracles]
      rw [executeStrategies_done]
      simp [mappedStoppedComplete, acceptedPath, scriptedPublicProver, guardedPublicVerifier]
  | sender next ih =>
      rcases messages with ⟨move, messages⟩
      rw [mappedStoppedComplete, ← ih]
      unfold publicStoppedVerifyWith
      simp only [guardedPublicProtocol, Protocol.public_tree, Protocol.public_roles,
        Protocol.public_oracles]
      rw [executeStrategies_public_sender]
      simp only [scriptedPublicProver, guardedPublicVerifier, acceptedPath, simulateQ_pure,
        pure_bind, bind_pure_comp, Functor.map_map]
  | oracle next ih =>
      rcases messages with ⟨message, messages⟩
      rw [mappedStoppedComplete, ← ih]
      unfold publicStoppedVerifyWith
      simp only [guardedPublicProtocol, Protocol.public_tree, Protocol.public_roles,
        Protocol.public_oracles]
      rw [executeStrategies_public_sender]
      simp only [scriptedPublicProver, guardedPublicVerifier, acceptedPath, simulateQ_pure,
        pure_bind, bind_pure_comp, Functor.map_map]
  | challenge next ih =>
      rcases messages with ⟨_, messages⟩
      unfold publicStoppedVerifyWith
      simp only [guardedPublicProtocol, scriptedPublicProver, guardedPublicVerifier, acceptedPath,
        mappedStoppedComplete]
      generalize guards.1 PUnit.unit = pass
      cases pass with
      | false => simp [guardedChallenge, decodeAfterGuard, executeStrategies_done]
      | true =>
          simp only [guardedChallenge, Protocol.public_tree, Protocol.public_roles,
            Protocol.public_oracles]
          rw [executeStrategies_public_receiver]
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
            OracleQuery.input_query, id_map, Verifier.liftAccessImpl_ambient,
            simulateQ_pure, pure_bind, bind_assoc, QueryImpl.id', Bool.not_true,
            Bool.false_eq_true, ite_false]
          simp only [map_bind, bind_pure_comp, Functor.map_map]
          apply bind_congr
          intro response
          rw [← ih]
          simp only [publicStoppedVerifyWith, Functor.map_map]
          rfl

end Interaction.Oracle.FiatShamir
