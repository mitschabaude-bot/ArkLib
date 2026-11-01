/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.FiatShamir.PublicExecutionCorrespondence

/-! # Transport of native stopped completion through full-prefix key embeddings -/

@[expose] public section

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec

namespace Interaction.Oracle.FiatShamir

open Security.StateRestoration

/-- Interpret a prefix of `coin` as a key of an enclosing restoration oracle. -/
def embeddedQuery {Input : Type} {allProtocol : Input → Protocol}
    {allCoin : (z : Input) → PublicCoin (allProtocol z)} {protocol : Protocol}
    {coin : PublicCoin protocol}
    (embed : Prefix PUnit coin → Key Input PUnit allCoin)
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) :
    QueryImpl (prefixSpec PUnit coin) (OracleComp (oracleSpec Input PUnit allCoin)) :=
  fun key => (cast (preserve key)) <$> liftM ((oracleSpec Input PUnit allCoin).query (embed key))

set_option backward.isDefEq.respectTransparency false in
theorem mappedStoppedComplete_eq_simulate {Input : Type} {allProtocol : Input → Protocol}
    {allCoin : (z : Input) → PublicCoin (allProtocol z)} {protocol : Protocol}
    (coin : PublicCoin protocol) (guards : GuardSchedule PUnit coin)
    (messages : Messages PUnit coin)
    (embed : Prefix PUnit coin → Key Input PUnit allCoin)
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) :
    mappedStoppedComplete coin guards messages embed preserve =
      simulateQ (embeddedQuery embed preserve) (stoppedCompletePrefix coin guards messages) := by
  induction coin with
  | done => simp [mappedStoppedComplete, stoppedCompletePrefix, simulateQ_pure]
  | sender next ih =>
      rcases messages with ⟨move, messages⟩
      have hcomp : (embeddedQuery embed preserve) ∘ₛ
          (reindexQuery (R := Prefix.Challenge (coin := .sender next)) (Sigma.mk move)) =
            embeddedQuery (fun key => embed ⟨move, key⟩) (fun key => preserve ⟨move, key⟩) := by
        funext key
        simp only [QueryImpl.apply_compose, reindexQuery, simulateQ_query,
          OracleQuery.cont_query, OracleQuery.input_query, id_map, embeddedQuery]
      simp only [mappedStoppedComplete, stoppedCompletePrefix, simulateQ_bind, simulateQ_pure]
      rw [← QueryImpl.simulateQ_compose, hcomp, ← ih]
  | oracle next ih =>
      rcases messages with ⟨message, messages⟩
      have hcomp : (embeddedQuery embed preserve) ∘ₛ
          (reindexQuery (R := Prefix.Challenge (coin := .oracle next)) (Prod.mk message)) =
            embeddedQuery (fun key => embed ⟨message, key⟩)
              (fun key => preserve ⟨message, key⟩) := by
        funext key
        simp only [QueryImpl.apply_compose, reindexQuery, simulateQ_query,
          OracleQuery.cont_query, OracleQuery.input_query, id_map, embeddedQuery]
      simp only [mappedStoppedComplete, stoppedCompletePrefix, simulateQ_bind, simulateQ_pure]
      rw [← QueryImpl.simulateQ_compose, hcomp, ← ih]
  | challenge next ih =>
      rcases messages with ⟨_, messages⟩
      have hcomp : (embeddedQuery embed preserve) ∘ₛ
          (reindexQuery (R := Prefix.Challenge (coin := .challenge next))
            (fun key : Prefix PUnit next => Sum.inr ⟨PUnit.unit, key⟩)) =
            embeddedQuery (fun key => embed (.inr ⟨PUnit.unit, key⟩))
              (fun key => preserve (.inr ⟨PUnit.unit, key⟩)) := by
        funext key
        simp only [QueryImpl.apply_compose, reindexQuery, simulateQ_query,
          OracleQuery.cont_query, OracleQuery.input_query, id_map, embeddedQuery]
      simp only [mappedStoppedComplete, stoppedCompletePrefix]
      cases hguard : guards.1 PUnit.unit with
      | false => simp [simulateQ_pure]
      | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ite_false,
            simulateQ_bind, simulateQ_pure, simulateQ_query,
            OracleQuery.cont_query, OracleQuery.input_query, id_map]
          simp only [embeddedQuery, bind_map_left, bind_pure_comp]
          apply bind_congr
          intro response
          rw [← QueryImpl.simulateQ_compose, hcomp, ← ih]

/-- Actual public strategy verification executes the native stopped completion, with the
same query order and stopping point, for the single-unit salt schedule. -/
theorem publicStoppedVerify_eq_stoppedComplete {Input : Type} {protocol : Input → Protocol}
    (coin : (z : Input) → PublicCoin (protocol z))
    (guards : (z : Input) → GuardSchedule PUnit (coin z)) (z : Input)
    (messages : Messages PUnit (coin z)) :
    publicStoppedVerify coin guards z messages = stoppedComplete coin guards z messages := by
  rw [publicStoppedVerify_eq_with, publicStoppedVerifyWith_eq_mapped,
    mappedStoppedComplete_eq_simulate, stoppedComplete]
  congr 1

end Interaction.Oracle.FiatShamir
