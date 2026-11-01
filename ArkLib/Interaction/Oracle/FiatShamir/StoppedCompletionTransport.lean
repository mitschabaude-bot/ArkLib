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
  sorry

/-- Actual public strategy verification executes the native stopped completion, with the
same query order and stopping point, for the single-unit salt schedule. -/
theorem publicStoppedVerify_eq_stoppedComplete {Input : Type} {protocol : Input → Protocol}
    (coin : (z : Input) → PublicCoin (protocol z))
    (guards : (z : Input) → GuardSchedule PUnit (coin z)) (z : Input)
    (messages : Messages PUnit (coin z)) :
    publicStoppedVerify coin guards z messages = stoppedComplete coin guards z messages := by
  sorry

end Interaction.Oracle.FiatShamir
