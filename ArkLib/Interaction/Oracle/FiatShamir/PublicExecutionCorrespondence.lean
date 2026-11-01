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
  sorry

end Interaction.Oracle.FiatShamir
