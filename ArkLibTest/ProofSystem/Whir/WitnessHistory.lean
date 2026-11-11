/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
import ArkLib.ProofSystem.Whir.WitnessCertificate

/-! Final algebraic games retain all preceding query-availability guards. -/

open Interaction.Oracle.Security.StandardBcs

namespace Whir.WitnessHistoryTest

variable {E : Type} [Field E] [DecidableEq E] [Finite E] [SampleableType E]

/-- An inactive history is rejected even when the current final word reveals every query. -/
theorem inactive_final_rejected (n columns queries : ℕ)
    (pre : {pre : PlaintextPrefix E n columns queries // pre.publicData.residual.length = 1})
    (challenge : E) :
    (finalBatchSchema n columns queries).check (pre, false) challenge = false := rfl

/-- An inactive closing history is rejected independently of its polynomial root. -/
theorem inactive_closing_rejected (n columns queries count : ℕ)
    (input : ClosingInput E n columns queries count) (challenge : E) :
    (closingSchema n columns queries count).check { input with active := false } challenge =
      false := rfl

/-- Every final-batch bad event certifies that the earlier query history remained active. -/
theorem final_bad_active (n columns queries : ℕ)
    (input : (finalBatchSchema (E := E) n columns queries).Input) (challenge : E)
    (bad : (finalBatchSchema n columns queries).Bad input challenge) : input.2 = true :=
  bad.1

/-- Every closing bad event certifies the retained activity guard. -/
theorem closing_bad_active (n columns queries count : ℕ)
    (input : ClosingInput E n columns queries count) (challenge : E)
    (bad : (closingSchema n columns queries count).Bad input challenge) : input.active = true :=
  bad.1

end Whir.WitnessHistoryTest
