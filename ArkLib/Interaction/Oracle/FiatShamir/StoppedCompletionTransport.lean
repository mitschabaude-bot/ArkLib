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

/-- Interpret a prefix of `rounds` as a key of an enclosing restoration oracle. -/
def embeddedQuery {Input : Type} {rounds : List Round} {allRounds : Input → List Round}
    (embed : Prefix PUnit rounds → Key Input PUnit allRounds)
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) :
    QueryImpl (prefixSpec PUnit rounds)
      (OracleComp (oracleSpec Input PUnit allRounds)) :=
  fun key => (cast (preserve key)) <$>
    liftM ((oracleSpec Input PUnit allRounds).query (embed key))

private theorem embeddedQuery_comp_prepend {Input : Type} {round : Round}
    {rounds : List Round} {allRounds : Input → List Round} (message : round.Message)
    (embed : Prefix PUnit (round :: rounds) → Key Input PUnit allRounds)
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) :
    (embeddedQuery embed preserve) ∘ₛ (prependQuery message PUnit.unit) =
      embeddedQuery (fun key => embed (Prefix.later message PUnit.unit key))
        (fun key => preserve (Prefix.later message PUnit.unit key)) := by
  funext key
  simp only [QueryImpl.apply_compose, prependQuery, simulateQ_query,
    OracleQuery.cont_query, OracleQuery.input_query, id_map, embeddedQuery]

set_option backward.isDefEq.respectTransparency false in
theorem mappedStoppedComplete_eq_simulate {Input : Type} {allRounds : Input → List Round}
    (rounds : List Round) (guards : GuardSchedule PUnit rounds)
    (messages : PublicMessages rounds)
    (embed : Prefix PUnit rounds → Key Input PUnit allRounds)
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) :
    mappedStoppedComplete rounds guards messages embed preserve =
      simulateQ (embeddedQuery embed preserve)
        (stoppedCompletePrefix rounds guards (withUnitSalts rounds messages)) := by
  induction rounds with
  | nil =>
      simp [mappedStoppedComplete, stoppedCompletePrefix, simulateQ_pure]
  | cons round rounds ih =>
      rcases guards with ⟨guard, next⟩
      rcases messages with ⟨message, messages⟩
      simp only [mappedStoppedComplete, stoppedCompletePrefix, withUnitSalts]
      cases hguard : guard message PUnit.unit with
      | false => simp [simulateQ_pure]
      | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ite_false,
            simulateQ_bind, simulateQ_pure, simulateQ_query,
            OracleQuery.cont_query, OracleQuery.input_query, id_map]
          simp only [embeddedQuery, bind_map_left, bind_pure_comp]
          apply bind_congr
          intro response
          rw [← QueryImpl.simulateQ_compose,
            embeddedQuery_comp_prepend message embed preserve]
          rw [← ih (next message PUnit.unit
            (cast (preserve (Prefix.here message PUnit.unit)) response)) messages
            (fun key => embed (Prefix.later message PUnit.unit key))
            (fun key => preserve (Prefix.later message PUnit.unit key))]

private theorem embeddedQuery_mk {Input : Type} (rounds : Input → List Round) (z : Input) :
    embeddedQuery (Input := Input) (allRounds := rounds) (fun pre => ⟨z, pre⟩) (fun _ => rfl) =
      inputQuery z := by
  funext pre
  change (cast (rfl : pre.Challenge = pre.Challenge)) <$>
    liftM ((oracleSpec Input PUnit rounds).query ⟨z, pre⟩) =
      liftM ((oracleSpec Input PUnit rounds).query ⟨z, pre⟩)
  have hcast : (cast (rfl : pre.Challenge = pre.Challenge)) =
      (id : pre.Challenge → pre.Challenge) := by
    funext x
    exact cast_eq _ x
  rw [hcast, id_map]

/-- Actual public strategy verification executes the native stopped completion, with the
same query order and stopping point, for the single-unit salt schedule. -/
theorem publicStoppedVerify_eq_stoppedComplete {Input : Type} (rounds : Input → List Round)
    (guards : (z : Input) → GuardSchedule PUnit (rounds z)) (z : Input)
    (messages : PublicMessages (rounds z)) :
    publicStoppedVerify rounds guards z messages =
      stoppedComplete rounds guards z (withUnitSalts (rounds z) messages) := by
  rw [publicStoppedVerify_eq_with, publicStoppedVerifyWith_eq_mapped,
    mappedStoppedComplete_eq_simulate, embeddedQuery_mk]
  rfl

end Interaction.Oracle.FiatShamir
