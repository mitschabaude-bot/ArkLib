/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.Interaction.Oracle.Security.KnowledgeComposition
public import ArkLib.Interaction.Oracle.Security.Soundness

/-!
# Round-by-round knowledge bounds actual extraction failure

A knowledge certificate whose fresh challenge programs are the actual verifier's
(`SamplesChallenges`) bounds the probability, over the actual interpreted execution, that a known
terminal witness extracts to an unknown input witness: by the largest sum of local errors along
a path of its challenge schedule (`ChallengeSchedule.maxError`). Each such path has a bad
verifier challenge (`extraction_failure_implies_bad_challenge`), and each challenge is bad with
probability at most its local error, whatever happened before it.

The prover is an arbitrary strategy, including probabilistic private continuations and
interpreted effects that fail to return; the ambient interpreter loses mass on failure.
-/

@[expose] public section

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec
open Interaction.Oracle.TypeTree
open scoped ENNReal

namespace Interaction.Oracle.Security

universe v w

namespace RoundExtractor

/-- The largest sum of local errors along a path of a challenge schedule. -/
noncomputable def ChallengeSchedule.maxError :
    {tree : Oracle.TypeTree.{0}} → (roles : tree.RoleDecoration) →
      ChallengeSchedule tree roles → ℝ≥0∞
  | .done, _, _ => 0
  | .public _ next, ⟨.sender, roles⟩, schedule =>
      ⨆ move, ChallengeSchedule.maxError (tree := next move) (roles move) (schedule.2 move)
  | .public _ next, ⟨.receiver, roles⟩, schedule =>
      schedule.1.2 +
        ⨆ move, ChallengeSchedule.maxError (tree := next move) (roles move) (schedule.2 move)
  | .oracle _ next, roles, schedule =>
      ⨆ message, ChallengeSchedule.maxError (tree := next PUnit.unit) (roles.2 PUnit.unit)
        (schedule message)

end RoundExtractor

open RoundExtractor

set_option backward.isDefEq.respectTransparency false in
/-- The actual interpreted execution reaches a bad verifier challenge, under the witness
extracted from its suffix, with probability at most the schedule's largest path error. -/
theorem executeStrategies_badChallenge_le {ι : Type} (ambient : OracleSpec ι)
    {m : Type → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] [MonadAttach m] [WeaklyLawfulMonadAttach m]
    (handler : QueryImpl ambient m) :
    (tree : Oracle.TypeTree.{0}) → (roles : tree.RoleDecoration) →
    (oracles : tree.OracleDecoration) → (initial : PFunctor) →
    (impl : QueryImpl (ofPFunctor initial) Id) → {state : KnowledgeState.{w}} →
    (extractor : RoundExtractor tree state) →
    (schedule : RoundExtractor.ChallengeSchedule tree roles) →
    extractor.IsLocallyBounded roles schedule →
    {OutP : tree.ExecutionPath → Type} → {OutV : tree.BranchPath → Type} →
    (prover : Prover.Strategy ambient tree roles OutP) →
    (verifier : Verifier.Strategy ambient tree roles oracles initial OutV) →
    SamplesChallenges ambient handler tree roles oracles initial impl _ verifier schedule →
    Pr{let result ← (simulateQ handler
      (executeStrategies ambient tree roles oracles initial impl prover verifier))}[
      ∃ witness, extractor.BadChallengeOnPath roles result.1 witness] ≤
      schedule.maxError roles := by
  intro tree
  induction tree with
  | done =>
    intro roles oracles initial impl state extractor schedule _ OutP OutV prover verifier _
    simp only [BadChallengeOnPath, exists_false, prEvent_false, zero_le]
  | «public» Moves rest ih =>
    intro roles oracles initial impl state extractor schedule bounded OutP OutV prover verifier
      fresh
    rcases roles with ⟨role, roles⟩
    cases role with
    | sender =>
      rw [executeStrategies_public_sender]
      simp only [simulateQ_bind, simulateQ_pure]
      apply prEvent_bind_le_of_forall_le_of_support
      intro chosen _
      apply prEvent_bind_le_of_forall_le_of_support
      intro next hnext
      have bound := ih chosen.1 (roles chosen.1) (oracles.2 chosen.1) initial impl
        (extractor chosen.1).2.2 (schedule.2 chosen.1) (bounded chosen.1)
        (OutP := fun path => OutP ⟨chosen.1, path⟩)
        (OutV := fun path => OutV ⟨chosen.1, path⟩) chosen.2 next (fresh chosen.1 next hnext)
      refine le_trans ?_ (bound.trans (le_iSup (fun move => ChallengeSchedule.maxError
        (tree := rest move) (roles move) (schedule.2 move)) chosen.1))
      simp only [prEvent_norm]
      refine prEvent_mono _ _ _ fun result h => ?_
      obtain ⟨witness, hbad⟩ := h
      rcases hbad with ⟨hrole, -⟩ | hbad
      · cases hrole
      · exact ⟨witness, hbad⟩
    | receiver =>
      rw [executeStrategies_public_receiver]
      simp only [simulateQ_bind, simulateQ_pure]
      let action := simulateQ handler
        (simulateQ (Verifier.liftAccessImpl ambient initial impl) verifier)
      have hstep : Pr{let chosen ← action}[extractor.badChallenge chosen.1] ≤ schedule.1.2 := by
        rw [fresh.1 extractor.badChallenge]
        exact ((_root_.RoundByRound.GameFamily.isBounded_iff _ _).mp bounded.1) () ()
      have htail := prEvent_bind_le_prEvent_add_of_support action
        (fun chosen => do
          let next ← simulateQ handler (prover chosen.1)
          let result ← simulateQ handler (executeStrategies ambient (rest chosen.1)
            (roles chosen.1) (oracles.2 chosen.1) initial impl
            (OutP := fun path => OutP ⟨chosen.1, path⟩)
            (OutV := fun path => OutV ⟨chosen.1, path⟩) next chosen.2)
          return (⟨⟨chosen.1, result.1⟩, result.2.1, result.2.2⟩ :
            (path : (TypeTree.public Moves rest).ExecutionPath) ×
              OutP path × OutV path.toBranchPath))
        (fun chosen => extractor.badChallenge chosen.1)
        (fun result => ∃ witness, extractor.BadChallengeOnPath ⟨.receiver, roles⟩ result.1
          witness)
        (ε := ⨆ move, ChallengeSchedule.maxError (tree := rest move) (roles move)
          (schedule.2 move))
        (by
          intro chosen hchosen hgood
          apply prEvent_bind_le_of_forall_le_of_support
          intro next _
          have bound := ih chosen.1 (roles chosen.1) (oracles.2 chosen.1) initial impl
            (extractor chosen.1).2.2 (schedule.2 chosen.1) (bounded.2 chosen.1)
            (OutP := fun path => OutP ⟨chosen.1, path⟩)
            (OutV := fun path => OutV ⟨chosen.1, path⟩) next chosen.2
            (fresh.2 chosen hchosen)
          refine le_trans ?_ (bound.trans (le_iSup (fun move => ChallengeSchedule.maxError
            (tree := rest move) (roles move) (schedule.2 move)) chosen.1))
          simp only [prEvent_norm]
          refine prEvent_mono _ _ _ fun result h => ?_
          obtain ⟨witness, hbad⟩ := h
          rcases hbad with ⟨-, hnot, hafter⟩ | hbad
          · exact (hgood ⟨_, hnot, hafter⟩).elim
          · exact ⟨witness, hbad⟩)
      exact htail.trans (add_le_add hstep le_rfl)
  | «oracle» Messages rest ih =>
    intro roles oracles initial impl state extractor schedule bounded OutP OutV prover verifier
      fresh
    rw [executeStrategies_oracle]
    simp only [simulateQ_bind, simulateQ_pure]
    apply prEvent_bind_le_of_forall_le_of_support
    intro chosen _
    apply prEvent_bind_le_of_forall_le_of_support
    intro next hnext
    have bound := ih (roles.2 PUnit.unit) (oracles.2 PUnit.unit)
      (Access.extend initial oracles.1) (Access.extendImpl initial oracles.1 impl chosen.1)
      (extractor chosen.1).2.2 (schedule chosen.1) (bounded chosen.1)
      (OutP := fun path => OutP ⟨chosen.1, path⟩)
      (OutV := fun path => OutV ⟨PUnit.unit, path⟩) chosen.2 next (fresh chosen.1 next hnext)
    refine le_trans ?_ (bound.trans (le_iSup (fun message => ChallengeSchedule.maxError
      (tree := rest PUnit.unit) (roles.2 PUnit.unit) (schedule message)) chosen.1))
    simp only [prEvent_norm]
    exact prEvent_mono _ _ _ fun result h => h

/-- **Knowledge soundness of actual execution.** Under a knowledge certificate whose challenge
programs are the actual verifier's, a known terminal witness extracts to an unknown input
witness with probability at most the schedule's largest path error. -/
theorem KnowledgeCertificate.executeStrategies_extraction_le {ι : Type}
    (ambient : OracleSpec ι) {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] [MonadAttach m]
    [WeaklyLawfulMonadAttach m] (handler : QueryImpl ambient m)
    {tree : Oracle.TypeTree.{0}} {roles : tree.RoleDecoration} {state : KnowledgeState.{w}}
    (certificate : KnowledgeCertificate tree roles state) (oracles : tree.OracleDecoration)
    (initial : PFunctor) (impl : QueryImpl (ofPFunctor initial) Id)
    {OutP : tree.ExecutionPath → Type} {OutV : tree.BranchPath → Type}
    (prover : Prover.Strategy ambient tree roles OutP)
    (verifier : Verifier.Strategy ambient tree roles oracles initial OutV)
    (fresh : SamplesChallenges ambient handler tree roles oracles initial impl _ verifier
      certificate.challenges) :
    Pr{let result ← (simulateQ handler
      (executeStrategies ambient tree roles oracles initial impl prover verifier))}[
      ∃ witness, (certificate.extractor.terminalState result.1).holds witness ∧
        ¬ state.holds (certificate.extractor.extractWitness result.1 witness)] ≤
      certificate.challenges.maxError roles := by
  refine le_trans (prEvent_mono _ _ _ fun result h => ?_)
    (executeStrategies_badChallenge_le ambient handler tree roles oracles initial impl
      certificate.extractor certificate.challenges certificate.local_bound prover verifier fresh)
  obtain ⟨witness, hgood, hbad⟩ := h
  exact ⟨witness, extraction_failure_implies_bad_challenge certificate.extractor roles
    certificate.prover_preserving result.1 witness hgood hbad⟩

end Interaction.Oracle.Security
