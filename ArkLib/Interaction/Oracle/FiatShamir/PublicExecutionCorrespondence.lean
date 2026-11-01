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

private def roundProver {ι : Type} (ambient : OracleSpec ι)
    (round : Round) (rounds : List Round)
    (next : round.Message → PUnit → round.Challenge → GuardSchedule PUnit rounds)
    (message : round.Message) (messages : PublicMessages rounds) :
    (pass : Bool) → Prover.Strategy ambient
      (publicRest round rounds next message pass).tree
      (publicRest round rounds next message pass).roles (fun _ => Unit)
  | false => ()
  | true => fun challenge => pure (scriptedPublicProver ambient rounds
      (next message PUnit.unit challenge) messages)

private def roundVerifier {Input : Type} {allRounds : Input → List Round}
    (round : Round) (rounds : List Round)
    (next : round.Message → PUnit → round.Challenge → GuardSchedule PUnit rounds)
    (message : round.Message)
    (embed : Prefix PUnit (round :: rounds) → Key Input PUnit allRounds)
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) :
    (pass : Bool) → OracleComp (oracleSpec Input PUnit allRounds + ofPFunctor 0)
      (Verifier.Strategy (oracleSpec Input PUnit allRounds)
        (publicRest round rounds next message pass).tree
        (publicRest round rounds next message pass).roles
        (publicRest round rounds next message pass).oracles 0 (fun _ => Unit))
  | true => pure (do
      let response ← liftM
        ((oracleSpec Input PUnit allRounds + ofPFunctor 0).query
          (.inl (embed (Prefix.here message PUnit.unit))))
      let challenge : round.Challenge := cast (preserve (Prefix.here message PUnit.unit)) response
      pure ⟨challenge,
        guardedPublicVerifier rounds (next message PUnit.unit challenge)
          (fun key => embed (Prefix.later message PUnit.unit key))
          (fun key => preserve (Prefix.later message PUnit.unit key))⟩)
  | false => pure (pure ())

private def roundDecode (round : Round) (rounds : List Round)
    (next : round.Message → PUnit → round.Challenge → GuardSchedule PUnit rounds)
    (message : round.Message) :
    (pass : Bool) → (publicRest round rounds next message pass).tree.ExecutionPath →
      Option (protocol (round :: rounds)).tree.ExecutionPath :=
  decodeAfterGuard round rounds next message
    (fun challenge suffix => acceptedPath rounds (next message PUnit.unit challenge) suffix)

private def roundAfterSend {Input : Type} {allRounds : Input → List Round}
    (round : Round) (rounds : List Round)
    (next : round.Message → PUnit → round.Challenge → GuardSchedule PUnit rounds)
    (message : round.Message) (messages : PublicMessages rounds)
    (embed : Prefix PUnit (round :: rounds) → Key Input PUnit allRounds)
    (preserve : ∀ key, (embed key).Challenge = key.Challenge)
    (pass : Bool) : OracleComp (oracleSpec Input PUnit allRounds)
      (Option (protocol (round :: rounds)).tree.ExecutionPath) :=
  (fun result => roundDecode round rounds next message pass result.1) <$>
    (do
      let verifier ← simulateQ
        (Verifier.liftAccessImpl (oracleSpec Input PUnit allRounds) 0 (fun q => nomatch q))
        (roundVerifier round rounds next message embed preserve pass)
      executeStrategies (oracleSpec Input PUnit allRounds)
        (publicRest round rounds next message pass).tree
        (publicRest round rounds next message pass).roles
        (publicRest round rounds next message pass).oracles 0 (fun q => nomatch q)
        (roundProver (oracleSpec Input PUnit allRounds)
          round rounds next message messages pass) verifier)

set_option backward.isDefEq.respectTransparency false in
private theorem roundAfterSend_eq_mapped {Input : Type} {allRounds : Input → List Round}
    (round : Round) (rounds : List Round)
    (next : round.Message → PUnit → round.Challenge → GuardSchedule PUnit rounds)
    (message : round.Message) (messages : PublicMessages rounds)
    (embed : Prefix PUnit (round :: rounds) → Key Input PUnit allRounds)
    (preserve : ∀ key, (embed key).Challenge = key.Challenge)
    (ih : ∀ (guards : GuardSchedule PUnit rounds) (messages : PublicMessages rounds)
      (embed : Prefix PUnit rounds → Key Input PUnit allRounds)
      (preserve : ∀ key, (embed key).Challenge = key.Challenge),
      publicStoppedVerifyWith rounds guards messages embed preserve =
        mappedStoppedComplete rounds guards messages embed preserve)
    (pass : Bool) :
    roundAfterSend round rounds next message messages embed preserve pass =
      if pass then (do
        let response ← liftM ((oracleSpec Input PUnit allRounds).query
          (embed (Prefix.here message PUnit.unit)))
        let challenge : round.Challenge :=
          cast (preserve (Prefix.here message PUnit.unit)) response
        let suffix ← mappedStoppedComplete rounds (next message PUnit.unit challenge)
          messages (fun key => embed (Prefix.later message PUnit.unit key))
          (fun key => preserve (Prefix.later message PUnit.unit key))
        return suffix.map fun tail => ⟨message, challenge, tail⟩)
      else pure none := by
  cases pass with
  | false =>
      simp [roundAfterSend, roundVerifier, publicRest, roundProver, roundDecode,
        decodeAfterGuard, executeStrategies_done]
  | true =>
      unfold roundAfterSend
      simp only [roundVerifier, roundProver, roundDecode, publicRest]
      simp only [Protocol.public_tree, Protocol.public_roles, Protocol.public_oracles]
      simp only [simulateQ_pure, pure_bind]
      rw [executeStrategies_public_receiver]
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
        OracleQuery.input_query, id_map, Verifier.liftAccessImpl_ambient,
        simulateQ_pure, pure_bind, bind_assoc]
      simp only [ite_true, QueryImpl.id']
      simp only [map_bind, bind_pure_comp, Functor.map_map]
      apply bind_congr
      intro response
      have htail := ih (next message PUnit.unit
          (cast (preserve (Prefix.here message PUnit.unit)) response)) messages
        (fun key => embed (Prefix.later message PUnit.unit key))
        (fun key => preserve (Prefix.later message PUnit.unit key))
      let challenge : round.Challenge :=
        cast (preserve (Prefix.here message PUnit.unit)) response
      let extend : (protocol rounds).tree.ExecutionPath →
          (protocol (round :: rounds)).tree.ExecutionPath :=
        fun tail => ⟨message, ⟨challenge, tail⟩⟩
      have mapped := congrArg
        (fun run : OracleComp (oracleSpec Input PUnit allRounds)
          (Option (protocol rounds).tree.ExecutionPath) => Option.map extend <$> run) htail
      convert mapped using 1
      all_goals simp only [publicStoppedVerifyWith, Functor.map_map, extend, challenge]
      all_goals rfl

set_option backward.isDefEq.respectTransparency false in
/-- The real public strategy executor is extensionally the guarded full-prefix completion. -/
theorem publicStoppedVerifyWith_eq_mapped {Input : Type} {allRounds : Input → List Round}
    (rounds : List Round) (guards : GuardSchedule PUnit rounds)
    (messages : PublicMessages rounds)
    (embed : Prefix PUnit rounds → Key Input PUnit allRounds)
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) :
    publicStoppedVerifyWith rounds guards messages embed preserve =
      mappedStoppedComplete rounds guards messages embed preserve := by
  induction rounds with
  | nil =>
      unfold publicStoppedVerifyWith
      simp only [guardedPublicProtocol, Protocol.done_tree, Protocol.done_roles,
        Protocol.done_oracles]
      rw [executeStrategies_done]
      simp [mappedStoppedComplete, acceptedPath, scriptedPublicProver,
        guardedPublicVerifier]
  | cons round rounds ih =>
      rcases guards with ⟨guard, next⟩
      rcases messages with ⟨message, messages⟩
      have hstep : publicStoppedVerifyWith (round :: rounds) (guard, next)
          (message, messages) embed preserve =
            roundAfterSend round rounds next message messages embed preserve
              (guard message PUnit.unit) := by
        unfold publicStoppedVerifyWith
        simp only [guardedPublicProtocol, Protocol.public_tree, Protocol.public_roles,
          Protocol.public_oracles]
        rw [executeStrategies_public_sender]
        simp only [scriptedPublicProver, PFunctor.FreeM.liftBind_eq,
          PFunctor.FreeM.bind_eq_bind, bind_pure_comp, pure_bind,
          map_bind, Functor.map_map]
        simp only [roundAfterSend, publicRest, roundProver, roundVerifier,
          roundDecode, map_bind]
        simp only [guardedPublicVerifier, acceptedPath]
        apply bind_congr
        intro continuation
        congr 1
      rw [hstep, roundAfterSend_eq_mapped round rounds next message messages
        embed preserve ih]
      cases hguard : guard message PUnit.unit <;>
        simp [mappedStoppedComplete, hguard]

end Interaction.Oracle.FiatShamir
