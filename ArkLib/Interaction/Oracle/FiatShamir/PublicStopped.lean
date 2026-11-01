/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.FiatShamir.PublicMessage
public import ArkLib.Interaction.Oracle.Security.StateRestorationStopped
public import ArkLib.Interaction.Oracle.Execution

/-!
# Public native stopped verifier for full-prefix Fiat–Shamir

The message node is genuinely public. After the prover sends it, a pure prefix guard selects
either termination or a verifier challenge node. The latter queries the typed full-prefix key
before continuing. The ordinary native strategy executor therefore performs no hash query at a
rejected round and never executes the suffix after rejection.
-/

@[expose] public section

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec
open Interaction.Oracle.TypeTree

namespace Interaction.Oracle.FiatShamir

open Security.StateRestoration

/-- Public protocol whose tree itself terminates at the first failed prefix guard. -/
def guardedPublicProtocol : (rounds : List Round) → GuardSchedule PUnit rounds → Protocol
  | [], _ => .done
  | round :: rounds, (guard, next) =>
      .public .sender round.Message fun message =>
        match guard message PUnit.unit with
        | false => .done
        | true => .public .receiver round.Challenge fun challenge =>
            guardedPublicProtocol rounds (next message PUnit.unit challenge)

/-- The continuation chosen after observing one public message and its guard result. -/
def publicRest (round : Round) (rounds : List Round)
    (next : round.Message → PUnit → round.Challenge → GuardSchedule PUnit rounds)
    (message : round.Message) : Bool → Protocol
  | false => .done
  | true => .public .receiver round.Challenge fun challenge =>
      guardedPublicProtocol rounds (next message PUnit.unit challenge)

/-- A selected public proof sends its next message at each reached sender node. -/
def scriptedPublicProver {ι : Type} (ambient : OracleSpec ι) :
    (rounds : List Round) → (guards : GuardSchedule PUnit rounds) →
    PublicMessages rounds →
    Prover.Strategy ambient (guardedPublicProtocol rounds guards).tree
      (guardedPublicProtocol rounds guards).roles (fun _ => Unit)
  | [], _, _ => ()
  | round :: rounds, (guard, next), (message, messages) =>
      let rest := publicRest round rounds next message
      let after : (pass : Bool) →
          Prover.Strategy ambient (rest pass).tree (rest pass).roles (fun _ => Unit)
        | false => ()
        | true => fun challenge => pure (scriptedPublicProver ambient rounds
            (next message PUnit.unit challenge) messages)
      pure ⟨message, after (guard message PUnit.unit)⟩

/-- Hash the full-prefix key only after the current public message has passed its guard. The
prefixes of `rounds` are embedded into the keys of an enclosing restoration oracle. -/
def guardedPublicVerifier {Input : Type} {allRounds : Input → List Round} :
    (rounds : List Round) → (guards : GuardSchedule PUnit rounds) →
    (embed : Prefix PUnit rounds → Key Input PUnit allRounds) →
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) →
    Verifier.Strategy (oracleSpec Input PUnit allRounds)
      (guardedPublicProtocol rounds guards).tree
      (guardedPublicProtocol rounds guards).roles
      (guardedPublicProtocol rounds guards).oracles 0 (fun _ => Unit)
  | [], _, _, _ => pure ()
  | round :: rounds, (guard, next), embed, preserve => fun message =>
      let rest := publicRest round rounds next message
      let after : (pass : Bool) → OracleComp (oracleSpec Input PUnit allRounds + ofPFunctor 0)
        (Verifier.Strategy (oracleSpec Input PUnit allRounds)
          (rest pass).tree (rest pass).roles (rest pass).oracles 0 (fun _ => Unit))
        | true => pure (do
          let response ← liftM
            ((oracleSpec Input PUnit allRounds + ofPFunctor 0).query
              (.inl (embed (Prefix.here message PUnit.unit))))
          let challenge : round.Challenge :=
            cast (preserve (Prefix.here message PUnit.unit)) response
          pure ⟨challenge,
            guardedPublicVerifier rounds (next message PUnit.unit challenge)
              (fun key => embed (Prefix.later message PUnit.unit key))
              (fun key => preserve (Prefix.later message PUnit.unit key))⟩)
        | false => pure (pure ())
      after (guard message PUnit.unit)

/-- The actual native strategy execution of one selected public proof of input `z`, querying the
keys of `z`. -/
def publicStoppedExecution {Input : Type} (rounds : Input → List Round)
    (guards : (z : Input) → GuardSchedule PUnit (rounds z)) (z : Input)
    (messages : PublicMessages (rounds z)) :=
  executeStrategies (oracleSpec Input PUnit rounds)
    (guardedPublicProtocol (rounds z) (guards z)).tree
    (guardedPublicProtocol (rounds z) (guards z)).roles
    (guardedPublicProtocol (rounds z) (guards z)).oracles 0
    (fun q => nomatch q)
    (scriptedPublicProver (oracleSpec Input PUnit rounds) (rounds z) (guards z) messages)
    (guardedPublicVerifier (allRounds := rounds) (rounds z) (guards z) (fun pre => ⟨z, pre⟩)
      (fun _ => rfl))

/-- Decode an accepted round using a continuation decoder for the remaining rounds. -/
def decodeAfterGuard (round : Round) (rounds : List Round)
    (next : round.Message → PUnit → round.Challenge → GuardSchedule PUnit rounds)
    (message : round.Message)
    (decodeTail : (challenge : round.Challenge) →
      (guardedPublicProtocol rounds (next message PUnit.unit challenge)).tree.ExecutionPath →
        Option (protocol rounds).tree.ExecutionPath) :
    (pass : Bool) → (publicRest round rounds next message pass).tree.ExecutionPath →
      Option (protocol (round :: rounds)).tree.ExecutionPath
  | false, _ => none
  | true, suffix =>
      (decodeTail suffix.1 suffix.2).map (fun tail => ⟨message, suffix.1, tail⟩)

/-- A reached public path yields a full restoration transcript exactly on acceptance. -/
def acceptedPath : (rounds : List Round) →
    (guards : GuardSchedule PUnit rounds) →
    (guardedPublicProtocol rounds guards).tree.ExecutionPath →
      Option (protocol rounds).tree.ExecutionPath
  | [], _, _ => some PUnit.unit
  | round :: rounds, (guard, next), path =>
      decodeAfterGuard round rounds next path.1
        (fun challenge suffix => acceptedPath rounds
          (next path.1 PUnit.unit challenge) suffix)
        (guard path.1 PUnit.unit) path.2

/-- Public stopped verification exposes acceptance together with the full concrete transcript. -/
def publicStoppedVerify {Input : Type} (rounds : Input → List Round)
    (guards : (z : Input) → GuardSchedule PUnit (rounds z)) (z : Input)
    (messages : PublicMessages (rounds z)) :
    OracleComp (oracleSpec Input PUnit rounds)
      (Option (protocol (rounds z)).tree.ExecutionPath) :=
  (fun result => acceptedPath (rounds z) (guards z) result.1) <$>
    publicStoppedExecution rounds guards z messages

/-- Route a stopped completion through a challenge-preserving embedding of its prefixes into a
restoration key domain. -/
def mappedStoppedComplete {Input : Type} {allRounds : Input → List Round} :
    (rounds : List Round) → (guards : GuardSchedule PUnit rounds) →
    PublicMessages rounds →
    (embed : Prefix PUnit rounds → Key Input PUnit allRounds) →
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) →
    OracleComp (oracleSpec Input PUnit allRounds)
      (Option (protocol rounds).tree.ExecutionPath)
  | [], _, _, _, _ => pure (some PUnit.unit)
  | round :: rounds, (guard, next), (message, messages), embed, preserve => do
      if !guard message PUnit.unit then
        return none
      let response ← liftM ((oracleSpec Input PUnit allRounds).query
        (embed (Prefix.here message PUnit.unit)))
      let challenge : round.Challenge := cast (preserve (Prefix.here message PUnit.unit)) response
      let suffix ← mappedStoppedComplete rounds (next message PUnit.unit challenge)
        messages (fun key => embed (Prefix.later message PUnit.unit key))
        (fun key => preserve (Prefix.later message PUnit.unit key))
      return suffix.map fun tail => ⟨message, challenge, tail⟩

/-- The same public native executor, with its prefixes embedded in a restoration key domain. -/
def publicStoppedVerifyWith {Input : Type} {allRounds : Input → List Round}
    (rounds : List Round) (guards : GuardSchedule PUnit rounds)
    (messages : PublicMessages rounds)
    (embed : Prefix PUnit rounds → Key Input PUnit allRounds)
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) :
    OracleComp (oracleSpec Input PUnit allRounds)
      (Option (protocol rounds).tree.ExecutionPath) :=
  (fun result => acceptedPath rounds guards result.1) <$>
    executeStrategies (oracleSpec Input PUnit allRounds)
      (guardedPublicProtocol rounds guards).tree
      (guardedPublicProtocol rounds guards).roles
      (guardedPublicProtocol rounds guards).oracles 0
      (fun q => nomatch q)
      (scriptedPublicProver (oracleSpec Input PUnit allRounds) rounds guards messages)
      (guardedPublicVerifier rounds guards embed preserve)

theorem publicStoppedVerify_eq_with {Input : Type} (rounds : Input → List Round)
    (guards : (z : Input) → GuardSchedule PUnit (rounds z)) (z : Input)
    (messages : PublicMessages (rounds z)) :
    publicStoppedVerify rounds guards z messages =
    publicStoppedVerifyWith (allRounds := rounds) (rounds z) (guards z) messages
      (fun pre => ⟨z, pre⟩)
      (fun _ => rfl) := rfl

end Interaction.Oracle.FiatShamir
