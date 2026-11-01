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

Every prover message is public (`publicProtocol`). At each challenge node a pure prefix guard
selects either termination or the verifier's challenge, which queries the typed full-prefix key
before continuing. The ordinary native strategy executor therefore performs no hash query at a
rejected challenge and never executes the suffix after rejection.
-/

@[expose] public section

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec
open Interaction.Oracle.TypeTree

namespace Interaction.Oracle.FiatShamir

open Security.StateRestoration

/-- A challenge node behind its guard: the challenge and its continuation if the guard passes,
termination otherwise. -/
def guardedChallenge (Challenge : Type) (rest : Challenge → Protocol) : Bool → Protocol
  | false => .done
  | true => .public .receiver Challenge rest

/-- Public protocol whose tree itself terminates at the first failed prefix guard. -/
def guardedPublicProtocol : {protocol : Protocol} → (coin : PublicCoin protocol) →
    GuardSchedule PUnit coin → Protocol
  | _, .done, _ => .done
  | _, @PublicCoin.sender Moves _ _ next, guards =>
      .public .sender Moves fun move => guardedPublicProtocol (next move) (guards move)
  | _, @PublicCoin.oracle Messages _ _ _ next, guards =>
      .public .sender Messages fun message => guardedPublicProtocol next (guards message)
  | _, @PublicCoin.challenge Challenge _ _ next, guards =>
      guardedChallenge Challenge (fun challenge =>
        guardedPublicProtocol next (guards.2 PUnit.unit challenge)) (guards.1 PUnit.unit)

/-- A selected public proof sends its next message at each reached sender node. -/
def scriptedPublicProver {ι : Type} (ambient : OracleSpec ι) :
    {protocol : Protocol} → (coin : PublicCoin protocol) → (guards : GuardSchedule PUnit coin) →
    Messages PUnit coin →
    Prover.Strategy ambient (guardedPublicProtocol coin guards).tree
      (guardedPublicProtocol coin guards).roles (fun _ => Unit)
  | _, .done, _, _ => ()
  | _, @PublicCoin.sender _ _ _ next, guards, ⟨move, messages⟩ =>
      pure ⟨move, scriptedPublicProver ambient (next move) (guards move) messages⟩
  | _, @PublicCoin.oracle _ _ _ _ next, guards, ⟨message, messages⟩ =>
      pure ⟨message, scriptedPublicProver ambient next (guards message) messages⟩
  | _, @PublicCoin.challenge Challenge _ _ next, guards, ⟨_, messages⟩ =>
      let after : (pass : Bool) → Prover.Strategy ambient
          (guardedChallenge Challenge (fun challenge =>
            guardedPublicProtocol next (guards.2 PUnit.unit challenge)) pass).tree
          (guardedChallenge Challenge (fun challenge =>
            guardedPublicProtocol next (guards.2 PUnit.unit challenge)) pass).roles
          (fun _ => Unit)
        | false => ()
        | true => fun challenge =>
            pure (scriptedPublicProver ambient next (guards.2 PUnit.unit challenge) messages)
      after (guards.1 PUnit.unit)

/-- Hash the full-prefix key only after the guard of a challenge has passed. The prefixes of
`coin` are embedded into the keys of an enclosing restoration oracle. -/
def guardedPublicVerifier {Input : Type} {allProtocol : Input → Protocol}
    {allCoin : (z : Input) → PublicCoin (allProtocol z)} :
    {protocol : Protocol} → (coin : PublicCoin protocol) → (guards : GuardSchedule PUnit coin) →
    (embed : Prefix PUnit coin → Key Input PUnit allCoin) →
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) →
    Verifier.Strategy (oracleSpec Input PUnit allCoin)
      (guardedPublicProtocol coin guards).tree
      (guardedPublicProtocol coin guards).roles
      (guardedPublicProtocol coin guards).oracles 0 (fun _ => Unit)
  | _, .done, _, _, _ => pure ()
  | _, @PublicCoin.sender _ _ _ next, guards, embed, preserve => fun move =>
      pure (guardedPublicVerifier (next move) (guards move) (fun key => embed ⟨move, key⟩)
        fun key => preserve ⟨move, key⟩)
  | _, @PublicCoin.oracle _ _ _ _ next, guards, embed, preserve => fun message =>
      pure (guardedPublicVerifier next (guards message) (fun key => embed ⟨message, key⟩)
        fun key => preserve ⟨message, key⟩)
  | _, @PublicCoin.challenge Challenge _ _ next, guards, embed, preserve =>
      let after : (pass : Bool) → Verifier.Strategy (oracleSpec Input PUnit allCoin)
          (guardedChallenge Challenge (fun challenge =>
            guardedPublicProtocol next (guards.2 PUnit.unit challenge)) pass).tree
          (guardedChallenge Challenge (fun challenge =>
            guardedPublicProtocol next (guards.2 PUnit.unit challenge)) pass).roles
          (guardedChallenge Challenge (fun challenge =>
            guardedPublicProtocol next (guards.2 PUnit.unit challenge)) pass).oracles 0
          (fun _ => Unit)
        | false => pure ()
        | true => do
            let response ← liftM ((oracleSpec Input PUnit allCoin + ofPFunctor 0).query
              (.inl (embed (.inl PUnit.unit))))
            let challenge : Challenge := cast (preserve (.inl PUnit.unit)) response
            pure ⟨challenge, guardedPublicVerifier next (guards.2 PUnit.unit challenge)
              (fun key => embed (.inr ⟨PUnit.unit, key⟩))
              fun key => preserve (.inr ⟨PUnit.unit, key⟩)⟩
      after (guards.1 PUnit.unit)

/-- The actual native strategy execution of one selected public proof of input `z`, querying the
keys of `z`. -/
def publicStoppedExecution {Input : Type} {protocol : Input → Protocol}
    (coin : (z : Input) → PublicCoin (protocol z))
    (guards : (z : Input) → GuardSchedule PUnit (coin z)) (z : Input)
    (messages : Messages PUnit (coin z)) :=
  executeStrategies (oracleSpec Input PUnit coin)
    (guardedPublicProtocol (coin z) (guards z)).tree
    (guardedPublicProtocol (coin z) (guards z)).roles
    (guardedPublicProtocol (coin z) (guards z)).oracles 0
    (fun q => nomatch q)
    (scriptedPublicProver (oracleSpec Input PUnit coin) (coin z) (guards z) messages)
    (guardedPublicVerifier (allCoin := coin) (coin z) (guards z) (fun pre => ⟨z, pre⟩)
      (fun _ => rfl))

/-- Decode a reached challenge node behind its guard. -/
def decodeAfterGuard {Challenge : Type} {rest : Challenge → Protocol} {Rest : Protocol}
    (decodeTail : (challenge : Challenge) → (rest challenge).tree.ExecutionPath →
      Option Rest.tree.ExecutionPath) :
    (pass : Bool) → (guardedChallenge Challenge rest pass).tree.ExecutionPath →
      Option (Protocol.public .receiver Challenge fun _ => Rest).tree.ExecutionPath
  | false, _ => none
  | true, suffix => (decodeTail suffix.1 suffix.2).map fun tail => ⟨suffix.1, tail⟩

/-- A reached public path yields a full restoration transcript exactly on acceptance. -/
def acceptedPath : {protocol : Protocol} → (coin : PublicCoin protocol) →
    (guards : GuardSchedule PUnit coin) →
    (guardedPublicProtocol coin guards).tree.ExecutionPath → Option protocol.tree.ExecutionPath
  | _, .done, _, _ => some PUnit.unit
  | _, @PublicCoin.sender _ _ _ next, guards, path =>
      (acceptedPath (next path.1) (guards path.1) path.2).map fun tail => ⟨path.1, tail⟩
  | _, @PublicCoin.oracle _ _ _ _ next, guards, path =>
      (acceptedPath next (guards path.1) path.2).map fun tail => ⟨path.1, tail⟩
  | _, @PublicCoin.challenge _ _ _ next, guards, path =>
      decodeAfterGuard (fun challenge suffix =>
        acceptedPath next (guards.2 PUnit.unit challenge) suffix) (guards.1 PUnit.unit) path

/-- Public stopped verification exposes acceptance together with the full concrete transcript. -/
def publicStoppedVerify {Input : Type} {protocol : Input → Protocol}
    (coin : (z : Input) → PublicCoin (protocol z))
    (guards : (z : Input) → GuardSchedule PUnit (coin z)) (z : Input)
    (messages : Messages PUnit (coin z)) :
    OracleComp (oracleSpec Input PUnit coin) (Option (protocol z).tree.ExecutionPath) :=
  (fun result => acceptedPath (coin z) (guards z) result.1) <$>
    publicStoppedExecution coin guards z messages

/-- Route a stopped completion through a challenge-preserving embedding of its prefixes into a
restoration key domain. -/
def mappedStoppedComplete {Input : Type} {allProtocol : Input → Protocol}
    {allCoin : (z : Input) → PublicCoin (allProtocol z)} :
    {protocol : Protocol} → (coin : PublicCoin protocol) → (guards : GuardSchedule PUnit coin) →
    Messages PUnit coin →
    (embed : Prefix PUnit coin → Key Input PUnit allCoin) →
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) →
    OracleComp (oracleSpec Input PUnit allCoin) (Option protocol.tree.ExecutionPath)
  | _, .done, _, _, _, _ => pure (some PUnit.unit)
  | _, @PublicCoin.sender _ _ _ next, guards, ⟨move, messages⟩, embed, preserve => do
      let suffix ← mappedStoppedComplete (next move) (guards move) messages
        (fun key => embed ⟨move, key⟩) fun key => preserve ⟨move, key⟩
      return suffix.map fun tail => ⟨move, tail⟩
  | _, @PublicCoin.oracle _ _ _ _ next, guards, ⟨message, messages⟩, embed, preserve => do
      let suffix ← mappedStoppedComplete next (guards message) messages
        (fun key => embed ⟨message, key⟩) fun key => preserve ⟨message, key⟩
      return suffix.map fun tail => ⟨message, tail⟩
  | _, @PublicCoin.challenge Challenge _ _ next, guards, ⟨_, messages⟩, embed, preserve => do
      if !guards.1 PUnit.unit then
        return none
      let response ← liftM ((oracleSpec Input PUnit allCoin).query (embed (.inl PUnit.unit)))
      let challenge : Challenge := cast (preserve (.inl PUnit.unit)) response
      let suffix ← mappedStoppedComplete next (guards.2 PUnit.unit challenge) messages
        (fun key => embed (.inr ⟨PUnit.unit, key⟩)) fun key => preserve (.inr ⟨PUnit.unit, key⟩)
      return suffix.map fun tail => ⟨challenge, tail⟩

/-- The same public native executor, with its prefixes embedded in a restoration key domain. -/
def publicStoppedVerifyWith {Input : Type} {allProtocol : Input → Protocol}
    {allCoin : (z : Input) → PublicCoin (allProtocol z)} {protocol : Protocol}
    (coin : PublicCoin protocol) (guards : GuardSchedule PUnit coin)
    (messages : Messages PUnit coin)
    (embed : Prefix PUnit coin → Key Input PUnit allCoin)
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) :
    OracleComp (oracleSpec Input PUnit allCoin) (Option protocol.tree.ExecutionPath) :=
  (fun result => acceptedPath coin guards result.1) <$>
    executeStrategies (oracleSpec Input PUnit allCoin)
      (guardedPublicProtocol coin guards).tree
      (guardedPublicProtocol coin guards).roles
      (guardedPublicProtocol coin guards).oracles 0
      (fun q => nomatch q)
      (scriptedPublicProver (oracleSpec Input PUnit allCoin) coin guards messages)
      (guardedPublicVerifier coin guards embed preserve)

theorem publicStoppedVerify_eq_with {Input : Type} {protocol : Input → Protocol}
    (coin : (z : Input) → PublicCoin (protocol z))
    (guards : (z : Input) → GuardSchedule PUnit (coin z)) (z : Input)
    (messages : Messages PUnit (coin z)) :
    publicStoppedVerify coin guards z messages =
    publicStoppedVerifyWith (allCoin := coin) (coin z) (guards z) messages
      (fun pre => ⟨z, pre⟩) (fun _ => rfl) := rfl

end Interaction.Oracle.FiatShamir
