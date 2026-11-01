/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.StateRestoration

/-!
# Public-message presentation of the restoration fragment

The restoration certificate is phrased over oracle-message nodes. A Fiat–Shamir proof instead
contains every prover message in the clear: `publicProtocol` sends each oracle message as a
public prover message. A proof is a `Messages PUnit coin`: the prover's moves and messages, with
the trivial per-challenge salt, since the single global salt is part of the statement. These are
distinct native protocol nodes: a public message is retained in the branch history, whereas an
oracle message contributes only a unit branch and its payload is available through its declared
oracle interface. This file gives the public protocol
and transports its *concrete execution path* to the certificate protocol's execution path.

The path equivalence by itself does not equate the two branch histories or grant a verifier access
to an oracle-message payload. A client transporting an observation or extractor must supply its
corresponding law explicitly.
-/

@[expose] public section

open Interaction.Oracle Interaction.TwoParty
open Interaction.Oracle.TypeTree

namespace Interaction.Oracle.FiatShamir

open Security.StateRestoration

/-- The protocol with every oracle message sent as a public prover message. -/
def publicProtocol : {protocol : Protocol} → PublicCoin protocol → Protocol
  | _, .done => .done
  | _, @PublicCoin.sender Moves _ _ next =>
      .public .sender Moves fun move => publicProtocol (next move)
  | _, @PublicCoin.oracle Messages _ _ _ next =>
      .public .sender Messages fun _ => publicProtocol next
  | _, @PublicCoin.challenge Challenge _ _ next =>
      .public .receiver Challenge fun _ => publicProtocol next

/-- The concrete path forgets whether a message node was public or oracle-authored. -/
def toRestorationPath : {protocol : Protocol} → (coin : PublicCoin protocol) →
    (publicProtocol coin).tree.ExecutionPath → protocol.tree.ExecutionPath
  | _, .done, _ => PUnit.unit
  | _, @PublicCoin.sender _ _ _ next, path => ⟨path.1, toRestorationPath (next path.1) path.2⟩
  | _, @PublicCoin.oracle _ _ _ _ next, path => ⟨path.1, toRestorationPath next path.2⟩
  | _, @PublicCoin.challenge _ _ _ next, path => ⟨path.1, toRestorationPath next path.2⟩

/-- Recover the same concrete public transcript from a restoration execution path. -/
def toPublicPath : {protocol : Protocol} → (coin : PublicCoin protocol) →
    protocol.tree.ExecutionPath → (publicProtocol coin).tree.ExecutionPath
  | _, .done, _ => PUnit.unit
  | _, @PublicCoin.sender _ _ _ next, path => ⟨path.1, toPublicPath (next path.1) path.2⟩
  | _, @PublicCoin.oracle _ _ _ _ next, path => ⟨path.1, toPublicPath next path.2⟩
  | _, @PublicCoin.challenge _ _ _ next, path => ⟨path.1, toPublicPath next path.2⟩

@[simp]
theorem toPublicPath_toRestorationPath {protocol : Protocol} (coin : PublicCoin protocol)
    (path : (publicProtocol coin).tree.ExecutionPath) :
    toPublicPath coin (toRestorationPath coin path) = path := by
  induction coin with
  | done => rfl
  | sender next ih => exact Sigma.ext rfl (heq_of_eq (ih path.1 path.2))
  | oracle next ih => exact Sigma.ext rfl (heq_of_eq (ih path.2))
  | challenge next ih => exact Sigma.ext rfl (heq_of_eq (ih path.2))

@[simp]
theorem toRestorationPath_toPublicPath {protocol : Protocol} (coin : PublicCoin protocol)
    (path : protocol.tree.ExecutionPath) :
    toRestorationPath coin (toPublicPath coin path) = path := by
  induction coin with
  | done => rfl
  | sender next ih => exact Sigma.ext rfl (heq_of_eq (ih path.1 path.2))
  | oracle next ih => exact Sigma.ext rfl (heq_of_eq (ih path.2))
  | challenge next ih => exact Sigma.ext rfl (heq_of_eq (ih path.2))

/-- A concrete transcript equivalence. Its branch-history projections remain distinct. -/
def pathEquiv {protocol : Protocol} (coin : PublicCoin protocol) :
    (publicProtocol coin).tree.ExecutionPath ≃ protocol.tree.ExecutionPath where
  toFun := toRestorationPath coin
  invFun := toPublicPath coin
  left_inv := toPublicPath_toRestorationPath coin
  right_inv := toRestorationPath_toPublicPath coin

end Interaction.Oracle.FiatShamir
