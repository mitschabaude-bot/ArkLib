/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.Interaction.Oracle.Protocol
public import VCVio.OracleComp.Constructions.SampleableType.Basic

/-!
# Public-coin protocols with challenge-independent shapes

`PublicCoin protocol` presents an oracle protocol whose verifier moves are uniform public
challenges and whose shape after a challenge does not depend on the challenge's value: a
challenge node has one continuation protocol for all challenges. The shape may still depend on
the statement and on the prover's public moves, and oracle messages never select a continuation.
This is the structure Fiat–Shamir and state restoration need: the random-oracle key of a
challenge is the execution prefix with its earlier challenges erased, and that prefix determines
the challenge's node.

The presentation is indexed by the protocol, so a protocol built from `Protocol` constructors
has it by the same constructors, and `append` composes it along a suffix that depends only on the
prover's public moves (`ErasedBranch`), as `KnowledgeCertificate.append` composes certificates.
-/

@[expose] public section

open Interaction.TwoParty

namespace Interaction.Oracle

/-- A public-coin protocol whose continuation after each verifier challenge is one protocol for
every challenge. Prover moves and oracle messages have decidable equality, as they are part of
the challenge keys; challenges have uniform samplers (so they are finite and nonempty). -/
inductive PublicCoin : Protocol.{0} → Type 1
  /-- The terminal protocol. -/
  | done : PublicCoin .done
  /-- A public prover move; the continuation may depend on it. -/
  | sender {Moves : Type} [DecidableEq Moves] {rest : Moves → Protocol.{0}}
      (next : (move : Moves) → PublicCoin (rest move)) :
      PublicCoin (.public .sender Moves rest)
  /-- A prover oracle message. -/
  | oracle {Messages : Type} [DecidableEq Messages] {interface : OracleInterface.{0, 0} Messages}
      {rest : Protocol.{0}} (next : PublicCoin rest) :
      PublicCoin (.oracleWith Messages interface rest)
  /-- A uniform verifier challenge, with one continuation for every challenge. -/
  | challenge {Challenge : Type} [SampleableType Challenge] {rest : Protocol.{0}}
      (next : PublicCoin rest) :
      PublicCoin (.public .receiver Challenge fun _ => rest)

namespace PublicCoin

/-- The prover's public moves along a complete branch: the structural choices with the
challenges erased. -/
@[reducible] def ErasedBranch {protocol : Protocol.{0}} (coin : PublicCoin protocol) : Type :=
  PublicCoin.rec (motive := fun _ _ => Type) PUnit
    (fun {Moves} _ _ _ branches => (move : Moves) × branches move)
    (fun _ branches => branches) (fun _ branches => branches) coin

/-- Erase the challenges of a complete structural branch. -/
def eraseBranch : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    protocol.tree.BranchPath → coin.ErasedBranch
  | _, .done, _ => PUnit.unit
  | _, @sender _ _ _ next, path => ⟨path.1, eraseBranch (next path.1) path.2⟩
  | _, @oracle _ _ _ _ next, path => eraseBranch next path.2
  | _, @challenge _ _ _ next, path => eraseBranch next path.2

/-- The protocol followed by a suffix selected by the prover's public moves alone. -/
abbrev appendProtocol {protocol : Protocol.{0}} (coin : PublicCoin protocol)
    (suffix : coin.ErasedBranch → Protocol.{0}) : Protocol.{0} :=
  ⟨PFunctor.FreeM.append protocol.tree fun path => (suffix (coin.eraseBranch path)).tree,
    PFunctor.FreeM.Displayed.Decoration.append protocol.roles
      (fun path => (suffix (coin.eraseBranch path)).roles),
    PFunctor.FreeM.Displayed.Decoration.append protocol.oracles
      (fun path => (suffix (coin.eraseBranch path)).oracles)⟩

/-- Public-coin presentations compose along a suffix that depends only on the prover's public
moves: then the suffix's shape after each challenge of the first protocol is again
challenge-independent. -/
def append : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    {suffix : coin.ErasedBranch → Protocol.{0}} →
    ((branch : coin.ErasedBranch) → PublicCoin (suffix branch)) →
    PublicCoin (coin.appendProtocol suffix)
  | _, .done, _, second => second PUnit.unit
  | _, @sender _ _ _ next, _, second =>
      .sender fun move => append (next move) fun branch => second ⟨move, branch⟩
  | _, @oracle _ _ _ _ next, _, second => .oracle (append next second)
  | _, @challenge _ _ _ next, _, second => .challenge (append next second)

end PublicCoin

end Interaction.Oracle
