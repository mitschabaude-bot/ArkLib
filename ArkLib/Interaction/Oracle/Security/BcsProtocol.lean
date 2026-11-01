/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.Interaction.Oracle.Security.HashChainObserver

/-!
# Committed oracle messages and their snapshots

The BCS transformation sends a commitment in place of each oracle message of a public-coin
protocol. A Fiat–Shamir verifier on a duplex challenger absorbs the commitment, and the message
behind it is read off the queries made to an auxiliary random oracle (the Merkle hashes): a
*snapshot* of that oracle's answers determines the message each commitment opens to.

A `Layout` records, over a public-coin protocol with draws, how a duplex verifier observes it with
commitments in place of oracle messages: the elements of each public move, the elements of each
commitment, the message a commitment opens to on a snapshot, and at each challenge the number of
squeezes and the elements of the draw's witness.

The snapshot protocol (`snapCoin`) is the protocol with every oracle message replaced by a
commitment move and a snapshot move at the start of each chain block, the moves absorbed by one
squeeze: at the start of the protocol and after each challenge that squeezes. Its observer
(`snapObserver`) observes elements of `F ⊕ Snap`: a snapshot move as itself, everything else as
the layout's elements of `F`. Erasing the snapshots from its chain inputs gives the duplex
verifier's actual inputs (`realEncode`). A path of the snapshot protocol opens to a path of the
protocol (`openPath`), each commitment opened on the latest snapshot before it.
-/

@[expose] public section

namespace Interaction.Oracle.Security.Bcs

open PublicCoin StateRestoration HashChain

/-- How a duplex verifier observes a protocol with draws `dec` whose oracle messages are
committed: the elements of each public move; for each oracle message, the elements of its
commitment and the message a commitment opens to on a snapshot; and at each challenge the number
of squeezes and the elements of the draw's witness. -/
@[reducible] def Layout (F Snap Com : Type) {C : Type} {protocol : Protocol.{0}}
    (coin : PublicCoin protocol) : Decoder C coin → Type :=
  PublicCoin.rec (motive := fun _ coin => Decoder C coin → Type) (fun _ => PUnit)
    (fun {Moves} _ _ _ lay dec => (Moves → List F) × ((move : Moves) → lay move (dec move)))
    (fun {Messages} _ _ _ _ lay dec => (Com → List F) × (Snap → Com → Messages) × lay dec)
    (@fun _ _ _ _ lay dec => ℕ × (dec.1.Witness → List F) × lay dec.2) coin

variable {F Snap Com C : Type}

/-- A snapshot move before `P` when a chain block starts. -/
def snapWrap (Snap : Type) : Bool → Protocol.{0} → Protocol.{0}
  | true, P => .public .sender Snap fun _ => P
  | false, P => P

/-- The snapshot protocol: each oracle message replaced by a commitment move, and a snapshot move
at the start of each chain block (`start`), the start of the protocol and after each challenge
that squeezes. -/
def snapProtocol (Snap Com : Type) : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    (dec : Decoder C coin) → Layout F Snap Com coin dec → Bool → Protocol.{0}
  | _, .done, _, _, _ => .done
  | _, @PublicCoin.sender Moves _ _ next, dec, lay, start => snapWrap Snap start <|
      .public .sender Moves fun move => snapProtocol Snap Com (next move) (dec move) (lay.2 move)
        false
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay, start => snapWrap Snap start <|
      .public .sender Com fun _ => snapProtocol Snap Com next dec lay.2.2 false
  | _, @PublicCoin.challenge Challenge _ _ next, dec, lay, start => snapWrap Snap start <|
      .public .receiver Challenge fun _ => snapProtocol Snap Com next dec.2 lay.2.2 (lay.1 != 0)

variable [DecidableEq Snap] [DecidableEq Com]

/-- A snapshot move keeps a protocol public-coin. -/
def snapWrapCoin {P : Protocol.{0}} (coin : PublicCoin P) :
    (start : Bool) → PublicCoin (snapWrap Snap start P)
  | true => .sender fun _ => coin
  | false => coin

/-- The snapshot protocol is public-coin. -/
def snapCoin : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    (dec : Decoder C coin) → (lay : Layout F Snap Com coin dec) → (start : Bool) →
    PublicCoin (snapProtocol Snap Com coin dec lay start)
  | _, .done, _, _, _ => .done
  | _, @PublicCoin.sender _ _ _ next, dec, lay, start => snapWrapCoin
      (.sender fun move => snapCoin (next move) (dec move) (lay.2 move) false) start
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay, start => snapWrapCoin
      (.sender fun _ => snapCoin next dec lay.2.2 false) start
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, start => snapWrapCoin
      (.challenge (snapCoin next dec.2 lay.2.2 (lay.1 != 0))) start

/-- Draws after a snapshot move. -/
def snapWrapDecoder {P : Protocol.{0}} {coin : PublicCoin P} (dec : Decoder C coin) :
    (start : Bool) → Decoder C (snapWrapCoin (Snap := Snap) coin start)
  | true => fun _ => dec
  | false => dec

/-- The draws of the snapshot protocol: the protocol's, at the same challenges. -/
def snapDecoder : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    (dec : Decoder C coin) → (lay : Layout F Snap Com coin dec) → (start : Bool) →
    Decoder C (snapCoin coin dec lay start)
  | _, .done, _, _, _ => PUnit.unit
  | _, @PublicCoin.sender _ _ _ next, dec, lay, start => snapWrapDecoder
      (coin := .sender fun move => snapCoin (next move) (dec move) (lay.2 move) false)
      (fun move => snapDecoder (next move) (dec move) (lay.2 move) false) start
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay, start => snapWrapDecoder
      (coin := .sender fun _ => snapCoin next dec lay.2.2 false)
      (fun _ => snapDecoder next dec lay.2.2 false) start
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, start => snapWrapDecoder
      (coin := .challenge (snapCoin next dec.2 lay.2.2 (lay.1 != 0)))
      (dec.1, snapDecoder next dec.2 lay.2.2 (lay.1 != 0)) start

/-- The observer after a snapshot move: the move as itself. -/
def snapWrapObserver {P : Protocol.{0}} {coin : PublicCoin P} {dec : Decoder C coin}
    (obs : Observer (F ⊕ Snap) coin dec) :
    (start : Bool) → Observer (F ⊕ Snap) (snapWrapCoin (Snap := Snap) coin start)
      (snapWrapDecoder dec start)
  | true => (fun T => [.inr T], fun _ => obs)
  | false => obs

/-- The observer of the snapshot protocol: a snapshot move as itself, every other move,
commitment and witness as the layout's elements, and each challenge's squeezes the layout's. -/
def snapObserver : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    (dec : Decoder C coin) → (lay : Layout F Snap Com coin dec) → (start : Bool) →
    Observer (F ⊕ Snap) (snapCoin coin dec lay start) (snapDecoder coin dec lay start)
  | _, .done, _, _, _ => PUnit.unit
  | _, @PublicCoin.sender _ _ _ next, dec, lay, start => snapWrapObserver
      (coin := .sender fun move => snapCoin (next move) (dec move) (lay.2 move) false)
      (dec := fun move => snapDecoder (next move) (dec move) (lay.2 move) false)
      (fun move => (lay.1 move).map .inl,
        fun move => snapObserver (next move) (dec move) (lay.2 move) false) start
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay, start => snapWrapObserver
      (coin := .sender fun _ => snapCoin next dec lay.2.2 false)
      (dec := fun _ => snapDecoder next dec lay.2.2 false)
      (fun c => (lay.1 c).map .inl, fun _ => snapObserver next dec lay.2.2 false) start
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, start => snapWrapObserver
      (coin := .challenge (snapCoin next dec.2 lay.2.2 (lay.1 != 0)))
      (dec := (dec.1, snapDecoder next dec.2 lay.2.2 (lay.1 != 0)))
      (lay.1, fun w => (lay.2.1 w).map .inl,
        snapObserver next dec.2 lay.2.2 (lay.1 != 0)) start

/-- The elements of `F` among elements of `F ⊕ Snap`. -/
def erase (l : List (F ⊕ Snap)) : List F := l.filterMap Sum.getLeft?

/-- A path of the snapshot protocol opened to a path of the protocol: each commitment opened on
the latest snapshot `T`. -/
def openPath : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    (dec : Decoder C coin) → (lay : Layout F Snap Com coin dec) → (start : Bool) → Snap →
    (snapProtocol Snap Com coin dec lay start).tree.ExecutionPath → protocol.tree.ExecutionPath
  | _, .done, _, _, _, _, _ => PUnit.unit
  | _, @PublicCoin.sender _ _ _ next, dec, lay, true, _, path =>
      ⟨path.2.1, openPath (next path.2.1) (dec path.2.1) (lay.2 path.2.1) false path.1 path.2.2⟩
  | _, @PublicCoin.sender _ _ _ next, dec, lay, false, T, path =>
      ⟨path.1, openPath (next path.1) (dec path.1) (lay.2 path.1) false T path.2⟩
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay, true, _, path =>
      ⟨lay.2.1 path.1 path.2.1, openPath next dec lay.2.2 false path.1 path.2.2⟩
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay, false, T, path =>
      ⟨lay.2.1 T path.1, openPath next dec lay.2.2 false T path.2⟩
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, true, _, path =>
      ⟨path.2.1, openPath next dec.2 lay.2.2 (lay.1 != 0) path.1 path.2.2⟩
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, false, T, path =>
      ⟨path.1, openPath next dec.2 lay.2.2 (lay.1 != 0) T path.2⟩

end Interaction.Oracle.Security.Bcs
