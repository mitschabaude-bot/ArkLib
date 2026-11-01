/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.Interaction.Oracle.Security.BcsProtocol

/-!
# Chain inputs of the snapshot protocol

A layout's observations are prefix-free (`Layout.PrefixFree`) when every move's and commitment's
observation is prefix-free and every witness's also suffix-free, and fill the chain blocks
(`Layout.Fills`) when every challenge that squeezes has observed elements since the last squeeze.

* `prefixFree_snapObserver`: the snapshot protocol's observer is then prefix-free, a snapshot
  observed as `[inr T]`, so its encoding of keys is injective (`Observer.encode_injective`).
* `realObserver`: the duplex verifier's actual observer of the snapshot protocol, a snapshot
  observed as nothing; `fills_realObserver`: it fills the chain blocks when the layout does.
* `erase_encodeFrom_snapObserver`: erasing the snapshots from the snapshot observer's chain inputs
  gives the actual observer's.
-/

@[expose] public section

namespace Interaction.Oracle.Security.Bcs

open PublicCoin StateRestoration HashChain

variable {F Snap Com C : Type}

/-- Every observation of the layout is prefix-free, and every draw witness also suffix-free. -/
def Layout.PrefixFree : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    (dec : Decoder C coin) → Layout F Snap Com coin dec → Prop
  | _, .done, _, _ => True
  | _, @PublicCoin.sender _ _ _ next, dec, lay =>
      HashChain.PrefixFree lay.1 ∧ ∀ move, Layout.PrefixFree (next move) (dec move) (lay.2 move)
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay =>
      HashChain.PrefixFree lay.1 ∧ Layout.PrefixFree next dec lay.2.2
  | _, @PublicCoin.challenge _ _ _ next, dec, lay =>
      HashChain.PrefixFree lay.2.1 ∧ HashChain.SuffixFree lay.2.1 ∧
        Layout.PrefixFree next dec.2 lay.2.2

/-- Every squeezing challenge has observations since the last squeeze: `filled` holds when some
observation since the last squeeze is not empty. -/
def Layout.Fills : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    (dec : Decoder C coin) → Layout F Snap Com coin dec → Prop → Prop
  | _, .done, _, _, _ => True
  | _, @PublicCoin.sender _ _ _ next, dec, lay, filled =>
      ∀ move, Layout.Fills (next move) (dec move) (lay.2 move) (filled ∨ lay.1 move ≠ [])
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay, filled =>
      ∀ c, Layout.Fills next dec lay.2.2 (filled ∨ lay.1 c ≠ [])
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, filled =>
      (lay.1 ≠ 0 → ∀ w, filled ∨ lay.2.1 w ≠ []) ∧
        ∀ w, Layout.Fills next dec.2 lay.2.2
          (if lay.1 = 0 then filled ∨ lay.2.1 w ≠ [] else False)

end Interaction.Oracle.Security.Bcs
