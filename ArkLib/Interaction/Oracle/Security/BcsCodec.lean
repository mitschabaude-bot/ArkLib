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
* `fills_snapObserver`: the snapshot protocol's observer fills every chain block, which starts
  with its snapshot move, so the first squeeze of every key absorbs a nonempty input
  (`Observer.encode_fst_ne_nil`).
-/

@[expose] public section

namespace Interaction.Oracle.Security.Bcs

open PublicCoin StateRestoration HashChain

variable {F Snap C : Type}

/-- Every observation of the layout is prefix-free, and every draw witness also suffix-free. -/
def Layout.PrefixFree : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    (dec : Decoder C coin) → Layout F Snap coin dec → Prop
  | _, .done, _, _ => True
  | _, @PublicCoin.sender _ _ _ next, dec, lay =>
      HashChain.PrefixFree lay.1 ∧ ∀ move, Layout.PrefixFree (next move) (dec move) (lay.2 move)
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay =>
      HashChain.PrefixFree lay.1.observe ∧ Layout.PrefixFree next dec lay.2
  | _, @PublicCoin.challenge _ _ _ next, dec, lay =>
      HashChain.PrefixFree lay.2.1 ∧ HashChain.SuffixFree lay.2.1 ∧
        Layout.PrefixFree next dec.2 lay.2.2

/-- Every squeezing challenge has observations since the last squeeze: `filled` holds when some
observation since the last squeeze is not empty. -/
def Layout.Fills : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    (dec : Decoder C coin) → Layout F Snap coin dec → Prop → Prop
  | _, .done, _, _, _ => True
  | _, @PublicCoin.sender _ _ _ next, dec, lay, filled =>
      ∀ move, Layout.Fills (next move) (dec move) (lay.2 move) (filled ∨ lay.1 move ≠ [])
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay, filled =>
      ∀ c, Layout.Fills next dec lay.2 (filled ∨ lay.1.observe c ≠ [])
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, filled =>
      (lay.1 ≠ 0 → ∀ w, filled ∨ lay.2.1 w ≠ []) ∧
        ∀ w, Layout.Fills next dec.2 lay.2.2
          (if lay.1 = 0 then filled ∨ lay.2.1 w ≠ [] else False)

/-! ### Mapped observations -/

section Observations

variable {α β γ : Type}

/-- Mapping a prefix-free observation by an injective map keeps it prefix-free. -/
theorem prefixFree_map {f : α → List β} (hf : HashChain.PrefixFree f) {g : β → γ}
    (hg : Function.Injective g) : HashChain.PrefixFree fun a => (f a).map g := by
  intro a b r r' h
  rcases List.append_eq_append_iff.mp h with ⟨c, hc, hr⟩ | ⟨c, hc, hr⟩
  · obtain ⟨l₁, l₂, hfb, h₁, rfl⟩ := List.map_eq_append_iff.mp hc
    obtain rfl := List.map_injective_iff.mpr hg h₁
    obtain ⟨rfl, rfl⟩ := hf a b l₂ [] (by rw [hfb, List.append_nil])
    simpa using hr
  · obtain ⟨l₁, l₂, hfa, h₁, rfl⟩ := List.map_eq_append_iff.mp hc
    obtain rfl := List.map_injective_iff.mpr hg h₁
    obtain ⟨rfl, rfl⟩ := hf a b [] l₂ (by rw [hfa, List.append_nil])
    simpa using hr.symm

/-- Mapping a suffix-free observation by an injective map keeps it suffix-free. -/
theorem suffixFree_map {f : α → List β} (hf : HashChain.SuffixFree f) {g : β → γ}
    (hg : Function.Injective g) : HashChain.SuffixFree fun a => (f a).map g := by
  intro a b r r' h
  rcases List.append_eq_append_iff.mp h with ⟨c, hc, hr⟩ | ⟨c, hc, hr⟩
  · obtain ⟨l₁, l₂, hfa, rfl, h₂⟩ := List.map_eq_append_iff.mp hr
    obtain rfl := List.map_injective_iff.mpr hg h₂
    obtain ⟨rfl, rfl⟩ := hf a b [] l₁ (by rw [hfa, List.nil_append])
    simpa using hc.symm
  · obtain ⟨l₁, l₂, hfb, rfl, h₂⟩ := List.map_eq_append_iff.mp hr
    obtain rfl := List.map_injective_iff.mpr hg h₂
    obtain ⟨rfl, rfl⟩ := hf a b l₁ [] (by rw [hfb, List.nil_append])
    simpa using hc

end Observations

/-! ### The snapshot observer -/

section SnapObserver

variable [DecidableEq Snap]

omit [DecidableEq Snap] in
/-- A snapshot move observed as itself is prefix-free. -/
theorem prefixFree_snap : HashChain.PrefixFree fun T : Snap => ([.inr T] : List (F ⊕ Snap)) :=
  prefixFree_of_length (fun _ _ h => by simpa using h) fun _ _ => rfl

/-- The snapshot observer is prefix-free when the layout is. -/
theorem prefixFree_snapObserver : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    (dec : Decoder C coin) → (lay : Layout F Snap coin dec) → (start : Bool) →
    Layout.PrefixFree coin dec lay →
    (snapObserver coin dec lay start).PrefixFree (snapCoin coin dec lay start)
      (snapDecoder coin dec lay start)
  | _, .done, _, _, _, _ => trivial
  | _, @PublicCoin.sender _ _ _ next, dec, lay, start, h => by
      have hf : (snapObserver (.sender next) dec lay false).PrefixFree
          (snapCoin (.sender next) dec lay false) (snapDecoder (.sender next) dec lay false) :=
        ⟨prefixFree_map h.1 Sum.inl_injective, fun move =>
          prefixFree_snapObserver (next move) (dec move) (lay.2 move) false (h.2 move)⟩
      cases start
      · exact hf
      · exact ⟨prefixFree_snap, fun _ => hf⟩
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay, start, h => by
      have hf : (snapObserver (.oracle next) dec lay false).PrefixFree
          (snapCoin (.oracle next) dec lay false) (snapDecoder (.oracle next) dec lay false) :=
        ⟨prefixFree_map h.1 Sum.inl_injective, fun _ =>
          prefixFree_snapObserver next dec lay.2 false h.2⟩
      cases start
      · exact hf
      · exact ⟨prefixFree_snap, fun _ => hf⟩
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, start, h => by
      have hf : (snapObserver (.challenge next) dec lay false).PrefixFree
          (snapCoin (.challenge next) dec lay false)
          (snapDecoder (.challenge next) dec lay false) :=
        ⟨prefixFree_map h.1 Sum.inl_injective, suffixFree_map h.2.1 Sum.inl_injective,
          prefixFree_snapObserver next dec.2 lay.2.2 (lay.1 != 0) h.2.2⟩
      cases start
      · exact hf
      · exact ⟨prefixFree_snap, fun _ => hf⟩

/-- The snapshot observer fills every chain block: a block starts with its snapshot move. -/
theorem fills_snapObserver : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    (dec : Decoder C coin) → (lay : Layout F Snap coin dec) → (start : Bool) →
    (filled : Prop) → (start = false → filled) →
    (snapObserver coin dec lay start).Fills (snapCoin coin dec lay start)
      (snapDecoder coin dec lay start) filled
  | _, .done, _, _, _, _, _ => trivial
  | _, @PublicCoin.sender _ _ _ next, dec, lay, start, filled, h => by
      have hf : ∀ filled : Prop, filled → (snapObserver (.sender next) dec lay false).Fills
          (snapCoin (.sender next) dec lay false) (snapDecoder (.sender next) dec lay false)
          filled := fun _ hfilled move =>
        fills_snapObserver (next move) (dec move) (lay.2 move) false _ fun _ => Or.inl hfilled
      cases start
      · exact hf filled (h rfl)
      · exact fun _ => hf _ (Or.inr (List.cons_ne_nil _ _))
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay, start, filled, h => by
      have hf : ∀ filled : Prop, filled → (snapObserver (.oracle next) dec lay false).Fills
          (snapCoin (.oracle next) dec lay false) (snapDecoder (.oracle next) dec lay false)
          filled := fun _ hfilled _ =>
        fills_snapObserver next dec lay.2 false _ fun _ => Or.inl hfilled
      cases start
      · exact hf filled (h rfl)
      · exact fun _ => hf _ (Or.inr (List.cons_ne_nil _ _))
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, start, filled, h => by
      have hf : ∀ filled : Prop, filled → (snapObserver (.challenge next) dec lay false).Fills
          (snapCoin (.challenge next) dec lay false)
          (snapDecoder (.challenge next) dec lay false) filled := fun _ hfilled =>
        ⟨fun _ _ => Or.inl hfilled, fun _ =>
          fills_snapObserver next dec.2 lay.2.2 (lay.1 != 0) _ fun hk => by
            split_ifs with h0
            · exact Or.inl hfilled
            · exact absurd (by simpa using hk : lay.1 = 0) h0⟩
      cases start
      · exact hf filled (h rfl)
      · exact fun _ => hf _ (Or.inr (List.cons_ne_nil _ _))

end SnapObserver

end Interaction.Oracle.Security.Bcs
