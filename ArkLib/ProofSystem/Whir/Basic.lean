/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon
public import ArkLib.ProofSystem.Sumcheck.Message.Compressed

/-!
# Binary WHIR tables, additive encodings, and weighted claims

The encoder is supplied through its column weights. `EncodingContract` identifies its image
with Reed–Solomon on an arbitrary injective additive domain. Instantiating these weights with
the novel basis, the ordered flat basis of the binary base field, and the executable additive
NTT is a separate algebraic obligation. No multiplicative FFT domain is used here.
-/

@[expose] public section

namespace Whir

/-- Boolean coordinates, with the first coordinates indexing the interleaved rows. -/
abbrev Cube (n : ℕ) := Fin n → Bool

/-- A multilinear polynomial represented by its values on the Boolean cube. -/
abbrev Table (F : Type) (n : ℕ) := Cube n → F

/-- A Boolean table stored as data so its entries are evaluated once. -/
inductive TableCache (F : Type) : ℕ → Type
  /-- The value at the unique zero-dimensional vertex. -/
  | leaf : F → TableCache F 0
  /-- The two restrictions of the first Boolean coordinate. -/
  | node {n : ℕ} : TableCache F n → TableCache F n → TableCache F (n + 1)

/-- Materialize every Boolean value before later coordinate lookups. -/
@[noinline] def TableCache.ofTable {F : Type} : {n : ℕ} → Table F n → TableCache F n
  | 0, f => .leaf (f Fin.elim0)
  | n + 1, f => .node
    (ofTable (n := n) (fun u => f (Fin.cons false u)))
    (ofTable (n := n) (fun u => f (Fin.cons true u)))

/-- Read one Boolean vertex from a materialized table. -/
def TableCache.get {F : Type} : {n : ℕ} → TableCache F n → Table F n
  | 0, .leaf value => fun _ => value
  | _ + 1, .node left right => fun u =>
    if u 0 then right.get (Fin.tail u) else left.get (Fin.tail u)

/-- Reading a materialized table returns its original value. -/
theorem TableCache.get_ofTable {F : Type} {n : ℕ} (f : Table F n) (u : Cube n) :
    (ofTable f).get u = f u := by
  induction n with
  | zero =>
    change f Fin.elim0 = f u
    exact congrArg f (funext fun i => Fin.elim0 i)
  | succ n ih =>
    simp only [ofTable, get, ih]
    cases bit : u 0 <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact congrArg f (by simpa only [bit] using Fin.cons_self_tail u)
    · exact congrArg f (by simpa only [bit] using Fin.cons_self_tail u)

/-- Capture the materialized values before constructing their lookup function. -/
@[macro_inline] def cacheTable {F : Type} {n : ℕ} (f : Table F n) : Table F n :=
  let image := TableCache.ofTable f
  fun u => image.get u

/-- Materializing a table preserves every Boolean value. -/
theorem cacheTable_eq {F : Type} {n : ℕ} (f : Table F n) : cacheTable f = f := by
  funext u
  exact TableCache.get_ofTable f u

/-- An interleaved word, queried one complete column at a time. -/
abbrev Word (F : Type) (lanes columns : ℕ) := Fin columns → Cube lanes → F

/-- A partial word hides whole columns; a hidden column never agrees with a codeword. -/
abbrev MaskedWord (F : Type) (lanes columns : ℕ) := Fin columns → Option (Cube lanes → F)

/-- Reveal every column of a full word. -/
def fullWord {F : Type} {lanes columns : ℕ} (word : Word F lanes columns) :
    MaskedWord F lanes columns := some ∘ word

/-- Fill every hidden column with the zero column. -/
def zeroFill {F : Type} [Zero F] {lanes columns : ℕ} (word : MaskedWord F lanes columns) :
    Word F lanes columns := fun x => (word x).getD 0

/-- Hiding preserves the values of all columns that remain known. -/
def MaskLE {F : Type} {lanes columns : ℕ} (small large : MaskedWord F lanes columns) : Prop :=
  ∀ x column, small x = some column → large x = some column

/-- Map known columns without revealing hidden columns. -/
def mapMasked {F E : Type} {lanes columns : ℕ} (f : F → E)
    (word : MaskedWord F lanes columns) : MaskedWord E lanes columns :=
  fun x => (word x).map (fun column u => f (column u))

/-- Columns agreeing simultaneously in every row, with hidden columns excluded. -/
def agreement {F : Type} [DecidableEq F] {lanes columns : ℕ}
    (word : MaskedWord F lanes columns) (codeword : Word F lanes columns) : Finset (Fin columns) :=
  Finset.univ.filter fun x => word x = some (codeword x)

/-- Hiding columns only removes agreements. -/
theorem agreement_mono {F : Type} [DecidableEq F] {lanes columns : ℕ}
    {small large : MaskedWord F lanes columns} (h : MaskLE small large)
    (codeword : Word F lanes columns) : agreement small codeword ⊆ agreement large codeword := by
  intro x hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, h x _ (Finset.mem_filter.mp hx).2⟩

/-- Zero filling preserves every known column. -/
theorem maskLE_zeroFill {F : Type} [Zero F] {lanes columns : ℕ}
    (word : MaskedWord F lanes columns) : MaskLE word (fullWord (zeroFill word)) := by
  intro x column hx
  simp only [fullWord, Function.comp_apply, zeroFill, hx, Option.getD_some]

/-- The tensor equality weight at a Boolean vertex. -/
def eqWeight {F : Type} [CommRing F] {n : ℕ} (z : Fin n → F) (u : Cube n) : F :=
  ∏ i, if u i then z i else 1 - z i

/-- Evaluation of the multilinear extension of a Boolean table. -/
def mle {F : Type} [CommRing F] {n : ℕ} (f : Table F n) (z : Fin n → F) : F :=
  ∑ u, eqWeight z u * f u

/-- Restriction of the first `count` coordinates to a public challenge vector. -/
def restrict {F : Type} [CommRing F] {count tail : ℕ} (f : Table F (count + tail))
    (r : Fin count → F) : Table F tail :=
  fun x => ∑ u : Cube count, eqWeight r u * f (Fin.addCases u x)

/-- Column weights of an encoder of rate `2⁻ʳᵃᵗᵉ` on an injective base-field domain. -/
structure Encoding (K : Type) (vars : ℕ) where
  /-- The inverse-rate exponent. -/
  rate : ℕ
  /-- The ordered additive domain. -/
  domain : Fin (2 ^ (vars + rate)) ↪ K
  /-- The novel-basis evaluation weights, before extension of scalars. -/
  weight : Fin (2 ^ (vars + rate)) → Table K vars

/-- The columns of an encoder. -/
abbrev Encoding.Columns {K : Type} {vars : ℕ} (enc : Encoding K vars) :=
  Fin (2 ^ (vars + enc.rate))

/-- Extension of the domain along a field embedding. -/
def Encoding.extendedDomain {K E : Type} [DivisionRing K] [Semiring E] [Nontrivial E] {vars : ℕ}
    (enc : Encoding K vars) (ι : K →+* E) : enc.Columns ↪ E :=
  ⟨fun x => ι (enc.domain x), ι.injective.comp enc.domain.injective⟩

/-- Evaluation of a message using the encoder's column weights over the challenge field. -/
def Encoding.encode {K E : Type} [Semiring K] [Semiring E] {vars : ℕ}
    (enc : Encoding K vars) (ι : K →+* E) (f : Table E vars) : enc.Columns → E :=
  fun x => ∑ u, ι (enc.weight x u) * f u

/-- Encode each row; messages are novel-basis coefficients within each row. -/
def Encoding.interleave {K E : Type} [Semiring K] [Semiring E] {vars lanes : ℕ}
    (enc : Encoding K vars) (ι : K →+* E) (f : Table E (lanes + vars)) :
    Word E lanes (2 ^ (vars + enc.rate)) :=
  fun x u => enc.encode ι (fun v => f (Fin.addCases u v)) x

/-- Enumerate a binary subspace using the first `i` vectors of an ordered 64-vector basis. -/
def binarySpanValue {K : Type} [AddCommMonoid K] (basis : Fin 64 → K) (i : Fin 64)
    (u : Cube i.val) : K :=
  ∑ j, if u j then basis ⟨j.val, lt_trans j.isLt i.isLt⟩ else 0

/-- Evaluate the normalized subspace polynomial `W_i(X) / W_i(basis_i)` from Annex D. -/
def normalizedSubspaceValue {K : Type} [Field K] (basis : Fin 64 → K) (i : Fin 64)
    (x : K) : K :=
  (∏ u : Cube i.val, (x - binarySpanValue basis i u)) /
    ∏ u : Cube i.val, (basis i - binarySpanValue basis i u)

/-- The algebraic contract for an additive novel-basis encoder; scalar extension is explicit. -/
structure EncodingContract {K E : Type} [Field K] [Field E] {vars : ℕ}
    (enc : Encoding K vars) (ι : K →+* E) : Prop where
  /-- The protocol has inverse rate at least two. -/
  rate_pos : 0 < enc.rate
  /-- The additive domain uses at most the 64 base-field basis vectors. -/
  dimension_le : vars + enc.rate ≤ 64
  /-- Domain order and weights come from one normalized binary novel basis. -/
  novel : ∃ basis : Fin 64 → K, basis 0 = 1 ∧
    (∀ x, enc.domain x = ∑ i : Fin (vars + enc.rate),
      if x.val.testBit i.val then basis (Fin.castLE dimension_le i) else 0) ∧
    ∀ x u, enc.weight x u = ∏ i : Fin vars,
      if u i then normalizedSubspaceValue basis
        ⟨i.val, lt_of_lt_of_le i.isLt ((Nat.le_add_right vars enc.rate).trans dimension_le)⟩
        (enc.domain x) else 1
  /-- The base domain is an additive subgroup. -/
  additive : ∃ S : AddSubgroup K, Set.range enc.domain = (S : Set K)
  /-- Encoding is injective on the message coefficients. -/
  injective : Function.Injective (enc.encode ι)
  /-- Novel-basis encoding has exactly the ordinary Reed–Solomon image. -/
  image : Set.range (enc.encode ι) =
    (ReedSolomon.code (enc.extendedDomain ι) (2 ^ vars) : Set (enc.Columns → E))

/-- A weighted-sum opening claim over the challenge field. -/
structure Claim (E : Type) (vars : ℕ) where
  /-- The Boolean table of the multilinear weight. -/
  weight : Table E vars
  /-- The claimed inner product. -/
  value : E

/-- Satisfaction of a weighted-sum claim by the message polynomial. -/
@[reducible]
def Claim.Holds {E : Type} [Semiring E] {vars : ℕ}
    (claim : Claim E vars) (f : Table E vars) : Prop :=
  ∑ u, claim.weight u * f u = claim.value

/-- Power batching, with the first input carrying coefficient one. -/
def batch {E : Type} [Semiring E] {vars : ℕ} (claims : List (Claim E vars))
    (r : E) : Claim E vars :=
  ⟨fun u => (claims.zipIdx.map fun (c, i) => r ^ i * c.weight u).sum,
    (claims.zipIdx.map fun (c, i) => r ^ i * c.value).sum⟩

/-- Retain batching powers before repeated coordinate evaluation. -/
@[noinline] def batchPowers {E : Type} [Semiring E] {vars : ℕ}
    (claims : List (Claim E vars)) (r : E) : Claim E vars :=
  let terms := claims.zipIdx.map fun (claim, index) => (r ^ index, claim)
  ⟨fun u => (terms.map fun term => term.1 * term.2.weight u).sum,
    (terms.map fun term => term.1 * term.2.value).sum⟩

/-- Shared batching powers preserve the complete claim. -/
@[csimp] theorem batch_code : @batch = @batchPowers := by
  funext E inst vars claims r
  simp only [batchPowers, batch, List.map_map, Function.comp_def]

/-- Proximity counts absolute column agreements against the original block length. -/
def Close {E : Type} [DecidableEq E] {lanes columns : ℕ}
    (radius : ℝ) (word : MaskedWord E lanes columns) (codeword : Word E lanes columns) : Prop :=
  (1 - radius) * columns ≤ (agreement word codeword).card

/-- Masked proximity uses the decoder's integer agreement cutoff. -/
theorem close_iff_cutoff {E : Type} [DecidableEq E] {lanes columns : ℕ}
    (γ : ℝ) (word : MaskedWord E lanes columns) (codeword : Word E lanes columns) :
    Close γ word codeword ↔ ⌈(1 - γ) * (columns : ℝ)⌉₊ ≤ (agreement word codeword).card := by
  exact Nat.ceil_le.symm

/-- Hiding columns only shrinks a proximity list. -/
theorem Close.mono {E : Type} [DecidableEq E] {lanes columns : ℕ} {radius : ℝ}
    {small large : MaskedWord E lanes columns} {codeword : Word E lanes columns}
    (h : MaskLE small large) (close : Close radius small codeword) :
    Close radius large codeword := by
  exact close.trans (by exact_mod_cast Finset.card_le_card (agreement_mono h codeword))

/-- Every masked list candidate is a candidate of the zero-filled word. -/
theorem Close.zeroFill {E : Type} [Zero E] [DecidableEq E] {lanes columns : ℕ} {radius : ℝ}
    {word : MaskedWord E lanes columns} {codeword : Word E lanes columns}
    (close : Close radius word codeword) : Close radius (fullWord (zeroFill word)) codeword :=
  close.mono (maskLE_zeroFill word)

/-- Full masks recover simultaneous full-word agreement. -/
theorem close_fullWord_iff {E : Type} [DecidableEq E] {lanes columns : ℕ}
    (radius : ℝ) (word codeword : Word E lanes columns) :
    Close radius (fullWord word) codeword ↔ (1 - radius) * columns ≤
      ((Finset.univ.filter fun x => ∀ u, word x u = codeword x u).card : ℝ) := by
  simp only [Close, agreement, fullWord, Function.comp_apply, Option.some.injEq, funext_iff]

/-- Folding is multilinear evaluation of an oracle column in its row coordinates. -/
def foldWord {E : Type} [CommRing E] {lanes columns : ℕ}
    (word : Word E lanes columns) (r : Fin lanes → E) : Fin columns → E :=
  fun x => mle (word x) r

/-- Fold known columns and preserve every hidden column. -/
def foldMaskedWord {E : Type} [CommRing E] {lanes columns : ℕ}
    (word : MaskedWord E lanes columns) (r : Fin lanes → E) : Fin columns → Option E :=
  fun x => (word x).map (fun column => mle column r)

/-- View scalar columns as columns with no row coordinates. -/
def scalarMaskedWord {E : Type} {columns : ℕ} (word : Fin columns → Option E) :
    MaskedWord E 0 columns := fun x => (word x).map (fun y _ => y)

/-- Sampled columns must be known before their values can be used as claims. -/
def queriesKnown {E : Type} {lanes columns queries : ℕ}
    (word : MaskedWord E lanes columns) (xs : Fin queries → Fin columns) : Bool :=
  (List.ofFn xs).all (fun x => (word x).isSome)

/-- The query guard requires each sampled column to be present. -/
theorem queriesKnown_iff {E : Type} {lanes columns queries : ℕ}
    (word : MaskedWord E lanes columns) (xs : Fin queries → Fin columns) :
    queriesKnown word xs = true ↔ ∀ q, (word (xs q)).isSome = true := by
  simp only [queriesKnown, List.all_eq_true, List.forall_mem_ofFn_iff]

/-- Scalar maps preserve full revelation. -/
@[simp] theorem mapMasked_fullWord {F E : Type} {lanes columns : ℕ} (f : F → E)
    (word : Word F lanes columns) :
    mapMasked f (fullWord word) = fullWord (fun x u => f (word x u)) := rfl

/-- Zero filling a fully revealed word recovers that word. -/
@[simp] theorem zeroFill_fullWord {F : Type} [Zero F] {lanes columns : ℕ}
    (word : Word F lanes columns) : zeroFill (fullWord word) = word := rfl

/-- Every query of a fully revealed word is known. -/
@[simp] theorem queriesKnown_fullWord {F : Type} {lanes columns queries : ℕ}
    (word : Word F lanes columns) (xs : Fin queries → Fin columns) :
    queriesKnown (fullWord word) xs = true := by
  apply (queriesKnown_iff _ _).mpr
  intro q
  rfl

/-- Folding a fully revealed word preserves full revelation of its scalar result. -/
@[simp] theorem foldMaskedWord_fullWord {F : Type} [CommRing F] {lanes columns : ℕ}
    (word : Word F lanes columns) (r : Fin lanes → F) :
    foldMaskedWord (fullWord word) r = fun x => some (foldWord word r x) := rfl

/-- Mapping values leaves query availability unchanged. -/
@[simp] theorem queriesKnown_mapMasked {F E : Type} {lanes columns queries : ℕ}
    (f : F → E) (word : MaskedWord F lanes columns) (xs : Fin queries → Fin columns) :
    queriesKnown (mapMasked f word) xs = queriesKnown word xs := by
  simp only [queriesKnown, mapMasked, Option.isSome_map]

/-- Zero fill commutes with scalar extension. -/
theorem zeroFill_mapMasked {F E : Type} [Semiring F] [Semiring E]
    {lanes columns : ℕ} (f : F →+* E) (word : MaskedWord F lanes columns) :
    zeroFill (mapMasked f word) = fun x u => f (zeroFill word x u) := by
  funext x u
  cases h : word x <;> simp only [zeroFill, mapMasked, h, Option.map_none,
    Option.map_some, Option.getD_none, Option.getD_some, Pi.zero_apply, map_zero]

/-- The scalar zero default is the fold of the zero-filled column. -/
theorem foldMaskedWord_getD {F : Type} [CommRing F] {lanes columns : ℕ}
    (word : MaskedWord F lanes columns) (r : Fin lanes → F) (x : Fin columns) :
    (foldMaskedWord word r x).getD 0 = foldWord (zeroFill word) r x := by
  cases h : word x <;> simp only [foldMaskedWord, foldWord, zeroFill, h,
    Option.map_none, Option.map_some, Option.getD_none, Option.getD_some,
    mle, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

/-- Known scalar columns agree with their zero-filled value. -/
theorem scalarColumn_eq {E : Type} [Zero E] {columns : ℕ}
    (word : MaskedWord E 0 columns) (x : Fin columns) (known : (word x).isSome = true) :
    word x = some (fun _ => zeroFill word x Fin.elim0) := by
  cases hc : word x with
  | none => simp only [hc, Option.isSome_none, Bool.false_eq_true] at known
  | some column =>
      simp only [zeroFill, hc, Option.getD_some, Option.some.injEq]
      funext u
      exact congrArg column (Subsingleton.elim _ _)

/-- Encoding commutes with interleaved folding, with no multiplicative-domain hypothesis. -/
theorem fold_interleave {K E : Type} [Semiring K] [CommRing E] {vars lanes : ℕ}
    (enc : Encoding K vars) (ι : K →+* E) (f : Table E (lanes + vars))
    (r : Fin lanes → E) :
    foldWord (enc.interleave ι f) r = enc.encode ι (restrict f r) := by
  funext x
  simp only [foldWord, mle, Encoding.interleave, Encoding.encode, restrict]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro u _
  ring

/-- The transmitted constant and quadratic coefficients of a Boolean sumcheck round. -/
abbrev Quadratic (E : Type) := Sumcheck.CompressedMessage E 1

/-- Evaluate the quadratic reconstructed from the running claim and transmitted pair. -/
def evalQuadratic {E : Type} [CommRing E] (current : E) (q : Quadratic E) (r : E) : E :=
  (Sumcheck.compressedOps 1).evaluate current q r

/-- Reconstruction enforces the Boolean sum at every running claim. -/
theorem evalQuadratic_boolean_sum {E : Type} [CommRing E] (current : E) (q : Quadratic E) :
    evalQuadratic current q 0 + evalQuadratic current q 1 = current := by
  simpa only [evalQuadratic, Sumcheck.compressed_evaluate_eq] using
    Sumcheck.compressed_boolean_sum current q

/-- Transport only the Boolean coordinate indices of a message table. -/
def castTable {E : Type} {n m : ℕ} (h : n = m) (f : Table E n) : Table E m :=
  fun u => f (u ∘ Fin.cast h)

/-- Restrict the first row coordinate of a message, retaining all remaining row coordinates. -/
def foldMessageOne {E : Type} [CommRing E] {lanes vars : ℕ}
    (f : Table E ((lanes + 1) + vars)) (r : E) : Table E (lanes + vars) :=
  restrict (castTable (by omega) f) (fun _ : Fin 1 => r)

/-- Materialize each affine restriction before it enters a later claim history. -/
@[macro_inline] def foldMessageCached {E : Type} [CommRing E] {lanes vars : ℕ}
    (f : Table E ((lanes + 1) + vars)) (r : E) : Table E (lanes + vars) :=
  cacheTable (restrict (castTable (by omega) f) (fun _ : Fin 1 => r))

/-- Shared affine restrictions preserve the complete fold operation. -/
@[csimp] theorem foldMessageOne_code : @foldMessageOne = @foldMessageCached := by
  funext E inst lanes vars f r
  exact (cacheTable_eq _).symm

/-- One affine fold over the row alphabet, with an entire column as one code symbol. -/
def foldRowsOne {E : Type} [CommRing E] {lanes columns : ℕ}
    (word : Word E (lanes + 1) columns) (r : E) : Word E lanes columns :=
  fun x u => (1 - r) * word x (Fin.cons false u) + r * word x (Fin.cons true u)

/-- One affine row fold preserves the mask. -/
def foldMaskedRowsOne {E : Type} [CommRing E] {lanes columns : ℕ}
    (word : MaskedWord E (lanes + 1) columns) (r : E) : MaskedWord E lanes columns :=
  fun x => (word x).map fun column u =>
    (1 - r) * column (Fin.cons false u) + r * column (Fin.cons true u)

/-- Affine row folding preserves inclusion of known columns. -/
theorem foldMaskedRowsOne_mono {E : Type} [CommRing E] {lanes columns : ℕ}
    {small large : MaskedWord E (lanes + 1) columns} (h : MaskLE small large) (r : E) :
    MaskLE (foldMaskedRowsOne small r) (foldMaskedRowsOne large r) := by
  intro x column hx
  cases hs : small x with
  | none => simp only [foldMaskedRowsOne, hs, Option.map_none] at hx; cases hx
  | some value => simpa only [foldMaskedRowsOne, hs, h x value hs, Option.map_some] using hx

/-- A known folded column is the affine fold of a known old column. -/
theorem known_of_foldMaskedRowsOne {E : Type} [CommRing E] {lanes columns : ℕ}
    (word : MaskedWord E (lanes + 1) columns) (r : E) (x : Fin columns)
    (column : Cube lanes → E) (hx : foldMaskedRowsOne word r x = some column) :
    ∃ old, word x = some old := by
  cases hs : word x with
  | none => simp only [foldMaskedRowsOne, hs, Option.map_none] at hx; cases hx
  | some value => exact ⟨value, rfl⟩

end Whir
