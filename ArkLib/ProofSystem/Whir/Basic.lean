/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon

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

/-- An interleaved word, queried one complete column at a time. -/
abbrev Word (F : Type) (lanes columns : ℕ) := Fin columns → Cube lanes → F

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

/-- Column distance uses simultaneous agreement in every interleaved row. -/
def Close {E : Type} [DecidableEq E] {lanes columns : ℕ}
    (radius : ℝ) (word codeword : Word E lanes columns) : Prop :=
  (1 - radius) * columns ≤
    ((Finset.univ.filter fun x => ∀ u, word x u = codeword x u).card : ℝ)

/-- Folding is multilinear evaluation of an oracle column in its row coordinates. -/
def foldWord {E : Type} [CommRing E] {lanes columns : ℕ}
    (word : Word E lanes columns) (r : Fin lanes → E) : Fin columns → E :=
  fun x => mle (word x) r

/-- Encoding commutes with interleaved folding, with no multiplicative-domain hypothesis. -/
theorem fold_interleave {K E : Type} [Semiring K] [CommRing E] {vars lanes : ℕ}
    (enc : Encoding K vars) (ι : K →+* E) (f : Table E (lanes + vars))
    (r : Fin lanes → E) :
    foldWord (enc.interleave ι f) r = enc.encode ι (restrict f r) := by
  sorry

/-- One Boolean sumcheck message, sent as its three coefficients. -/
abbrev Quadratic (E : Type) := Fin 3 → E

/-- Evaluation of a degree-at-most-two sumcheck message. -/
def evalQuadratic {E : Type} [Semiring E] (q : Quadratic E) (r : E) : E :=
  q 0 + q 1 * r + q 2 * r ^ 2

end Whir
