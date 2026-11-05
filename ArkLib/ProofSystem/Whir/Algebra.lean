/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.ProofSystem.Whir.Basic
public import ArkLib.ProofSystem.RingSwitching.Packing.Batching
public import Mathlib.Tactic.ComputeDegree

/-!
# Boolean-table identities for WHIR

Coordinate transport, multilinear restrictions and power batching are independent of the
encoding's security parameters. Polynomial collision bounds apply to fixed tables and claims.
-/

@[expose] public section

open scoped BigOperators NNReal ENNReal

namespace Whir

/-- Splitting Boolean coordinates into their row and column blocks. -/
def splitCubeEquiv (n m : ℕ) : Cube (n + m) ≃ Cube n × Cube m where
  toFun u := (fun i => u (Fin.castAdd m i), fun i => u (Fin.natAdd n i))
  invFun uv := Fin.addCases uv.1 uv.2
  left_inv u := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  right_inv uv := by
    rcases uv with ⟨u, v⟩
    simp only [Prod.mk.injEq]
    constructor <;> funext i <;> simp

/-- A cube sum splits into sums over its two coordinate blocks. -/
theorem sum_cube_add {E : Type} [AddCommMonoid E] {n m : ℕ} (f : Table E (n + m)) :
    ∑ u, f u = ∑ v : Cube n, ∑ w : Cube m, f (Fin.addCases v w) := by
  rw [← (splitCubeEquiv n m).symm.sum_comp f, Fintype.sum_prod_type]
  rfl

/-- Separate the first Boolean coordinate from the remaining coordinates. -/
def splitFirstCubeEquiv (n : ℕ) : Cube (n + 1) ≃ Bool × Cube n where
  toFun u := (u 0, Fin.tail u)
  invFun uv := Fin.cons uv.1 uv.2
  left_inv u := Fin.cons_self_tail u
  right_inv uv := by simp only [Fin.cons_zero, Fin.tail_cons]

/-- A Boolean cube sum splits into its first-coordinate false and true slices. -/
theorem sum_cube_succ {E : Type} [AddCommMonoid E] {n : ℕ} (f : Table E (n + 1)) :
    ∑ u, f u = (∑ u, f (Fin.cons false u)) + ∑ u, f (Fin.cons true u) := by
  rw [← (splitFirstCubeEquiv n).symm.sum_comp f, Fintype.sum_prod_type,
    Fintype.sum_bool, add_comm]
  rfl

/-- Equality weights split into the first affine weight and the remaining tensor weight. -/
theorem eqWeight_cons {E : Type} [CommRing E] {n : ℕ} (r : E) (rs : Fin n → E)
    (b : Bool) (u : Cube n) :
    eqWeight (Fin.cons r rs) (Fin.cons b u) = (if b then r else 1 - r) * eqWeight rs u := by
  simp only [eqWeight, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

/-- Equality weights multiply across coordinate blocks. -/
theorem eqWeight_add {E : Type} [CommRing E] {n m : ℕ}
    (r : Fin (n + m) → E) (u : Cube n) (v : Cube m) :
    eqWeight r (Fin.addCases u v) =
      eqWeight (fun i => r (Fin.castAdd m i)) u *
        eqWeight (fun i => r (Fin.natAdd n i)) v := by
  simp only [eqWeight, Fin.prod_univ_add, Fin.addCases_left, Fin.addCases_right]

/-- A single Boolean coordinate contributes its two affine evaluations. -/
theorem sum_cube_one {E : Type} [AddCommMonoid E] (f : Table E 1) :
    ∑ u, f u = f (fun _ => false) + f (fun _ => true) := by
  rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp f, Fintype.sum_bool, add_comm]
  rfl

/-- Coordinate transport is invertible. -/
@[simp]
theorem castTable_inverse {E : Type} {n m : ℕ} (h : n = m) (f : Table E n) :
    castTable h.symm (castTable h f) = f := by
  subst m
  rfl

/-- Weighted claims commute with transport of their Boolean coordinates. -/
theorem claim_cast_holds {E : Type} [Semiring E] {n m : ℕ} (h : n = m)
    (weight f : Table E n) (value : E) :
    (⟨castTable h weight, value⟩ : Claim E m).Holds (castTable h f) ↔
      (⟨weight, value⟩ : Claim E n).Holds f := by
  subst m
  rfl

/-- The zero-row encoder is the scalar encoder, after removing the empty row coordinates. -/
theorem interleave_zero {K E : Type} [Semiring K] [Semiring E] {vars : ℕ}
    (enc : Encoding K vars) (ι : K →+* E) (f : Table E vars) :
    enc.interleave ι (castTable (Nat.zero_add vars).symm f) =
      fun x (_ : Cube 0) => enc.encode ι f x := by
  funext x u
  unfold Encoding.interleave Encoding.encode castTable
  apply Finset.sum_congr rfl
  intro v _
  congr 1
  apply congrArg f
  funext i
  change Fin.addCases u v (Fin.cast (Nat.zero_add vars).symm i) = v i
  rw [show Fin.cast (Nat.zero_add vars).symm i = Fin.natAdd 0 i from Fin.ext (by simp)]
  exact Fin.addCases_right i

/-- One fold is affine interpolation between the first-coordinate Boolean slices. -/
theorem foldMessageOne_apply {E : Type} [CommRing E] {lanes vars : ℕ}
    (f : Table E ((lanes + 1) + vars)) (r : E) (u : Cube (lanes + vars)) :
    foldMessageOne f r u =
      (1 - r) * castTable (by omega) f (Fin.addCases (fun _ : Fin 1 => false) u) +
        r * castTable (by omega) f (Fin.addCases (fun _ : Fin 1 => true) u) := by
  unfold foldMessageOne restrict
  rw [sum_cube_one]
  simp only [eqWeight, Fin.prod_univ_one, Bool.false_eq_true, ite_false, ite_true]

/-- The one-coordinate transport respects the row/message coordinate split. -/
theorem castTable_first_split {E : Type} {lanes vars : ℕ}
    (f : Table E ((lanes + 1) + vars)) (b : Bool) (u : Cube lanes) (v : Cube vars) :
    castTable (by omega) f (Fin.addCases (fun _ : Fin 1 => b) (Fin.addCases u v)) =
      f (Fin.addCases (Fin.cons b u) v) := by
  apply congrArg f
  funext i
  change (Fin.addCases (fun _ : Fin 1 => b) (Fin.addCases u v) : Cube (1 + (lanes + vars)))
    (Fin.cast (by omega) i) = (Fin.addCases (Fin.cons b u) v : Cube ((lanes + 1) + vars)) i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · rw [show Fin.cast (by omega) (Fin.castAdd vars (0 : Fin (lanes + 1))) =
          Fin.castAdd (lanes + vars) (0 : Fin 1) from Fin.ext (by simp)]
      simp only [Fin.addCases_left, Fin.cons_zero]
    · rw [show Fin.cast (by omega) (Fin.castAdd vars j.succ) =
          Fin.natAdd 1 (Fin.castAdd vars j) from Fin.ext (by simp; omega)]
      simp only [Fin.addCases_right, Fin.addCases_left, Fin.cons_succ]
  · rw [show Fin.cast (by omega) (Fin.natAdd (lanes + 1) j) =
        Fin.natAdd 1 (Fin.natAdd lanes j) from Fin.ext (by simp; omega)]
    simp only [Fin.addCases_right]

/-- One affine row fold commutes with interleaved encoding. -/
theorem foldRowsOne_interleave {K E : Type} [Semiring K] [CommRing E] {vars lanes : ℕ}
    (enc : Encoding K vars) (ι : K →+* E) (f : Table E ((lanes + 1) + vars)) (r : E) :
    foldRowsOne (enc.interleave ι f) r = enc.interleave ι (foldMessageOne f r) := by
  funext x u
  simp only [foldRowsOne, Encoding.interleave, Encoding.encode, foldMessageOne_apply,
    castTable_first_split, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  ring

/-- Sequential restriction in the first coordinate equals restriction by the full vector. -/
theorem restrict_foldMessageOne {E : Type} [CommRing E] {lanes vars : ℕ}
    (f : Table E ((lanes + 1) + vars)) (r : E) (rs : Fin lanes → E) :
    restrict (foldMessageOne f r) rs = restrict f (Fin.cons r rs) := by
  funext v
  simp only [restrict, foldMessageOne_apply, castTable_first_split]
  rw [sum_cube_succ]
  simp only [eqWeight_cons, Bool.false_eq_true, ite_false, ite_true]
  simp_rw [mul_add, Finset.sum_add_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro u _ <;> ring

/-- An empty restriction only removes the empty coordinate block. -/
theorem restrict_zero {E : Type} [CommRing E] {vars : ℕ} (f : Table E (0 + vars)) :
    restrict f (Fin.elim0 : Fin 0 → E) = castTable (Nat.zero_add vars) f := by
  funext v
  simp only [restrict, eqWeight, Fin.prod_univ_zero, one_mul, Fintype.sum_unique, castTable]
  apply congrArg f
  funext i
  have hi : i = Fin.natAdd 0 (Fin.cast (Nat.zero_add vars) i) := Fin.ext (by simp)
  conv_lhs => rw [hi, Fin.addCases_right]
  rfl

/-- Multilinear evaluation may be performed one coordinate at a time. -/
theorem mle_cons {E : Type} [CommRing E] {n : ℕ} (f : Table E (n + 1))
    (r : E) (rs : Fin n → E) :
    mle f (Fin.cons r rs) = mle
      (fun u => (1 - r) * f (Fin.cons false u) + r * f (Fin.cons true u)) rs := by
  unfold mle
  rw [sum_cube_succ]
  simp only [eqWeight_cons, Bool.false_eq_true, ite_false, ite_true]
  simp_rw [mul_add, Finset.sum_add_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro u _ <;> ring

/-- Sequential row folds equal folding at the full public challenge vector. -/
theorem foldWord_cons {E : Type} [CommRing E] {lanes columns : ℕ}
    (word : Word E (lanes + 1) columns) (r : E) (rs : Fin lanes → E) :
    foldWord (foldRowsOne word r) rs = foldWord word (Fin.cons r rs) := by
  funext x
  exact (mle_cons (word x) r rs).symm

/-- Folding no rows returns the unique entry of the empty Boolean row. -/
theorem foldWord_zero {E : Type} [CommRing E] {columns : ℕ}
    (word : Word E 0 columns) : foldWord word (Fin.elim0 : Fin 0 → E) =
      fun x => word x Fin.elim0 := by
  funext x
  simp only [foldWord, mle, eqWeight, Fin.prod_univ_zero, one_mul, Fintype.sum_unique]
  rfl

/-- Appending an empty coordinate block does not change a Boolean vector. -/
theorem addCases_empty {n : ℕ} (u : Cube n) (v : Cube 0) :
    (Fin.addCases u v : Cube (n + 0)) = u := by
  funext i
  have hi : i = Fin.castAdd 0 i := Fin.ext rfl
  conv_lhs => rw [hi, Fin.addCases_left]

/-- With no encoding coordinates, the message fold is the ordinary first-coordinate affine fold. -/
theorem foldMessageOne_zero_apply {E : Type} [CommRing E] {n : ℕ}
    (f : Table E (n + 1)) (r : E) (u : Cube n) :
    foldMessageOne (vars := 0) f r u =
      (1 - r) * f (Fin.cons false u) + r * f (Fin.cons true u) := by
  rw [foldMessageOne_apply]
  have hfalse := castTable_first_split (vars := 0) f false u Fin.elim0
  have htrue := castTable_first_split (vars := 0) f true u Fin.elim0
  simp only [addCases_empty] at hfalse htrue
  rw [hfalse, htrue]

/-- Multilinear evaluation of an ordinary one-coordinate restriction. -/
theorem mle_foldMessageOne {E : Type} [CommRing E] {n : ℕ}
    (f : Table E (n + 1)) (r : E) (rs : Fin n → E) :
    mle (foldMessageOne (vars := 0) f r) rs = mle f (Fin.cons r rs) := by
  rw [mle_cons]
  congr 1
  funext u
  exact foldMessageOne_zero_apply f r u

/-- Ordered batching coefficients can be indexed by the finite set of list positions. -/
theorem zipIdx_eq_ofFn {α : Type} (xs : List α) :
    xs.zipIdx = List.ofFn (fun i : Fin xs.length => (xs[i], i.val)) := by
  apply List.ext_getElem <;> simp

/-- Batching satisfaction is equality of the two power-weighted value families. -/
theorem batch_holds_iff {E : Type} [CommRing E] {n : ℕ}
    (claims : List (Claim E n)) (f : Table E n) (r : E) :
    (batch claims r).Holds f ↔
      (∑ i : Fin claims.length, r ^ i.val * ∑ u, claims[i].weight u * f u) =
        ∑ i : Fin claims.length, r ^ i.val * claims[i].value := by
  unfold Claim.Holds batch
  simp only [zipIdx_eq_ofFn, List.map_ofFn, List.sum_ofFn, Function.comp_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

/-- Every input claim implies their power batch. -/
theorem batch_holds {E : Type} [CommRing E] {n : ℕ}
    (claims : List (Claim E n)) (f : Table E n) (r : E)
    (h : ∀ c ∈ claims, c.Holds f) : (batch claims r).Holds f := by
  rw [batch_holds_iff]
  apply Finset.sum_congr rfl
  intro i _
  rw [h claims[i] (List.getElem_mem i.isLt)]

/-- A fixed false family can satisfy its power batch only at a polynomial collision. -/
theorem prob_batch_fixed_le {E : Type} [Field E] [Fintype E] [SampleableType E] {n : ℕ}
    (claims : List (Claim E n)) (f : Table E n)
    (lost : ∃ c ∈ claims, ¬ c.Holds f) :
    Pr{let r ←$ᵗ E}[(batch claims r).Holds f] ≤
      ((claims.length - 1 : ℕ) : ENNReal) / Fintype.card E := by
  classical
  have different : (fun i : Fin claims.length => ∑ u, claims[i].weight u * f u) ≠
      (fun i : Fin claims.length => claims[i].value) := by
    intro heq
    obtain ⟨c, hc, hfalse⟩ := lost
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    exact hfalse (congrFun heq ⟨i, hi⟩)
  have h := (RingSwitching.Packing.BatchingStrategy.gammaPowers E claims.length).separates
    _ _ different
  change Pr{let r ←$ᵗ E}[
    (∑ i : Fin claims.length, r ^ i.val * ∑ u, claims[i].weight u * f u) =
      ∑ i : Fin claims.length, r ^ i.val * claims[i].value] ≤
    (((claims.length - 1 : ℕ) : ℝ≥0) / (Fintype.card E : ℝ≥0) : ℝ≥0) at h
  rw [ENNReal.coe_div (by simp), ENNReal.coe_natCast, ENNReal.coe_natCast] at h
  simpa only [batch_holds_iff] using h

/-- Boolean tables and `Fin 2` tables use the same ordered coordinate values. -/
def cubeFinTwoEquiv (n : ℕ) : (Fin n → Fin 2) ≃ Cube n :=
  Equiv.arrowCongr (Equiv.refl _) finTwoEquiv

/-- Multilinear evaluation agrees with the equality-kernel expansion on `Fin 2`. -/
theorem mle_eq_finTwo {E : Type} [CommRing E] {n : ℕ} (f : Table E n)
    (r : Fin n → E) :
    mle f r = ∑ u : Fin n → Fin 2,
      MvPolynomial.eqTilde (u : Fin n → E) r * f (cubeFinTwoEquiv n u) := by
  rw [mle, ← (cubeFinTwoEquiv n).sum_comp]
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  rw [MvPolynomial.eqTilde_eq_prod]
  apply Finset.prod_congr rfl
  intro i _
  have scalar (b : Fin 2) : (if finTwoEquiv b then r i else 1 - r i) =
      (b : E) * r i + (1 - (b : E)) * (1 - r i) := by
    fin_cases b <;> simp [finTwoEquiv]
  exact scalar (u i)

/-- Two distinct fixed Boolean tables collide at a random point with probability at most `n/q`. -/
theorem prob_mle_collision_le {E : Type} [Field E] [Fintype E] [SampleableType E]
    {n : ℕ} (f g : Table E n) (different : f ≠ g) :
    Pr{let r ←$ᵗ (Fin n → E)}[mle f r = mle g r] ≤
      (n : ENNReal) / Fintype.card E := by
  have hne : (fun u => f (cubeFinTwoEquiv n u)) ≠ (fun u => g (cubeFinTwoEquiv n u)) := by
    intro h
    apply different
    funext u
    simpa only [Equiv.apply_symm_apply] using congrFun h ((cubeFinTwoEquiv n).symm u)
  have h := (RingSwitching.Packing.BatchingStrategy.eqFold E n).separates _ _ hne
  change Pr{let r ←$ᵗ (Fin n → E)}[
    (∑ u : Fin n → Fin 2, MvPolynomial.eqTilde (u : Fin n → E) r *
      f (cubeFinTwoEquiv n u)) =
    ∑ u : Fin n → Fin 2, MvPolynomial.eqTilde (u : Fin n → E) r *
      g (cubeFinTwoEquiv n u)] ≤ ((n : ℝ≥0) / (Fintype.card E : ℝ≥0) : ℝ≥0) at h
  rw [ENNReal.coe_div (by simp), ENNReal.coe_natCast, ENNReal.coe_natCast] at h
  simpa only [mle_eq_finTwo] using h

/-- A finite list union costs at most its length times the uniform per-member error. -/
theorem prob_exists_list_le {α β : Type} (sample : ProbComp α)
    (candidates : List β) (event : β → α → Prop) (ε : ENNReal)
    (bound : ∀ f ∈ candidates, Pr{let r ← sample}[event f r] ≤ ε) :
    Pr{let r ← sample}[∃ f ∈ candidates, event f r] ≤ candidates.length * ε := by
  classical
  have h := prEvent_exists_finset_le_card_mul candidates.toFinset sample event
    (fun f hf => bound f (List.mem_toFinset.mp hf))
  simp only [List.mem_toFinset] at h
  refine h.trans ?_
  gcongr
  exact_mod_cast List.toFinset_card_le candidates

/-- Collision events over distinct members cost one error per unordered pair. -/
theorem prob_pair_collision_le {α β δ : Type}
    (sample : ProbComp α) (candidates : Finset β) (value : β → α → δ)
    (ε : ENNReal)
    (bound : ∀ f ∈ candidates, ∀ g ∈ candidates, f ≠ g →
      Pr{let r ← sample}[value f r = value g r] ≤ ε) :
    Pr{let r ← sample}[∃ f ∈ candidates, ∃ g ∈ candidates,
      f ≠ g ∧ value f r = value g r] ≤ (candidates.card.choose 2 : ENNReal) * ε := by
  classical
  let pairs := candidates.powersetCard 2
  let event := fun (pair : Finset β) r => ∃ f g,
    pair = {f, g} ∧ f ≠ g ∧ value f r = value g r
  have inclusion := prEvent_mono sample (fun r => ∃ f ∈ candidates, ∃ g ∈ candidates,
    f ≠ g ∧ value f r = value g r) (fun r => ∃ pair ∈ pairs, event pair r) (by
    rintro r ⟨f, hf, g, hg, hne, heq⟩
    refine ⟨{f, g}, Finset.mem_powersetCard.mpr ⟨?_, Finset.card_pair hne⟩,
      f, g, rfl, hne, heq⟩
    simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hf hg)
  have per : ∀ pair ∈ pairs, Pr{let r ← sample}[event pair r] ≤ ε := by
    intro pair hp
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hp
    obtain ⟨f, g, hne, rfl⟩ := Finset.card_eq_two.mp hcard
    refine (prEvent_mono sample _ (fun r => value f r = value g r) ?_).trans
      (bound f (hsub (by simp)) g (hsub (by simp)) hne)
    rintro r ⟨f', g', heq, hne', heval⟩
    have hf' : f' = f ∨ f' = g := by
      have : f' ∈ ({f, g} : Finset β) := heq ▸ Finset.mem_insert_self f' {g'}
      simpa only [Finset.mem_insert, Finset.mem_singleton] using this
    have hg' : g' = f ∨ g' = g := by
      have : g' ∈ ({f, g} : Finset β) := heq ▸
        Finset.mem_insert_of_mem (Finset.mem_singleton_self g')
      simpa only [Finset.mem_insert, Finset.mem_singleton] using this
    rcases hf' with rfl | rfl <;> rcases hg' with rfl | rfl
    · exact (hne' rfl).elim
    · exact heval
    · exact heval.symm
    · exact (hne' rfl).elim
  simpa only [pairs, Finset.card_powersetCard] using inclusion.trans
    (prEvent_exists_finset_le_card_mul pairs sample event per)

/-- A real list budget preserves the unrounded `dL/q` union error. -/
theorem list_union_error_le {E : Type} [Fintype E] [Nonempty E] (length d : ℕ)
    (L : ℝ) (hL : (length : ℝ) ≤ L) :
    (length : ENNReal) * ((d : ENNReal) / Fintype.card E) ≤
      ENNReal.ofReal (d * L / Fintype.card E) := by
  have hcard : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  rw [ENNReal.ofReal_div_of_pos hcard, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  have hlen : (length : ENNReal) ≤ ENNReal.ofReal L := by
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hL
  calc
    _ = ((d : ENNReal) * length) / Fintype.card E := by
      simp only [div_eq_mul_inv, mul_assoc, mul_comm]
    _ ≤ _ := by gcongr

/-- The affine polynomial of a table in its first coordinate, with the other bits fixed. -/
noncomputable def affineSlice {E : Type} [CommRing E] {lanes vars : ℕ}
    (f : Table E ((lanes + 1) + vars)) (u : Cube (lanes + vars)) : Polynomial E :=
  Polynomial.C (castTable (by omega) f (Fin.addCases (fun _ : Fin 1 => false) u)) *
      (1 - Polynomial.X) +
    Polynomial.C (castTable (by omega) f (Fin.addCases (fun _ : Fin 1 => true) u)) * Polynomial.X

/-- The honest quadratic for one weighted Boolean Sumcheck round. -/
noncomputable def foldPolynomial {E : Type} [CommRing E] {lanes vars : ℕ}
    (weight f : Table E ((lanes + 1) + vars)) : Polynomial E :=
  ∑ u, affineSlice weight u * affineSlice f u

/-- The three transmitted coefficients interpreted as an ordinary polynomial. -/
noncomputable def quadraticPolynomial {E : Type} [CommRing E] (q : Quadratic E) : Polynomial E :=
  Polynomial.C (q 0) + Polynomial.C (q 1) * Polynomial.X + Polynomial.C (q 2) * Polynomial.X ^ 2

/-- Evaluation of the honest quadratic is the folded weighted inner product. -/
theorem foldPolynomial_eval {E : Type} [CommRing E] {lanes vars : ℕ}
    (weight f : Table E ((lanes + 1) + vars)) (r : E) :
    (foldPolynomial weight f).eval r = ∑ u, foldMessageOne weight r u * foldMessageOne f r u := by
  simp only [foldPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul, affineSlice,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_one, Polynomial.eval_X, foldMessageOne_apply]
  apply Finset.sum_congr rfl
  intro u _
  ring

/-- The honest weighted round polynomial has degree at most two. -/
theorem foldPolynomial_degree {E : Type} [CommRing E] {lanes vars : ℕ}
    (weight f : Table E ((lanes + 1) + vars)) : (foldPolynomial weight f).natDegree ≤ 2 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro u _
  unfold affineSlice
  compute_degree

/-- The transmitted polynomial evaluates to the protocol's explicit quadratic evaluator. -/
theorem quadraticPolynomial_eval {E : Type} [CommRing E] (q : Quadratic E) (r : E) :
    (quadraticPolynomial q).eval r = evalQuadratic q r := by
  simp only [quadraticPolynomial, evalQuadratic, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

/-- The transmitted polynomial has degree at most two. -/
theorem quadraticPolynomial_degree {E : Type} [CommRing E] (q : Quadratic E) :
    (quadraticPolynomial q).natDegree ≤ 2 := by
  unfold quadraticPolynomial
  compute_degree

/-- A sum is invariant under coordinate transport. -/
theorem sum_castTable {E : Type} [AddCommMonoid E] {n m : ℕ}
    (h : n = m) (f : Table E n) : ∑ u, castTable h f u = ∑ u, f u := by
  subst m
  rfl

/-- The honest polynomial's two Boolean values sum to the old inner product. -/
theorem foldPolynomial_boolean_sum {E : Type} [CommRing E] {lanes vars : ℕ}
    (weight f : Table E ((lanes + 1) + vars)) :
    (foldPolynomial weight f).eval 0 + (foldPolynomial weight f).eval 1 =
      ∑ u, weight u * f u := by
  rw [foldPolynomial_eval, foldPolynomial_eval]
  simp only [foldMessageOne_apply, sub_zero, one_mul, zero_mul, add_zero, sub_self, zero_add]
  let h : (lanes + 1) + vars = 1 + (lanes + vars) := by omega
  let g := castTable h (fun u => weight u * f u)
  have heq : (∑ u, castTable h weight (Fin.addCases (fun _ : Fin 1 => false) u) *
      castTable h f (Fin.addCases (fun _ : Fin 1 => false) u)) +
      (∑ u, castTable h weight (Fin.addCases (fun _ : Fin 1 => true) u) *
      castTable h f (Fin.addCases (fun _ : Fin 1 => true) u)) = ∑ u, g u := by
    rw [sum_cube_add (n := 1) (m := lanes + vars), sum_cube_one]
    rfl
  exact heq.trans (sum_castTable h _)

/-- A false fixed weighted claim survives one checked round only at a quadratic collision. -/
theorem prob_fold_fixed_le {E : Type} [Field E] [Fintype E] [SampleableType E]
    {lanes vars : ℕ} (candidate : Table E ((lanes + 1) + vars))
    (claim : Claim E ((lanes + 1) + vars)) (q : Quadratic E)
    (check : evalQuadratic q 0 + evalQuadratic q 1 = claim.value)
    (lost : ¬ claim.Holds candidate) :
    Pr{let r ←$ᵗ E}[
      (⟨foldMessageOne claim.weight r, evalQuadratic q r⟩ : Claim E (lanes + vars)).Holds
        (foldMessageOne candidate r)] ≤ (2 : ENNReal) / Fintype.card E := by
  have different : foldPolynomial claim.weight candidate ≠ quadraticPolynomial q := by
    intro same
    apply lost
    change (∑ u, claim.weight u * candidate u) = claim.value
    rw [← foldPolynomial_boolean_sum, same, quadraticPolynomial_eval, quadraticPolynomial_eval]
    exact check
  have h := Probability.prob_polynomial_eval_eq_le different
    (foldPolynomial_degree claim.weight candidate) (quadraticPolynomial_degree q)
  simpa only [foldPolynomial_eval, quadraticPolynomial_eval, Claim.Holds, Nat.cast_ofNat] using h

end Whir
