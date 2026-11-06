/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.ProofSystem.Whir.Knowledge
public import ArkLib.ProofSystem.Whir.Algebra
public import ArkLib.ProofSystem.Whir.Parameters
public import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved
public import ArkLib.Data.CodingTheory.ReedSolomon.PowerAgreement
public import ArkLib.Data.CodingTheory.ReedSolomon.ScalarDescent
public import ArkLib.Data.CodingTheory.ProximityGenerator.ListPreimages

/-!
# Encoding adapters for WHIR proximity lists

The encoder contract identifies every row with an ordinary Reed–Solomon codeword.
Column proximity and interleaved Johnson counting use the same block metric.
-/

@[expose] public section

namespace Whir

/-- Exhaustive classical proximity enumeration; an efficient decoder can refine this list. -/
noncomputable def nearbyDecoder {K E : Type} [Semiring K] [Semiring E] [Fintype E]
    [DecidableEq E] {vars : ℕ} (enc : Encoding K vars) (ι : K →+* E) (γ : ℝ)
    (lanes : ℕ) : ListDecoder (E := E) enc lanes := by
  classical
  exact ⟨fun word => (Finset.univ.filter fun f => Close γ word (enc.interleave ι f)).toList⟩


/-- Column proximity is the relative Hamming bound on whole columns. -/
theorem close_iff_relHammingDist {E : Type} [DecidableEq E] {lanes columns : ℕ}
    (hcolumns : 0 < columns) (γ : ℝ) (word codeword : Word E lanes columns) :
    Close γ word codeword ↔ (Code.relHammingDist word codeword : ℝ) ≤ γ := by
  classical
  have hn : (0 : ℝ) < columns := by exact_mod_cast hcolumns
  rw [Code.relHammingDist_coe, Fintype.card_fin, div_le_iff₀ hn]
  have hsum : (Code.agree word codeword : ℝ) + (hammingDist word codeword : ℝ) = columns := by
    have h := Code.agree_add_hammingDist (u := word) (v := codeword)
    rw [Fintype.card_fin] at h
    exact_mod_cast h
  have ha : Code.agree word codeword =
      (Finset.univ.filter fun x => ∀ u, word x u = codeword x u).card := by
    simp only [Code.agree, funext_iff]
  rw [ha] at hsum
  unfold Close
  constructor <;> intro h <;> nlinarith

/-- Interleaved encoding is injective whenever the scalar encoder is injective. -/
theorem interleave_injective {K E : Type} [Field K] [Field E] {vars lanes : ℕ}
    (enc : Encoding K vars) (ι : K →+* E) (contract : EncodingContract enc ι) :
    Function.Injective (enc.interleave (lanes := lanes) ι) := by
  intro f g hfg
  funext u
  obtain ⟨⟨v, w⟩, rfl⟩ := (splitCubeEquiv lanes vars).symm.surjective u
  exact congrFun (contract.injective (funext fun x => congrFun (congrFun hfg x) v)) w

/-- Every encoded row is a Reed–Solomon codeword on the extended domain. -/
theorem interleave_mem {K E : Type} [Field K] [Field E] {vars lanes : ℕ}
    (enc : Encoding K vars) (ι : K →+* E) (contract : EncodingContract enc ι)
    (f : Table E (lanes + vars)) :
    enc.interleave ι f ∈
      ((ReedSolomon.code (enc.extendedDomain ι) (2 ^ vars))^⋈(Cube lanes)) := by
  intro u
  rw [← contract.image]
  exact ⟨_, rfl⟩

/-- Every array of Reed–Solomon rows is the encoding of a message table. -/
theorem interleave_surjective {K E : Type} [Field K] [Field E] {vars lanes : ℕ}
    (enc : Encoding K vars) (ι : K →+* E) (contract : EncodingContract enc ι)
    (word : Word E lanes (2 ^ (vars + enc.rate)))
    (mem : word ∈ ((ReedSolomon.code (enc.extendedDomain ι) (2 ^ vars))^⋈(Cube lanes))) :
    ∃ f, enc.interleave ι f = word := by
  classical
  have rows : ∀ u, ∃ f, enc.encode ι f = fun x => word x u := by
    intro u
    have hu := mem u
    rw [← contract.image] at hu
    exact hu
  choose f hf using rows
  refine ⟨fun u => f ((splitCubeEquiv lanes vars u).1) ((splitCubeEquiv lanes vars u).2), ?_⟩
  funext x u
  change enc.encode ι (fun v => f (fun i => Fin.addCases u v (Fin.castAdd vars i))
    (fun i => Fin.addCases u v (Fin.natAdd lanes i))) x = word x u
  simpa only [Fin.addCases_left, Fin.addCases_right] using congrFun (hf u) x

/-- Encoding a lifted base-field message equals lifting its encoded values. -/
theorem encode_scalar_extension {K E : Type} [CommSemiring K] [CommSemiring E]
    {vars : ℕ} (enc : Encoding K vars) (ι : K →+* E) (f : Table K vars) :
    enc.encode ι (fun u => ι (f u)) = fun x => ι (enc.encode (RingHom.id K) f x) := by
  funext x
  simp only [Encoding.encode, RingHom.id_apply, map_sum, map_mul]

/-- Interleaved encoding commutes with extension of the message coefficients. -/
theorem interleave_scalar_extension {K E : Type} [CommSemiring K] [CommSemiring E]
    {vars lanes : ℕ} (enc : Encoding K vars) (ι : K →+* E) (f : Table K (lanes + vars)) :
    enc.interleave ι (fun u => ι (f u)) =
      fun x u => ι (enc.interleave (RingHom.id K) f x u) := by
  funext x u
  exact congrFun (encode_scalar_extension enc ι (fun v => f (Fin.addCases u v))) x

/-- The affine MCA input consists of the zero slice and the difference of the two slices. -/
def foldMcaInput {E : Type} [Ring E] {lanes columns : ℕ}
    (word : Word E (lanes + 1) columns) : Fin 2 → Word E lanes columns :=
  ![fun x u => word x (Fin.cons false u),
    fun x u => word x (Fin.cons true u) - word x (Fin.cons false u)]

/-- Outside MCA, every nearby folded polynomial has an old nearby polynomial preimage.
This is a deterministic coding statement, separate from Sumcheck and list union probabilities. -/
theorem fold_preimage_of_not_isMCA {K E : Type} [Field K] [Field E] [DecidableEq E]
    [Fintype E] {vars lanes : ℕ} (enc : Encoding K vars) (ι : K →+* E)
    (contract : EncodingContract enc ι) (sec : LevelSecurity) (valid : sec.Valid enc)
    (word : Word E (lanes + 1) (2 ^ (vars + enc.rate))) (r : E)
    (good : ¬ CoreDefinitions.IsMCA (CoreDefinitions.AffineLineGenerator E)
      ((ReedSolomon.code (enc.extendedDomain ι) (2 ^ vars))^⋈(Cube lanes))
      r (foldMcaInput word) (radius enc sec))
    (f : Table E (lanes + vars))
    (close : Close (radius enc sec) (foldRowsOne word r) (enc.interleave ι f)) :
    ∃ g, Close (radius enc sec) word (enc.interleave ι g) ∧ foldMessageOne g r = f := by
  classical
  let C := (ReedSolomon.code (enc.extendedDomain ι) (2 ^ vars))^⋈(Cube lanes)
  let T := Finset.univ.filter fun x => ∀ u,
    foldRowsOne word r x u = enc.interleave ι f x u
  have combination : (fun x => ∑ j, CoreDefinitions.AffineLineGenerator E r j •
      foldMcaInput word j x) = foldRowsOne word r := by
    funext x u
    simp only [CoreDefinitions.AffineLineGenerator, Fin.sum_univ_two, foldMcaInput,
      Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      one_mul, foldRowsOne]
    ring
  have hdim : 2 ^ vars ≤ ⌈(Fintype.card enc.Columns : ℝ) * (1 - radius enc sec)⌉₊ := by
    have hbound : (2 ^ vars : ℝ) ≤
        (Fintype.card enc.Columns : ℝ) * (1 - radius enc sec) := by
      simpa only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, mul_comm] using
        (dimension_lt_agreement valid).le
    have h := hbound.trans (Nat.le_ceil
      ((Fintype.card enc.Columns : ℝ) * (1 - radius enc sec)))
    exact_mod_cast h
  have hdet := (ReedSolomon.determinedByAgreement_code (enc.extendedDomain ι) hdim
    ).moduleInterleavedCode (κ := Cube lanes)
  have large : (Fintype.card enc.Columns : ℝ) * (1 - radius enc sec) ≤ T.card := by
    simpa only [Close, T, Fintype.card_fin, mul_comm] using close
  obtain ⟨p, hp, hcomb, hexact⟩ := CoreDefinitions.list_preimages_of_not_isMCA
    (CoreDefinitions.AffineLineGenerator E) C (radius enc sec) hdet r (foldMcaInput word)
    good (enc.interleave ι f) (interleave_mem enc ι contract f) T large (by
      intro x hx
      rw [congrFun combination x]
      exact funext fun u => ((Finset.mem_filter.mp hx).2 u).symm)
  have rows (j : Fin 2) (u : Cube lanes) :
      (fun x => p j x u) ∈ ReedSolomon.code (enc.extendedDomain ι) (2 ^ vars) := by
    have heq : Matrix.transpose (p j) u = (fun x => p j x u) := by
      funext x
      exact Matrix.transpose_apply _ _ _
    rw [← heq]
    exact hp j u
  let old : Word E (lanes + 1) (2 ^ (vars + enc.rate)) := fun x u =>
    if u 0 then p 0 x (Fin.tail u) + p 1 x (Fin.tail u) else p 0 x (Fin.tail u)
  have old_mem : old ∈
      ((ReedSolomon.code (enc.extendedDomain ι) (2 ^ vars))^⋈(Cube (lanes + 1))) := by
    intro u
    change (fun x => if u 0 then p 0 x (Fin.tail u) + p 1 x (Fin.tail u)
      else p 0 x (Fin.tail u)) ∈ ReedSolomon.code (enc.extendedDomain ι) (2 ^ vars)
    by_cases hb : u 0 = true
    · simp only [hb, ite_true]
      have heq : ((fun x => p 0 x (Fin.tail u)) + (fun x => p 1 x (Fin.tail u))) =
          (fun x => p 0 x (Fin.tail u) + p 1 x (Fin.tail u)) := by
        funext x
        exact Pi.add_apply _ _ _
      rw [← heq]
      exact (ReedSolomon.code _ _).add_mem (rows 0 (Fin.tail u)) (rows 1 (Fin.tail u))
    · simpa only [hb, Bool.false_eq_true, ite_false] using rows 0 (Fin.tail u)
  obtain ⟨g, hg⟩ := interleave_surjective enc ι contract old old_mem
  have old_close : Close (radius enc sec) word old := by
    unfold Close
    rw [show (1 - radius enc sec) * (2 ^ (vars + enc.rate) : ℕ) =
      (Fintype.card enc.Columns : ℝ) * (1 - radius enc sec) by
        simp only [Fintype.card_fin, mul_comm]]
    refine large.trans ?_
    exact_mod_cast Finset.card_le_card (show T ⊆ _ from by
      intro x hx
      have hx' : enc.interleave ι f x = ∑ j,
          CoreDefinitions.AffineLineGenerator E r j • foldMcaInput word j x := by
        rw [congrFun combination x]
        exact funext fun u => ((Finset.mem_filter.mp hx).2 u).symm
      have he := (hexact x).mp hx'
      have h0 := he 0
      have h1 := he 1
      simp only [foldMcaInput, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, fun u => ?_⟩
      dsimp [old]
      rw [h0, h1]
      cases hb : u 0 <;> simp only [Bool.false_eq_true, ite_false, ite_true]
      · congr 1
        simpa only [hb] using (Fin.cons_self_tail u).symm
      · rw [add_sub_cancel]
        congr 1
        simpa only [hb] using (Fin.cons_self_tail u).symm)
  refine ⟨g, hg ▸ old_close, interleave_injective enc ι contract ?_⟩
  rw [← foldRowsOne_interleave, hg, hcomb]
  funext x u
  simp only [foldRowsOne, old, Fin.cons_zero, Fin.tail_cons, Bool.false_eq_true,
    ite_false, ite_true, CoreDefinitions.AffineLineGenerator, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul]
  ring

/-- Classical proximity enumeration satisfies the Johnson contract without a row factor. -/
theorem nearbyDecoder_correct {K E : Type} [Field K] [Field E] [DecidableEq E]
    [Fintype E] {vars : ℕ} (enc : Encoding K vars) (ι : K →+* E)
    (contract : EncodingContract enc ι) (sec : LevelSecurity) (valid : sec.Valid enc)
    (lanes : ℕ) :
    (nearbyDecoder enc ι (radius enc sec) lanes).Correct ι
      (radius enc sec) (listBound enc sec) := by
  classical
  refine ⟨fun _ => Finset.nodup_toList _, ?_, ?_⟩
  · intro word f
    simp only [nearbyDecoder, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
  · intro word
    let T := Finset.univ.filter fun f => Close (radius enc sec) word (enc.interleave ι f)
    let C := (ReedSolomon.code (enc.extendedDomain ι) (2 ^ vars))^⋈(Cube lanes)
    have pairwise : ∀ c ∈ (C : Set (enc.Columns → Cube lanes → E)),
        ∀ c' ∈ (C : Set (enc.Columns → Cube lanes → E)), c ≠ c' →
        (Code.agree c c' : ℝ) ≤ Real.sqrt (dimensionRate enc) ^ 2 *
          Fintype.card enc.Columns := by
      intro c hc c' hc' hne
      obtain ⟨x, hx⟩ := Function.ne_iff.mp hne
      obtain ⟨u, hu⟩ := Function.ne_iff.mp hx
      have row_ne : (fun x => c x u) ≠ (fun x => c' x u) :=
        fun h => hu (congrFun h x)
      have hle : Code.agree c c' ≤ Code.agree (fun x => c x u) (fun x => c' x u) := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact congrFun hx u
      have hlt := ReedSolomon.agree_lt_of_mem_code (hc u) (hc' u) row_ne
      have hbound : (Code.agree c c' : ℝ) ≤ 2 ^ vars := by exact_mod_cast hle.trans hlt.le
      rw [Real.sq_sqrt (dimensionRate_pos enc).le]
      simpa only [dimensionRate, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat,
        div_mul_cancel₀ _ (by positivity : (2 ^ (vars + enc.rate) : ℝ) ≠ 0)] using hbound
    have hbound := Code.card_le_of_pairwise_agree_le
      (Real.sqrt_pos.mpr (dimensionRate_pos enc)) valid.2.2.2.1 pairwise
      word (T.image (enc.interleave ι)) (by
        rintro c hc
        obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hc
        apply Code.mem_closeCodewordsRel_iff.mpr
        exact ⟨interleave_mem enc ι contract f,
          (close_iff_relHammingDist (by positivity) _ _ _).mp (Finset.mem_filter.mp hf).2⟩)
    rw [Finset.card_image_of_injective T (interleave_injective enc ι contract)] at hbound
    simpa only [nearbyDecoder, Finset.length_toList, T, listBound] using hbound

end Whir
