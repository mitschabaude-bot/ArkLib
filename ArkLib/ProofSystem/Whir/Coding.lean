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
    Close γ (fullWord word) codeword ↔ (Code.relHammingDist word codeword : ℝ) ≤ γ := by
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
  simp only [Close, agreement, fullWord, Function.comp_apply, Option.some.injEq,
    funext_iff]
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
    (word : MaskedWord E (lanes + 1) (2 ^ (vars + enc.rate))) (r : E)
    (good : ¬ CoreDefinitions.IsMCA (CoreDefinitions.AffineLineGenerator E)
      ((ReedSolomon.code (enc.extendedDomain ι) (2 ^ vars))^⋈(Cube lanes))
      r (foldMcaInput (zeroFill word)) (radius enc sec))
    (f : Table E (lanes + vars))
    (close : Close (radius enc sec) (foldMaskedRowsOne word r) (enc.interleave ι f)) :
    ∃ g, Close (radius enc sec) word (enc.interleave ι g) ∧ foldMessageOne g r = f := by
  sorry

/-- Classical proximity enumeration satisfies the Johnson contract without a row factor. -/
theorem nearbyDecoder_correct {K E : Type} [Field K] [Field E] [DecidableEq E]
    [Fintype E] {vars : ℕ} (enc : Encoding K vars) (ι : K →+* E)
    (contract : EncodingContract enc ι) (sec : LevelSecurity) (valid : sec.Valid enc)
    (lanes : ℕ) :
    (nearbyDecoder enc ι (radius enc sec) lanes).Correct ι
      (radius enc sec) (listBound enc sec) := by
  sorry

end Whir
