/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.ProofSystem.Whir.Coding
public import ArkLib.ProofSystem.Whir.Algebra
public import ArkLib.ProofSystem.Whir.Parameters
public import Mathlib.Data.Nat.Choose.Cast

/-!
# Annex B local events for list-lifting extraction

MCA supplies list preimages. A union over the old list bounds false-claim preimages whose
fold satisfies the reduced claim. OOD separates the new list before its answer fixes the
candidate tested by queries. These statements supply the six local errors of `certificate`.
-/

@[expose] public section

open Interaction Interaction.Oracle.Security OracleComp OracleSpec
open scoped ProbabilityTheory

namespace Whir

/-- A nearby folded message has no nearby preimage in the previous list. -/
def ListFoldFailure {K E : Type} [CommRing E] {vars lanes : ℕ} {enc : Encoding K vars}
    (before : ListDecoder (E := E) enc (lanes + 1))
    (after : ListDecoder (E := E) enc lanes)
    (word : Word E (lanes + 1) (2 ^ (vars + enc.rate))) (r : E) : Prop :=
  ∃ f ∈ after.decode (foldRowsOne word r),
    ∀ g ∈ before.decode word, foldMessageOne g r ≠ f

/-- A satisfying list preimage is preferred over every preimage violating the old claims. -/
theorem listLift_of_valid_preimage {E : Type} [Zero E] {n m : ℕ}
    (candidates : List (Table E n)) (view : Table E n → Table E m)
    (valid : Table E n → Prop) (successor : Table E m)
    (exists_valid : ∃ f ∈ candidates, view f = successor ∧ valid f) :
    listLift candidates view valid successor ∈ candidates ∧
      view (listLift candidates view valid successor) = successor ∧
      valid (listLift candidates view valid successor) := by
  classical
  simp only [listLift, dite_eq_left exists_valid]
  exact Classical.choose_spec exists_valid

/-- In the absence of a valid preimage, an existing list preimage is still selected. -/
theorem listLift_of_preimage {E : Type} [Zero E] {n m : ℕ}
    (candidates : List (Table E n)) (view : Table E n → Table E m)
    (valid : Table E n → Prop) (successor : Table E m)
    (exists_preimage : ∃ f ∈ candidates, view f = successor) :
    listLift candidates view valid successor ∈ candidates ∧
      view (listLift candidates view valid successor) = successor := by
  classical
  by_cases good : ∃ f ∈ candidates, view f = successor ∧ valid f
  · exact (listLift_of_valid_preimage candidates view valid successor good).imp_right And.left
  · simp only [listLift, dite_eq_right good, dite_eq_left exists_preimage]
    exact Classical.choose_spec exists_preimage

/-- Batching's failed backward map is contained in the false-list-member batching event. -/
theorem batch_lift_failure_subset {K E : Type} [Semiring K] [CommRing E] [DecidableEq E]
    {vars lanes : ℕ} {enc : Encoding K vars} (ι : K →+* E) (γ L : ℝ)
    (decoder : ListDecoder (E := E) enc lanes) (correct : decoder.Correct ι γ L)
    (word : Word E lanes (2 ^ (vars + enc.rate)))
    (claims : List (Claim E (lanes + vars))) (active : Bool) (r : E)
    (bad : ∃ f,
      (candidateState enc ι γ word [batch claims r] active).holds f ∧
      ¬ (candidateState enc ι γ word claims active).holds
        (listLift (decoder.decode word) id (fun g => ∀ c ∈ claims, c.Holds g) f)) :
    ∃ f ∈ decoder.decode word, (∃ c ∈ claims, ¬ c.Holds f) ∧ (batch claims r).Holds f := by
  classical
  obtain ⟨f, ⟨ha, hf, hb⟩, hbad⟩ := bad
  have hmem := (correct.mem_iff word f).mpr hf
  have hbatch := hb (batch claims r) (by simp only [List.mem_singleton])
  have hfalse : ¬ ∀ c ∈ claims, c.Holds f := by
    intro hall
    have lift := listLift_of_valid_preimage (decoder.decode word) id
      (fun g => ∀ c ∈ claims, c.Holds g) f ⟨f, hmem, rfl, hall⟩
    exact hbad ⟨ha, (correct.mem_iff _ _).mp lift.1, lift.2.2⟩
  exact ⟨f, hmem, by simpa only [not_forall, exists_prop] using hfalse, hbatch⟩

/-- Nearby extension-field codewords of the initial base-field oracle have base-field messages.
Agreement above the code dimension allows interpolation on base-field points. This connects
Annex B's extension-field list relation to `initialState` and its base-field decoder. -/
theorem initial_list_descends {K E : Type} [Field K] [Field E]
    [DecidableEq K] [DecidableEq E] {vars lanes : ℕ} (enc : Encoding K vars) (ι : K →+* E)
    (base_contract : EncodingContract enc (RingHom.id K)) (contract : EncodingContract enc ι)
    (sec : LevelSecurity) (valid : sec.Valid enc)
    (word : Word K lanes (2 ^ (vars + enc.rate))) (f : Table E (lanes + vars))
    (close : Close (radius enc sec) (fun x u => ι (word x u)) (enc.interleave ι f)) :
    ∃ g : Table K (lanes + vars), f = (fun u => ι (g u)) ∧
      Close (radius enc sec) word (enc.interleave (RingHom.id K) g) := by
  classical
  let T := Finset.univ.filter fun x => ∀ u, ι (word x u) = enc.interleave ι f x u
  have large : 2 ^ vars ≤ T.card := by
    have hclose : (1 - radius enc sec) * 2 ^ (vars + enc.rate) ≤ (T.card : ℝ) := by
      simpa only [Close, T, Nat.cast_pow, Nat.cast_ofNat] using close
    have h : (2 ^ vars : ℝ) ≤ T.card := (dimension_lt_agreement valid).le.trans hclose
    exact_mod_cast h
  have rows : ∀ u : Cube lanes, ∃ base : enc.Columns → K,
      base ∈ ReedSolomon.code enc.domain (2 ^ vars) ∧
        (fun x => enc.interleave ι f x u) = fun x => ι (base x) := by
    intro u
    exact ReedSolomon.exists_base_codeword_of_agreement enc.domain ι (2 ^ vars)
      (fun x => word x u) (fun x => enc.interleave ι f x u)
      (interleave_mem enc ι contract f u) T large
      (fun x hx => ((Finset.mem_filter.mp hx).2 u).symm)
  choose base hbase heq using rows
  have base_mem : (fun x u => base u x) ∈
      ((ReedSolomon.code enc.domain (2 ^ vars))^⋈(Cube lanes)) := by
    intro u
    change (fun x => base u x) ∈ ReedSolomon.code enc.domain (2 ^ vars)
    exact hbase u
  have hdomain : enc.extendedDomain (RingHom.id K) = enc.domain := by
    ext x
    rfl
  obtain ⟨g, hg⟩ := interleave_surjective enc (RingHom.id K) base_contract (fun x u => base u x)
    (by rwa [hdomain])
  have message : f = fun u => ι (g u) := by
    apply interleave_injective enc ι contract
    rw [interleave_scalar_extension, hg]
    funext x u
    exact congrFun (heq u) x
  refine ⟨g, message, ?_⟩
  rw [message, interleave_scalar_extension] at close
  unfold Close at close ⊢
  simpa only [ι.injective.eq_iff] using close

/-- List lifting uses MCA over the remaining row interleaving, with no row-count factor. -/
theorem prob_listFoldFailure_le {K E : Type} [Field K] [Field E] [DecidableEq E]
    [Fintype E] [SampleableType E] {vars lanes : ℕ} {enc : Encoding K vars}
    (ι : K →+* E) (contract : EncodingContract enc ι)
    (sec : LevelSecurity) (valid : sec.Valid enc)
    (before : ListDecoder (E := E) enc (lanes + 1))
    (after : ListDecoder (E := E) enc lanes)
    (before_correct : before.Correct ι (radius enc sec) (listBound enc sec))
    (after_correct : after.Correct ι (radius enc sec) (listBound enc sec))
    (word : Word E (lanes + 1) (2 ^ (vars + enc.rate))) :
    Pr{let r ←$ᵗ E}[ListFoldFailure before after word r] ≤ mcaError (E := E) enc sec := by
  classical
  let C := (ReedSolomon.code (enc.extendedDomain ι) (2 ^ vars))^⋈(Cube lanes)
  have inclusion := prEvent_mono ($ᵗ E) (ListFoldFailure before after word)
    (fun r => CoreDefinitions.IsMCA (CoreDefinitions.AffineLineGenerator E) C
      r (foldMcaInput word) (radius enc sec)) (by
        rintro r ⟨f, hf, absent⟩
        by_contra good
        obtain ⟨g, hg, hgf⟩ := fold_preimage_of_not_isMCA enc ι contract sec valid word r good f
          ((after_correct.mem_iff _ _).mp hf)
        exact absent g ((before_correct.mem_iff _ _).mpr hg) hgf)
  have supremum : Pr{let r ←$ᵗ E}[CoreDefinitions.IsMCA
      (CoreDefinitions.AffineLineGenerator E) C r (foldMcaInput word) (radius enc sec)] ≤
      CoreDefinitions.mcaError (CoreDefinitions.AffineLineGenerator E) C (radius enc sec) :=
    le_iSup (fun U => Pr{let r ←$ᵗ E}[CoreDefinitions.IsMCA
      (CoreDefinitions.AffineLineGenerator E) C r U (radius enc sec)]) (foldMcaInput word)
  refine inclusion.trans (supremum.trans ?_)
  rw [CoreDefinitions.mcaError_moduleInterleavedCode_eq_of_card_le
    (CoreDefinitions.AffineLineGenerator E) _ _ le_rfl]
  exact mcaError_additive_le enc ι sec valid

/-- Batching can make a false list member satisfy the batch only at the stated list-root loss. -/
theorem prob_batch_escape_le {K E : Type} [Semiring K] [Field E] [DecidableEq E]
    [Fintype E] [SampleableType E] {vars lanes : ℕ} {enc : Encoding K vars}
    (ι : K →+* E) (sec : LevelSecurity)
    (decoder : ListDecoder (E := E) enc lanes)
    (correct : decoder.Correct ι (radius enc sec) (listBound enc sec))
    (word : Word E lanes (2 ^ (vars + enc.rate)))
    (claims : List (Claim E (lanes + vars))) :
    Pr{let r ←$ᵗ E}[∃ f ∈ decoder.decode word,
      (∃ c ∈ claims, ¬ c.Holds f) ∧ (batch claims r).Holds f] ≤
        batchError (E := E) enc sec claims.length := by
  classical
  let event := fun f r => (∃ c ∈ claims, ¬ c.Holds f) ∧ (batch claims r).Holds f
  have hper : ∀ f ∈ decoder.decode word, Pr{let r ←$ᵗ E}[event f r] ≤
      ((claims.length - 1 : ℕ) : ENNReal) / Fintype.card E := by
    intro f _
    by_cases lost : ∃ c ∈ claims, ¬ c.Holds f
    · exact (prEvent_mono ($ᵗ E) _ _ (fun _ h => h.2)).trans
        (prob_batch_fixed_le claims f lost)
    · exact (prEvent_eq_zero_of_forall_not ($ᵗ E) _ (fun _ h => lost h.1)).le.trans zero_le
  exact (prob_exists_list_le ($ᵗ E) (decoder.decode word) event _ hper).trans
    (list_union_error_le (E := E) _ _ _ (correct.length_le word))

/-- Only old list members violating the current claim contribute sumcheck root collisions.
The per-member degree-two bound is the Boolean specialization of Sumcheck's round error. -/
theorem prob_fold_claimEscape_le {K E : Type} [Semiring K] [Field E] [DecidableEq E]
    [Fintype E] [SampleableType E] {vars lanes : ℕ} {enc : Encoding K vars}
    (ι : K →+* E) (sec : LevelSecurity)
    (before : ListDecoder (E := E) enc (lanes + 1))
    (correct : before.Correct ι (radius enc sec) (listBound enc sec))
    (word : Word E (lanes + 1) (2 ^ (vars + enc.rate)))
    (claim : Claim E ((lanes + 1) + vars)) (q : Quadratic E) :
    Pr{let r ←$ᵗ E}[∃ f ∈ before.decode word, ¬ claim.Holds f ∧
      (⟨foldMessageOne claim.weight r, evalQuadratic claim.value q r⟩ :
        Claim E (lanes + vars)).Holds
        (foldMessageOne f r)] ≤
      ENNReal.ofReal (2 * listBound enc sec / Fintype.card E) := by
  classical
  let event := fun f r => ¬ claim.Holds f ∧
    (⟨foldMessageOne claim.weight r, evalQuadratic claim.value q r⟩ : Claim E (lanes + vars)).Holds
      (foldMessageOne f r)
  have hper : ∀ f ∈ before.decode word, Pr{let r ←$ᵗ E}[event f r] ≤
      (2 : ENNReal) / Fintype.card E := by
    intro f _
    by_cases lost : ¬ claim.Holds f
    · exact (prEvent_mono ($ᵗ E) _ _ (fun _ h => h.2)).trans
        (prob_fold_fixed_le f claim q lost)
    · exact (prEvent_eq_zero_of_forall_not ($ᵗ E) _ (fun _ h => lost h.1)).le.trans zero_le
  exact (prob_exists_list_le ($ᵗ E) (before.decode word) event _ hper).trans
    (list_union_error_le (E := E) _ 2 _ (correct.length_le word))

/-- Fold-list failure or a false old member becoming true contains every failed lift. -/
theorem fold_lift_failure_subset {K E : Type} [Semiring K] [CommRing E] [DecidableEq E]
    {vars lanes : ℕ} {enc : Encoding K vars} (ι : K →+* E) (γ L : ℝ)
    (before : ListDecoder (E := E) enc (lanes + 1))
    (after : ListDecoder (E := E) enc lanes)
    (before_correct : before.Correct ι γ L) (after_correct : after.Correct ι γ L)
    (word : Word E (lanes + 1) (2 ^ (vars + enc.rate)))
    (claim : Claim E ((lanes + 1) + vars)) (q : Quadratic E) (active : Bool) (r : E)
    (bad : ∃ f,
      (candidateState enc ι γ (foldRowsOne word r)
        [⟨foldMessageOne claim.weight r, evalQuadratic claim.value q r⟩] active).holds f ∧
      ¬ (candidateState enc ι γ word [claim] active).holds
        (listLift (before.decode word) (fun g => foldMessageOne g r) claim.Holds f)) :
    ListFoldFailure before after word r ∨
      ∃ f ∈ before.decode word, ¬ claim.Holds f ∧
        (⟨foldMessageOne claim.weight r, evalQuadratic claim.value q r⟩ :
          Claim E (lanes + vars)).Holds
          (foldMessageOne f r) := by
  classical
  obtain ⟨f, ⟨ha, hf, hclaim⟩, hbad⟩ := bad
  by_cases failure : ListFoldFailure before after word r
  · exact Or.inl failure
  · right
    have hmem := (after_correct.mem_iff _ _).mpr hf
    have preimage : ∃ g ∈ before.decode word, foldMessageOne g r = f := by
      by_contra absent
      exact failure ⟨f, hmem, fun g hg he => absent ⟨g, hg, he⟩⟩
    let g := listLift (before.decode word) (fun g => foldMessageOne g r) claim.Holds f
    have lift := listLift_of_preimage (before.decode word)
      (fun g => foldMessageOne g r) claim.Holds f preimage
    refine ⟨g, lift.1, ?_, ?_⟩
    · intro hg
      exact hbad ⟨ha, (before_correct.mem_iff _ _).mp lift.1,
        by simpa only [List.mem_singleton, forall_eq] using hg⟩
    · rw [lift.2]
      exact hclaim _ (List.mem_singleton_self _)

/-- The witness-indexed fold failure is bounded by list lifting plus the sumcheck union. -/
theorem prob_fold_lift_failure_le {K E : Type} [Field K] [Field E] [DecidableEq E]
    [Fintype E] [SampleableType E] {vars lanes : ℕ} {enc : Encoding K vars}
    (ι : K →+* E) (contract : EncodingContract enc ι)
    (sec : LevelSecurity) (valid : sec.Valid enc)
    (before : ListDecoder (E := E) enc (lanes + 1))
    (after : ListDecoder (E := E) enc lanes)
    (before_correct : before.Correct ι (radius enc sec) (listBound enc sec))
    (after_correct : after.Correct ι (radius enc sec) (listBound enc sec))
    (word : Word E (lanes + 1) (2 ^ (vars + enc.rate)))
    (claim : Claim E ((lanes + 1) + vars)) (q : Quadratic E) (active : Bool) :
    Pr{let r ←$ᵗ E}[∃ f,
      (candidateState enc ι (radius enc sec) (foldRowsOne word r)
        [⟨foldMessageOne claim.weight r, evalQuadratic claim.value q r⟩] active).holds f ∧
      ¬ (candidateState enc ι (radius enc sec) word [claim] active).holds
        (listLift (before.decode word) (fun g => foldMessageOne g r) claim.Holds f)] ≤
      foldError (E := E) enc sec := by
  classical
  have inclusion := prEvent_mono ($ᵗ E) _ _ fun r bad =>
    fold_lift_failure_subset ι _ _ before after before_correct after_correct
      word claim q active r bad
  refine inclusion.trans ((prEvent_or_le ($ᵗ E) _ _).trans ?_)
  exact (add_le_add
    (prob_listFoldFailure_le ι contract sec valid before after before_correct after_correct word)
    (prob_fold_claimEscape_le ι sec before before_correct word claim q)).trans_eq
      (add_comm _ _)

/-- OOD collisions are bounded over the new list fixed before the fresh point is sent. -/
theorem prob_ood_collision_le {K E : Type} [Semiring K] [Field E] [DecidableEq E]
    [Fintype E] [SampleableType E] {vars lanes : ℕ} {enc : Encoding K vars}
    (ι : K →+* E) (sec : LevelSecurity) (valid : sec.Valid enc)
    (decoder : ListDecoder (E := E) enc lanes)
    (correct : decoder.Correct ι (radius enc sec) (listBound enc sec))
    (word : Word E lanes (2 ^ (vars + enc.rate))) :
    Pr{let z ←$ᵗ (Fin (lanes + vars) → E)}[
      ∃ f ∈ decoder.decode word, ∃ g ∈ decoder.decode word, f ≠ g ∧ mle f z = mle g z] ≤
        oodError (E := E) enc sec (lanes + vars) := by
  classical
  let candidates := (decoder.decode word).toFinset
  have h := prob_pair_collision_le ($ᵗ (Fin (lanes + vars) → E)) candidates mle
    ((lanes + vars : ℕ) / (Fintype.card E : ENNReal))
    (fun f _ g _ hne => prob_mle_collision_le f g hne)
  simp only [candidates, List.mem_toFinset] at h
  refine h.trans ?_
  have hL := correct.length_le word
  have hcount : (candidates.card : ℝ) ≤ listBound enc sec := by
    have hn : (candidates.card : ℝ) ≤ (decoder.decode word).length := by
      exact_mod_cast List.toFinset_card_le (decoder.decode word)
    exact hn.trans hL
  have hL1 := one_le_listBound valid
  have hchoose : (candidates.card.choose 2 : ℝ) ≤
      listBound enc sec * (listBound enc sec - 1) / 2 := by
    rw [Nat.cast_choose_two]
    by_cases hc : candidates.card = 0
    · simp only [hc, Nat.cast_zero, zero_mul, zero_div]
      positivity
    · have h1 : (1 : ℝ) ≤ candidates.card := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hc
      gcongr
  have hcard : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  unfold oodError
  have hreal := ENNReal.ofReal_le_ofReal
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hchoose
      (show (0 : ℝ) ≤ (lanes + vars : ℕ) by positivity)) hcard.le)
  refine le_trans (le_of_eq ?_) hreal
  rw [ENNReal.ofReal_div_of_pos hcard, ENNReal.ofReal_mul (by positivity)]
  simp only [ENNReal.ofReal_natCast, candidates, mul_div_assoc]

/-- Once OOD separates the new list, its answer pins at most one candidate before queries. -/
theorem ood_answer_unique {E : Type} [CommRing E] {vars : ℕ}
    (candidates : List (Table E vars)) (z : Fin vars → E)
    (separated : ∀ f ∈ candidates, ∀ g ∈ candidates, mle f z = mle g z → f = g)
    (answer : E) (f g : Table E vars) (hf : f ∈ candidates) (hg : g ∈ candidates)
    (hf_answer : mle f z = answer) (hg_answer : mle g z = answer) : f = g := by
  exact separated f hf g hg (hf_answer.trans hg_answer.symm)

/-- A fixed, far candidate passes all consistency queries with probability `(1 - gamma)^t`.
Fixing the candidate before the queries is essential for the absence of a list-size factor. -/
theorem prob_query_escape_le {K E : Type} [Semiring K] [Semiring E] [DecidableEq E]
    {vars queries : ℕ} (enc : Encoding K vars) (ι : K →+* E) (sec : LevelSecurity)
    (valid : sec.Valid enc) (folded : enc.Columns → E) (candidate : Table E vars)
    (far : ((Finset.univ.filter fun x => folded x = enc.encode ι candidate x).card : ℝ) <
      (1 - radius enc sec) * 2 ^ (vars + enc.rate)) :
    Pr{let xs ←$ᵗ (Fin queries → enc.Columns)}[
      ∀ q, folded (xs q) = enc.encode ι candidate (xs q)] ≤ queryError enc sec queries := by
  classical
  let S := Finset.univ.filter fun x => folded x = enc.encode ι candidate x
  have hN : (0 : ℝ) < 2 ^ (vars + enc.rate) := by positivity
  have hr : (S.card : ℝ) / 2 ^ (vars + enc.rate) ≤ 1 - radius enc sec :=
    (div_le_iff₀ hN).mpr far.le
  have hbound : (S.card : ENNReal) / (2 ^ (vars + enc.rate) : ℕ) ≤
      ENNReal.ofReal (1 - radius enc sec) := by
    have hh := ENNReal.ofReal_le_ofReal hr
    simpa only [ENNReal.ofReal_div_of_pos hN, ENNReal.ofReal_natCast,
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
      Nat.cast_pow, Nat.cast_ofNat] using hh
  calc
    _ = ((S.card : ENNReal) / (2 ^ (vars + enc.rate) : ℕ)) ^ queries := by
      simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.card_fin] using
        Probability.prob_uniform_pi_mem_finset_eq S queries
    _ ≤ _ := by
      rw [queryError, ENNReal.ofReal_pow (sub_nonneg.mpr (radius_lt_one valid).le)]
      exact pow_le_pow_left' hbound queries

/-- Final batching has a fixed plaintext candidate and therefore has no Johnson list factor. -/
theorem prob_final_batch_escape_le {E : Type} [Field E]
    [Fintype E] [SampleableType E] {vars : ℕ}
    (claims : List (Claim E vars)) (candidate : Table E vars)
    (lost : ∃ c ∈ claims, ¬ c.Holds candidate) :
    Pr{let r ←$ᵗ E}[(batch claims r).Holds candidate] ≤
      ((claims.length - 1 : ℕ) : ENNReal) / Fintype.card E := by
  exact prob_batch_fixed_le claims candidate lost

/-- A fixed plaintext and fixed weight give the degree-two Boolean Sumcheck round error. -/
theorem prob_closing_escape_le {E : Type} [Field E] [Fintype E] [SampleableType E]
    {vars : ℕ} (candidate : Table E (vars + 1)) (claim : Claim E (vars + 1))
    (q : Quadratic E)
    (lost : ¬ claim.Holds candidate) :
    Pr{let r ←$ᵗ E}[
      (⟨foldMessageOne (vars := 0) claim.weight r, evalQuadratic claim.value q r⟩ :
        Claim E vars).Holds
        (foldMessageOne (vars := 0) candidate r)] ≤ (2 : ENNReal) / Fintype.card E := by
  exact prob_fold_fixed_le (vars := 0) candidate claim q lost

end Whir
