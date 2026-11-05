/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.ProofSystem.Whir.Knowledge

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
  sorry

/-- In the absence of a valid preimage, an existing list preimage is still selected. -/
theorem listLift_of_preimage {E : Type} [Zero E] {n m : ℕ}
    (candidates : List (Table E n)) (view : Table E n → Table E m)
    (valid : Table E n → Prop) (successor : Table E m)
    (exists_preimage : ∃ f ∈ candidates, view f = successor) :
    listLift candidates view valid successor ∈ candidates ∧
      view (listLift candidates view valid successor) = successor := by
  sorry

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
  sorry

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
  sorry

/-- The scalar Johnson MCA bound specializes to an additive domain in any characteristic.
The numerical comparison uses `johnsonExceptionCount_le_comparisonEstimate`. -/
theorem mcaError_additive_le {K E : Type} [Field K] [Field E] [Fintype E]
    [SampleableType E] {vars : ℕ} (enc : Encoding K vars) (ι : K →+* E)
    (sec : LevelSecurity) (valid : sec.Valid enc) :
    CoreDefinitions.mcaError (CoreDefinitions.AffineLineGenerator E)
      (ReedSolomon.code (enc.extendedDomain ι) (2 ^ vars)) (radius enc sec) ≤
        mcaError (E := E) enc sec := by
  sorry

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
  sorry

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
  sorry

/-- Only old list members violating the current claim contribute sumcheck root collisions.
The per-member degree-two bound is the Boolean specialization of Sumcheck's round error. -/
theorem prob_fold_claimEscape_le {K E : Type} [Semiring K] [Field E] [DecidableEq E]
    [Fintype E] [SampleableType E] {vars lanes : ℕ} {enc : Encoding K vars}
    (ι : K →+* E) (sec : LevelSecurity)
    (before : ListDecoder (E := E) enc (lanes + 1))
    (correct : before.Correct ι (radius enc sec) (listBound enc sec))
    (word : Word E (lanes + 1) (2 ^ (vars + enc.rate)))
    (claim : Claim E ((lanes + 1) + vars)) (q : Quadratic E)
    (check : evalQuadratic q 0 + evalQuadratic q 1 = claim.value) :
    Pr{let r ←$ᵗ E}[∃ f ∈ before.decode word, ¬ claim.Holds f ∧
      (⟨foldMessageOne claim.weight r, evalQuadratic q r⟩ : Claim E (lanes + vars)).Holds
        (foldMessageOne f r)] ≤
      ENNReal.ofReal (2 * listBound enc sec / Fintype.card E) := by
  sorry

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
        [⟨foldMessageOne claim.weight r, evalQuadratic q r⟩] active).holds f ∧
      ¬ (candidateState enc ι γ word [claim] active).holds
        (listLift (before.decode word) (fun g => foldMessageOne g r) claim.Holds f)) :
    ListFoldFailure before after word r ∨
      ∃ f ∈ before.decode word, ¬ claim.Holds f ∧
        (⟨foldMessageOne claim.weight r, evalQuadratic q r⟩ : Claim E (lanes + vars)).Holds
          (foldMessageOne f r) := by
  sorry

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
    (claim : Claim E ((lanes + 1) + vars)) (q : Quadratic E) (active : Bool)
    (check : evalQuadratic q 0 + evalQuadratic q 1 = claim.value) :
    Pr{let r ←$ᵗ E}[∃ f,
      (candidateState enc ι (radius enc sec) (foldRowsOne word r)
        [⟨foldMessageOne claim.weight r, evalQuadratic q r⟩] active).holds f ∧
      ¬ (candidateState enc ι (radius enc sec) word [claim] active).holds
        (listLift (before.decode word) (fun g => foldMessageOne g r) claim.Holds f)] ≤
      foldError (E := E) enc sec := by
  sorry

/-- Classical proximity enumeration satisfies the Johnson contract without a row factor. -/
theorem nearbyDecoder_correct {K E : Type} [Field K] [Field E] [DecidableEq E]
    [Fintype E] {vars : ℕ} (enc : Encoding K vars) (ι : K →+* E)
    (contract : EncodingContract enc ι) (sec : LevelSecurity) (valid : sec.Valid enc)
    (lanes : ℕ) :
    (nearbyDecoder enc ι (radius enc sec) lanes).Correct ι
      (radius enc sec) (listBound enc sec) := by
  sorry

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
  sorry

/-- Once OOD separates the new list, its answer pins at most one candidate before queries. -/
theorem ood_answer_unique {E : Type} [CommRing E] {vars : ℕ}
    (candidates : List (Table E vars)) (z : Fin vars → E)
    (separated : ∀ f ∈ candidates, ∀ g ∈ candidates, mle f z = mle g z → f = g)
    (answer : E) (f g : Table E vars) (hf : f ∈ candidates) (hg : g ∈ candidates)
    (hf_answer : mle f z = answer) (hg_answer : mle g z = answer) : f = g := by
  sorry

/-- A fixed, far candidate passes all consistency queries with probability `(1 - gamma)^t`.
Fixing the candidate before the queries is essential for the absence of a list-size factor. -/
theorem prob_query_escape_le {K E : Type} [Semiring K] [Semiring E] [DecidableEq E]
    {vars queries : ℕ} (enc : Encoding K vars) (ι : K →+* E) (sec : LevelSecurity)
    (valid : sec.Valid enc) (folded : enc.Columns → E) (candidate : Table E vars)
    (far : ((Finset.univ.filter fun x => folded x = enc.encode ι candidate x).card : ℝ) <
      (1 - radius enc sec) * 2 ^ (vars + enc.rate)) :
    Pr{let xs ←$ᵗ (Fin queries → enc.Columns)}[
      ∀ q, folded (xs q) = enc.encode ι candidate (xs q)] ≤ queryError enc sec queries := by
  sorry

/-- Final batching has a fixed plaintext candidate and therefore has no Johnson list factor. -/
theorem prob_final_batch_escape_le {E : Type} [Field E]
    [Fintype E] [SampleableType E] {vars : ℕ}
    (claims : List (Claim E vars)) (candidate : Table E vars)
    (lost : ∃ c ∈ claims, ¬ c.Holds candidate) :
    Pr{let r ←$ᵗ E}[(batch claims r).Holds candidate] ≤
      ((claims.length - 1 : ℕ) : ENNReal) / Fintype.card E := by
  sorry

/-- A fixed plaintext and fixed weight give the degree-two Boolean Sumcheck round error. -/
theorem prob_closing_escape_le {E : Type} [Field E] [Fintype E] [SampleableType E]
    {vars : ℕ} (candidate : Table E (vars + 1)) (claim : Claim E (vars + 1))
    (q : Quadratic E) (check : evalQuadratic q 0 + evalQuadratic q 1 = claim.value)
    (lost : ¬ claim.Holds candidate) :
    Pr{let r ←$ᵗ E}[
      (⟨foldMessageOne (vars := 0) claim.weight r, evalQuadratic q r⟩ : Claim E vars).Holds
        (foldMessageOne (vars := 0) candidate r)] ≤ (2 : ENNReal) / Fintype.card E := by
  sorry

end Whir
