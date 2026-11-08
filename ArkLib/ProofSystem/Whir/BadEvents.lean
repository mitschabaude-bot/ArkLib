/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.ProofSystem.Whir.LocalBounds

/-! # Monotone algebraic bad events for masked WHIR prefixes -/

@[expose] public section

open Interaction Interaction.Oracle.Security OracleComp OracleSpec
open scoped ProbabilityTheory

namespace Whir

section Lists

variable {K E : Type} [Semiring K] [CommRing E] [DecidableEq E]
    {vars lanes : ℕ} {enc : Encoding K vars}

/-- A nearby old candidate violates an input claim but satisfies the power batch. -/
def BadBatch (ι : K →+* E) (γ : ℝ)
    (word : MaskedWord E lanes (2 ^ (vars + enc.rate)))
    (claims : List (Claim E (lanes + vars))) (r : E) : Prop :=
  ∃ f, Close γ word (enc.interleave ι f) ∧
    (∃ c ∈ claims, ¬ c.Holds f) ∧ (batch claims r).Holds f

/-- Certified decoding makes the batching bad set executable. -/
def checkBadBatch (decoder : ListDecoder (E := E) enc lanes)
    (word : MaskedWord E lanes (2 ^ (vars + enc.rate)))
    (claims : List (Claim E (lanes + vars))) (r : E) : Bool :=
  (decoder.decode word).any fun f =>
    claims.any (fun c => !decide (c.Holds f)) && decide ((batch claims r).Holds f)

/-- The batching checker decides the mathematical bad event. -/
theorem checkBadBatch_iff (ι : K →+* E) (γ L : ℝ)
    (decoder : ListDecoder (E := E) enc lanes) (correct : decoder.Correct ι γ L)
    (word : MaskedWord E lanes (2 ^ (vars + enc.rate)))
    (claims : List (Claim E (lanes + vars))) (r : E) :
    checkBadBatch decoder word claims r = true ↔ BadBatch ι γ word claims r := by
  simp only [checkBadBatch, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_eq, correct.mem_iff, BadBatch]

/-- Batching escape is contained in the monotone bad set for every mask. -/
theorem batch_escape_subset_bad (ι : K →+* E) (γ L : ℝ)
    (decoder : ListDecoder (E := E) enc lanes) (correct : decoder.Correct ι γ L)
    (word : MaskedWord E lanes (2 ^ (vars + enc.rate)))
    (claims : List (Claim E (lanes + vars))) (active : Bool) (r : E)
    (escape : ∃ f, (candidateState enc ι γ word [batch claims r] active).holds f ∧
      ¬ (candidateState enc ι γ word claims active).holds
        (listLift (decoder.decode word) id (fun g => ∀ c ∈ claims, c.Holds g) f)) :
    BadBatch ι γ word claims r := by
  obtain ⟨f, hf, bad⟩ := batch_lift_failure_subset ι γ L decoder correct word claims active r escape
  exact ⟨f, (correct.mem_iff _ _).mp hf, bad⟩

/-- Hiding columns cannot create a batching bad event. -/
theorem BadBatch.mono {ι : K →+* E} {γ : ℝ}
    {small large : MaskedWord E lanes (2 ^ (vars + enc.rate))}
    (h : MaskLE small large) {claims : List (Claim E (lanes + vars))} {r : E}
    (bad : BadBatch ι γ small claims r) : BadBatch ι γ large claims r := by
  obtain ⟨f, close, rest⟩ := bad
  exact ⟨f, close.mono h, rest⟩

/-- OOD is bad exactly when two masked list members collide at the sampled point. -/
def BadOod (ι : K →+* E) (γ : ℝ)
    (word : MaskedWord E lanes (2 ^ (vars + enc.rate))) (z : Fin (lanes + vars) → E) : Prop :=
  ∃ f g, Close γ word (enc.interleave ι f) ∧ Close γ word (enc.interleave ι g) ∧
    f ≠ g ∧ mle f z = mle g z

/-- The OOD checker compares only certified decoded candidates. -/
def checkBadOod (decoder : ListDecoder (E := E) enc lanes)
    (word : MaskedWord E lanes (2 ^ (vars + enc.rate))) (z : Fin (lanes + vars) → E) : Bool :=
  (decoder.decode word).any fun f => (decoder.decode word).any fun g =>
    decide (f ≠ g ∧ mle f z = mle g z)

/-- Certified lists make the OOD checker exact. -/
theorem checkBadOod_iff (ι : K →+* E) (γ L : ℝ)
    (decoder : ListDecoder (E := E) enc lanes) (correct : decoder.Correct ι γ L)
    (word : MaskedWord E lanes (2 ^ (vars + enc.rate))) (z : Fin (lanes + vars) → E) :
    checkBadOod decoder word z = true ↔ BadOod ι γ word z := by
  simp only [checkBadOod, List.any_eq_true, decide_eq_true_eq, correct.mem_iff, BadOod]
  aesop

/-- An OOD knowledge escape supplies a collision in the new masked list. -/
theorem ood_escape_subset_bad (ι : K →+* E) (γ L : ℝ)
    (decoder : ListDecoder (E := E) enc lanes) (correct : decoder.Correct ι γ L)
    (word : MaskedWord E lanes (2 ^ (vars + enc.rate))) (old : Table E (lanes + vars) → Prop)
    (z : Fin (lanes + vars) → E) (active : Bool)
    (escape : ∃ witness,
      ¬ (active = true ∧ old (match witness with | .inl f => f | .inr _ => 0)) ∧
      (oodState old (decoder.decode word) z active).holds witness) : BadOod ι γ word z := by
  obtain ⟨witness, bad, good⟩ := escape
  cases witness with
  | inl f => exact (bad good).elim
  | inr pair =>
      exact ⟨pair.1, pair.2, (correct.mem_iff _ _).mp good.2.1,
        (correct.mem_iff _ _).mp good.2.2.1, good.2.2.2⟩

/-- Hiding columns cannot introduce an OOD collision. -/
theorem BadOod.mono {ι : K →+* E} {γ : ℝ}
    {small large : MaskedWord E lanes (2 ^ (vars + enc.rate))}
    (h : MaskLE small large) {z : Fin (lanes + vars) → E} (bad : BadOod ι γ small z) :
    BadOod ι γ large z := by
  obtain ⟨f, g, hf, hg, rest⟩ := bad
  exact ⟨f, g, hf.mono h, hg.mono h, rest⟩

/-- A false old list member becomes true under the transmitted quadratic at the challenge. -/
def BadFoldClaim (ι : K →+* E) (γ : ℝ)
    (word : MaskedWord E (lanes + 1) (2 ^ (vars + enc.rate)))
    (claim : Claim E ((lanes + 1) + vars)) (q : Quadratic E) (r : E) : Prop :=
  ∃ f, Close γ word (enc.interleave ι f) ∧ ¬ claim.Holds f ∧
    (⟨foldMessageOne claim.weight r, evalQuadratic claim.value q r⟩ :
      Claim E (lanes + vars)).Holds (foldMessageOne f r)

/-- Certified old-list decoding decides the false-claim fold event. -/
def checkBadFoldClaim (before : ListDecoder (E := E) enc (lanes + 1))
    (word : MaskedWord E (lanes + 1) (2 ^ (vars + enc.rate)))
    (claim : Claim E ((lanes + 1) + vars)) (q : Quadratic E) (r : E) : Bool :=
  (before.decode word).any fun f => decide (¬ claim.Holds f ∧
    (⟨foldMessageOne claim.weight r, evalQuadratic claim.value q r⟩ :
      Claim E (lanes + vars)).Holds (foldMessageOne f r))

/-- The false-claim fold checker is exact under the decoder contract. -/
theorem checkBadFoldClaim_iff (ι : K →+* E) (γ L : ℝ)
    (before : ListDecoder (E := E) enc (lanes + 1)) (correct : before.Correct ι γ L)
    (word : MaskedWord E (lanes + 1) (2 ^ (vars + enc.rate)))
    (claim : Claim E ((lanes + 1) + vars)) (q : Quadratic E) (r : E) :
    checkBadFoldClaim before word claim q r = true ↔ BadFoldClaim ι γ word claim q r := by
  simp only [checkBadFoldClaim, List.any_eq_true, decide_eq_true_eq,
    correct.mem_iff, BadFoldClaim]

/-- Hiding columns cannot create a false-claim fold collision. -/
theorem BadFoldClaim.mono {ι : K →+* E} {γ : ℝ}
    {small large : MaskedWord E (lanes + 1) (2 ^ (vars + enc.rate))}
    (h : MaskLE small large) {claim : Claim E ((lanes + 1) + vars)} {q : Quadratic E} {r : E}
    (bad : BadFoldClaim ι γ small claim q r) : BadFoldClaim ι γ large claim q r := by
  obtain ⟨f, hf, rest⟩ := bad
  exact ⟨f, hf.mono h, rest⟩

/-- On a large known agreement set the folded word extends to code but the rows do not jointly. -/
def BadMCA (ι : K →+* E) (γ : ℝ)
    (word : MaskedWord E (lanes + 1) (2 ^ (vars + enc.rate))) (r : E) : Prop :=
  ∃ f, Close γ (foldMaskedRowsOne word r) (enc.interleave ι f) ∧
    ¬ ∃ g : Table E ((lanes + 1) + vars),
      ∀ x ∈ agreement (foldMaskedRowsOne word r) (enc.interleave ι f),
        word x = some (enc.interleave ι g x)

/-- Masked MCA checks every folded candidate and its joint old-list extensions. -/
def checkBadMCA (ι : K →+* E)
    (before : ListDecoder (E := E) enc (lanes + 1)) (after : ListDecoder (E := E) enc lanes)
    (word : MaskedWord E (lanes + 1) (2 ^ (vars + enc.rate))) (r : E) : Bool :=
  (after.decode (foldMaskedRowsOne word r)).any fun f =>
    !(before.decode word).any fun g => decide
      (∀ x ∈ agreement (foldMaskedRowsOne word r) (enc.interleave ι f),
        word x = some (enc.interleave ι g x))

/-- The MCA checker decides the subset event through the two certified masked decoders. -/
theorem checkBadMCA_iff (ι : K →+* E) (γ L : ℝ)
    (before : ListDecoder (E := E) enc (lanes + 1)) (after : ListDecoder (E := E) enc lanes)
    (hc : before.Correct ι γ L) (hc' : after.Correct ι γ L)
    (word : MaskedWord E (lanes + 1) (2 ^ (vars + enc.rate))) (r : E) :
    checkBadMCA ι before after word r = true ↔ BadMCA ι γ word r := by
  sorry

/-- Hiding removes possible MCA agreement sets without creating a joint extension obstruction. -/
theorem BadMCA.mono {ι : K →+* E} {γ : ℝ}
    {small large : MaskedWord E (lanes + 1) (2 ^ (vars + enc.rate))}
    (h : MaskLE small large) {r : E} (bad : BadMCA ι γ small r) : BadMCA ι γ large r := by
  sorry

/-- Every masked MCA witness is a full-word MCA witness of the zero-filled word. -/
theorem BadMCA.zeroFill {ι : K →+* E} {γ : ℝ}
    {word : MaskedWord E (lanes + 1) (2 ^ (vars + enc.rate))} {r : E}
    (bad : BadMCA ι γ word r) : BadMCA ι γ (fullWord (zeroFill word)) r :=
  bad.mono (maskLE_zeroFill word)

/-- The fold bad set combines subset MCA and a false old-list claim becoming true. -/
def BadFold (ι : K →+* E) (γ : ℝ)
    (word : MaskedWord E (lanes + 1) (2 ^ (vars + enc.rate)))
    (claim : Claim E ((lanes + 1) + vars)) (q : Quadratic E) (r : E) : Prop :=
  BadMCA ι γ word r ∨ BadFoldClaim ι γ word claim q r

/-- The fold checker combines the certified MCA and claim-collision checkers. -/
def checkBadFold (ι : K →+* E)
    (before : ListDecoder (E := E) enc (lanes + 1)) (after : ListDecoder (E := E) enc lanes)
    (word : MaskedWord E (lanes + 1) (2 ^ (vars + enc.rate)))
    (claim : Claim E ((lanes + 1) + vars)) (q : Quadratic E) (r : E) : Bool :=
  checkBadMCA ι before after word r || checkBadFoldClaim before word claim q r

/-- Certified folded lists make the fold checker equivalent to its mathematical event. -/
theorem checkBadFold_iff (ι : K →+* E) (γ L : ℝ)
    (before : ListDecoder (E := E) enc (lanes + 1)) (after : ListDecoder (E := E) enc lanes)
    (hc : before.Correct ι γ L) (hc' : after.Correct ι γ L)
    (word : MaskedWord E (lanes + 1) (2 ^ (vars + enc.rate)))
    (claim : Claim E ((lanes + 1) + vars)) (q : Quadratic E) (r : E) :
    checkBadFold ι before after word claim q r = true ↔ BadFold ι γ word claim q r := by
  simp only [checkBadFold, Bool.or_eq_true, checkBadMCA_iff ι γ L before after hc hc',
    checkBadFoldClaim_iff ι γ L before hc, BadFold]

/-- Hiding columns cannot create a fold bad event. -/
theorem BadFold.mono {ι : K →+* E} {γ : ℝ}
    {small large : MaskedWord E (lanes + 1) (2 ^ (vars + enc.rate))}
    (h : MaskLE small large) {claim : Claim E ((lanes + 1) + vars)} {q : Quadratic E} {r : E}
    (bad : BadFold ι γ small claim q r) : BadFold ι γ large claim q r :=
  bad.elim (fun hbad => Or.inl (hbad.mono h)) (fun hbad => Or.inr (hbad.mono h))

end Lists

section FoldEscape

variable {K E : Type} [Field K] [Field E] [DecidableEq E]
    {vars lanes : ℕ} {enc : Encoding K vars}

/-- Fold escape is contained in subset MCA or the false-claim list event for every mask. -/
theorem fold_escape_subset_bad
    (ι : K →+* E) (contract : EncodingContract enc ι) (sec : LevelSecurity)
    (valid : sec.Valid enc)
    (before : ListDecoder (E := E) enc (lanes + 1)) (after : ListDecoder (E := E) enc lanes)
    (hc : before.Correct ι (radius enc sec) (listBound enc sec))
    (hc' : after.Correct ι (radius enc sec) (listBound enc sec))
    (word : MaskedWord E (lanes + 1) (2 ^ (vars + enc.rate)))
    (claim : Claim E ((lanes + 1) + vars)) (q : Quadratic E) (active : Bool) (r : E)
    (escape : ∃ f,
      (candidateState enc ι (radius enc sec) (foldMaskedRowsOne word r)
        [⟨foldMessageOne claim.weight r, evalQuadratic claim.value q r⟩] active).holds f ∧
      ¬ (candidateState enc ι (radius enc sec) word [claim] active).holds
        (listLift (before.decode word) (fun g => foldMessageOne g r) claim.Holds f)) :
    BadFold ι (radius enc sec) word claim q r := by
  sorry

end FoldEscape

section Bounds

variable {K E : Type} [Field K] [Field E] [DecidableEq E] [Fintype E] [SampleableType E]
    {vars lanes : ℕ} {enc : Encoding K vars}

/-- Zero fill gives the original list batching error with no mask penalty. -/
theorem prob_badBatch_le (ι : K →+* E) (sec : LevelSecurity)
    (decoder : ListDecoder (E := E) enc lanes)
    (correct : decoder.Correct ι (radius enc sec) (listBound enc sec))
    (word : MaskedWord E lanes (2 ^ (vars + enc.rate)))
    (claims : List (Claim E (lanes + vars))) :
    Pr{let r ←$ᵗ E}[BadBatch ι (radius enc sec) word claims r] ≤
      batchError (E := E) enc sec claims.length := by
  refine (prEvent_mono ($ᵗ E) _ _ ?_).trans
    (prob_batch_escape_le ι sec decoder correct (fullWord (zeroFill word)) claims)
  rintro r ⟨f, hf, rest⟩
  exact ⟨f, (correct.mem_iff _ _).mpr hf.zeroFill, rest⟩

/-- Zero fill gives the original unordered-pair OOD collision bound. -/
theorem prob_badOod_le (ι : K →+* E) (sec : LevelSecurity) (valid : sec.Valid enc)
    (decoder : ListDecoder (E := E) enc lanes)
    (correct : decoder.Correct ι (radius enc sec) (listBound enc sec))
    (word : MaskedWord E lanes (2 ^ (vars + enc.rate))) :
    Pr{let z ←$ᵗ (Fin (lanes + vars) → E)}[BadOod ι (radius enc sec) word z] ≤
      oodError (E := E) enc sec (lanes + vars) := by
  refine (prEvent_mono ($ᵗ (Fin (lanes + vars) → E)) _ _ ?_).trans
    (prob_ood_collision_le ι sec valid decoder correct (fullWord (zeroFill word)))
  rintro z ⟨f, g, hf, hg, rest⟩
  exact ⟨f, (correct.mem_iff _ _).mpr hf.zeroFill,
    g, (correct.mem_iff _ _).mpr hg.zeroFill, rest⟩

/-- A masked subset obstruction is the existing full-word BCHKS event after zero fill. -/
theorem badMCA_implies_isMCA_zeroFill (ι : K →+* E) (contract : EncodingContract enc ι)
    (sec : LevelSecurity) (valid : sec.Valid enc)
    (word : MaskedWord E (lanes + 1) (2 ^ (vars + enc.rate))) (r : E)
    (bad : BadMCA ι (radius enc sec) word r) :
    CoreDefinitions.IsMCA (CoreDefinitions.AffineLineGenerator E)
      ((ReedSolomon.code (enc.extendedDomain ι) (2 ^ vars))^⋈(Cube lanes))
      r (foldMcaInput (zeroFill word)) (radius enc sec) := by
  sorry

/-- Zero fill bounds subset MCA by the full-word BCHKS event at the same radius and rate. -/
theorem prob_badMCA_le (ι : K →+* E) (contract : EncodingContract enc ι)
    (sec : LevelSecurity) (valid : sec.Valid enc)
    (word : MaskedWord E (lanes + 1) (2 ^ (vars + enc.rate))) :
    Pr{let r ←$ᵗ E}[BadMCA ι (radius enc sec) word r] ≤ mcaError (E := E) enc sec := by
  let C := (ReedSolomon.code (enc.extendedDomain ι) (2 ^ vars))^⋈(Cube lanes)
  refine (prEvent_mono ($ᵗ E) _ _ (fun r bad =>
    badMCA_implies_isMCA_zeroFill ι contract sec valid word r bad)).trans ?_
  have supremum : Pr{let r ←$ᵗ E}[CoreDefinitions.IsMCA
      (CoreDefinitions.AffineLineGenerator E) C r (foldMcaInput (zeroFill word))
      (radius enc sec)] ≤
      CoreDefinitions.mcaError (CoreDefinitions.AffineLineGenerator E) C (radius enc sec) :=
    le_iSup (fun U => Pr{let r ←$ᵗ E}[CoreDefinitions.IsMCA
      (CoreDefinitions.AffineLineGenerator E) C r U (radius enc sec)])
      (foldMcaInput (zeroFill word))
  refine supremum.trans ?_
  rw [CoreDefinitions.mcaError_moduleInterleavedCode_eq_of_card_le
    (CoreDefinitions.AffineLineGenerator E) _ _ le_rfl]
  exact mcaError_additive_le enc ι sec valid

/-- Zero fill preserves the original degree-two old-list root bound. -/
theorem prob_badFoldClaim_le (ι : K →+* E) (sec : LevelSecurity)
    (before : ListDecoder (E := E) enc (lanes + 1))
    (correct : before.Correct ι (radius enc sec) (listBound enc sec))
    (word : MaskedWord E (lanes + 1) (2 ^ (vars + enc.rate)))
    (claim : Claim E ((lanes + 1) + vars)) (q : Quadratic E) :
    Pr{let r ←$ᵗ E}[BadFoldClaim ι (radius enc sec) word claim q r] ≤
      ENNReal.ofReal (2 * listBound enc sec / Fintype.card E) := by
  refine (prEvent_mono ($ᵗ E) _ _ ?_).trans
    (prob_fold_claimEscape_le ι sec before correct (fullWord (zeroFill word)) claim q)
  rintro r ⟨f, hf, rest⟩
  exact ⟨f, (correct.mem_iff _ _).mpr hf.zeroFill, rest⟩

/-- The fold bad set has exactly the original MCA plus list-root error. -/
theorem prob_badFold_le (ι : K →+* E) (contract : EncodingContract enc ι)
    (sec : LevelSecurity) (valid : sec.Valid enc)
    (before : ListDecoder (E := E) enc (lanes + 1))
    (correct : before.Correct ι (radius enc sec) (listBound enc sec))
    (word : MaskedWord E (lanes + 1) (2 ^ (vars + enc.rate)))
    (claim : Claim E ((lanes + 1) + vars)) (q : Quadratic E) :
    Pr{let r ←$ᵗ E}[BadFold ι (radius enc sec) word claim q r] ≤
      foldError (E := E) enc sec := by
  exact (prEvent_or_le ($ᵗ E) _ _).trans ((add_le_add
    (prob_badMCA_le ι contract sec valid word)
    (prob_badFoldClaim_le ι sec before correct word claim q)).trans_eq (add_comm _ _))

end Bounds

end Whir
