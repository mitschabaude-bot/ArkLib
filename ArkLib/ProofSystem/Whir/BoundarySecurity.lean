/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.ProofSystem.Whir.LocalSecurity

/-!
# Knowledge bounds at WHIR level boundaries

OOD separates a fixed new list. Its answer fixes a candidate before fresh column queries.
The final plaintext is also fixed before its query challenge.
-/

@[expose] public section

open Interaction Interaction.Oracle Interaction.Oracle.Security OracleComp OracleSpec
open scoped ProbabilityTheory

namespace Whir

/-- The classical decoder's exact membership does not require its cardinality estimate. -/
theorem nearbyDecoder_mem_iff {K E : Type} [Semiring K] [Semiring E]
    [DecidableEq E] [Fintype E] {vars lanes : ℕ} (enc : Encoding K vars) (ι : K →+* E)
    (γ : ℝ) (word : MaskedWord E lanes (2 ^ (vars + enc.rate))) (f : Table E (lanes + vars)) :
    f ∈ (nearbyDecoder enc ι γ lanes).decode word ↔ Close γ word (enc.interleave ι f) := by
  classical
  simp only [nearbyDecoder, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The level state consists of a current-list member satisfying its claims. -/
theorem levelState_holds_iff {K E : Type} [Semiring K] [Semiring E]
    [DecidableEq E] (ι : K →+* E) {n : ℕ} (s : Schedule K n)
    (sec : SecurityParameters s) (decoders : DecoderFamily (E := E) s)
    (correct : DecoderFamily.Correct ι s decoders sec) (word : oracleMessage E s) (claims : List
      (Claim E n))
    (active : Bool) (f : Table E n) :
    (levelState ι s sec word claims active).holds f ↔
      active = true ∧ f ∈ levelList s decoders word ∧ ∀ c ∈ claims, c.Holds f := by
  cases s with
  | last lanes tail enc queries =>
    exact and_congr_right fun _ => and_congr_left fun _ => (correct lanes).mem_iff word f |>.symm
  | more lanes enc queries rest =>
    exact and_congr_right fun _ => and_congr_left fun _ => (correct.1 lanes).mem_iff word f |>.symm

/-- Boundary claims are precisely the residual, the OOD answer and the sampled equations. -/
theorem nextClaims_holds_iff {K E : Type} [Semiring K] [CommRing E] {tail queries : ℕ}
    (enc : Encoding K tail) (ι : K →+* E) (residual : Claim E tail)
    (z : Fin tail → E) (answer : E) (xs : Fin queries → enc.Columns)
    (folded : enc.Columns → E) (f : Table E tail) :
    (∀ c ∈ nextClaims enc ι residual z answer xs folded, c.Holds f) ↔
      residual.Holds f ∧ mle f z = answer ∧
        ∀ q, folded (xs q) = enc.encode ι f (xs q) := by
  simp only [nextClaims, List.forall_mem_cons, List.forall_mem_ofFn_iff, Claim.Holds,
    mle, Encoding.encode, eq_comm]

/-- At zero rows, column proximity is ordinary scalar agreement with the plaintext encoder. -/
theorem close_zero_iff {K E : Type} [Semiring K] [Semiring E] [DecidableEq E]
    {tail : ℕ} (enc : Encoding K tail) (ι : K →+* E) (γ : ℝ)
    (word : MaskedWord E 0 (2 ^ (tail + enc.rate))) (candidate : Table E tail) :
    Close γ word (enc.interleave ι (castTable (Nat.zero_add tail).symm candidate)) ↔
      (1 - γ) * 2 ^ (tail + enc.rate) ≤
        ((Finset.univ.filter fun x =>
          word x = some (fun _ => enc.encode ι candidate x)).card : ℝ) := by
  sorry

/-- A far plaintext fixed before sampling has exactly the Annex B query escape bound. -/
theorem prob_far_queries_le {K E : Type} [Semiring K] [Semiring E] [DecidableEq E]
    {tail queries : ℕ} (enc : Encoding K tail) (ι : K →+* E) (sec : LevelSecurity)
    (valid : sec.Valid enc) (word : MaskedWord E 0 (2 ^ (tail + enc.rate)))
    (candidate : Table E tail)
    (far : ¬ Close (radius enc sec) word
      (enc.interleave ι (castTable (Nat.zero_add tail).symm candidate))) :
    Pr{let xs ←$ᵗ (Fin queries → enc.Columns)}[
      ∀ q, word (xs q) = some (fun _ => enc.encode ι candidate (xs q))] ≤
        queryError enc sec queries := by
  sorry

/-- Plaintext query backward failure is a far fixed plaintext passing its sampled equations. -/
theorem last_query_local_bound {K E : Type} [Semiring K] [CommRing E]
    [DecidableEq E] {tail : ℕ} (lanes queries : ℕ)
    (enc : Encoding K tail) (ι : K →+* E) (sec : LevelSecurity)
    (decoder : ListDecoder (E := E) enc 0) (valid : sec.Valid enc)
    (word : MaskedWord E 0 (2 ^ (tail + enc.rate))) (claim : Claim E (0 + tail))
    (candidate : Table E tail) (active : Bool) :
    Pr{let xs ←$ᵗ (Fin queries → enc.Columns)}[
      ((lastExtractor lanes queries enc ι
      (fun w f => Close (radius enc sec) w (enc.interleave ι f)) decoder word claim active
        candidate).2.2).badChallenge xs] ≤
        queryError enc sec queries := by
  sorry

/-- The last-level suffix assembles its query, final batching and closing bounds. -/
theorem lastExtractor_bounded {K E : Type} [Field K] [Field E] [DecidableEq E]
    [Fintype E] [SampleableType E] {tail : ℕ} (lanes queries : ℕ)
    (enc : Encoding K tail) (ι : K →+* E) (sec : LevelSecurity)
    (decoder : ListDecoder (E := E) enc 0) (valid : sec.Valid enc)
    (word : MaskedWord E 0 (2 ^ (tail + enc.rate))) (claim : Claim E (0 + tail)) (active : Bool) :
    (lastExtractor lanes queries enc ι
      (fun w f => Close (radius enc sec) w (enc.interleave ι f)) decoder word claim
        active).IsLocallyBounded
      (transition E (.last lanes tail enc queries)).roles
      ⟨PUnit.unit, fun _ =>
        ⟨⟨$ᵗ (Fin queries → enc.Columns), queryError enc sec queries⟩, fun _ =>
          ⟨⟨$ᵗ E, (queries : ENNReal) / Fintype.card E⟩, fun _ =>
            scalarChallenges ((2 : ENNReal) / Fintype.card E)
              (rest := .done) PUnit.unit tail⟩⟩⟩ := by
  sorry

/-- The entering OOD challenge pays only unordered collisions in the next level's fixed list. -/
theorem entering_ood_local_bound {K E : Type} [Field K] [Field E] [DecidableEq E]
    [Fintype E] [SampleableType E] (ι : K →+* E) {n : ℕ} (s : Schedule K n)
    (sec : SecurityParameters s) (decoders : DecoderFamily (E := E) s)
    (correct : DecoderFamily.Correct ι s decoders sec) (valid : s.Valid ι sec) (word :
      oracleMessage E s)
    (old : Table E n → Prop) (active : Bool) :
    Pr{let z ←$ᵗ (Fin n → E)}[∃ witness,
      ¬ (active = true ∧ old (match witness with | .inl f => f | .inr _ => 0)) ∧
      (oodState old (levelList s decoders word) z active).holds witness] ≤
        enteringOodError (E := E) s sec := by
  refine (prEvent_mono ($ᵗ (Fin n → E)) _
    (fun z => OodCollision (levelList s decoders word) z) ?_).trans ?_
  · rintro z ⟨witness, bad, good⟩
    cases witness with
    | inl f => exact (bad good).elim
    | inr pair => exact ⟨pair.1, good.2.1, pair.2, good.2.2.1, good.2.2.2⟩
  · cases s with
    | last lanes tail enc queries =>
      exact prob_ood_collision_le ι sec valid.2.1 _
        (correct lanes) word
    | more lanes enc queries rest =>
      exact prob_ood_collision_le ι sec.1 valid.2.1 _
        (correct.1 lanes) word

/-- Boundary query failure tests the one candidate fixed by the OOD answer. -/
theorem boundary_query_local_bound {K E : Type} [Field K] [Field E]
    [DecidableEq E] {tail queries : ℕ} (enc : Encoding K tail) (ι : K →+* E)
    (sec : LevelSecurity) (valid : sec.Valid enc)
    (decoder : ListDecoder (E := E) enc 0)
    (correct : decoder.Correct ι (radius enc sec) (listBound enc sec))
    (rest : Schedule K tail) (nextSec : SecurityParameters rest)
    (decoders : DecoderFamily (E := E) rest)
    (nextCorrect : DecoderFamily.Correct ι rest decoders nextSec) (nextWord : oracleMessage E rest)
    (word : MaskedWord E 0 (2 ^ (tail + enc.rate))) (claim : Claim E (0 + tail))
    (z : Fin tail → E) (answer : E) (active : Bool) :
    Pr{let xs ←$ᵗ (Fin queries → enc.Columns)}[∃ f,
      ¬ (oodState (fun g => (candidateState enc ι (radius enc sec) word [claim] active).holds
          (castTable (Nat.zero_add tail).symm g))
          (levelList rest decoders nextWord) z active).holds
        (boundaryLift (decoder.decode word)
          (castTable (Nat.zero_add tail)) claim.Holds (levelList rest decoders nextWord) z f) ∧
      (levelState ι rest nextSec nextWord
        (nextClaims enc ι ⟨castTable (Nat.zero_add tail) claim.weight, claim.value⟩
          z answer xs (fun x => zeroFill word x Fin.elim0)) active).holds f] ≤
        queryError enc sec queries := by
  sorry

/-- A boundary assembles its entering OOD bound, fixed-candidate query bound and next level. -/
theorem boundaryExtractor_bounded {K E : Type} [Field K] [Field E]
    [DecidableEq E] [Fintype E] [SampleableType E] {tail : ℕ}
    (lanes queries : ℕ) (enc : Encoding K tail) (ι : K →+* E)
    (sec : LevelSecurity) (valid : sec.Valid enc)
    (decoder : ListDecoder (E := E) enc 0)
    (correct : decoder.Correct ι (radius enc sec) (listBound enc sec))
    (rest : Schedule K tail) (nextSec : SecurityParameters rest)
    (decoders : DecoderFamily (E := E) rest)
    (nextCorrect : DecoderFamily.Correct ι rest decoders nextSec) (nextValid : rest.Valid ι nextSec)
    (suffix : (word : oracleMessage E rest) → (claims : List (Claim E tail)) →
      (active : Bool) → RoundExtractor (opening E rest).tree
        (levelState ι rest nextSec word claims active))
    (bounded : ∀ word claims active, (suffix word claims active).IsLocallyBounded
      (opening E rest).roles (challenges (E := E) rest nextSec claims.length))
    (word : MaskedWord E 0 (2 ^ (tail + enc.rate))) (claim : Claim E (0 + tail)) (active : Bool) :
    (boundaryExtractor lanes queries enc ι
      (fun w f => Close (radius enc sec) w (enc.interleave ι f))
      rest (proximityFamily ι rest nextSec) decoder decoders suffix
      word claim active).IsLocallyBounded
      (transition E (.more lanes enc queries rest)).roles
      (fun _ => ⟨⟨$ᵗ (Fin tail → E), enteringOodError (E := E) rest nextSec⟩, fun _ =>
        ⟨PUnit.unit, fun _ =>
          ⟨⟨$ᵗ (Fin queries → enc.Columns), queryError enc sec queries⟩, fun _ =>
            challenges rest nextSec (queries + 2)⟩⟩⟩) := by
  sorry

end Whir
