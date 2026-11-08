/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.ProofSystem.Whir.BoundarySecurity

/-!
# Recursive assembly of WHIR local bounds

Batching and fold bounds compose with the boundary and closing blocks. The initial map uses
base-field descent and the executable decoder's exact-coverage contract.
-/

@[expose] public section

open Interaction Interaction.Oracle Interaction.Oracle.Security OracleComp OracleSpec
open scoped ProbabilityTheory

namespace Whir

/-- Encoded batching pays one power-polynomial error for each current list member. -/
theorem batch_local_bound {K E : Type} [Field K] [Field E] [DecidableEq E]
    [Fintype E] [SampleableType E] {vars lanes : ℕ} (enc : Encoding K vars) (ι : K →+* E)
    (sec : LevelSecurity) (decoder : ListDecoder (E := E) enc lanes)
    (correct : decoder.Correct ι (radius enc sec) (listBound enc sec))
    (word : MaskedWord E lanes (2 ^ (vars + enc.rate)))
    (claims : List (Claim E (lanes + vars))) (active : Bool) :
    Pr{let r ←$ᵗ E}[∃ f,
      ¬ (candidateState enc ι (radius enc sec) word claims active).holds
        (listLift (decoder.decode word) id
          (fun g => ∀ c ∈ claims, c.Holds g) f) ∧
      (candidateState enc ι (radius enc sec) word [batch claims r] active).holds f] ≤
        batchError (E := E) enc sec claims.length := by
  exact (prEvent_mono ($ᵗ E) _ _ (fun r ⟨f, bad, good⟩ =>
    batch_lift_failure_subset ι _ _ _ correct word claims active r ⟨f, good, bad⟩)).trans
      (prob_batch_escape_le ι sec _ correct word claims)

/-- The extension-field opening satisfies all six rows of its exact challenge schedule. -/
theorem levelExtractor_bounded {K E : Type} [Field K] [Field E]
    [DecidableEq E] [Fintype E] [SampleableType E] (ι : K →+* E) {n : ℕ}
    (s : Schedule K n) (sec : SecurityParameters s) (decoders : DecoderFamily (E := E) s)
    (familyCorrect : DecoderFamily.Correct ι s decoders sec) (valid : s.Valid ι sec)
    (word : oracleMessage E s) (claims : List (Claim E n)) (active : Bool) :
    (levelExtractor ι s (proximityFamily ι s sec) decoders word claims active).IsLocallyBounded
      (opening E s).roles
      (challenges (E := E) s sec claims.length) := by
  induction s generalizing active with
  | last lanes tail enc queries =>
      refine ⟨localGame_bounded _ _ _
        (batch_local_bound enc ι sec (decoders lanes) (familyCorrect lanes) word claims active), ?_⟩
      intro r
      exact foldExtractor_bounded enc ι sec decoders familyCorrect valid.2.1 valid.2.2.2 _ _
        (lastExtractor_bounded lanes queries enc ι sec (decoders 0) valid.2.1) lanes word _ active
  | more lanes enc queries rest ih =>
      refine ⟨localGame_bounded _ _ _
        (batch_local_bound enc ι sec.1 (decoders.1 lanes) (familyCorrect.1 lanes) word claims
          active), ?_⟩
      intro r
      exact foldExtractor_bounded enc ι sec.1 decoders.1 familyCorrect.1 valid.2.1 valid.2.2.2.1 _ _
        (boundaryExtractor_bounded lanes queries enc ι sec.1 valid.2.1
          (decoders.1 0) (familyCorrect.1 0) rest sec.2 decoders.2 familyCorrect.2
          valid.2.2.2.2 _ (ih sec.2 decoders.2 familyCorrect.2 valid.2.2.2.2)) lanes word _ active

/-- A current extension-field witness yields a valid base-field initial selection. -/
theorem initial_selection_of_current_witness {K E : Type} [Field K] [Field E]
    [DecidableEq K] [DecidableEq E] {vars lanes : ℕ} (enc : Encoding K vars) (ι : K →+* E)
    (base : EncodingContract enc (RingHom.id K)) (contract : EncodingContract enc ι)
    (sec : LevelSecurity) (valid : sec.Valid enc)
    (decoder : ListDecoder (E := K) enc lanes)
    (correct : decoder.Correct (RingHom.id K) (radius enc sec) (listBound enc sec))
    (word : MaskedWord K lanes (2 ^ (vars + enc.rate))) (claims : List (Claim E (lanes + vars)))
    (f : Table E (lanes + vars))
    (close : Close (radius enc sec) (mapMasked ι word) (enc.interleave ι f))
    (hclaims : ∀ c ∈ claims, c.Holds f) :
    (initialState enc ι (radius enc sec) word claims).holds
      (initialExtractor decoder ι word claims) := by
  obtain ⟨g, rfl, hg⟩ := initial_list_descends enc ι base contract sec valid word f close
  exact initialExtractor_holds decoder _ _ correct ι word claims ⟨g, hg, hclaims⟩

/-- The root map can fail only when a false extension-field list member survives batching. -/
theorem initial_batch_local_bound {K E : Type} [Field K] [Field E]
    [DecidableEq K] [DecidableEq E] [Fintype E] [SampleableType E]
    {vars lanes : ℕ} (enc : Encoding K vars) (ι : K →+* E)
    (base : EncodingContract enc (RingHom.id K)) (contract : EncodingContract enc ι)
    (sec : LevelSecurity) (valid : sec.Valid enc)
    (decoder : ListDecoder (E := K) enc lanes)
    (correct : decoder.Correct (RingHom.id K) (radius enc sec) (listBound enc sec))
    (word : MaskedWord K lanes (2 ^ (vars + enc.rate))) (claims : List (Claim E (lanes + vars))) :
    Pr{let r ←$ᵗ E}[∃ f,
      ¬ (initialState enc ι (radius enc sec) word claims).holds
        (initialExtractor decoder ι word claims) ∧
      (candidateState enc ι (radius enc sec) (mapMasked ι word) [batch claims r]
        true).holds f] ≤ batchError (E := E) enc sec claims.length := by
  classical
  let current := nearbyDecoder enc ι (radius enc sec) lanes
  have hcurrent := nearbyDecoder_correct enc ι contract sec valid lanes
  refine (prEvent_mono ($ᵗ E) _ _ ?_).trans
    (prob_batch_escape_le ι sec current hcurrent (mapMasked ι word) claims)
  rintro r ⟨f, bad, good⟩
  refine ⟨f, (hcurrent.mem_iff _ _).mpr good.2.1, ?_,
    good.2.2 _ (List.mem_singleton_self _)⟩
  by_contra no_false
  have all : ∀ c ∈ claims, c.Holds f := by
    simpa only [not_exists, not_and, not_not] using no_false
  exact bad (initial_selection_of_current_witness enc ι base contract sec valid decoder correct
    word claims f good.2.1 all)

/-- The base-field opening extractor has all Annex B local bounds, including its root map. -/
theorem openingExtractor_bounded {K E : Type} [Field K] [Field E]
    [DecidableEq K] [DecidableEq E] [Fintype E] [SampleableType E] (ι : K →+* E)
    {n : ℕ} (s : Schedule K n) (sec : SecurityParameters s) (decoders : DecoderFamily (E := E) s)
    (familyCorrect : DecoderFamily.Correct ι s decoders sec) (valid : s.Valid ι sec)
    (word : oracleMessage K s) (claims : List (Claim E n)) (decoder : InitialDecoder s)
    (correct : InitialDecoder.Correct decoder sec) :
    (openingExtractor ι s (proximityFamily ι s sec)
      (openingState ι s sec word claims).holds decoders word claims decoder).IsLocallyBounded
        (opening E s).roles
      (challenges (E := E) s sec claims.length) := by
  cases s with
  | last lanes tail enc queries =>
      exact ⟨localGame_bounded _ _ _ (initial_batch_local_bound enc ι
        valid.2.2.1 valid.2.2.2 sec valid.2.1 decoder correct word claims),
        (levelExtractor_bounded ι _ sec decoders familyCorrect valid (mapMasked ι word)
          claims true).2⟩
  | more lanes enc queries rest =>
      exact ⟨localGame_bounded _ _ _ (initial_batch_local_bound enc ι
        valid.2.2.1 valid.2.2.2.1 sec.1 valid.2.1 decoder correct word claims),
        (levelExtractor_bounded ι _ sec decoders familyCorrect valid (mapMasked ι word)
          claims true).2⟩

end Whir
