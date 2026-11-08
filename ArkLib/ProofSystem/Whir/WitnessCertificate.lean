/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.ProofSystem.Whir.WitnessAnnotation

/-!
# Authenticated witness CI for the WHIR opening

The initial masked word is explicit authenticated context. Composition supplies the word extracted
at its earlier commitment node and authenticates it together with the opening's later oracle
messages. The opening has no initial commitment node of its own.
-/

@[expose] public section

open Interaction Interaction.Oracle Interaction.Oracle.Security OracleComp OracleSpec
open Interaction.Oracle.Security.StandardBcs
open Interaction.Oracle.Security.StateRestoration

namespace Whir

/-- The initial backward selection can escape only through the current masked batching event. -/
theorem initial_batch_escape_subset_bad {K E : Type} [Field K] [Field E]
    [DecidableEq K] [DecidableEq E] {vars lanes : ℕ} (enc : Encoding K vars) (ι : K →+* E)
    (base : EncodingContract enc (RingHom.id K)) (contract : EncodingContract enc ι)
    (sec : LevelSecurity) (valid : sec.Valid enc)
    (decoder : ListDecoder (E := K) enc lanes)
    (correct : decoder.Correct (RingHom.id K) (radius enc sec) (listBound enc sec))
    (word : MaskedWord K lanes (2 ^ (vars + enc.rate))) (claims : List (Claim E (lanes + vars)))
    (r : E) (escape : ∃ f,
      ¬ (initialState enc ι (radius enc sec) word claims).holds
        (initialExtractor decoder ι word claims) ∧
      (candidateState enc ι (radius enc sec) (mapMasked ι word) [batch claims r] true).holds f) :
    BadBatch ι (radius enc sec) (mapMasked ι word) claims r := by
  classical
  obtain ⟨f, bad, good⟩ := escape
  refine ⟨f, good.2.1, ?_, good.2.2 _ (List.mem_singleton_self _)⟩
  by_contra absent
  apply bad
  apply initial_selection_of_current_witness enc ι base contract sec valid decoder correct
    word claims f good.2.1
  simpa only [not_exists, not_and, not_not] using absent

/-- The opening annotation retains its supplied initial mask in the first algebraic input. -/
noncomputable def openingAnnotation {K E : Type} [Field K] [Field E]
    [DecidableEq K] [DecidableEq E] [Fintype E] [SampleableType E]
    (ι : K →+* E) {n : ℕ} (s : Schedule K n) (sec : SecurityParameters s)
    (decoders : DecoderFamily (E := E) s)
    (familyCorrect : DecoderFamily.Correct ι s decoders sec) (valid : s.Valid ι sec)
    (word : oracleMessage K s) (claims : List (Claim E n)) (decoder : InitialDecoder s)
    (correct : InitialDecoder.Correct decoder sec) :
    BadAnnotation (openingPublicCoin s)
      (openingSchemas ι s sec decoders familyCorrect valid claims.length)
      (certificate ι s sec decoders familyCorrect valid word claims decoder correct).extractor := by
  cases s with
  | last lanes tail enc queries =>
      refine ⟨⟨mapMasked ι word, ⟨claims, rfl⟩, true⟩, ⟨?_, ?_⟩⟩
      · intro r _ escape
        exact ⟨rfl, initial_batch_escape_subset_bad enc ι valid.2.2.1 valid.2.2.2 sec valid.2.1
          decoder correct word claims r escape⟩
      · exact (levelAnnotation ι (.last lanes tail enc queries) sec decoders familyCorrect
          valid (mapMasked ι word) claims true).2.2
  | more lanes enc queries rest =>
      refine ⟨⟨mapMasked ι word, ⟨claims, rfl⟩, true⟩, ⟨?_, ?_⟩⟩
      · intro r _ escape
        exact ⟨rfl, initial_batch_escape_subset_bad enc ι valid.2.2.1 valid.2.2.2.1 sec.1 valid.2.1
          decoder correct word claims r escape⟩
      · exact (levelAnnotation ι (.more lanes enc queries rest) sec decoders familyCorrect
          valid (mapMasked ι word) claims true).2.2

/-- The concrete opening refinement authenticates its external initial word and strict prefix. -/
noncomputable def witnessCertificate {K E Com : Type} [Field K] [Field E]
    [DecidableEq K] [DecidableEq E] [DecidableEq Com] [Fintype E] [SampleableType E]
    (ι : K →+* E) {n : ℕ} (s : Schedule K n) (sec : SecurityParameters s)
    (decoders : DecoderFamily (E := E) s)
    (familyCorrect : DecoderFamily.Correct ι s decoders sec) (valid : s.Valid ι sec)
    (word : oracleMessage K s) (claims : List (Claim E n)) (decoder : InitialDecoder s)
    (correct : InitialDecoder.Correct decoder sec)
    (Authentication : Key PUnit PUnit (fun _ => compiledCoin Com (openingPublicCoin (E := E) s)) →
      Type)
    (authenticate : (key : Key PUnit PUnit
      (fun _ => compiledCoin Com (openingPublicCoin (E := E) s))) →
      oracleMessage K s → PrefixMessages (openingPublicCoin s) key.2 → Authentication key → Bool) :
    WitnessKnowledgeCertificate (Com := Com) (fun _ : PUnit => openingPublicCoin s)
      (fun _ => openingState ι s sec word claims)
      (fun _ => certificate ι s sec decoders familyCorrect valid word claims decoder correct) :=
  BadAnnotation.certificate (fun _ => openingPublicCoin s)
    (fun _ => openingState ι s sec word claims)
    (fun _ => certificate ι s sec decoders familyCorrect valid word claims decoder correct)
    (fun _ => openingSchemas ι s sec decoders familyCorrect valid claims.length)
    (fun _ => openingAnnotation ι s sec decoders familyCorrect valid word claims decoder correct)
    Authentication (fun key messages auth => authenticate key word messages auth)

section Decomposition

variable {K E Com Openings Coins : Type} [Field K] [Field E]
    [DecidableEq K] [DecidableEq E] [DecidableEq Com] [Fintype E] [SampleableType E]
    [SampleableType Coins] (ι : K →+* E) {n : ℕ} (s : Schedule K n)
    (sec : SecurityParameters s) (decoders : DecoderFamily (E := E) s)
    (familyCorrect : DecoderFamily.Correct ι s decoders sec) (valid : s.Valid ι sec)
    (word : oracleMessage K s) (claims : List (Claim E n)) (decoder : InitialDecoder s)
    (correct : InitialDecoder.Correct decoder sec)
    (Authentication : Key PUnit PUnit (fun _ => compiledCoin Com (openingPublicCoin (E := E) s)) →
      Type)
    (authenticate : (key : Key PUnit PUnit
      (fun _ => compiledCoin Com (openingPublicCoin (E := E) s))) →
      oracleMessage K s → PrefixMessages (openingPublicCoin s) key.2 → Authentication key → Bool)

local notation "coin" => (fun _ : PUnit => openingPublicCoin (E := E) s)
local notation "state" => (fun _ : PUnit => openingState ι s sec word claims)
local notation "cert" => (fun _ : PUnit =>
  certificate ι s sec decoders familyCorrect valid word claims decoder correct)
local notation "refinement" => witnessCertificate ι s sec decoders familyCorrect valid
  word claims decoder correct Authentication authenticate

/-- WHIR opening failure splits into disagreement, authenticated algebraic CI, and query CI. -/
theorem knowledgeSoundness_witness
    (A : Coins → FSProof PUnit Com Openings coin)
    (ext : (c : Coins) → ExtractedMessages (openingPublicCoin s) (A c).2.1)
    (auth : (c : Coins) → (pre : Prefix PUnit (compiledCoin Com (openingPublicCoin (E := E) s))) →
      Authentication ⟨(A c).1, pre⟩)
    (h : Interaction.Oracle.Security.StateRestoration.Table PUnit PUnit
      (fun _ => compiledCoin Com (openingPublicCoin (E := E) s)))
    (accept : FSProof PUnit Com Openings coin → Prop)
    (terminalWitness : (c : Coins) → ((cert (A c).1).extractor.terminalState
      (extractedPath (openingPublicCoin s) (A c).2.1 (ext c))).Witness)
    (Disagree : Coins → Prop)
    (transfer : ∀ c, verify coin h accept (A c) → ¬ Disagree c →
      ((cert (A c).1).extractor.terminalState
        (extractedPath (openingPublicCoin s) (A c).2.1 (ext c))).holds (terminalWitness c))
    (authenticated : ∀ c r selected,
      selectedPrefix (openingPublicCoin s) (A c).2.1 (ext c) r = some selected →
      authenticate ⟨(A c).1, selected.1⟩ word selected.2 (auth c selected.1) = true)
    (count : ℕ) (bound : ChallengeBound (Com := Com) coin count) :
    Pr{let c ← ($ᵗ Coins : ProbComp Coins)}[
      verify coin h accept (A c) ∧ ¬ (openingState ι s sec word claims).holds
        (compositeExtractor coin state (fun x => (cert x).extractor) A ext terminalWitness c)] ≤
    Pr{let c ← ($ᵗ Coins : ProbComp Coins)}[Disagree c] +
      (∑ r ∈ Finset.range count, witnessCI (refinement).toWitnessCIRelation h
        (reductionAdversary (refinement).toWitnessCIRelation A ext auth r)) +
      ∑ r ∈ Finset.range count,
        queryRel (refinement).toWitnessCIRelation state cert A ext h r :=
  StandardBcs.knowledgeSoundness_witness coin state cert refinement A ext auth h accept
    terminalWitness Disagree transfer authenticated count bound

end Decomposition

end Whir
