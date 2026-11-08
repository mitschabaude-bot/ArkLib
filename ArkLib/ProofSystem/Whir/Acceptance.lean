/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.ProofSystem.Whir.Transcript

/-!
# Acceptance supplies WHIR terminal knowledge

The extractor's accumulated checks and weighted final scalar relation coincide with the concrete
transcript predicate, independently of the initial witness-selection map.
-/

@[expose] public section

open Interaction Interaction.Oracle Interaction.Oracle.Security

namespace Whir

/-- Terminal knowledge of a level is exactly its initial activity and transcript acceptance. -/
theorem level_terminal_iff {K E : Type} [Semiring K] [CommRing E]
    [DecidableEq E] (ι : K →+* E) {n : ℕ} (s : Schedule K n)
    (sec : SecurityParameters s) (decoders : DecoderFamily (E := E) s) (word : oracleMessage E s)
      (claims : List (Claim E n))
    (active : Bool) (path : (opening E s).tree.ExecutionPath) :
    (∃ witness, ((levelExtractor ι s (proximityFamily ι s sec) decoders word claims
      active).terminalState path).holds witness) ↔
      active = true ∧ accepts ι s word claims path = true := by
  induction s generalizing active with
  | last lanes tail enc queries =>
      unfold accepts
      change LevelSecurity at sec
      change (lanes : ℕ) → ListDecoder (E := E) enc lanes at decoders
      change MaskedWord E lanes (2 ^ (tail + enc.rate)) at word
      change ((_ : E) × (scalarRounds E lanes
        (transition E (.last lanes tail enc queries))).tree.ExecutionPath) at path
      change (∃ witness, ((foldExtractor enc (fun _ w f => Close (radius enc sec) w
        (enc.interleave ι f)) decoders
        (lastExtractor lanes queries enc ι
      (fun w f => Close (radius enc sec) w (enc.interleave ι f)) (decoders 0)) lanes word (batch
        claims path.1)
          active).terminalState path.2).holds witness) ↔ _
      erw [foldExtractor_terminalState]
      erw [lastExtractor_terminalState]
      erw [closing_terminal_iff]
      simp only [zeroFill_scalar_fold, castTable_inverse,
        Bool.and_eq_true_iff, decide_eq_true_eq]
      simp only [queriesKnown, scalarMaskedWord, foldMaskedWord, Option.isSome_map]
      tauto
  | more lanes enc queries rest ih =>
      unfold accepts
      change LevelSecurity × SecurityParameters rest at sec
      change ((lanes : ℕ) → ListDecoder (E := E) enc lanes) ×
        DecoderFamily (E := E) rest at decoders
      change MaskedWord E lanes (2 ^ (_ + enc.rate)) at word
      change ((_ : E) × (scalarRounds E lanes
        (transition E (.more lanes enc queries rest))).tree.ExecutionPath) at path
      change (∃ witness, ((foldExtractor enc (fun _ w f => Close (radius enc sec.1) w
        (enc.interleave ι f)) decoders.1
        (boundaryExtractor lanes queries enc ι
          (fun w f => Close (radius enc sec.1) w (enc.interleave ι f))
          rest (proximityFamily ι rest sec.2) (decoders.1 0) decoders.2
          (levelExtractor ι rest (proximityFamily ι rest sec.2) decoders.2))
        lanes word (batch claims path.1) active).terminalState path.2).holds witness) ↔ _
      erw [foldExtractor_terminalState]
      erw [boundaryExtractor_terminalState]
      erw [ih]
      simp only [zeroFill_scalar_fold, castTable_inverse,
        Bool.and_eq_true_iff]
      simp only [queriesKnown, scalarMaskedWord, foldMaskedWord, Option.isSome_map]
      tauto

/-- Replacing the initial backward map does not change the terminal state. -/
theorem openingExtractor_terminalState {K E : Type} [Semiring K] [CommRing E]
    [DecidableEq K] [DecidableEq E] (ι : K →+* E) {n : ℕ}
    (s : Schedule K n) (sec : SecurityParameters s) (decoders : DecoderFamily (E := E) s) (word :
      oracleMessage K s)
    (claims : List (Claim E n)) (decoder : InitialDecoder s)
    (path : (opening E s).tree.ExecutionPath) :
    (openingExtractor ι s (proximityFamily ι s sec)
      (openingState ι s sec word claims).holds decoders word claims decoder).terminalState path =
      (levelExtractor ι s (proximityFamily ι s sec) decoders (mapMasked ι word) claims
        true).terminalState path := by
  cases s <;> rfl

end Whir
