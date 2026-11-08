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
  sorry

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
