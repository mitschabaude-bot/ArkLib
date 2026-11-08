/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.ProofSystem.Whir.Assembly
public import ArkLib.ProofSystem.Whir.Acceptance
public import ArkLib.ProofSystem.Whir.BadEvents
public import ArkLib.ProofSystem.Whir.PlaintextBadEvents

/-!
# WHIR opening knowledge certificate

The concrete list-lifting extractor and uniform challenge schedule have the six Annex B errors.
-/

@[expose] public section

open Interaction Interaction.Oracle Interaction.Oracle.Security OracleComp OracleSpec

namespace Whir

/-- WHIR's opening certificate with explicit list-lifting maps and Annex B's local errors. -/
noncomputable def certificate {K E : Type} [Field K] [Field E]
    [DecidableEq K] [DecidableEq E] [Fintype E] [SampleableType E]
    (ι : K →+* E) {n : ℕ} (s : Schedule K n) (sec : SecurityParameters s) (decoders :
      DecoderFamily (E := E) s)
    (familyCorrect : DecoderFamily.Correct ι s decoders sec)
    (valid : s.Valid ι sec) (word : oracleMessage K s) (claims : List (Claim E n))
    (decoder : InitialDecoder s) (correct : InitialDecoder.Correct decoder sec) :
    KnowledgeCertificate (opening E s).tree (opening E s).roles
      (openingState ι s sec word claims) where
  extractor := openingExtractor ι s (proximityFamily ι s sec)
      (openingState ι s sec word claims).holds decoders word claims decoder
  challenges := challenges (E := E) s sec claims.length
  prover_preserving := openingExtractor_preserving ι s sec decoders familyCorrect word claims
    decoder
  local_bound := openingExtractor_bounded ι s sec decoders familyCorrect valid word claims
    decoder correct

/-- Acceptance supplies terminal knowledge for the concrete certificate's terminal carrier. -/
theorem accepts_terminal {K E : Type} [Field K] [Field E]
    [DecidableEq K] [DecidableEq E] [Fintype E] [SampleableType E]
    (ι : K →+* E) {n : ℕ} (s : Schedule K n) (sec : SecurityParameters s) (decoders :
      DecoderFamily (E := E) s)
    (familyCorrect : DecoderFamily.Correct ι s decoders sec)
    (valid : s.Valid ι sec) (word : oracleMessage K s) (claims : List (Claim E n))
    (decoder : InitialDecoder s) (correct : InitialDecoder.Correct decoder sec)
    (path : (opening E s).tree.ExecutionPath)
    (accepted : accepts ι s (mapMasked ι word) claims path = true) :
    ∃ witness, ((certificate ι s sec decoders familyCorrect valid word claims decoder
      correct).extractor.terminalState
      path).holds witness := by
  change ∃ witness,
    ((openingExtractor ι s (proximityFamily ι s sec)
      (openingState ι s sec word claims).holds decoders word claims decoder).terminalState
        path).holds witness
  rw [openingExtractor_terminalState]
  exact (level_terminal_iff ι s sec decoders _ claims true path).mpr ⟨rfl, accepted⟩

end Whir
