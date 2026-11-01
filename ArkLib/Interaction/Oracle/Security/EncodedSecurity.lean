/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.EncodedCompletion
public import ArkLib.Interaction.Oracle.Security.EncodedChallengeCost

/-!
# Encoded-domain adversaries in native restoration security

An arbitrary encoded-domain oracle adversary is routed through the strict codec with a private
memoized off-image cache, then through the common-challenge interpreter into the actual native
restoration oracle. The returned selection is unchanged and the final native oracle cache is
carried into stopped completion.
-/

@[expose] public section

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec MeasureTheory
open Interaction.Oracle.TypeTree

namespace Interaction.Oracle.Security.StateRestoration

universe w

variable {Input Salt C D W : Type} {protocol : Input → Protocol}
  {coin : (z : Input) → PublicCoin (protocol z)}

/-- The adversary-phase budget is exactly the expected distinct native hash-log count of the
adversary program itself. Surface query logging does not add hash queries. -/
theorem expectedAdversaryFreshKeys_eq_expectedFreshQueryCharge
    [DecidableEq Input] [DecidableEq Salt]
    (coin : (z : Input) → PublicCoin (protocol z))
    (adversary : RandomizedRestorationAdversary Input Salt W coin) :
    expectedAdversaryFreshKeys coin adversary =
      expectedFreshQueryCharge adversary (fun _ => 1) := by
  let : MeasurableSpace
      (((Option (Selection Input Salt W coin) ×
        QueryLog (unifSpec + oracleSpec Input Salt coin)) ×
          QueryLog (oracleSpec Input Salt coin)) ×
            (oracleSpec Input Salt coin).QueryCache) := ⊤
  let : MeasurableSpace
      ((Option (Selection Input Salt W coin) ×
        QueryLog (oracleSpec Input Salt coin)) ×
          (oracleSpec Input Salt coin).QueryCache) := ⊤
  simp only [expectedAdversaryFreshKeys, expectedFreshQueryCharge,
    freshQueryCharge, Finset.sum_const, nsmul_eq_mul, mul_one]
  have herase : (fun result => ((result.1.1.1, result.1.2), result.2)) <$>
      randomOracleLoggedRun adversary.withQueryLog ∅ =
      randomOracleLoggedRun adversary ∅ := by
    rw [← randomOracleLoggedRun_map (fun pair => pair.1) adversary.withQueryLog ∅]
    congr 1
    exact loggingOracle.fst_map_run_simulateQ adversary
  rw [← herase, lintegral_evalDist_map_of_discrete]

/-- Forgetting the external writer/off-image cache from the selected value does not erase any
actual native hash query or alter its distinct-key expectation. -/
theorem encodedNativeAdversary_expectedKeys_eq_route
    [DecidableEq Input] [DecidableEq Salt] [DecidableEq D] [SampleableType C]
    (coin : (z : Input) → PublicCoin (protocol z))
    (common : CommonChallenge Input Salt C coin)
    (codec : StrictCodec (Key Input Salt coin) D)
    (external : OracleComp (unifSpec + (D →ₒ C))
      (Option (Selection Input Salt W coin))) :
    expectedAdversaryFreshKeys coin
      (encodedNativeAdversary common codec external) =
    expectedFreshQueryCharge
      (common.simulateNative (codec.routeProgram external ∅)) (fun _ => 1) := by
  rw [expectedAdversaryFreshKeys_eq_expectedFreshQueryCharge]
  let : MeasurableSpace
      ((Option (Selection Input Salt W coin) ×
        QueryLog (oracleSpec Input Salt coin)) ×
          (oracleSpec Input Salt coin).QueryCache) := ⊤
  let : MeasurableSpace
      ((((Option (Selection Input Salt W coin) × QueryLog (D →ₒ C)) ×
        (D →ₒ C).QueryCache) × QueryLog (oracleSpec Input Salt coin)) ×
          (oracleSpec Input Salt coin).QueryCache) := ⊤
  simp only [expectedFreshQueryCharge, freshQueryCharge, Finset.sum_const,
    nsmul_eq_mul, mul_one]
  unfold encodedNativeAdversary
  rw [randomOracleLoggedRun_map, lintegral_evalDist_map_of_discrete]

/-- The native certificate applies to the actual stopped joint run of the encoded adversary.
The resource term is the native image-query count. Its external transport is separate. -/
theorem encodedNativeReduction_knowledge_soundness
    [DecidableEq Input] [DecidableEq Salt] [DecidableEq D] [SampleableType C]
    (coin : (z : Input) → PublicCoin (protocol z))
    (common : CommonChallenge Input Salt C coin)
    (codec : StrictCodec (Key Input Salt coin) D)
    (external : OracleComp (unifSpec + (D →ₒ C))
      (Option (Selection Input Salt W coin)))
    (guards : (z : Input) → GuardSchedule Salt (coin z))
    (errors : (z : Input) → Errors (coin z))
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol z).tree (state z))
    (Z : Set Input)
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol z).roles)
    (bounded : ∀ z ∈ Z, RoundExtractor.IsLocallyBounded (extractor z)
      (protocol z).roles (errorSchedule (coin z) (errors z)))
    (Rin : (z : Input) → (state z).Witness → Prop)
    (Rout : (z : Input) → (path : (protocol z).tree.ExecutionPath) → W → Prop)
    (terminalWitness : (z : Input) → (path : (protocol z).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (inputLaw : ∀ z witness, (state z).holds witness ↔ Rin z witness)
    (outputLaw : ∀ z path witness,
      Rout z path witness →
        ((extractor z).terminalState path).holds (terminalWitness z path witness)) :
    Pr{let joint ← (randomOracleLoggedRun
      (randomizedStoppedRestoredExecutionWithAdversaryLog coin guards
        (encodedNativeAdversary common codec external)) ∅)}[
      badStoppedRelation state extractor Rin Rout terminalWitness Z joint.1.1.1] ≤
      maxError errors *
        expectedAdversaryFreshKeys coin (encodedNativeAdversary common codec external) +
      sumError errors := by
  have h := randomizedStopped_knowledge_soundness_actualAdversary coin guards errors
    (encodedNativeAdversary common codec external) state extractor Z preserving bounded
    Rin Rout terminalWitness inputLaw outputLaw
  exact h.1.trans h.2

end Interaction.Oracle.Security.StateRestoration
