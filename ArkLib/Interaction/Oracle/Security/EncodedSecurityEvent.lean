/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.EncodedSecurity
public import ArkLib.Interaction.Oracle.Security.EncodedChallengeCoupling
public import ArkLib.Data.OracleComp.RandomOracleCost
public import ArkLib.Interaction.Oracle.Security.EncodedCharge

/-!
# Actual encoded-domain stopped event

The external adversary and encoded stopped verifier share one lazy random oracle. Their
selected-result distribution agrees with the native stopped experiment through the strict
codec and the uniform common challenge representations.
-/

@[expose] public section

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec MeasureTheory
open Interaction.Oracle.TypeTree

namespace Interaction.Oracle.Security.StateRestoration

variable {Input Salt C D W : Type} {protocol : Input → Protocol}

/-- The actual external stopped game and the native stopped joint game have the same selected
result distribution, including failure and guard rejection. -/
theorem encodedExternalStopped_evalDist_result_eq_native
    [DecidableEq Input] [DecidableEq Salt] [DecidableEq D] [SampleableType C]
    (coin : (z : Input) → PublicCoin (protocol z))
    (common : CommonChallenge Input Salt C coin)
    (codec : StrictCodec (Key Input Salt coin) D)
    (guards : (z : Input) → GuardSchedule Salt (coin z))
    (external : OracleComp (unifSpec + (D →ₒ C))
      (Option (Selection Input Salt W coin))) :
    letI : MeasurableSpace
      (Option (Outcome Input W protocol)) := ⊤
    𝒟[(fun joint => joint.1.1) <$> randomOracleLoggedRun
      (encodedExternalStoppedExecution coin common codec guards external) ∅] =
    𝒟[(fun joint => joint.1.1.1) <$> randomOracleLoggedRun
      (randomizedStoppedRestoredExecutionWithAdversaryLog coin guards
        (encodedNativeAdversary common codec external)) ∅] := by
  let : MeasurableSpace
      (Option (Outcome Input W protocol)) := ⊤
  let Result := Option (Outcome Input W protocol)
  let Routed := ((Result × QueryLog (D →ₒ C)) × (D →ₒ C).QueryCache)
  let : MeasurableSpace
      ((Routed × QueryLog (Key Input Salt coin →ₒ C)) ×
        (Key Input Salt coin →ₒ C).QueryCache) := ⊤
  let : MeasurableSpace
      ((Routed × QueryLog (oracleSpec Input Salt coin)) ×
        (oracleSpec Input Salt coin).QueryCache) := ⊤
  let externalProgram :=
    encodedExternalStoppedExecution coin common codec guards external
  let routedProgram := codec.routeProgram externalProgram ∅
  let nativeProgram := common.simulateNative routedProgram
  let nativeStopped := nativeStoppedExecution coin guards
    (encodedNativeAdversary common codec external)
  have hroute := codec.routeProgram_externalProjection externalProgram
    (∅ : (Key Input Salt coin →ₒ C).QueryCache)
    (∅ : (D →ₒ C).QueryCache)
  rw [codec.mergeCache_empty] at hroute
  have hchallenge := common.evalDist_randomOracleLoggedRun_simulateNative
    routedProgram (∅ : (oracleSpec Input Salt coin).QueryCache)
  have hcache : common.toCommonCache
      (∅ : (oracleSpec Input Salt coin).QueryCache) = ∅ := by
    apply QueryCache.ext
    intro key
    simp [CommonChallenge.toCommonCache]
  have hsource := encodedExternalStopped_route_nativeValue coin common codec
    guards external
  have herase := randomizedStoppedExecution_eraseSourceLog coin guards
    (encodedNativeAdversary common codec external)
  calc
    _ = 𝒟[(fun joint => joint.1.1.1.1) <$>
        randomOracleLoggedRun routedProgram ∅] := by
          rw [← hroute]
          simp only [Functor.map_map]
          rfl
    _ = 𝒟[(fun joint => joint.1.1.1.1) <$>
        randomOracleLoggedRun nativeProgram ∅] := by
          have hchallenge' := congrArg
            (fun measure => Measure.map (fun joint => joint.1.1.1.1) measure)
            hchallenge.symm
          rw [evalDist_map_of_discrete, evalDist_map_of_discrete]
          rw [evalDist_map_of_discrete,
            Measure.map_map Measurable.of_discrete Measurable.of_discrete] at hchallenge'
          rw [hcache] at hchallenge'
          simpa only [CommonChallenge.encodeJoint, Function.comp_def] using hchallenge'
    _ = 𝒟[(fun joint => joint.1.1) <$>
        randomOracleLoggedRun nativeStopped ∅] := by
          dsimp only [nativeStopped, nativeProgram, routedProgram]
          rw [← hsource]
          simp only [randomOracleLoggedRun_map, Functor.map_map]
          rfl
    _ = _ := by
          dsimp only [nativeStopped]
          rw [← herase]
          simp only [randomOracleLoggedRun_map, Functor.map_map]

/-- Every event on the selected stopped result has the same probability in the actual
external encoded oracle experiment and the native certificate experiment. -/
theorem encodedExternalStopped_prEvent_eq_native
    [DecidableEq Input] [DecidableEq Salt] [DecidableEq D] [SampleableType C]
    (coin : (z : Input) → PublicCoin (protocol z))
    (common : CommonChallenge Input Salt C coin)
    (codec : StrictCodec (Key Input Salt coin) D)
    (guards : (z : Input) → GuardSchedule Salt (coin z))
    (external : OracleComp (unifSpec + (D →ₒ C))
      (Option (Selection Input Salt W coin)))
    (event : Option (Outcome Input W protocol) → Prop) :
    Pr{let joint ← (randomOracleLoggedRun
      (encodedExternalStoppedExecution coin common codec guards external) ∅)}[
        event joint.1.1] =
    Pr{let joint ← (randomOracleLoggedRun
      (randomizedStoppedRestoredExecutionWithAdversaryLog coin guards
        (encodedNativeAdversary common codec external)) ∅)}[
        event joint.1.1.1] := by
  let : MeasurableSpace
      (Option (Outcome Input W protocol)) := ⊤
  have hresult := encodedExternalStopped_evalDist_result_eq_native
    coin common codec guards external
  have hevent := (evalDistEq_iff_evalDist_eq.mpr hresult).prEvent_eq event
  simpa only [prEvent_map] using hevent

/-- The actual external image-weighted query charge equals the native certificate experiment's
charge. The equality includes adversary failure, early rejection, and repeated cache hits. -/
theorem encodedExternalStopped_expectedCharge_eq_native
    [DecidableEq Input] [DecidableEq Salt] [DecidableEq D] [SampleableType C]
    (coin : (z : Input) → PublicCoin (protocol z))
    (common : CommonChallenge Input Salt C coin)
    (codec : StrictCodec (Key Input Salt coin) D)
    (guards : (z : Input) → GuardSchedule Salt (coin z))
    (external : OracleComp (unifSpec + (D →ₒ C))
      (Option (Selection Input Salt W coin)))
    (weight : Key Input Salt coin → ENNReal) :
    expectedFreshQueryCharge
      (encodedExternalStoppedExecution coin common codec guards external)
      (codec.encodedWeight weight) =
    expectedFreshQueryCharge
      (randomizedStoppedRestoredExecutionWithAdversaryLog coin guards
        (encodedNativeAdversary common codec external)) weight := by
  let externalProgram :=
    encodedExternalStoppedExecution coin common codec guards external
  let routedProgram := codec.routeProgram externalProgram ∅
  let nativeProgram := common.simulateNative routedProgram
  let nativeAdversary := encodedNativeAdversary common codec external
  let nativeJoint := randomizedStoppedRestoredExecutionWithAdversaryLog
    coin guards nativeAdversary
  have hsource := encodedExternalStopped_route_nativeValue coin common codec
    guards external
  have herase := randomizedStoppedExecution_eraseSourceLog coin guards nativeAdversary
  symm
  calc
    _ = expectedFreshQueryCharge
        (nativeStoppedExecution coin guards nativeAdversary) weight := by
          rw [← herase]
          exact (OracleComp.expectedFreshQueryCharge_map nativeJoint Prod.fst weight).symm
    _ = expectedFreshQueryCharge nativeProgram weight := by
          rw [← hsource]
          exact OracleComp.expectedFreshQueryCharge_map nativeProgram
            (fun result => result.1.1) weight
    _ = expectedFreshQueryCharge routedProgram weight :=
          common.expectedFreshQueryCharge_simulateNative routedProgram weight
    _ = expectedFreshQueryCharge externalProgram (codec.encodedWeight weight) :=
          codec.expectedNativeCharge_eq_external externalProgram weight

/-- The external stopped run's own weighted cost is bounded by its original adversary's
expected distinct queries and the round-error sum. This resource bound needs no security
certificate or acceptance hypothesis. -/
theorem encodedExternalStopped_expectedCharge_le_adversaryCount
    [DecidableEq D] [SampleableType C]
    (coin : (z : Input) → PublicCoin (protocol z))
    (common : CommonChallenge Input Salt C coin)
    (codec : StrictCodec (Key Input Salt coin) D)
    (guards : (z : Input) → GuardSchedule Salt (coin z))
    (errors : (z : Input) → Errors (coin z))
    (external : OracleComp (unifSpec + (D →ₒ C))
      (Option (Selection Input Salt W coin))) :
    expectedFreshQueryCharge
      (encodedExternalStoppedExecution coin common codec guards external)
      (codec.encodedWeight (keyError errors)) ≤
    maxError errors * expectedFreshQueryCharge external (fun _ => 1) +
      sumError errors := by
  classical
  rw [encodedExternalStopped_expectedCharge_eq_native]
  let nativeAdversary := encodedNativeAdversary common codec external
  have hcost := expectedStoppedFreshCharge_le_actualAdversary_and_sum
    coin guards errors nativeAdversary
  have hcount : expectedAdversaryFreshKeys coin nativeAdversary ≤
      expectedFreshQueryCharge external (fun _ => 1) := by
    rw [encodedNativeAdversary_expectedKeys_eq_route]
    rw [common.expectedFreshQueryCharge_simulateNative]
    exact codec.expectedNativeFreshKeys_le_external external
  calc
    _ ≤ maxError errors *
        expectedStoppedJointAdversaryKeys coin guards nativeAdversary +
          sumError errors := hcost.1.trans hcost.2
    _ = maxError errors * expectedAdversaryFreshKeys coin nativeAdversary +
          sumError errors := by
            rw [expectedStoppedJointAdversaryKeys_eq_expectedAdversaryFreshKeys]
    _ ≤ _ := by
      gcongr

/-- The actual external stopped verifier's bad accepted event is bounded by the image-weighted
distinct-key charge of its own complete, cached encoded-domain run. Off-image keys have weight
zero, and every executed verifier or adversary query remains in the observed log. -/
theorem encodedExternalStopped_knowledge_soundness_sharp
    [DecidableEq D] [SampleableType C]
    (coin : (z : Input) → PublicCoin (protocol z))
    (common : CommonChallenge Input Salt C coin)
    (codec : StrictCodec (Key Input Salt coin) D)
    (guards : (z : Input) → GuardSchedule Salt (coin z))
    (errors : (z : Input) → Errors (coin z))
    (external : OracleComp (unifSpec + (D →ₒ C))
      (Option (Selection Input Salt W coin)))
    (state : Input → KnowledgeState)
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
      (encodedExternalStoppedExecution coin common codec guards external) ∅)}[
      badStoppedRelation state extractor Rin Rout terminalWitness Z joint.1.1] ≤
    expectedFreshQueryCharge
      (encodedExternalStoppedExecution coin common codec guards external)
      (codec.encodedWeight (keyError errors)) := by
  classical
  rw [encodedExternalStopped_expectedCharge_eq_native]
  rw [encodedExternalStopped_prEvent_eq_native coin common codec guards
    external (badStoppedRelation state extractor Rin Rout terminalWitness Z)]
  exact randomizedStopped_badRelation_le_expectedFreshCharge
    coin guards errors (encodedNativeAdversary common codec external)
    state extractor Z preserving bounded Rin Rout terminalWitness inputLaw outputLaw

/-- The external bad accepted event also obeys the familiar query budget form. The budget is
the expected number of distinct keys queried by the original external adversary, including
off-image keys and failed selections; stopped verifier coin cost at most the error sum. -/
theorem encodedExternalStopped_knowledge_soundness_adversaryCount
    [DecidableEq D] [SampleableType C]
    (coin : (z : Input) → PublicCoin (protocol z))
    (common : CommonChallenge Input Salt C coin)
    (codec : StrictCodec (Key Input Salt coin) D)
    (guards : (z : Input) → GuardSchedule Salt (coin z))
    (errors : (z : Input) → Errors (coin z))
    (external : OracleComp (unifSpec + (D →ₒ C))
      (Option (Selection Input Salt W coin)))
    (state : Input → KnowledgeState)
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
      (encodedExternalStoppedExecution coin common codec guards external) ∅)}[
      badStoppedRelation state extractor Rin Rout terminalWitness Z joint.1.1] ≤
    maxError errors * expectedFreshQueryCharge external (fun _ => 1) +
      sumError errors := by
  exact (encodedExternalStopped_knowledge_soundness_sharp coin common codec guards
    errors external state extractor Z preserving bounded Rin Rout terminalWitness
    inputLaw outputLaw).trans
      (encodedExternalStopped_expectedCharge_le_adversaryCount
        coin common codec guards errors external)

end Interaction.Oracle.Security.StateRestoration
