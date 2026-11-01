/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.FiatShamir.InducedAdversary
public import ArkLib.Interaction.Oracle.FiatShamir.StoppedCompletionTransport
public import ArkLib.Interaction.Oracle.Security.StateRestorationStoppedBudget

/-!
# Knowledge security of native single-salt Fiat–Shamir

The public-coin protocol is a function of the statement. The adversary selects a statement, one
global salt, a full message proof for that statement's protocol and a terminal seed. Verification
runs the public-message native strategy executor. Both phases share the same lazy challenge oracle,
keyed by `(statement, salt)` and a prefix of the statement's protocol; verification stops before
querying a challenge whose prefix guard fails. Errors may depend on the statement and the node: the
bounds charge the largest node error over all statements per distinct adversary key, and the
largest path sum of errors for verification.
-/

@[expose] public section

open Interaction.Oracle OracleComp OracleSpec MeasureTheory

namespace Interaction.Oracle.FiatShamir

open Security Security.StateRestoration

universe w

variable {Statement GlobalSalt Witness : Type} {protocol : Statement → Protocol}
    {coin : (statement : Statement) → PublicCoin (protocol statement)}

/-- A malicious single-salt prover may interleave private coins and typed challenge queries. -/
abbrev SingleSaltAdversary (Statement GlobalSalt Witness : Type) {protocol : Statement → Protocol}
    (coin : (statement : Statement) → PublicCoin (protocol statement)) :=
  OracleComp (unifSpec + saltedSpec Statement GlobalSalt coin)
    (Option (SaltedSelection Statement GlobalSalt Witness coin))

/-- Execute native verification after the selected proof, retaining the adversary phase log.
Failure retains all spent queries. No verifier round is executed after a failed guard. -/
def singleSaltExecution (coin : (statement : Statement) → PublicCoin (protocol statement))
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (coin z.1))
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness coin) :
    OracleComp (unifSpec + saltedSpec Statement GlobalSalt coin)
      (Option (Outcome (Statement × GlobalSalt) Witness (saltedProtocol GlobalSalt protocol)) ×
        QueryLog (unifSpec + saltedSpec Statement GlobalSalt coin)) := do
  let (selected, log) ← adversary.withQueryLog
  match selected with
  | none => pure (none, log)
  | some ⟨statement, (salt, messages), witness⟩ =>
      let path ← simulateQ (restorationQueries (Statement × GlobalSalt) PUnit
          (saltedCoin GlobalSalt coin))
        (publicStoppedVerify (saltedCoin GlobalSalt coin) guards (statement, salt) messages)
      pure (path.map (fun p => ⟨(statement, salt), p, witness⟩), log)

private theorem withQueryLog_map_output {ι : Type} {spec : OracleSpec ι} {α β : Type}
    (f : α → β) (computation : OracleComp spec α) :
    (f <$> computation).withQueryLog =
      (fun result => (f result.1, result.2)) <$> computation.withQueryLog := by
  simp only [map_eq_pure_bind, withQueryLog_bind, withQueryLog_pure,
    pure_bind, Prod.map_apply, id_eq, List.append_nil]

/-- The native joint experiment is exactly the induced stopped-restoration program. -/
theorem singleSaltExecution_eq_stopped
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (coin z.1))
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness coin) :
    singleSaltExecution coin guards adversary =
      randomizedStoppedRestoredExecutionWithAdversaryLog (saltedCoin GlobalSalt coin) guards
        (inducedAdversary adversary) := by
  unfold singleSaltExecution randomizedStoppedRestoredExecutionWithAdversaryLog inducedAdversary
  rw [withQueryLog_map_output]
  simp only [map_eq_pure_bind, bind_assoc, pure_bind]
  congr 1
  funext selectedAndLog
  rcases selectedAndLog with ⟨selected, log⟩
  cases selected with
  | none => rfl
  | some selected =>
      rcases selected with ⟨statement, ⟨salt, messages⟩, witness⟩
      simp only [toRestorationSelection, randomizedStoppedCompletionAfterAdversaryLog,
        publicStoppedVerify_eq_stoppedComplete]

/-- The adversary phase includes its selected proof, ordered logs and final challenge cache. -/
abbrev SingleSaltAdversaryResult (Statement GlobalSalt Witness : Type) {protocol : Statement →
    Protocol}
    (coin : (statement : Statement) → PublicCoin (protocol statement)) :=
  (((Option (SaltedSelection Statement GlobalSalt Witness coin) ×
      QueryLog (unifSpec + saltedSpec Statement GlobalSalt coin)) ×
        QueryLog (saltedSpec Statement GlobalSalt coin)) ×
          (saltedSpec Statement GlobalSalt coin).QueryCache)

/-- Expected distinct challenge keys queried by the malicious prover, including failed outputs. -/
noncomputable def expectedSingleSaltAdversaryKeys
    [DecidableEq Statement] [DecidableEq GlobalSalt]
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness coin) : ENNReal :=
  letI : MeasurableSpace (SingleSaltAdversaryResult Statement GlobalSalt Witness coin) := ⊤
  ∫⁻ phase, ((freshKeysOfLog phase.1.2).card : ENNReal)
    ∂𝒟[randomOracleLoggedRun adversary.withQueryLog ∅]

/-- Repackaging a single-salt proof preserves the actual expected distinct adversary cost. -/
theorem expectedSingleSaltAdversaryKeys_eq_induced
    [DecidableEq Statement] [DecidableEq GlobalSalt]
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness coin) :
    expectedSingleSaltAdversaryKeys adversary =
      expectedAdversaryFreshKeys (saltedCoin GlobalSalt coin) (inducedAdversary adversary) := by
  let : MeasurableSpace (SingleSaltAdversaryResult Statement GlobalSalt Witness coin) := ⊤
  let : MeasurableSpace
      (((Option (Selection (Statement × GlobalSalt) PUnit Witness
          (saltedCoin GlobalSalt coin)) ×
          QueryLog (unifSpec + saltedSpec Statement GlobalSalt coin)) ×
            QueryLog (saltedSpec Statement GlobalSalt coin)) ×
              (saltedSpec Statement GlobalSalt coin).QueryCache) := ⊤
  unfold expectedSingleSaltAdversaryKeys expectedAdversaryFreshKeys inducedAdversary
  rw [withQueryLog_map_output, randomOracleLoggedRun_map,
    lintegral_evalDist_map_of_discrete]

/-- Native verification performs the prefix checks, then the explicit terminal acceptance check.
The terminal check is pure; source observations use a matched stateless handler. -/
def singleSaltVerify (coin : (statement : Statement) → PublicCoin (protocol statement))
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (coin z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol z.1).tree.ExecutionPath → Bool)
    (z : Statement × GlobalSalt) (messages : Messages PUnit (coin z.1)) :
    OracleComp (saltedSpec Statement GlobalSalt coin)
      (Option (protocol z.1).tree.ExecutionPath) :=
  (fun path => path.filter (accepts z)) <$>
    publicStoppedVerify (saltedCoin GlobalSalt coin) guards z messages

/-- Filter the returned transcript using the terminal check, leaving all phase logs intact. -/
def acceptSingleSaltResult
    (accepts : (z : Statement × GlobalSalt) → (protocol z.1).tree.ExecutionPath → Bool)
    (result : Option (Outcome (Statement × GlobalSalt) Witness (saltedProtocol GlobalSalt
        protocol)) ×
        QueryLog (unifSpec + saltedSpec Statement GlobalSalt coin)) :=
  (result.1.filter (fun selected => accepts selected.1 selected.2.1), result.2)

/-- The joint experiment whose returned value records actual prefix and terminal acceptance. -/
def singleSaltAcceptedExecution (coin : (statement : Statement) → PublicCoin (protocol statement))
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (coin z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol z.1).tree.ExecutionPath → Bool)
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness coin) :=
  acceptSingleSaltResult accepts <$> singleSaltExecution coin guards adversary

/-- Terminal filtering preserves the exact ordered challenge log and final lazy cache. -/
theorem singleSaltAcceptedExecution_loggedRun
    [DecidableEq Statement] [DecidableEq GlobalSalt]
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (coin z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol z.1).tree.ExecutionPath → Bool)
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness coin)
    (cache : (saltedSpec Statement GlobalSalt coin).QueryCache) :
    randomOracleLoggedRun (singleSaltAcceptedExecution coin guards accepts adversary) cache =
      (fun result => ((acceptSingleSaltResult accepts result.1.1, result.1.2), result.2)) <$>
        randomOracleLoggedRun (singleSaltExecution coin guards adversary) cache := by
  exact randomOracleLoggedRun_map _ _ _

/-- The accepted experiment executes the concrete native verifier after the adversary phase. -/
theorem singleSaltAcceptedExecution_eq_verify
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (coin z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol z.1).tree.ExecutionPath → Bool)
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness coin) :
    singleSaltAcceptedExecution coin guards accepts adversary = (do
      let (selected, log) ← adversary.withQueryLog
      match selected with
      | none => pure (none, log)
      | some ⟨statement, (salt, messages), witness⟩ =>
          let path ← simulateQ (restorationQueries (Statement × GlobalSalt) PUnit
              (saltedCoin GlobalSalt coin))
            (singleSaltVerify coin guards accepts (statement, salt) messages)
          pure (path.map (fun p => ⟨(statement, salt), p, witness⟩), log)) := by
  unfold singleSaltAcceptedExecution singleSaltExecution
  simp only [map_eq_pure_bind, bind_assoc]
  congr 1
  funext selectedAndLog
  rcases selectedAndLog with ⟨selected, log⟩
  cases selected with
  | none => rfl
  | some selected =>
      rcases selected with ⟨statement, ⟨salt, messages⟩, witness⟩
      simp only [singleSaltVerify, map_eq_pure_bind, simulateQ_bind, simulateQ_pure,
        bind_assoc, pure_bind]
      congr 1
      funext path
      cases path with
      | none => rfl
      | some path =>
          cases h : accepts (statement, salt) path <;>
            simp [acceptSingleSaltResult, Option.filter, h]

/-- Pure terminal rejection changes acceptance, but not the joint run's distinct-query charge. -/
theorem singleSaltAcceptedExecution_expectedCharge
    [DecidableEq Statement] [DecidableEq GlobalSalt]
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (coin z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol z.1).tree.ExecutionPath → Bool)
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness coin)
    (errors : (z : Statement × GlobalSalt) → Errors (coin z.1)) :
    expectedFreshQueryCharge (singleSaltAcceptedExecution coin guards accepts adversary)
        (keyError errors) =
      expectedFreshQueryCharge (singleSaltExecution coin guards adversary) (keyError errors) := by
  let : MeasurableSpace (StoppedJointResult (Statement × GlobalSalt) PUnit Witness
      (saltedCoin GlobalSalt coin)) := ⊤
  unfold expectedFreshQueryCharge
  rw [singleSaltAcceptedExecution_loggedRun, lintegral_evalDist_map_of_discrete]

/-- The filtered failure event requires both the actual terminal check and the output relation. -/
theorem badRelation_acceptSingleSaltResult
    (state : (Statement × GlobalSalt) → KnowledgeState.{w})
    (extractor : (z : Statement × GlobalSalt) → RoundExtractor (protocol z.1).tree
      (state z))
    (Rin : (z : Statement × GlobalSalt) → (state z).Witness → Prop)
    (Rout : (z : Statement × GlobalSalt) → (protocol z.1).tree.ExecutionPath →
      Witness → Prop)
    (seed : (z : Statement × GlobalSalt) → (path : (protocol z.1).tree.ExecutionPath) →
      Witness → ((extractor z).terminalState path).Witness)
    (Z : Set (Statement × GlobalSalt))
    (accepts : (z : Statement × GlobalSalt) → (protocol z.1).tree.ExecutionPath → Bool)
    (result : Option (Outcome (Statement × GlobalSalt) Witness (saltedProtocol GlobalSalt
        protocol)) ×
        QueryLog (unifSpec + saltedSpec Statement GlobalSalt coin)) :
    badStoppedRelation state extractor Rin Rout seed Z (acceptSingleSaltResult accepts result).1 ↔
      badStoppedRelation state extractor Rin
        (fun z path witness => accepts z path = true ∧ Rout z path witness) seed Z result.1 := by
  rcases result with ⟨selected, log⟩
  cases selected with
  | none => rfl
  | some selected =>
      rcases selected with ⟨z, path, witness⟩
      cases h : accepts z path <;>
        simp [acceptSingleSaltResult, Option.filter, badStoppedRelation, h]

/-- Native single-salt knowledge security from all-prefix local certificates. Acceptance runs
both the prefix guards and terminal check; extraction uses the supplied terminal seed verbatim. -/
theorem singleSalt_knowledge_soundness
    [DecidableEq Statement] [DecidableEq GlobalSalt]
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (coin z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol z.1).tree.ExecutionPath → Bool)
    (errors : (z : Statement × GlobalSalt) → Errors (coin z.1))
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness coin)
    (state : (Statement × GlobalSalt) → KnowledgeState.{w})
    (extractor : (z : Statement × GlobalSalt) → RoundExtractor (protocol z.1).tree
      (state z))
    (Z : Set (Statement × GlobalSalt))
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol z.1).roles)
    (bounded : ∀ z ∈ Z, RoundExtractor.IsLocallyBounded (extractor z)
      (protocol z.1).roles (errorSchedule (coin z.1) (errors z)))
    (Rin : (z : Statement × GlobalSalt) → (state z).Witness → Prop)
    (Rout : (z : Statement × GlobalSalt) → (protocol z.1).tree.ExecutionPath →
      Witness → Prop)
    (seed : (z : Statement × GlobalSalt) → (path : (protocol z.1).tree.ExecutionPath) →
      Witness → ((extractor z).terminalState path).Witness)
    (inputLaw : ∀ z witness, (state z).holds witness ↔ Rin z witness)
    (outputLaw : ∀ z path witness, accepts z path = true → Rout z path witness →
      ((extractor z).terminalState path).holds (seed z path witness)) :
    Pr{let joint ← (randomOracleLoggedRun
      (singleSaltAcceptedExecution coin guards accepts adversary) ∅)}[
      badStoppedRelation state extractor Rin Rout seed Z joint.1.1.1] ≤
    expectedFreshQueryCharge (singleSaltAcceptedExecution coin guards accepts adversary)
      (keyError errors) := by
  have bound := randomizedStopped_badRelation_le_expectedFreshCharge
    (saltedCoin GlobalSalt coin) guards errors
    (inducedAdversary adversary) state extractor Z preserving bounded Rin
    (fun z path witness => accepts z path = true ∧ Rout z path witness) seed inputLaw
    (fun z path witness accepted => outputLaw z path witness accepted.1 accepted.2)
  rw [← singleSaltExecution_eq_stopped guards adversary] at bound
  rw [singleSaltAcceptedExecution_expectedCharge]
  refine le_trans ?_ bound
  rw [singleSaltAcceptedExecution_loggedRun, prEvent_map]
  exact (prEvent_congr _ _ _
    (fun result : StoppedJointResult (Statement × GlobalSalt) PUnit Witness
        (saltedCoin GlobalSalt coin) =>
      badRelation_acceptSingleSaltResult state extractor Rin Rout seed Z accepts result.1.1)).le

/-- Expected cost of verifier challenge calls actually executed in the accepted-output experiment.
Terminal rejection does not erase the calls that preceded it. Cached hits are counted as calls. -/
noncomputable def expectedSingleSaltVerifierCost
    [DecidableEq Statement] [DecidableEq GlobalSalt]
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (coin z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol z.1).tree.ExecutionPath → Bool)
    (errors : (z : Statement × GlobalSalt) → Errors (coin z.1))
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness coin) : ENNReal :=
  letI : MeasurableSpace (StoppedJointResult (Statement × GlobalSalt) PUnit Witness
      (saltedCoin GlobalSalt coin)) := ⊤
  ∫⁻ result, stoppedVerifierRoundCost errors result.1.1.2 result.1.2
    ∂𝒟[randomOracleLoggedRun (singleSaltAcceptedExecution coin guards accepts adversary) ∅]

/-- Native execution preserves the exact expected cost of reached verifier coin. -/
theorem expectedSingleSaltVerifierCost_eq_stopped
    [DecidableEq Statement] [DecidableEq GlobalSalt]
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (coin z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol z.1).tree.ExecutionPath → Bool)
    (errors : (z : Statement × GlobalSalt) → Errors (coin z.1))
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness coin) :
    expectedSingleSaltVerifierCost guards accepts errors adversary =
      expectedStoppedVerifierRoundCost (saltedCoin GlobalSalt coin) guards errors
          (inducedAdversary adversary) := by
  let : MeasurableSpace (StoppedJointResult (Statement × GlobalSalt) PUnit Witness
      (saltedCoin GlobalSalt coin)) := ⊤
  unfold expectedSingleSaltVerifierCost expectedStoppedVerifierRoundCost
  rw [singleSaltAcceptedExecution_loggedRun, lintegral_evalDist_map_of_discrete,
    singleSaltExecution_eq_stopped guards adversary]
  rfl

/-- Actual native query costs separate adversary distinct keys from reached verifier calls. -/
theorem singleSalt_query_cost
    [DecidableEq Statement] [DecidableEq GlobalSalt]
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (coin z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol z.1).tree.ExecutionPath → Bool)
    (errors : (z : Statement × GlobalSalt) → Errors (coin z.1))
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness coin) :
    expectedFreshQueryCharge (singleSaltAcceptedExecution coin guards accepts adversary)
        (keyError errors) ≤
      maxError errors * expectedSingleSaltAdversaryKeys adversary +
        expectedSingleSaltVerifierCost guards accepts errors adversary ∧
    expectedSingleSaltVerifierCost guards accepts errors adversary ≤ sumError errors := by
  rw [singleSaltAcceptedExecution_expectedCharge,
    singleSaltExecution_eq_stopped guards adversary,
    expectedSingleSaltVerifierCost_eq_stopped guards accepts errors adversary,
    expectedSingleSaltAdversaryKeys_eq_induced]
  constructor
  · simpa only [expectedStoppedJointAdversaryKeys_eq_expectedAdversaryFreshKeys] using
      expectedStoppedFreshCharge_le_actualRounds (saltedCoin GlobalSalt coin) guards errors
          (inducedAdversary adversary)
  · exact expectedStoppedVerifierRoundCost_le_sum (saltedCoin GlobalSalt coin) guards errors
      (inducedAdversary adversary)

/-- An actual supported-run cap on the malicious prover bounds its expected distinct-key cost. -/
theorem expectedSingleSaltAdversaryKeys_le_queryBound
    [DecidableEq Statement] [DecidableEq GlobalSalt]
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness coin) (Q : ℕ)
    (queryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    expectedSingleSaltAdversaryKeys adversary ≤ Q := by
  rw [expectedSingleSaltAdversaryKeys_eq_induced]
  apply expectedAdversaryFreshKeys_le_queryBound (saltedCoin GlobalSalt coin)
    (inducedAdversary adversary) Q
  intro phase supported
  unfold inducedAdversary at supported
  rw [withQueryLog_map_output, randomOracleLoggedRun_map, support_map] at supported
  obtain ⟨original, originalSupported, rfl⟩ := supported
  exact queryBound original originalSupported

/-- The actual malicious prover query cap yields the standard `Q * max error + sum errors`
bound. The named extractor and seed are fixed independently of the query budget. -/
theorem singleSalt_knowledge_soundness_queryBound
    [DecidableEq Statement] [DecidableEq GlobalSalt]
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (coin z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol z.1).tree.ExecutionPath → Bool)
    (errors : (z : Statement × GlobalSalt) → Errors (coin z.1))
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness coin)
    (state : (Statement × GlobalSalt) → KnowledgeState.{w})
    (extractor : (z : Statement × GlobalSalt) → RoundExtractor (protocol z.1).tree
      (state z))
    (Z : Set (Statement × GlobalSalt))
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol z.1).roles)
    (bounded : ∀ z ∈ Z, RoundExtractor.IsLocallyBounded (extractor z)
      (protocol z.1).roles (errorSchedule (coin z.1) (errors z)))
    (Rin : (z : Statement × GlobalSalt) → (state z).Witness → Prop)
    (Rout : (z : Statement × GlobalSalt) → (protocol z.1).tree.ExecutionPath →
      Witness → Prop)
    (seed : (z : Statement × GlobalSalt) → (path : (protocol z.1).tree.ExecutionPath) →
      Witness → ((extractor z).terminalState path).Witness)
    (inputLaw : ∀ z witness, (state z).holds witness ↔ Rin z witness)
    (outputLaw : ∀ z path witness, accepts z path = true → Rout z path witness →
      ((extractor z).terminalState path).holds (seed z path witness))
    (Q : ℕ)
    (queryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    Pr{let joint ← (randomOracleLoggedRun
      (singleSaltAcceptedExecution coin guards accepts adversary) ∅)}[
      badStoppedRelation state extractor Rin Rout seed Z joint.1.1.1] ≤
    Q * maxError errors + sumError errors := by
  have security := singleSalt_knowledge_soundness guards accepts errors adversary
    state extractor Z preserving bounded Rin Rout seed inputLaw outputLaw
  have cost := singleSalt_query_cost guards accepts errors adversary
  calc
    _ ≤ expectedFreshQueryCharge (singleSaltAcceptedExecution coin guards accepts adversary)
          (keyError errors) := security
    _ ≤ maxError errors * expectedSingleSaltAdversaryKeys adversary +
          expectedSingleSaltVerifierCost guards accepts errors adversary := cost.1
    _ ≤ maxError errors * Q + sumError errors :=
      add_le_add (mul_le_mul' le_rfl (expectedSingleSaltAdversaryKeys_le_queryBound
        adversary Q queryBound)) cost.2
    _ = _ := by rw [mul_comm]

/-- Uniform local errors and an actual adversary cap give the standard `(Q + k) * error`
query charge, where every path of every statement's protocol pays at most `k * error`. Early
rejection can make the sharper expected-cost bound strictly smaller. -/
theorem singleSalt_uniform_query_cost
    [DecidableEq Statement] [DecidableEq GlobalSalt]
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (coin z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol z.1).tree.ExecutionPath → Bool)
    (error : ENNReal)
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness coin) (Q k : ℕ)
    (queryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q)
    (path_le : ∀ statement, pathError (coin statement) (fun _ => error) ≤ k * error) :
    expectedFreshQueryCharge (singleSaltAcceptedExecution coin guards accepts adversary)
      (keyError (fun _ _ => error)) ≤ (Q + k : ℕ) * error := by
  have cost := singleSalt_query_cost guards accepts (fun _ _ => error) adversary
  have maximum : maxError (coin := saltedCoin GlobalSalt coin) (fun _ _ => error) ≤ error :=
    iSup_le fun _ => iSup_le fun _ => le_rfl
  have total : sumError (coin := saltedCoin GlobalSalt coin) (fun _ _ => error) ≤
      (k : ENNReal) * error :=
    iSup_le fun z => path_le z.1
  calc
    _ ≤ maxError (coin := saltedCoin GlobalSalt coin) (fun _ _ => error) *
          expectedSingleSaltAdversaryKeys adversary +
          expectedSingleSaltVerifierCost guards accepts (fun _ _ => error) adversary := cost.1
    _ ≤ error * Q + (k : ENNReal) * error :=
      add_le_add (mul_le_mul' maximum
        (expectedSingleSaltAdversaryKeys_le_queryBound adversary Q queryBound))
        (cost.2.trans total)
    _ = _ := by rw [Nat.cast_add, add_mul, mul_comm error (Q : ENNReal)]

end Interaction.Oracle.FiatShamir
