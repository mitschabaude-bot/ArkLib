/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.StateRestorationRandomizedKnowledge

/-!
# Stopped state restoration

A pure guard checks each authored message prefix before that round's challenge is queried.
The adversary still supplies complete messages, so rejection needs no invented message. A guard
may depend on the input and all earlier messages, salts, and challenges through its continuation,
but it cannot inspect its own or a later challenge. The stopped completion reads the same cached
restoration oracle as the adversary and returns no full path after rejection.
-/

@[expose] public section

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec MeasureTheory
open Interaction.Oracle.TypeTree

namespace Interaction.Oracle.Security.StateRestoration

universe w

variable {Input Salt W : Type} {rounds : Input → List Round}

/-- A tree of pure, prefix-dependent guards. The continuation can close over the current
message, salt, and sampled challenge; the current guard itself cannot read that challenge. -/
def GuardSchedule (Salt : Type) : List Round → Type
  | [] => PUnit
  | round :: rounds => (round.Message → Salt → Bool) ×
      (round.Message → Salt → round.Challenge → GuardSchedule Salt rounds)

/-- Complete an authored message sequence against the prefix oracle only while its guards pass.
Every guard runs before the corresponding hash access. Returned failure retains all preceding
oracle effects. -/
def stoppedCompletePrefix {Salt : Type} : (rounds : List Round) →
    GuardSchedule Salt rounds → Messages Salt rounds →
      OracleComp (prefixSpec Salt rounds) (Option (protocol rounds).tree.ExecutionPath)
  | [], _, _ => pure (some PUnit.unit)
  | round :: rounds, guards, (message, salt, messages) => do
      if !guards.1 message salt then
        return none
      let challenge ← liftM ((prefixSpec Salt (round :: rounds)).query
        (Prefix.here message salt))
      let suffix ← simulateQ (prependQuery message salt)
        (stoppedCompletePrefix rounds (guards.2 message salt challenge) messages)
      return suffix.map fun path => ⟨message, challenge, path⟩

/-- Complete the selected input's message sequence only while that input's guards pass, at the
keys of the selected input. -/
def stoppedComplete {Input Salt : Type} (rounds : Input → List Round)
    (guards : (z : Input) → GuardSchedule Salt (rounds z)) (z : Input)
    (messages : Messages Salt (rounds z)) :
    OracleComp (oracleSpec Input Salt rounds) (Option (protocol (rounds z)).tree.ExecutionPath) :=
  simulateQ (inputQuery z) (stoppedCompletePrefix (rounds z) (guards z) messages)

/-- Fixed-table result of stopped prefix completion. It agrees with the ordinary reconstructed
path on acceptance, and has no full path when a guard rejects. -/
def prefixStoppedPath {Salt : Type} : (rounds : List Round) →
    GuardSchedule Salt rounds → Messages Salt rounds →
      PrefixTable Salt rounds → Option (protocol rounds).tree.ExecutionPath
  | [], _, _, _ => some PUnit.unit
  | _ :: rounds, guards, (message, salt, messages), table =>
      if guards.1 message salt then
        let challenge := table (Prefix.here message salt)
        (prefixStoppedPath rounds (guards.2 message salt challenge) messages
          (fun q => table (Prefix.later message salt q))).map
            (fun path => ⟨message, challenge, path⟩)
      else none

/-- Ordered prefixes actually requested by stopped prefix completion under a fixed table. A
rejecting round and every subsequent round contribute no prefix. -/
def prefixStoppedKeys {Salt : Type} : (rounds : List Round) →
    GuardSchedule Salt rounds → Messages Salt rounds →
      PrefixTable Salt rounds → List (Prefix Salt rounds)
  | [], _, _, _ => []
  | _ :: rounds, guards, (message, salt, messages), table =>
      if guards.1 message salt then
        let challenge := table (Prefix.here message salt)
        Prefix.here message salt ::
          (prefixStoppedKeys rounds (guards.2 message salt challenge) messages
            (fun q => table (Prefix.later message salt q))).map (Prefix.later message salt)
      else []

/-- Pure guard acceptance over the reconstructed prefix answer table. -/
def prefixGuardsPass {Salt : Type} : (rounds : List Round) →
    GuardSchedule Salt rounds → Messages Salt rounds → PrefixTable Salt rounds → Bool
  | [], _, _, _ => true
  | _ :: rounds, guards, (message, salt, messages), table =>
      guards.1 message salt &&
        prefixGuardsPass rounds
          (guards.2 message salt (table (Prefix.here message salt))) messages
          (fun q => table (Prefix.later message salt q))

/-- Fixed-table result of stopped completion of the selected input. -/
def stoppedPath {Input Salt : Type} (rounds : Input → List Round)
    (guards : (z : Input) → GuardSchedule Salt (rounds z)) (z : Input)
    (messages : Messages Salt (rounds z)) (table : Table Input Salt rounds) :
    Option (protocol (rounds z)).tree.ExecutionPath :=
  prefixStoppedPath (rounds z) (guards z) messages (Table.fibre table z)

/-- Ordered keys actually requested by stopped completion of the selected input. -/
def stoppedKeys {Input Salt : Type} (rounds : Input → List Round)
    (guards : (z : Input) → GuardSchedule Salt (rounds z)) (z : Input)
    (messages : Messages Salt (rounds z)) (table : Table Input Salt rounds) :
    List (Key Input Salt rounds) :=
  (prefixStoppedKeys (rounds z) (guards z) messages (Table.fibre table z)).map (Sigma.mk z)

/-- Pure guard acceptance of the selected input over the reconstructed answer table. -/
def guardsPass {Input Salt : Type} (rounds : Input → List Round)
    (guards : (z : Input) → GuardSchedule Salt (rounds z)) (z : Input)
    (messages : Messages Salt (rounds z)) (table : Table Input Salt rounds) : Bool :=
  prefixGuardsPass (rounds z) (guards z) messages (Table.fibre table z)

/-- On a fully accepted guard path, stopped reconstruction is the existing full path. -/
theorem prefixStoppedPath_eq_some_prefixPath {Salt : Type}
    (rounds : List Round) (guards : GuardSchedule Salt rounds)
    (messages : Messages Salt rounds) (table : PrefixTable Salt rounds)
    (passed : prefixGuardsPass rounds guards messages table = true) :
    prefixStoppedPath rounds guards messages table = some (prefixPath rounds messages table) := by
  revert guards messages table
  induction rounds with
  | nil => intro guards messages table passed; rfl
  | cons round rounds ih =>
      intro guards messages table passed
      rcases messages with ⟨message, salt, messages⟩
      simp only [prefixGuardsPass, Bool.and_eq_true] at passed
      simp only [prefixStoppedPath, passed.1, ite_true, prefixPath]
      rw [ih _ _ _ passed.2]
      rfl

/-- On a fully accepted guard path, stopped reconstruction is the existing full native path. -/
theorem stoppedPath_eq_some_completedPath {Input Salt : Type}
    (rounds : Input → List Round) (guards : (z : Input) → GuardSchedule Salt (rounds z))
    (z : Input) (messages : Messages Salt (rounds z)) (table : Table Input Salt rounds)
    (passed : guardsPass rounds guards z messages table = true) :
    stoppedPath rounds guards z messages table =
      some (completedPath rounds z messages table) :=
  prefixStoppedPath_eq_some_prefixPath (rounds z) (guards z) messages _ passed

/-- A stopped prefix result can be a full path only if all guards passed. -/
theorem prefixStoppedPath_some_implies_pass {Salt : Type}
    (rounds : List Round) (guards : GuardSchedule Salt rounds)
    (messages : Messages Salt rounds) (table : PrefixTable Salt rounds)
    {path : (protocol rounds).tree.ExecutionPath}
    (result : prefixStoppedPath rounds guards messages table = some path) :
    prefixGuardsPass rounds guards messages table = true := by
  revert guards messages table path
  induction rounds with
  | nil => intro guards messages table path result; rfl
  | cons round rounds ih =>
      intro guards messages table path result
      rcases messages with ⟨message, salt, messages⟩
      simp only [prefixStoppedPath] at result
      split at result
      · rename_i hguard
        simp only [prefixGuardsPass, hguard, Bool.true_and]
        cases hsuffix : prefixStoppedPath rounds
            (guards.2 message salt (table (Prefix.here message salt))) messages
            (fun q => table (Prefix.later message salt q)) with
        | none =>
            simp only [hsuffix] at result
            cases result
        | some tail =>
            exact ih _ _ _ hsuffix
      · simp at result

/-- A stopped result can be a full path only if all guards passed. -/
theorem stoppedPath_some_implies_pass {Input Salt : Type}
    (rounds : Input → List Round) (guards : (z : Input) → GuardSchedule Salt (rounds z))
    (z : Input) (messages : Messages Salt (rounds z)) (table : Table Input Salt rounds)
    {path : (protocol (rounds z)).tree.ExecutionPath}
    (result : stoppedPath rounds guards z messages table = some path) :
    guardsPass rounds guards z messages table = true :=
  prefixStoppedPath_some_implies_pass (rounds z) (guards z) messages _ result

/-- An accepted stopped prefix run queries exactly the full path's prefixes. -/
theorem prefixStoppedKeys_of_pass {Salt : Type}
    (rounds : List Round) (guards : GuardSchedule Salt rounds)
    (messages : Messages Salt rounds) (table : PrefixTable Salt rounds)
    (passed : prefixGuardsPass rounds guards messages table = true) :
    prefixStoppedKeys rounds guards messages table = prefixKeys rounds messages := by
  revert guards messages table
  induction rounds with
  | nil => intro guards messages table passed; rfl
  | cons round rounds ih =>
      intro guards messages table passed
      rcases messages with ⟨message, salt, messages⟩
      simp only [prefixGuardsPass, Bool.and_eq_true] at passed
      simp only [prefixStoppedKeys, passed.1, ite_true, prefixKeys]
      rw [ih _ _ _ passed.2]

/-- An accepted stopped run queries exactly the full path's challenge keys. -/
theorem stoppedKeys_of_pass {Input Salt : Type}
    (rounds : Input → List Round) (guards : (z : Input) → GuardSchedule Salt (rounds z))
    (z : Input) (messages : Messages Salt (rounds z)) (table : Table Input Salt rounds)
    (passed : guardsPass rounds guards z messages table = true) :
    stoppedKeys rounds guards z messages table = completionKeys rounds z messages := by
  simp only [stoppedKeys, completionKeys]
  rw [prefixStoppedKeys_of_pass (rounds z) (guards z) messages _ passed]

set_option backward.isDefEq.respectTransparency false in
/-- The stopped prefix completion's fixed-table result uses the same path reconstruction. -/
theorem stoppedCompletePrefix_eval {Salt : Type}
    (rounds : List Round) (guards : GuardSchedule Salt rounds)
    (messages : Messages Salt rounds) (table : PrefixTable Salt rounds) :
    evalWithAnswerFn (QueryImpl.ofFn table) (stoppedCompletePrefix rounds guards messages) =
      prefixStoppedPath rounds guards messages table := by
  induction rounds with
  | nil => rfl
  | cons round rounds ih =>
      rcases messages with ⟨message, salt, messages⟩
      simp only [stoppedCompletePrefix]
      by_cases hg : guards.1 message salt = true
      · simp only [hg, Bool.not_true, Bool.false_eq_true, ite_false,
          evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query,
          QueryImpl.ofFn_apply, evalWithAnswerFn_simulateQ,
          prependQuery, evalWithAnswerFn_pure, prefixStoppedPath, ite_true]
        congr 1
        change evalWithAnswerFn
            (QueryImpl.ofFn (fun q => table (Prefix.later message salt q)))
            (stoppedCompletePrefix rounds
              (guards.2 message salt (table (Prefix.here message salt))) messages) =
          prefixStoppedPath rounds
            (guards.2 message salt (table (Prefix.here message salt))) messages
            (fun q => table (Prefix.later message salt q))
        simpa only [QueryImpl.ofFn_apply] using
          ih (guards.2 message salt (table (Prefix.here message salt)))
            messages (fun q => table (Prefix.later message salt q))
      · have hg' : guards.1 message salt = false := Bool.eq_false_iff.mpr hg
        simp [hg', prefixStoppedPath]

/-- The stopped completion's fixed-table result uses the same native path reconstruction. -/
theorem stoppedComplete_eval {Input Salt : Type}
    (rounds : Input → List Round) (guards : (z : Input) → GuardSchedule Salt (rounds z))
    (z : Input) (messages : Messages Salt (rounds z)) (table : Table Input Salt rounds) :
    evalWithAnswerFn (QueryImpl.ofFn table) (stoppedComplete rounds guards z messages) =
      stoppedPath rounds guards z messages table := by
  simp only [stoppedComplete, evalWithAnswerFn_simulateQ, inputQuery,
    evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply, stoppedPath]
  exact stoppedCompletePrefix_eval (rounds z) (guards z) messages (Table.fibre table z)

/-- The fixed-table ordered prefix-query log contains precisely the executed prefixes. -/
theorem stoppedCompletePrefix_log_keys {Salt : Type}
    (rounds : List Round) (guards : GuardSchedule Salt rounds)
    (messages : Messages Salt rounds) (table : PrefixTable Salt rounds) :
    (tableQueryLog (stoppedCompletePrefix rounds guards messages) table).map Sigma.fst =
      prefixStoppedKeys rounds guards messages table := by
  induction rounds with
  | nil => simp [stoppedCompletePrefix, prefixStoppedKeys]
  | cons round rounds ih =>
      rcases messages with ⟨message, salt, messages⟩
      by_cases hg : guards.1 message salt = true
      · simp only [stoppedCompletePrefix, hg, Bool.not_true, Bool.false_eq_true, ite_false,
          tableQueryLog_bind, tableQueryLog_pure, List.append_nil,
          tableQueryLog_simulateQ, prependQuery,
          evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply,
          tableQueryLog_query, List.singleton_append, List.map_cons,
          ← List.map_eq_flatMap, List.map_map, Function.comp_def,
          prefixStoppedKeys, ite_true]
        congr 1
        simpa only [List.flatMap_singleton, List.map_map, Function.comp_def] using
          congrArg (List.map (Prefix.later message salt))
            (ih (guards.2 message salt (table (Prefix.here message salt)))
              messages (fun q => table (Prefix.later message salt q)))
      · have hg' : guards.1 message salt = false := Bool.eq_false_iff.mpr hg
        simp [stoppedCompletePrefix, prefixStoppedKeys, hg']

/-- The fixed-table ordered query log contains precisely the executed challenge keys. -/
theorem stoppedComplete_log_keys {Input Salt : Type}
    (rounds : Input → List Round) (guards : (z : Input) → GuardSchedule Salt (rounds z))
    (z : Input) (messages : Messages Salt (rounds z)) (table : Table Input Salt rounds) :
    (tableQueryLog (stoppedComplete rounds guards z messages) table).map Sigma.fst =
      stoppedKeys rounds guards z messages table := by
  simp only [stoppedComplete, tableQueryLog_simulateQ, inputQuery, evalWithAnswerFn_liftM_query,
    QueryImpl.ofFn_apply, tableQueryLog_query, ← List.map_eq_flatMap, List.map_map,
    Function.comp_def, stoppedKeys]
  rw [← stoppedCompletePrefix_log_keys (rounds z) (guards z) messages (Table.fibre table z),
    List.map_map]
  rfl

/-- Run a randomized adversary and then stop completion at the first failing guard. The source
phase is logged as returned data without creating new oracle effects. -/
def randomizedStoppedCompletionAfterAdversaryLog (rounds : Input → List Round)
    (guards : (z : Input) → GuardSchedule Salt (rounds z))
    (selectedAndLog : Option (Selection Input Salt W rounds) ×
      QueryLog (unifSpec + oracleSpec Input Salt rounds)) :
    OracleComp (unifSpec + oracleSpec Input Salt rounds)
      (Option (Outcome Input W rounds) ×
        QueryLog (unifSpec + oracleSpec Input Salt rounds)) := do
  match selectedAndLog.1 with
  | none => pure (none, selectedAndLog.2)
  | some ⟨z, messages, witness⟩ =>
      let path ← simulateQ (restorationQueries Input Salt rounds)
        (stoppedComplete rounds guards z messages)
      pure (path.map (fun p => ⟨z, p, witness⟩), selectedAndLog.2)

/-- The actual joint stopped game shares one lazy random-oracle cache across both phases. -/
def randomizedStoppedRestoredExecutionWithAdversaryLog (rounds : Input → List Round)
    (guards : (z : Input) → GuardSchedule Salt (rounds z))
    (adversary : RandomizedRestorationAdversary Input Salt W rounds) :
    OracleComp (unifSpec + oracleSpec Input Salt rounds)
      (Option (Outcome Input W rounds) ×
        QueryLog (unifSpec + oracleSpec Input Salt rounds)) :=
  adversary.withQueryLog >>=
    randomizedStoppedCompletionAfterAdversaryLog rounds guards

/-- The same-cache stopped handoff includes the exact result, ordered hash log, and final cache.
This law includes failed adversary selections and rejected guard paths. -/
theorem randomizedStoppedRestoredExecutionWithAdversaryLog_handoff
    [DecidableEq Input] [DecidableEq Salt]
    (rounds : Input → List Round) (guards : (z : Input) → GuardSchedule Salt (rounds z))
    (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (cache : (oracleSpec Input Salt rounds).QueryCache) :
    randomOracleLoggedRun
        (randomizedStoppedRestoredExecutionWithAdversaryLog rounds guards adversary) cache =
      randomOracleLoggedRun adversary.withQueryLog cache >>= fun phase =>
        (fun suffix => ((suffix.1.1, phase.1.2 ++ suffix.1.2), suffix.2)) <$>
          randomOracleLoggedRun
            (randomizedStoppedCompletionAfterAdversaryLog rounds guards phase.1.1)
            phase.2 := by
  exact randomOracleLoggedRun_bind adversary.withQueryLog
    (randomizedStoppedCompletionAfterAdversaryLog rounds guards) cache

/-- Fixed-table version of the same joint handoff, used to derive the bad-key witness from
the all-prefix certificate on each supported private-randomness branch. -/
theorem randomizedStoppedRestoredExecutionWithAdversaryLog_fixedTable_handoff
    [DecidableEq Input] [DecidableEq Salt]
    (rounds : Input → List Round) (guards : (z : Input) → GuardSchedule Salt (rounds z))
    (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (table : Table Input Salt rounds)
    (cache : (oracleSpec Input Salt rounds).QueryCache) :
    fixedTableLoggedRun
        (randomizedStoppedRestoredExecutionWithAdversaryLog rounds guards adversary)
        table cache =
      fixedTableLoggedRun adversary.withQueryLog table cache >>= fun phase =>
        (fun suffix => ((suffix.1.1, phase.1.2 ++ suffix.1.2), suffix.2)) <$>
          fixedTableLoggedRun
            (randomizedStoppedCompletionAfterAdversaryLog rounds guards phase.1.1)
            table phase.2 := by
  exact fixedTableLoggedRun_bind adversary.withQueryLog
    (randomizedStoppedCompletionAfterAdversaryLog rounds guards) table cache

/-- Accepted fixed-table stopped completion is the existing full native execution path, with
exactly its full challenge-key log. Rejected paths retain their shorter ordered log. -/
theorem fixedTable_stoppedCompletion_result_keys [DecidableEq Input] [DecidableEq Salt]
    (rounds : Input → List Round) (guards : (z : Input) → GuardSchedule Salt (rounds z))
    (z : Input) (messages : Messages Salt (rounds z))
    (table : Table Input Salt rounds)
    (cache : (oracleSpec Input Salt rounds).QueryCache)
    (agree : cache.AgreesWithFn (QueryImpl.ofFn table))
    (result : ((Option (protocol (rounds z)).tree.ExecutionPath ×
      QueryLog (oracleSpec Input Salt rounds)) ×
      (oracleSpec Input Salt rounds).QueryCache))
    (supported : result ∈ support (fixedTableLoggedRun
      (simulateQ (restorationQueries Input Salt rounds)
        (stoppedComplete rounds guards z messages)) table cache)) :
    result.1.1 = stoppedPath rounds guards z messages table ∧
      result.1.2.map Sigma.fst = stoppedKeys rounds guards z messages table := by
  obtain ⟨hpath, hlog, _⟩ := fixedTable_restorationQueries_run
    (stoppedComplete rounds guards z messages) table cache agree result supported
  exact ⟨hpath.trans (stoppedComplete_eval rounds guards z messages table),
    by rw [hlog]; exact stoppedComplete_log_keys rounds guards z messages table⟩

/-- The terminal seed is supplied by the adversary, then validated by the accepted relation.
An invalid named backward extraction on an accepted stopped path has a bad key among the actual
queried keys of that stopped completion. -/
theorem badExtractOnStoppedPath_has_bad_key
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol (rounds z)).tree (state z))
    (Z : Set Input)
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol (rounds z)).roles)
    (terminalWitness : (z : Input) → (path : (protocol (rounds z)).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (guards : (z : Input) → GuardSchedule Salt (rounds z))
    (z : Input) (messages : Messages Salt (rounds z)) (witness : W)
    (table : Table Input Salt rounds)
    (path : (protocol (rounds z)).tree.ExecutionPath)
    (accepted : stoppedPath rounds guards z messages table = some path)
    (bad : badExtractOnPath state extractor Z terminalWitness (some ⟨z, path, witness⟩)) :
    ∃ key ∈ stoppedKeys rounds guards z messages table,
      badKey state extractor Z key table := by
  have passed := stoppedPath_some_implies_pass rounds guards z messages table accepted
  have hpath := stoppedPath_eq_some_completedPath rounds guards z messages table passed
  have heq : path = completedPath rounds z messages table :=
    Option.some.inj (accepted.symm.trans hpath)
  subst path
  obtain ⟨key, hkey, hbad⟩ := badExtractOnPath_completion
    state extractor Z preserving terminalWitness z messages witness table bad
  exact ⟨key, by rw [stoppedKeys_of_pass rounds guards z messages table passed]; exact hkey,
    hbad⟩

/-- A selected source result executes only its stopped completion, preserving the source log.
The suffix log is exactly the list of keys visited before acceptance or rejection. -/
theorem fixedTable_stoppedCompletionAfterAdversaryLog_selected
    [DecidableEq Input] [DecidableEq Salt]
    (rounds : Input → List Round) (guards : (z : Input) → GuardSchedule Salt (rounds z))
    (z : Input) (messages : Messages Salt (rounds z)) (witness : W)
    (adversaryLog : QueryLog (unifSpec + oracleSpec Input Salt rounds))
    (table : Table Input Salt rounds)
    (cache : (oracleSpec Input Salt rounds).QueryCache)
    (agree : cache.AgreesWithFn (QueryImpl.ofFn table))
    (result : (((Option (Outcome Input W rounds) ×
      QueryLog (unifSpec + oracleSpec Input Salt rounds)) ×
        QueryLog (oracleSpec Input Salt rounds)) ×
          (oracleSpec Input Salt rounds).QueryCache))
    (supported : result ∈ support (fixedTableLoggedRun
      (randomizedStoppedCompletionAfterAdversaryLog rounds guards
        (some ⟨z, messages, witness⟩, adversaryLog)) table cache)) :
    result.1.1 =
      ((stoppedPath rounds guards z messages table).map
        (fun path => ⟨z, path, witness⟩), adversaryLog) ∧
      result.1.2.map Sigma.fst = stoppedKeys rounds guards z messages table := by
  have hprogram : randomizedStoppedCompletionAfterAdversaryLog rounds guards
      (some ⟨z, messages, witness⟩, adversaryLog) =
      (fun path => (path.map (fun p => ⟨z, p, witness⟩), adversaryLog)) <$>
        simulateQ (restorationQueries Input Salt rounds)
          (stoppedComplete rounds guards z messages) := by
    simp only [randomizedStoppedCompletionAfterAdversaryLog, map_eq_pure_bind]
  rw [hprogram, fixedTableLoggedRun_map, support_map] at supported
  obtain ⟨completion, hcompletion, rfl⟩ := supported
  obtain ⟨hpath, hkeys⟩ := fixedTable_stoppedCompletion_result_keys
    rounds guards z messages table cache agree completion hcompletion
  exact ⟨by simp [hpath], hkeys⟩

/-- Fixed-table trace decomposition of the actual stopped game. The suffix log is retained even
when a guard rejects; a failed source selection has no suffix queries. -/
theorem fixedTable_stopped_trace [DecidableEq Input] [DecidableEq Salt]
    (rounds : Input → List Round) (guards : (z : Input) → GuardSchedule Salt (rounds z))
    (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (table : Table Input Salt rounds)
    (result : (((Option (Outcome Input W rounds) ×
      QueryLog (unifSpec + oracleSpec Input Salt rounds)) ×
        QueryLog (oracleSpec Input Salt rounds)) ×
          (oracleSpec Input Salt rounds).QueryCache))
    (supported : result ∈ support (fixedTableLoggedRun
      (randomizedStoppedRestoredExecutionWithAdversaryLog rounds guards adversary)
      table ∅)) :
    (result.1.1.1 = none ∧ result.1.2 = result.1.1.2.snd) ∨
      ∃ z messages witness suffixLog,
        result.1.1.1 =
          (stoppedPath rounds guards z messages table).map
            (fun path => ⟨z, path, witness⟩) ∧
        result.1.2 = result.1.1.2.snd ++ suffixLog ∧
        suffixLog.map Sigma.fst = stoppedKeys rounds guards z messages table := by
  rw [randomizedStoppedRestoredExecutionWithAdversaryLog_fixedTable_handoff]
    at supported
  obtain ⟨phase, hphase, hrest⟩ := (mem_support_bind_iff _ _ _).mp supported
  rw [support_map] at hrest
  obtain ⟨suffix, hsuffix, rfl⟩ := hrest
  have hsource := fixedTable_withQueryLog_hashLog_eq adversary table ∅ phase hphase
  have hagree : phase.2.AgreesWithFn (QueryImpl.ofFn table) :=
    fixedTable_cache_agrees adversary.withQueryLog table ∅ (by simp [QueryCache.AgreesWithFn])
      phase hphase
  rcases phase with ⟨⟨⟨selected, sourceLog⟩, hashLog⟩, phaseCache⟩
  cases selected with
  | none =>
      have hsuffix' : suffix = (((none, sourceLog), []), phaseCache) := by
        simpa [randomizedStoppedCompletionAfterAdversaryLog, fixedTableLoggedRun]
          using hsuffix
      subst suffix
      left
      simp [hsource]
  | some selected =>
      rcases selected with ⟨z, messages, witness⟩
      obtain ⟨hout, hkeys⟩ := fixedTable_stoppedCompletionAfterAdversaryLog_selected
        rounds guards z messages witness sourceLog table phaseCache hagree suffix hsuffix
      right
      refine ⟨z, messages, witness, suffix.1.2, ?_, ?_, hkeys⟩
      · exact congrArg Prod.fst hout
      · simp only [hsource, hout]

/-- A failed extraction on a supported stopped run is witnessed by a bad key in that same
run's ordered hash log. This implication comes from preservation and the full accepted path. -/
theorem fixedTable_stopped_badExtract_has_bad_query [DecidableEq Input] [DecidableEq Salt]
    (rounds : Input → List Round) (guards : (z : Input) → GuardSchedule Salt (rounds z))
    (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol (rounds z)).tree (state z))
    (Z : Set Input)
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol (rounds z)).roles)
    (terminalWitness : (z : Input) → (path : (protocol (rounds z)).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (table : Table Input Salt rounds)
    (result : (((Option (Outcome Input W rounds) ×
      QueryLog (unifSpec + oracleSpec Input Salt rounds)) ×
        QueryLog (oracleSpec Input Salt rounds)) ×
          (oracleSpec Input Salt rounds).QueryCache))
    (supported : result ∈ support (fixedTableLoggedRun
      (randomizedStoppedRestoredExecutionWithAdversaryLog rounds guards adversary)
      table ∅))
    (bad : badExtractOnPath state extractor Z terminalWitness result.1.1.1) :
    ∃ query ∈ result.1.2, badKey state extractor Z query.1 table := by
  rcases fixedTable_stopped_trace rounds guards adversary table result supported with
    ⟨hnone, _⟩ | ⟨z, messages, witness, suffixLog, hresult, hlog, hkeys⟩
  · rw [hnone] at bad
    exact False.elim bad
  · cases hpath : stoppedPath rounds guards z messages table with
    | none =>
        rw [hpath] at hresult
        rw [hresult] at bad
        exact False.elim bad
    | some path =>
        have hbad : badExtractOnPath state extractor Z terminalWitness
            (some ⟨z, path, witness⟩) := by
          simpa only [hpath, Option.map_some, hresult] using bad
        obtain ⟨key, hkey, hbadkey⟩ := badExtractOnStoppedPath_has_bad_key
          state extractor Z preserving terminalWitness guards z messages witness table
            path hpath hbad
        have hmem : key ∈ suffixLog.map Sigma.fst := by simpa only [hkeys] using hkey
        obtain ⟨query, hquery, hquerykey⟩ := List.mem_map.mp hmem
        refine ⟨query, ?_, ?_⟩
        · rw [hlog]
          exact List.mem_append.mpr (Or.inr hquery)
        · simpa only [hquerykey] using hbadkey

/-- The accepted relation failure on the actual stopped result. The supplied `W` is an
explicit terminal seed; extraction applies the named backward map to that very seed. -/
def badStoppedRelation
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol (rounds z)).tree (state z))
    (Rin : (z : Input) → (state z).Witness → Prop)
    (Rout : (z : Input) → (path : (protocol (rounds z)).tree.ExecutionPath) → W → Prop)
    (terminalWitness : (z : Input) → (path : (protocol (rounds z)).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (Z : Set Input)
    (result : Option (Outcome Input W rounds)) : Prop :=
  match result with
  | none => False
  | some ⟨z, path, witness⟩ =>
      z ∈ Z ∧ Rout z path witness ∧
        ¬ Rin z ((extractor z).extractWitness path (terminalWitness z path witness))

/-- The accepted failure relation entails the certificate's terminal-validity failure event. -/
theorem badStoppedRelation_implies_badExtractOnPath
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol (rounds z)).tree (state z))
    (Rin : (z : Input) → (state z).Witness → Prop)
    (Rout : (z : Input) → (path : (protocol (rounds z)).tree.ExecutionPath) → W → Prop)
    (terminalWitness : (z : Input) → (path : (protocol (rounds z)).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (Z : Set Input)
    (inputLaw : ∀ z witness, (state z).holds witness ↔ Rin z witness)
    (outputLaw : ∀ z path witness,
      Rout z path witness →
        ((extractor z).terminalState path).holds (terminalWitness z path witness))
    (result : Option (Outcome Input W rounds))
    (bad : badStoppedRelation state extractor Rin Rout terminalWitness Z result) :
    badExtractOnPath state extractor Z (fun z path => terminalWitness z path) result := by
  cases result with
  | none => exact bad
  | some selected =>
      rcases selected with ⟨z, path, witness⟩
      change z ∈ Z ∧ Rout z path witness ∧
        ¬ Rin z ((extractor z).extractWitness path (terminalWitness z path witness)) at bad
      change z ∈ Z ∧
        ((extractor z).terminalState path).holds (terminalWitness z path witness) ∧
        ¬ (state z).holds ((extractor z).extractWitness path
          (terminalWitness z path witness))
      exact ⟨bad.1, outputLaw z path witness bad.2.1,
        fun h => bad.2.2 ((inputLaw z _).mp h)⟩

/-- All-prefix local certificates charge an accepted invalid named extraction to a distinct
challenge key in the same stopped cached run. Inputs and salts need only decidable equality;
adversarial private samples may be interleaved with repeated and out-of-order hash queries. -/
theorem randomizedStopped_badRelation_le_expectedFreshCharge
    [DecidableEq Input] [DecidableEq Salt]
    (rounds : Input → List Round) (guards : (z : Input) → GuardSchedule Salt (rounds z))
    (errors : (z : Input) → RoundErrors (rounds z))
    (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol (rounds z)).tree (state z))
    (Z : Set Input)
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol (rounds z)).roles)
    (bounded : ∀ z ∈ Z, RoundExtractor.IsLocallyBounded (extractor z)
      (protocol (rounds z)).roles (roundErrorSchedule (rounds z) (errors z)))
    (Rin : (z : Input) → (state z).Witness → Prop)
    (Rout : (z : Input) → (path : (protocol (rounds z)).tree.ExecutionPath) → W → Prop)
    (terminalWitness : (z : Input) → (path : (protocol (rounds z)).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (inputLaw : ∀ z witness, (state z).holds witness ↔ Rin z witness)
    (outputLaw : ∀ z path witness,
      Rout z path witness →
        ((extractor z).terminalState path).holds (terminalWitness z path witness)) :
    Pr{let joint ← (randomOracleLoggedRun
      (randomizedStoppedRestoredExecutionWithAdversaryLog rounds guards adversary) ∅)}[
      badStoppedRelation state extractor Rin Rout terminalWitness Z joint.1.1.1] ≤
    expectedFreshQueryCharge
      (randomizedStoppedRestoredExecutionWithAdversaryLog rounds guards adversary)
      (keyError errors) := by
  apply prEvent_randomOracle_le_expectedFreshQueryCharge
    (randomizedStoppedRestoredExecutionWithAdversaryLog rounds guards adversary)
    (fun result => badStoppedRelation state extractor Rin Rout terminalWitness Z result.1)
    (badKey state extractor Z) (keyError errors)
  · intro table result supported bad
    obtain ⟨query, hquery, hbad⟩ := fixedTable_stopped_badExtract_has_bad_query
      rounds guards adversary state extractor Z preserving
        (fun z path => terminalWitness z path) table result supported
        (badStoppedRelation_implies_badExtractOnPath state extractor Rin Rout
          terminalWitness Z inputLaw outputLaw result.1.1.1 bad)
    exact ⟨query.1, (mem_freshKeysOfLog _ _).mpr ⟨query, hquery, rfl⟩, hbad⟩
  · intro key table
    exact badKey_round_resample_bound state extractor Z errors bounded key table

set_option backward.isDefEq.respectTransparency false in
/-- The cost of reached stopped rounds is at most the sum of all local round errors. -/
theorem prefixStoppedKeys_error_sum_le {Salt : Type} (rounds : List Round)
    (errors : RoundErrors rounds) (guards : GuardSchedule Salt rounds)
    (messages : Messages Salt rounds) (table : PrefixTable Salt rounds) :
    ((prefixStoppedKeys rounds guards messages table).map (prefixError errors)).sum ≤
      ∑ j, errors j := by
  induction rounds with
  | nil => cases messages; simp [prefixStoppedKeys]
  | cons round rounds ih =>
      rcases messages with ⟨message, salt, messages⟩
      by_cases hg : guards.1 message salt = true
      · have htail := ih (fun j => errors j.succ)
          (guards.2 message salt (table (Prefix.here message salt))) messages
          (fun q => table (Prefix.later message salt q))
        simpa only [prefixStoppedKeys, hg, ite_true, List.map_cons, List.sum_cons,
          List.map_map, Function.comp_def, prefixError, List.length_cons,
          Fin.sum_univ_succ]
          using add_le_add_right htail (errors 0)
      · have hg' : guards.1 message salt = false := Bool.eq_false_iff.mpr hg
        simp only [prefixStoppedKeys, hg']
        exact zero_le

/-- The cost of reached stopped rounds is at most the largest total error of one input's
rounds. -/
theorem stoppedKeys_error_sum_le (rounds : Input → List Round)
    (errors : (z : Input) → RoundErrors (rounds z))
    (guards : (z : Input) → GuardSchedule Salt (rounds z))
    (z : Input) (messages : Messages Salt (rounds z)) (table : Table Input Salt rounds) :
    ((stoppedKeys rounds guards z messages table).map (keyError errors)).sum ≤
      sumError errors := by
  simp only [stoppedKeys, List.map_map]
  exact (prefixStoppedKeys_error_sum_le (rounds z) (errors z) (guards z) messages
    (Table.fibre table z)).trans (le_iSup (fun z => ∑ j, errors z j) z)

/-- A joint stopped log charges the adversary's distinct keys and only verifier calls that
actually executed. Repeated or previously cached verifier keys can make the bound strict. -/
theorem roundFreshCharge_append_le_stopped [DecidableEq Input] [DecidableEq Salt]
    (errors : (z : Input) → RoundErrors (rounds z))
    (adversaryLog : QueryLog (unifSpec + oracleSpec Input Salt rounds))
    (suffixLog : QueryLog (oracleSpec Input Salt rounds)) :
    roundFreshCharge errors (adversaryLog.snd ++ suffixLog) ≤
      (adversaryHashKeys adversaryLog).card * maxError errors +
        ((suffixLog.map Sigma.fst).map (keyError errors)).sum := by
  let A : Finset (Key Input Salt rounds) := (adversaryLog.snd.map Sigma.fst).toFinset
  let C : Finset (Key Input Salt rounds) := (suffixLog.map Sigma.fst).toFinset
  have hA : (∑ key ∈ A, keyError errors key) ≤ A.card * maxError errors := by
    calc
      (∑ key ∈ A, keyError errors key) ≤ ∑ _key ∈ A, maxError errors :=
        Finset.sum_le_sum (fun key _ => keyError_le_maxError errors key)
      _ = A.card * maxError errors := by
        simp only [Finset.sum_const, nsmul_eq_mul]
  have hC : (∑ key ∈ C, keyError errors key) ≤
      ((suffixLog.map Sigma.fst).map (keyError errors)).sum :=
    sum_toFinset_le_list_sum (keyError errors) (suffixLog.map Sigma.fst)
  have hUnion :
      (∑ key ∈ A ∪ C, keyError errors key) ≤
        (∑ key ∈ A, keyError errors key) + (∑ key ∈ C, keyError errors key) := by
    calc
      (∑ key ∈ A ∪ C, keyError errors key) ≤
          (∑ key ∈ A ∪ C, keyError errors key) +
            (∑ key ∈ A ∩ C, keyError errors key) := le_add_right le_rfl
      _ = (∑ key ∈ A, keyError errors key) +
          (∑ key ∈ C, keyError errors key) := Finset.sum_union_inter
  have hset : ((adversaryLog.snd ++ suffixLog).map Sigma.fst).toFinset = A ∪ C := by
    simp [A, C]
  change (∑ key ∈ ((adversaryLog.snd ++ suffixLog).map Sigma.fst).toFinset,
    keyError errors key) ≤ _
  rw [hset]
  exact hUnion.trans (add_le_add hA hC)

/-- Actual executed verifier-round cost: remove the adversary phase's ordered hash prefix
from the joint log and sum the round error of each remaining call. -/
def stoppedVerifierRoundCost [DecidableEq Input] [DecidableEq Salt]
    (errors : (z : Input) → RoundErrors (rounds z))
    (adversaryLog : QueryLog (unifSpec + oracleSpec Input Salt rounds))
    (jointLog : QueryLog (oracleSpec Input Salt rounds)) : ENNReal :=
  (((jointLog.drop adversaryLog.snd.length).map Sigma.fst).map (keyError errors)).sum

/-- Every supported fixed-table stopped run pays at most the source distinct-key cost plus
the sum for its actually executed verifier rounds. Failed selections still pay source costs. -/
theorem fixedTable_stopped_freshCharge_le_actualRounds
    [DecidableEq Input] [DecidableEq Salt]
    (rounds : Input → List Round) (guards : (z : Input) → GuardSchedule Salt (rounds z))
    (errors : (z : Input) → RoundErrors (rounds z))
    (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (table : Table Input Salt rounds)
    (result : (((Option (Outcome Input W rounds) ×
      QueryLog (unifSpec + oracleSpec Input Salt rounds)) ×
        QueryLog (oracleSpec Input Salt rounds)) ×
          (oracleSpec Input Salt rounds).QueryCache))
    (supported : result ∈ support (fixedTableLoggedRun
      (randomizedStoppedRestoredExecutionWithAdversaryLog rounds guards adversary)
      table ∅)) :
    freshQueryCharge (keyError errors) result.1.2 ≤
      (adversaryHashKeys result.1.1.2).card * maxError errors +
        stoppedVerifierRoundCost errors result.1.1.2 result.1.2 := by
  change roundFreshCharge errors result.1.2 ≤ _
  rcases fixedTable_stopped_trace rounds guards adversary table result supported with
    ⟨_, hlog⟩ | ⟨z, messages, witness, suffixLog, _, hlog, hkeys⟩
  · rw [hlog]
    simpa [stoppedVerifierRoundCost] using
      roundFreshCharge_adversary_le errors result.1.1.2
  · rw [hlog]
    simpa [stoppedVerifierRoundCost] using
      roundFreshCharge_append_le_stopped errors result.1.1.2 suffixLog

/-- The same actual verifier cost is bounded by the full round-error sum on every supported
run. This is a separate estimate; the refined bound above retains the early-stop savings. -/
theorem fixedTable_stopped_verifierCost_le_sum
    [DecidableEq Input] [DecidableEq Salt]
    (rounds : Input → List Round) (guards : (z : Input) → GuardSchedule Salt (rounds z))
    (errors : (z : Input) → RoundErrors (rounds z))
    (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (table : Table Input Salt rounds)
    (result : (((Option (Outcome Input W rounds) ×
      QueryLog (unifSpec + oracleSpec Input Salt rounds)) ×
        QueryLog (oracleSpec Input Salt rounds)) ×
          (oracleSpec Input Salt rounds).QueryCache))
    (supported : result ∈ support (fixedTableLoggedRun
      (randomizedStoppedRestoredExecutionWithAdversaryLog rounds guards adversary)
      table ∅)) :
    stoppedVerifierRoundCost errors result.1.1.2 result.1.2 ≤ sumError errors := by
  rcases fixedTable_stopped_trace rounds guards adversary table result supported with
    ⟨_, hlog⟩ | ⟨z, messages, witness, suffixLog, _, hlog, hkeys⟩
  · rw [hlog]
    simp [stoppedVerifierRoundCost]
  · rw [hlog]
    simpa [stoppedVerifierRoundCost, hkeys] using
      stoppedKeys_error_sum_le rounds errors guards z messages table

end Interaction.Oracle.Security.StateRestoration
