/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.StateRestorationRandomizedKnowledge

/-!
# Stopped state restoration

A pure guard checks each authored message prefix before that challenge is queried.
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

variable {Input Salt W : Type} {protocol : Input → Protocol}
  {coin : (z : Input) → PublicCoin (protocol z)}

/-- A tree of pure, prefix-dependent guards, one before each challenge. A guard reads the salt of
its challenge and, through its continuation, the earlier prover moves, oracle payloads, salts and
challenges; it cannot read its own or a later challenge. -/
@[reducible] def GuardSchedule (Salt : Type) {protocol : Protocol} (coin : PublicCoin protocol) :
    Type :=
  PublicCoin.rec (motive := fun _ _ => Type) PUnit
    (fun {Moves} _ _ _ guards => (move : Moves) → guards move)
    (fun {Messages} _ _ _ _ guards => Messages → guards)
    (@fun Challenge _ _ _ guards => (Salt → Bool) × (Salt → Challenge → guards)) coin

/-- Complete an authored message sequence against the prefix oracle only while its guards pass.
Every guard runs before the corresponding hash access. Returned failure retains all preceding
oracle effects. -/
def stoppedCompletePrefix {Salt : Type} : {protocol : Protocol} → (coin : PublicCoin protocol) →
    GuardSchedule Salt coin → Messages Salt coin →
      OracleComp (prefixSpec Salt coin) (Option protocol.tree.ExecutionPath)
  | _, .done, _, _ => pure (some PUnit.unit)
  | _, @PublicCoin.sender _ _ _ next, guards, ⟨move, messages⟩ => do
      let suffix ← simulateQ (reindexQuery (R := Prefix.Challenge (coin := .sender next))
        (Sigma.mk move)) (stoppedCompletePrefix (next move) (guards move) messages)
      return suffix.map fun path => ⟨move, path⟩
  | _, @PublicCoin.oracle _ _ _ _ next, guards, ⟨message, messages⟩ => do
      let suffix ← simulateQ (reindexQuery (R := Prefix.Challenge (coin := .oracle next))
        (Prod.mk message)) (stoppedCompletePrefix next (guards message) messages)
      return suffix.map fun path => ⟨message, path⟩
  | _, @PublicCoin.challenge Challenge _ _ next, guards, ⟨salt, messages⟩ => do
      if !guards.1 salt then
        return none
      let challenge ← liftM ((prefixSpec Salt (@PublicCoin.challenge Challenge _ _ next)).query
        (Sum.inl salt))
      let suffix ← simulateQ (reindexQuery
        (R := Prefix.Challenge (coin := @PublicCoin.challenge Challenge _ _ next))
        (fun q : Prefix Salt next => Sum.inr ⟨salt, q⟩))
        (stoppedCompletePrefix next (guards.2 salt challenge) messages)
      return suffix.map fun path => ⟨challenge, path⟩

/-- Complete the selected input's message sequence only while that input's guards pass, at the
keys of the selected input. -/
def stoppedComplete {Input Salt : Type} {protocol : Input → Protocol}
    (coin : (z : Input) → PublicCoin (protocol z))
    (guards : (z : Input) → GuardSchedule Salt (coin z)) (z : Input)
    (messages : Messages Salt (coin z)) :
    OracleComp (oracleSpec Input Salt coin) (Option (protocol z).tree.ExecutionPath) :=
  simulateQ (inputQuery z) (stoppedCompletePrefix (coin z) (guards z) messages)

/-- Fixed-table result of stopped prefix completion. It agrees with the ordinary reconstructed
path on acceptance, and has no full path when a guard rejects. -/
def prefixStoppedPath {Salt : Type} : {protocol : Protocol} → (coin : PublicCoin protocol) →
    GuardSchedule Salt coin → Messages Salt coin →
      PrefixTable Salt coin → Option protocol.tree.ExecutionPath
  | _, .done, _, _, _ => some PUnit.unit
  | _, @PublicCoin.sender _ _ _ next, guards, ⟨move, messages⟩, table =>
      (prefixStoppedPath (next move) (guards move) messages fun q => table ⟨move, q⟩).map
        fun path => ⟨move, path⟩
  | _, @PublicCoin.oracle _ _ _ _ next, guards, ⟨message, messages⟩, table =>
      (prefixStoppedPath next (guards message) messages fun q => table ⟨message, q⟩).map
        fun path => ⟨message, path⟩
  | _, @PublicCoin.challenge _ _ _ next, guards, ⟨salt, messages⟩, table =>
      if guards.1 salt then
        (prefixStoppedPath next (guards.2 salt (table (.inl salt))) messages
          fun q => table (.inr ⟨salt, q⟩)).map fun path => ⟨table (.inl salt), path⟩
      else none

/-- Ordered prefixes actually requested by stopped prefix completion under a fixed table. A
rejecting challenge and every later one contribute no prefix. -/
def prefixStoppedKeys {Salt : Type} : {protocol : Protocol} → (coin : PublicCoin protocol) →
    GuardSchedule Salt coin → Messages Salt coin → PrefixTable Salt coin →
      List (Prefix Salt coin)
  | _, .done, _, _, _ => []
  | _, @PublicCoin.sender _ _ _ next, guards, ⟨move, messages⟩, table =>
      (prefixStoppedKeys (next move) (guards move) messages fun q => table ⟨move, q⟩).map
        (Sigma.mk move)
  | _, @PublicCoin.oracle _ _ _ _ next, guards, ⟨message, messages⟩, table =>
      (prefixStoppedKeys next (guards message) messages fun q => table ⟨message, q⟩).map
        (Prod.mk message)
  | _, @PublicCoin.challenge _ _ _ next, guards, ⟨salt, messages⟩, table =>
      if guards.1 salt then
        .inl salt :: (prefixStoppedKeys next (guards.2 salt (table (.inl salt))) messages
          fun q => table (.inr ⟨salt, q⟩)).map fun q => .inr ⟨salt, q⟩
      else []

/-- Pure guard acceptance over the reconstructed prefix answer table. -/
def prefixGuardsPass {Salt : Type} : {protocol : Protocol} → (coin : PublicCoin protocol) →
    GuardSchedule Salt coin → Messages Salt coin → PrefixTable Salt coin → Bool
  | _, .done, _, _, _ => true
  | _, @PublicCoin.sender _ _ _ next, guards, ⟨move, messages⟩, table =>
      prefixGuardsPass (next move) (guards move) messages fun q => table ⟨move, q⟩
  | _, @PublicCoin.oracle _ _ _ _ next, guards, ⟨message, messages⟩, table =>
      prefixGuardsPass next (guards message) messages fun q => table ⟨message, q⟩
  | _, @PublicCoin.challenge _ _ _ next, guards, ⟨salt, messages⟩, table =>
      guards.1 salt && prefixGuardsPass next (guards.2 salt (table (.inl salt))) messages
        fun q => table (.inr ⟨salt, q⟩)

/-- Fixed-table result of stopped completion of the selected input. -/
def stoppedPath {Input Salt : Type} {protocol : Input → Protocol}
    (coin : (z : Input) → PublicCoin (protocol z))
    (guards : (z : Input) → GuardSchedule Salt (coin z)) (z : Input)
    (messages : Messages Salt (coin z)) (table : Table Input Salt coin) :
    Option (protocol z).tree.ExecutionPath :=
  prefixStoppedPath (coin z) (guards z) messages (Table.fibre table z)

/-- Ordered keys actually requested by stopped completion of the selected input. -/
def stoppedKeys {Input Salt : Type} {protocol : Input → Protocol}
    (coin : (z : Input) → PublicCoin (protocol z))
    (guards : (z : Input) → GuardSchedule Salt (coin z)) (z : Input)
    (messages : Messages Salt (coin z)) (table : Table Input Salt coin) :
    List (Key Input Salt coin) :=
  (prefixStoppedKeys (coin z) (guards z) messages (Table.fibre table z)).map (Sigma.mk z)

/-- Pure guard acceptance of the selected input over the reconstructed answer table. -/
def guardsPass {Input Salt : Type} {protocol : Input → Protocol}
    (coin : (z : Input) → PublicCoin (protocol z))
    (guards : (z : Input) → GuardSchedule Salt (coin z)) (z : Input)
    (messages : Messages Salt (coin z)) (table : Table Input Salt coin) : Bool :=
  prefixGuardsPass (coin z) (guards z) messages (Table.fibre table z)

/-- On a fully accepted guard path, stopped reconstruction is the existing full path. -/
theorem prefixStoppedPath_eq_some_prefixPath {Salt : Type} {protocol : Protocol}
    (coin : PublicCoin protocol) (guards : GuardSchedule Salt coin)
    (messages : Messages Salt coin) (table : PrefixTable Salt coin)
    (passed : prefixGuardsPass coin guards messages table = true) :
    prefixStoppedPath coin guards messages table = some (prefixPath coin messages table) := by
  induction coin with
  | done => rfl
  | sender next ih =>
      rcases messages with ⟨move, messages⟩
      simp only [prefixGuardsPass] at passed
      simp only [prefixStoppedPath, prefixPath, ih move _ _ _ passed]
      rfl
  | oracle next ih =>
      rcases messages with ⟨message, messages⟩
      simp only [prefixGuardsPass] at passed
      simp only [prefixStoppedPath, prefixPath, ih _ _ _ passed]
      rfl
  | challenge next ih =>
      rcases messages with ⟨salt, messages⟩
      simp only [prefixGuardsPass, Bool.and_eq_true] at passed
      simp only [prefixStoppedPath, passed.1, ite_true, prefixPath, ih _ _ _ passed.2]
      rfl

/-- On a fully accepted guard path, stopped reconstruction is the existing full native path. -/
theorem stoppedPath_eq_some_completedPath {Input Salt : Type} {protocol : Input → Protocol}
    (coin : (z : Input) → PublicCoin (protocol z))
    (guards : (z : Input) → GuardSchedule Salt (coin z))
    (z : Input) (messages : Messages Salt (coin z)) (table : Table Input Salt coin)
    (passed : guardsPass coin guards z messages table = true) :
    stoppedPath coin guards z messages table = some (completedPath coin z messages table) :=
  prefixStoppedPath_eq_some_prefixPath (coin z) (guards z) messages _ passed

/-- A stopped prefix result can be a full path only if all guards passed. -/
theorem prefixStoppedPath_some_implies_pass {Salt : Type} {protocol : Protocol}
    (coin : PublicCoin protocol) (guards : GuardSchedule Salt coin)
    (messages : Messages Salt coin) (table : PrefixTable Salt coin)
    {path : protocol.tree.ExecutionPath}
    (result : prefixStoppedPath coin guards messages table = some path) :
    prefixGuardsPass coin guards messages table = true := by
  induction coin with
  | done => rfl
  | sender next ih =>
      rcases messages with ⟨move, messages⟩
      simp only [prefixStoppedPath] at result
      cases htail : prefixStoppedPath (next move) (guards move) messages
          (fun q => table ⟨move, q⟩) with
      | none => rw [htail] at result; cases result
      | some tail => exact ih move _ _ _ htail
  | oracle next ih =>
      rcases messages with ⟨message, messages⟩
      simp only [prefixStoppedPath] at result
      cases htail : prefixStoppedPath next (guards message) messages
          (fun q => table ⟨message, q⟩) with
      | none => rw [htail] at result; cases result
      | some tail => exact ih _ _ _ htail
  | challenge next ih =>
      rcases messages with ⟨salt, messages⟩
      simp only [prefixStoppedPath] at result
      split at result
      · rename_i hguard
        simp only [prefixGuardsPass, hguard, Bool.true_and]
        cases htail : prefixStoppedPath next (guards.2 salt (table (.inl salt))) messages
            (fun q => table (.inr ⟨salt, q⟩)) with
        | none => rw [htail] at result; cases result
        | some tail => exact ih _ _ _ htail
      · cases result

/-- A stopped result can be a full path only if all guards passed. -/
theorem stoppedPath_some_implies_pass {Input Salt : Type} {protocol : Input → Protocol}
    (coin : (z : Input) → PublicCoin (protocol z))
    (guards : (z : Input) → GuardSchedule Salt (coin z))
    (z : Input) (messages : Messages Salt (coin z)) (table : Table Input Salt coin)
    {path : (protocol z).tree.ExecutionPath}
    (result : stoppedPath coin guards z messages table = some path) :
    guardsPass coin guards z messages table = true :=
  prefixStoppedPath_some_implies_pass (coin z) (guards z) messages _ result

/-- An accepted stopped prefix run queries exactly the full path's prefixes. -/
theorem prefixStoppedKeys_of_pass {Salt : Type} {protocol : Protocol}
    (coin : PublicCoin protocol) (guards : GuardSchedule Salt coin)
    (messages : Messages Salt coin) (table : PrefixTable Salt coin)
    (passed : prefixGuardsPass coin guards messages table = true) :
    prefixStoppedKeys coin guards messages table = prefixKeys coin messages := by
  induction coin with
  | done => rfl
  | sender next ih =>
      rcases messages with ⟨move, messages⟩
      simp only [prefixGuardsPass] at passed
      simp only [prefixStoppedKeys, prefixKeys, ih move _ _ _ passed]
  | oracle next ih =>
      rcases messages with ⟨message, messages⟩
      simp only [prefixGuardsPass] at passed
      simp only [prefixStoppedKeys, prefixKeys, ih _ _ _ passed]
  | challenge next ih =>
      rcases messages with ⟨salt, messages⟩
      simp only [prefixGuardsPass, Bool.and_eq_true] at passed
      simp only [prefixStoppedKeys, passed.1, ite_true, prefixKeys, ih _ _ _ passed.2]

/-- An accepted stopped run queries exactly the full path's challenge keys. -/
theorem stoppedKeys_of_pass {Input Salt : Type} {protocol : Input → Protocol}
    (coin : (z : Input) → PublicCoin (protocol z))
    (guards : (z : Input) → GuardSchedule Salt (coin z))
    (z : Input) (messages : Messages Salt (coin z)) (table : Table Input Salt coin)
    (passed : guardsPass coin guards z messages table = true) :
    stoppedKeys coin guards z messages table = completionKeys coin z messages := by
  simp only [stoppedKeys, completionKeys]
  rw [prefixStoppedKeys_of_pass (coin z) (guards z) messages _ passed]

set_option backward.isDefEq.respectTransparency false in
/-- The stopped prefix completion's fixed-table result uses the same path reconstruction. -/
theorem stoppedCompletePrefix_eval {Salt : Type} {protocol : Protocol}
    (coin : PublicCoin protocol) (guards : GuardSchedule Salt coin)
    (messages : Messages Salt coin) (table : PrefixTable Salt coin) :
    evalWithAnswerFn (QueryImpl.ofFn table) (stoppedCompletePrefix coin guards messages) =
      prefixStoppedPath coin guards messages table := by
  induction coin with
  | done => rfl
  | sender next ih =>
      rcases messages with ⟨move, messages⟩
      simp only [stoppedCompletePrefix, evalWithAnswerFn_bind, evalWithAnswerFn_reindexQuery,
        prefixStoppedPath]
      erw [ih]
      rfl
  | oracle next ih =>
      rcases messages with ⟨message, messages⟩
      simp only [stoppedCompletePrefix, evalWithAnswerFn_bind, evalWithAnswerFn_reindexQuery,
        prefixStoppedPath]
      erw [ih]
      rfl
  | challenge next ih =>
      rcases messages with ⟨salt, messages⟩
      by_cases hg : guards.1 salt = true
      · simp only [stoppedCompletePrefix, hg, Bool.not_true, Bool.false_eq_true, ite_false,
          evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply,
          evalWithAnswerFn_reindexQuery, prefixStoppedPath, ite_true]
        erw [ih]
        rfl
      · have hg' : guards.1 salt = false := Bool.eq_false_iff.mpr hg
        simp [stoppedCompletePrefix, hg', prefixStoppedPath]

/-- The stopped completion's fixed-table result uses the same native path reconstruction. -/
theorem stoppedComplete_eval {Input Salt : Type} {protocol : Input → Protocol}
    (coin : (z : Input) → PublicCoin (protocol z))
    (guards : (z : Input) → GuardSchedule Salt (coin z))
    (z : Input) (messages : Messages Salt (coin z)) (table : Table Input Salt coin) :
    evalWithAnswerFn (QueryImpl.ofFn table) (stoppedComplete coin guards z messages) =
      stoppedPath coin guards z messages table := by
  rw [stoppedComplete, evalWithAnswerFn_reindexQuery]
  exact stoppedCompletePrefix_eval (coin z) (guards z) messages (Table.fibre table z)

/-- The fixed-table ordered prefix-query log contains precisely the executed prefixes. -/
theorem stoppedCompletePrefix_log_keys {Salt : Type} {protocol : Protocol}
    (coin : PublicCoin protocol) (guards : GuardSchedule Salt coin)
    (messages : Messages Salt coin) (table : PrefixTable Salt coin) :
    (tableQueryLog (stoppedCompletePrefix coin guards messages) table).map Sigma.fst =
      prefixStoppedKeys coin guards messages table := by
  induction coin with
  | done => simp [stoppedCompletePrefix, prefixStoppedKeys]
  | sender next ih =>
      rcases messages with ⟨move, messages⟩
      simp only [stoppedCompletePrefix, tableQueryLog_bind, List.map_append]
      erw [tableQueryLog_pure, tableQueryLog_reindexQuery, ih move]
      simp only [List.map_nil, List.append_nil, prefixStoppedKeys]
  | oracle next ih =>
      rcases messages with ⟨message, messages⟩
      simp only [stoppedCompletePrefix, tableQueryLog_bind, List.map_append]
      erw [tableQueryLog_pure, tableQueryLog_reindexQuery, ih]
      simp only [List.map_nil, List.append_nil, prefixStoppedKeys]
  | challenge next ih =>
      rcases messages with ⟨salt, messages⟩
      by_cases hg : guards.1 salt = true
      · simp only [stoppedCompletePrefix, hg, Bool.not_true, Bool.false_eq_true, ite_false,
          tableQueryLog_bind, List.map_append]
        erw [tableQueryLog_pure, tableQueryLog_query, tableQueryLog_reindexQuery, ih]
        simp only [List.map_nil, List.append_nil, prefixStoppedKeys, hg, ite_true,
          List.map_cons, List.singleton_append]
        rfl
      · have hg' : guards.1 salt = false := Bool.eq_false_iff.mpr hg
        simp [stoppedCompletePrefix, prefixStoppedKeys, hg']

/-- The fixed-table ordered query log contains precisely the executed challenge keys. -/
theorem stoppedComplete_log_keys {Input Salt : Type} {protocol : Input → Protocol}
    (coin : (z : Input) → PublicCoin (protocol z))
    (guards : (z : Input) → GuardSchedule Salt (coin z))
    (z : Input) (messages : Messages Salt (coin z)) (table : Table Input Salt coin) :
    (tableQueryLog (stoppedComplete coin guards z messages) table).map Sigma.fst =
      stoppedKeys coin guards z messages table := by
  rw [stoppedComplete, tableQueryLog_reindexQuery, stoppedKeys,
    stoppedCompletePrefix_log_keys (coin z) (guards z) messages (Table.fibre table z)]

/-- Run a randomized adversary and then stop completion at the first failing guard. The source
phase is logged as returned data without creating new oracle effects. -/
def randomizedStoppedCompletionAfterAdversaryLog (coin : (z : Input) → PublicCoin (protocol z))
    (guards : (z : Input) → GuardSchedule Salt (coin z))
    (selectedAndLog : Option (Selection Input Salt W coin) ×
      QueryLog (unifSpec + oracleSpec Input Salt coin)) :
    OracleComp (unifSpec + oracleSpec Input Salt coin)
      (Option (Outcome Input W protocol) ×
        QueryLog (unifSpec + oracleSpec Input Salt coin)) := do
  match selectedAndLog.1 with
  | none => pure (none, selectedAndLog.2)
  | some ⟨z, messages, witness⟩ =>
      let path ← simulateQ (restorationQueries Input Salt coin)
        (stoppedComplete coin guards z messages)
      pure (path.map (fun p => ⟨z, p, witness⟩), selectedAndLog.2)

/-- The actual joint stopped game shares one lazy random-oracle cache across both phases. -/
def randomizedStoppedRestoredExecutionWithAdversaryLog (coin : (z : Input) → PublicCoin (protocol
    z))
    (guards : (z : Input) → GuardSchedule Salt (coin z))
    (adversary : RandomizedRestorationAdversary Input Salt W coin) :
    OracleComp (unifSpec + oracleSpec Input Salt coin)
      (Option (Outcome Input W protocol) ×
        QueryLog (unifSpec + oracleSpec Input Salt coin)) :=
  adversary.withQueryLog >>=
    randomizedStoppedCompletionAfterAdversaryLog coin guards

/-- The same-cache stopped handoff includes the exact result, ordered hash log, and final cache.
This law includes failed adversary selections and rejected guard paths. -/
theorem randomizedStoppedRestoredExecutionWithAdversaryLog_handoff
    [DecidableEq Input] [DecidableEq Salt]
    (coin : (z : Input) → PublicCoin (protocol z)) (guards : (z : Input) → GuardSchedule Salt (coin
        z))
    (adversary : RandomizedRestorationAdversary Input Salt W coin)
    (cache : (oracleSpec Input Salt coin).QueryCache) :
    randomOracleLoggedRun
        (randomizedStoppedRestoredExecutionWithAdversaryLog coin guards adversary) cache =
      randomOracleLoggedRun adversary.withQueryLog cache >>= fun phase =>
        (fun suffix => ((suffix.1.1, phase.1.2 ++ suffix.1.2), suffix.2)) <$>
          randomOracleLoggedRun
            (randomizedStoppedCompletionAfterAdversaryLog coin guards phase.1.1)
            phase.2 := by
  exact randomOracleLoggedRun_bind adversary.withQueryLog
    (randomizedStoppedCompletionAfterAdversaryLog coin guards) cache

/-- Fixed-table version of the same joint handoff, used to derive the bad-key witness from
the all-prefix certificate on each supported private-randomness branch. -/
theorem randomizedStoppedRestoredExecutionWithAdversaryLog_fixedTable_handoff
    [DecidableEq Input] [DecidableEq Salt]
    (coin : (z : Input) → PublicCoin (protocol z)) (guards : (z : Input) → GuardSchedule Salt (coin
        z))
    (adversary : RandomizedRestorationAdversary Input Salt W coin)
    (table : Table Input Salt coin)
    (cache : (oracleSpec Input Salt coin).QueryCache) :
    fixedTableLoggedRun
        (randomizedStoppedRestoredExecutionWithAdversaryLog coin guards adversary)
        table cache =
      fixedTableLoggedRun adversary.withQueryLog table cache >>= fun phase =>
        (fun suffix => ((suffix.1.1, phase.1.2 ++ suffix.1.2), suffix.2)) <$>
          fixedTableLoggedRun
            (randomizedStoppedCompletionAfterAdversaryLog coin guards phase.1.1)
            table phase.2 := by
  exact fixedTableLoggedRun_bind adversary.withQueryLog
    (randomizedStoppedCompletionAfterAdversaryLog coin guards) table cache

/-- Accepted fixed-table stopped completion is the existing full native execution path, with
exactly its full challenge-key log. Rejected paths retain their shorter ordered log. -/
theorem fixedTable_stoppedCompletion_result_keys [DecidableEq Input] [DecidableEq Salt]
    (coin : (z : Input) → PublicCoin (protocol z)) (guards : (z : Input) → GuardSchedule Salt (coin
        z))
    (z : Input) (messages : Messages Salt (coin z))
    (table : Table Input Salt coin)
    (cache : (oracleSpec Input Salt coin).QueryCache)
    (agree : cache.AgreesWithFn (QueryImpl.ofFn table))
    (result : ((Option (protocol z).tree.ExecutionPath ×
      QueryLog (oracleSpec Input Salt coin)) ×
      (oracleSpec Input Salt coin).QueryCache))
    (supported : result ∈ support (fixedTableLoggedRun
      (simulateQ (restorationQueries Input Salt coin)
        (stoppedComplete coin guards z messages)) table cache)) :
    result.1.1 = stoppedPath coin guards z messages table ∧
      result.1.2.map Sigma.fst = stoppedKeys coin guards z messages table := by
  obtain ⟨hpath, hlog, _⟩ := fixedTable_restorationQueries_run
    (stoppedComplete coin guards z messages) table cache agree result supported
  exact ⟨hpath.trans (stoppedComplete_eval coin guards z messages table),
    by rw [hlog]; exact stoppedComplete_log_keys coin guards z messages table⟩

/-- The terminal seed is supplied by the adversary, then validated by the accepted relation.
An invalid named backward extraction on an accepted stopped path has a bad key among the actual
queried keys of that stopped completion. -/
theorem badExtractOnStoppedPath_has_bad_key
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol z).tree (state z))
    (Z : Set Input)
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol z).roles)
    (terminalWitness : (z : Input) → (path : (protocol z).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (guards : (z : Input) → GuardSchedule Salt (coin z))
    (z : Input) (messages : Messages Salt (coin z)) (witness : W)
    (table : Table Input Salt coin)
    (path : (protocol z).tree.ExecutionPath)
    (accepted : stoppedPath coin guards z messages table = some path)
    (bad : badExtractOnPath state extractor Z terminalWitness (some ⟨z, path, witness⟩)) :
    ∃ key ∈ stoppedKeys coin guards z messages table,
      badKey state extractor Z key table := by
  have passed := stoppedPath_some_implies_pass coin guards z messages table accepted
  have hpath := stoppedPath_eq_some_completedPath coin guards z messages table passed
  have heq : path = completedPath coin z messages table :=
    Option.some.inj (accepted.symm.trans hpath)
  subst path
  obtain ⟨key, hkey, hbad⟩ := badExtractOnPath_completion
    state extractor Z preserving terminalWitness z messages witness table bad
  exact ⟨key, by rw [stoppedKeys_of_pass coin guards z messages table passed]; exact hkey,
    hbad⟩

/-- A selected source result executes only its stopped completion, preserving the source log.
The suffix log is exactly the list of keys visited before acceptance or rejection. -/
theorem fixedTable_stoppedCompletionAfterAdversaryLog_selected
    [DecidableEq Input] [DecidableEq Salt]
    (coin : (z : Input) → PublicCoin (protocol z)) (guards : (z : Input) → GuardSchedule Salt (coin
        z))
    (z : Input) (messages : Messages Salt (coin z)) (witness : W)
    (adversaryLog : QueryLog (unifSpec + oracleSpec Input Salt coin))
    (table : Table Input Salt coin)
    (cache : (oracleSpec Input Salt coin).QueryCache)
    (agree : cache.AgreesWithFn (QueryImpl.ofFn table))
    (result : (((Option (Outcome Input W protocol) ×
      QueryLog (unifSpec + oracleSpec Input Salt coin)) ×
        QueryLog (oracleSpec Input Salt coin)) ×
          (oracleSpec Input Salt coin).QueryCache))
    (supported : result ∈ support (fixedTableLoggedRun
      (randomizedStoppedCompletionAfterAdversaryLog coin guards
        (some ⟨z, messages, witness⟩, adversaryLog)) table cache)) :
    result.1.1 =
      ((stoppedPath coin guards z messages table).map
        (fun path => ⟨z, path, witness⟩), adversaryLog) ∧
      result.1.2.map Sigma.fst = stoppedKeys coin guards z messages table := by
  have hprogram : randomizedStoppedCompletionAfterAdversaryLog coin guards
      (some ⟨z, messages, witness⟩, adversaryLog) =
      (fun path => (path.map (fun p => ⟨z, p, witness⟩), adversaryLog)) <$>
        simulateQ (restorationQueries Input Salt coin)
          (stoppedComplete coin guards z messages) := by
    simp only [randomizedStoppedCompletionAfterAdversaryLog, map_eq_pure_bind]
  rw [hprogram, fixedTableLoggedRun_map, support_map] at supported
  obtain ⟨completion, hcompletion, rfl⟩ := supported
  obtain ⟨hpath, hkeys⟩ := fixedTable_stoppedCompletion_result_keys
    coin guards z messages table cache agree completion hcompletion
  exact ⟨by simp [hpath], hkeys⟩

/-- Fixed-table trace decomposition of the actual stopped game. The suffix log is retained even
when a guard rejects; a failed source selection has no suffix queries. -/
theorem fixedTable_stopped_trace [DecidableEq Input] [DecidableEq Salt]
    (coin : (z : Input) → PublicCoin (protocol z)) (guards : (z : Input) → GuardSchedule Salt (coin
        z))
    (adversary : RandomizedRestorationAdversary Input Salt W coin)
    (table : Table Input Salt coin)
    (result : (((Option (Outcome Input W protocol) ×
      QueryLog (unifSpec + oracleSpec Input Salt coin)) ×
        QueryLog (oracleSpec Input Salt coin)) ×
          (oracleSpec Input Salt coin).QueryCache))
    (supported : result ∈ support (fixedTableLoggedRun
      (randomizedStoppedRestoredExecutionWithAdversaryLog coin guards adversary)
      table ∅)) :
    (result.1.1.1 = none ∧ result.1.2 = result.1.1.2.snd) ∨
      ∃ z messages witness suffixLog,
        result.1.1.1 =
          (stoppedPath coin guards z messages table).map
            (fun path => ⟨z, path, witness⟩) ∧
        result.1.2 = result.1.1.2.snd ++ suffixLog ∧
        suffixLog.map Sigma.fst = stoppedKeys coin guards z messages table := by
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
        coin guards z messages witness sourceLog table phaseCache hagree suffix hsuffix
      right
      refine ⟨z, messages, witness, suffix.1.2, ?_, ?_, hkeys⟩
      · exact congrArg Prod.fst hout
      · simp only [hsource, hout]

/-- A failed extraction on a supported stopped run is witnessed by a bad key in that same
run's ordered hash log. This implication comes from preservation and the full accepted path. -/
theorem fixedTable_stopped_badExtract_has_bad_query [DecidableEq Input] [DecidableEq Salt]
    (coin : (z : Input) → PublicCoin (protocol z)) (guards : (z : Input) → GuardSchedule Salt (coin
        z))
    (adversary : RandomizedRestorationAdversary Input Salt W coin)
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol z).tree (state z))
    (Z : Set Input)
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol z).roles)
    (terminalWitness : (z : Input) → (path : (protocol z).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (table : Table Input Salt coin)
    (result : (((Option (Outcome Input W protocol) ×
      QueryLog (unifSpec + oracleSpec Input Salt coin)) ×
        QueryLog (oracleSpec Input Salt coin)) ×
          (oracleSpec Input Salt coin).QueryCache))
    (supported : result ∈ support (fixedTableLoggedRun
      (randomizedStoppedRestoredExecutionWithAdversaryLog coin guards adversary)
      table ∅))
    (bad : badExtractOnPath state extractor Z terminalWitness result.1.1.1) :
    ∃ query ∈ result.1.2, badKey state extractor Z query.1 table := by
  rcases fixedTable_stopped_trace coin guards adversary table result supported with
    ⟨hnone, _⟩ | ⟨z, messages, witness, suffixLog, hresult, hlog, hkeys⟩
  · rw [hnone] at bad
    exact False.elim bad
  · cases hpath : stoppedPath coin guards z messages table with
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
    (extractor : (z : Input) → RoundExtractor (protocol z).tree (state z))
    (Rin : (z : Input) → (state z).Witness → Prop)
    (Rout : (z : Input) → (path : (protocol z).tree.ExecutionPath) → W → Prop)
    (terminalWitness : (z : Input) → (path : (protocol z).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (Z : Set Input)
    (result : Option (Outcome Input W protocol)) : Prop :=
  match result with
  | none => False
  | some ⟨z, path, witness⟩ =>
      z ∈ Z ∧ Rout z path witness ∧
        ¬ Rin z ((extractor z).extractWitness path (terminalWitness z path witness))

/-- The accepted failure relation entails the certificate's terminal-validity failure event. -/
theorem badStoppedRelation_implies_badExtractOnPath
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol z).tree (state z))
    (Rin : (z : Input) → (state z).Witness → Prop)
    (Rout : (z : Input) → (path : (protocol z).tree.ExecutionPath) → W → Prop)
    (terminalWitness : (z : Input) → (path : (protocol z).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (Z : Set Input)
    (inputLaw : ∀ z witness, (state z).holds witness ↔ Rin z witness)
    (outputLaw : ∀ z path witness,
      Rout z path witness →
        ((extractor z).terminalState path).holds (terminalWitness z path witness))
    (result : Option (Outcome Input W protocol))
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
    (coin : (z : Input) → PublicCoin (protocol z)) (guards : (z : Input) → GuardSchedule Salt (coin
        z))
    (errors : (z : Input) → Errors (coin z))
    (adversary : RandomizedRestorationAdversary Input Salt W coin)
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
      (randomizedStoppedRestoredExecutionWithAdversaryLog coin guards adversary) ∅)}[
      badStoppedRelation state extractor Rin Rout terminalWitness Z joint.1.1.1] ≤
    expectedFreshQueryCharge
      (randomizedStoppedRestoredExecutionWithAdversaryLog coin guards adversary)
      (keyError errors) := by
  apply prEvent_randomOracle_le_expectedFreshQueryCharge
    (randomizedStoppedRestoredExecutionWithAdversaryLog coin guards adversary)
    (fun result => badStoppedRelation state extractor Rin Rout terminalWitness Z result.1)
    (badKey state extractor Z) (keyError errors)
  · intro table result supported bad
    obtain ⟨query, hquery, hbad⟩ := fixedTable_stopped_badExtract_has_bad_query
      coin guards adversary state extractor Z preserving
        (fun z path => terminalWitness z path) table result supported
        (badStoppedRelation_implies_badExtractOnPath state extractor Rin Rout
          terminalWitness Z inputLaw outputLaw result.1.1.1 bad)
    exact ⟨query.1, (mem_freshKeysOfLog _ _).mpr ⟨query, hquery, rfl⟩, hbad⟩
  · intro key table
    exact badKey_resample_bound state extractor Z errors bounded key table

/-- The cost of the reached challenges is at most the largest path sum of errors. -/
theorem prefixStoppedKeys_error_sum_le {Salt : Type} {protocol : Protocol}
    (coin : PublicCoin protocol) (errors : Errors coin) (guards : GuardSchedule Salt coin)
    (messages : Messages Salt coin) (table : PrefixTable Salt coin) :
    ((prefixStoppedKeys coin guards messages table).map (prefixError errors)).sum ≤
      pathError coin errors := by
  induction coin with
  | done => simp [prefixStoppedKeys]
  | sender next ih =>
      rcases messages with ⟨move, messages⟩
      simp only [prefixStoppedKeys, List.map_map, pathError]
      exact (ih move (fun q => errors ⟨move, q⟩) _ messages _).trans
        (le_iSup (fun move => pathError (next move) fun q => errors ⟨move, q⟩) move)
  | oracle next ih =>
      rcases messages with ⟨message, messages⟩
      simp only [prefixStoppedKeys, List.map_map, pathError]
      exact (ih (fun q => errors ⟨message, q⟩) _ messages _).trans
        (le_iSup (fun message => pathError next fun q => errors ⟨message, q⟩) message)
  | challenge next ih =>
      rcases messages with ⟨salt, messages⟩
      simp only [prefixStoppedKeys, pathError]
      split
      · simp only [List.map_cons, List.sum_cons, List.map_map]
        exact add_le_add le_rfl (ih (fun q => errors (.inr ⟨PUnit.unit, q⟩)) _ messages _)
      · exact zero_le

/-- The cost of reached stopped coin is at most the largest total error of one input's
coin. -/
theorem stoppedKeys_error_sum_le (coin : (z : Input) → PublicCoin (protocol z))
    (errors : (z : Input) → Errors (coin z))
    (guards : (z : Input) → GuardSchedule Salt (coin z))
    (z : Input) (messages : Messages Salt (coin z)) (table : Table Input Salt coin) :
    ((stoppedKeys coin guards z messages table).map (keyError errors)).sum ≤
      sumError errors := by
  simp only [stoppedKeys, List.map_map]
  exact (prefixStoppedKeys_error_sum_le (coin z) (errors z) (guards z) messages
    (Table.fibre table z)).trans (le_iSup (fun z => pathError (coin z) (errors z)) z)

/-- A joint stopped log charges the adversary's distinct keys and only verifier calls that
actually executed. Repeated or previously cached verifier keys can make the bound strict. -/
theorem distinctKeyCharge_append_le_stopped [DecidableEq Input] [DecidableEq Salt]
    (errors : (z : Input) → Errors (coin z))
    (adversaryLog : QueryLog (unifSpec + oracleSpec Input Salt coin))
    (suffixLog : QueryLog (oracleSpec Input Salt coin)) :
    distinctKeyCharge errors (adversaryLog.snd ++ suffixLog) ≤
      (adversaryHashKeys adversaryLog).card * maxError errors +
        ((suffixLog.map Sigma.fst).map (keyError errors)).sum := by
  let A : Finset (Key Input Salt coin) := (adversaryLog.snd.map Sigma.fst).toFinset
  let C : Finset (Key Input Salt coin) := (suffixLog.map Sigma.fst).toFinset
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
from the joint log and sum the node error of each remaining call. -/
noncomputable def stoppedVerifierRoundCost [DecidableEq Input] [DecidableEq Salt]
    (errors : (z : Input) → Errors (coin z))
    (adversaryLog : QueryLog (unifSpec + oracleSpec Input Salt coin))
    (jointLog : QueryLog (oracleSpec Input Salt coin)) : ENNReal :=
  (((jointLog.drop adversaryLog.snd.length).map Sigma.fst).map (keyError errors)).sum

/-- Every supported fixed-table stopped run pays at most the source distinct-key cost plus
the sum for its actually executed verifier coin. Failed selections still pay source costs. -/
theorem fixedTable_stopped_freshCharge_le_actualRounds
    [DecidableEq Input] [DecidableEq Salt]
    (coin : (z : Input) → PublicCoin (protocol z)) (guards : (z : Input) → GuardSchedule Salt (coin
        z))
    (errors : (z : Input) → Errors (coin z))
    (adversary : RandomizedRestorationAdversary Input Salt W coin)
    (table : Table Input Salt coin)
    (result : (((Option (Outcome Input W protocol) ×
      QueryLog (unifSpec + oracleSpec Input Salt coin)) ×
        QueryLog (oracleSpec Input Salt coin)) ×
          (oracleSpec Input Salt coin).QueryCache))
    (supported : result ∈ support (fixedTableLoggedRun
      (randomizedStoppedRestoredExecutionWithAdversaryLog coin guards adversary)
      table ∅)) :
    freshQueryCharge (keyError errors) result.1.2 ≤
      (adversaryHashKeys result.1.1.2).card * maxError errors +
        stoppedVerifierRoundCost errors result.1.1.2 result.1.2 := by
  change distinctKeyCharge errors result.1.2 ≤ _
  rcases fixedTable_stopped_trace coin guards adversary table result supported with
    ⟨_, hlog⟩ | ⟨z, messages, witness, suffixLog, _, hlog, hkeys⟩
  · rw [hlog]
    simpa [stoppedVerifierRoundCost] using
      distinctKeyCharge_adversary_le errors result.1.1.2
  · rw [hlog]
    simpa [stoppedVerifierRoundCost] using
      distinctKeyCharge_append_le_stopped errors result.1.1.2 suffixLog

/-- The same actual verifier cost is bounded by the full path error sum on every supported
run. This is a separate estimate; the refined bound above retains the early-stop savings. -/
theorem fixedTable_stopped_verifierCost_le_sum
    [DecidableEq Input] [DecidableEq Salt]
    (coin : (z : Input) → PublicCoin (protocol z)) (guards : (z : Input) → GuardSchedule Salt (coin
        z))
    (errors : (z : Input) → Errors (coin z))
    (adversary : RandomizedRestorationAdversary Input Salt W coin)
    (table : Table Input Salt coin)
    (result : (((Option (Outcome Input W protocol) ×
      QueryLog (unifSpec + oracleSpec Input Salt coin)) ×
        QueryLog (oracleSpec Input Salt coin)) ×
          (oracleSpec Input Salt coin).QueryCache))
    (supported : result ∈ support (fixedTableLoggedRun
      (randomizedStoppedRestoredExecutionWithAdversaryLog coin guards adversary)
      table ∅)) :
    stoppedVerifierRoundCost errors result.1.1.2 result.1.2 ≤ sumError errors := by
  rcases fixedTable_stopped_trace coin guards adversary table result supported with
    ⟨_, hlog⟩ | ⟨z, messages, witness, suffixLog, _, hlog, hkeys⟩
  · rw [hlog]
    simp [stoppedVerifierRoundCost]
  · rw [hlog]
    simpa [stoppedVerifierRoundCost, hkeys] using
      stoppedKeys_error_sum_le coin errors guards z messages table

end Interaction.Oracle.Security.StateRestoration
