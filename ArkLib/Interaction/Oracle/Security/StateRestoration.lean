/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.Knowledge
public import ArkLib.Interaction.Oracle.Protocol
public import VCVio.OracleComp.QueryTracking.RandomOracle.FreshQuery

/-!
# Backward extraction in the state-restoration experiment

A public-coin oracle protocol whose rounds are a function of its input is presented using the
existing protocol tree: input `z` runs `protocol (rounds z)`. A restoration key is an input `z`
together with a salted prefix of `rounds z`, which fixes the round, the prover-message prefix, and
the salt prefix; the input is the outermost component. Previous verifier challenges are
deliberately absent from the key. A key's knowledge state reconstructs its strict ancestors from
the same table, and changing its own response cannot change that state.

For an arbitrary adaptive adversary, completion reads the selected transcript's challenges from
the same cached oracle. A valid terminal knowledge witness whose backward extraction fails has
probability at most `(Q + k) * error`, where every input has at most `k` rounds. Inputs and salts
may have infinite types; challenges have finite nonempty uniform samplers. The probability proof
allows out-of-order and repeated queries.
This module proves the knowledge bound on execution paths. The concrete verifier realization and
its terminal witness relations are separate endpoint obligations, not assumed execution equations.
-/

@[expose] public section

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec
open Interaction.Oracle.TypeTree

namespace Interaction.Oracle.Security.StateRestoration

/-- One round: a prover oracle message, its permitted interface, and a uniform challenge. -/
structure Round where
  Message : Type
  Challenge : Type
  interface : OracleInterface Message
  decEqMessage : DecidableEq Message
  finiteMessage : Finite Message
  finiteChallenge : Finite Challenge
  nonemptyChallenge : Nonempty Challenge
  sampleChallenge : SampleableType Challenge

attribute [instance] Round.decEqMessage Round.finiteMessage Round.finiteChallenge
  Round.nonemptyChallenge Round.sampleChallenge

/-- The fixed presentation uses oracle-message and public-receiver nodes. -/
def protocol : List Round → Protocol
  | [] => .done
  | round :: rounds => .oracleWith round.Message round.interface
      (.public .receiver round.Challenge (fun _ => protocol rounds))

/-- A salted prefix encodes its round by its depth and retains each prover message and salt
through that round. No earlier verifier response is part of a prefix. -/
@[reducible] def Prefix (Salt : Type) : List Round → Type
  | [] => Empty
  | round :: rounds => (round.Message × Salt) ⊕ (round.Message × Salt × Prefix Salt rounds)

namespace Prefix

variable {Salt : Type}

/-- The first round prefix for this prover message and salt. -/
@[match_pattern, reducible] def here {round : Round} {rounds : List Round}
    (message : round.Message) (salt : Salt) : Prefix Salt (round :: rounds) :=
  Sum.inl ⟨message, salt⟩

/-- A later round prefix, retaining this earlier prover message and salt. -/
@[match_pattern, reducible] def later {round : Round} {rounds : List Round}
    (message : round.Message) (salt : Salt) (pre : Prefix Salt rounds) :
    Prefix Salt (round :: rounds) := Sum.inr ⟨message, salt, pre⟩

instance instDecidableEq [DecidableEq Salt] :
    (rounds : List Round) → DecidableEq (Prefix Salt rounds)
  | [] => inferInstanceAs (DecidableEq Empty)
  | round :: rounds =>
      letI := instDecidableEq rounds
      inferInstanceAs (DecidableEq ((round.Message × Salt) ⊕
        (round.Message × Salt × Prefix Salt rounds)))

instance instFinite [Finite Salt] : (rounds : List Round) → Finite (Prefix Salt rounds)
  | [] => inferInstanceAs (Finite Empty)
  | round :: rounds =>
      letI : Finite (Prefix Salt rounds) := instFinite rounds
      inferInstanceAs (Finite ((round.Message × Salt) ⊕
        (round.Message × Salt × Prefix Salt rounds)))

/-- The answer type is the challenge alphabet of the prefix's round. -/
@[reducible] def Challenge : {rounds : List Round} → Prefix Salt rounds → Type
  | [], pre => nomatch pre
  | round :: _, .inl _ => round.Challenge
  | _ :: _, .inr (_, _, pre) => pre.Challenge

/-- Rounds following the challenge addressed by this prefix. -/
def remaining : {rounds : List Round} → Prefix Salt rounds → List Round
  | [], pre => nomatch pre
  | _ :: rounds, .inl _ => rounds
  | _ :: _, .inr (_, _, pre) => pre.remaining

instance {rounds : List Round} (pre : Prefix Salt rounds) : Finite pre.Challenge := by
  induction rounds with
  | nil => exact pre.elim
  | cons round rounds ih =>
      cases pre with
      | inl _ => exact round.finiteChallenge
      | inr data => exact ih data.2.2

instance {rounds : List Round} (pre : Prefix Salt rounds) : Nonempty pre.Challenge := by
  induction rounds with
  | nil => exact pre.elim
  | cons round rounds ih =>
      cases pre with
      | inl _ => exact round.nonemptyChallenge
      | inr data => exact ih data.2.2

instance {rounds : List Round} (pre : Prefix Salt rounds) : SampleableType pre.Challenge := by
  induction rounds with
  | nil => exact pre.elim
  | cons round rounds ih =>
      cases pre with
      | inl _ => exact round.sampleChallenge
      | inr data => exact ih data.2.2

end Prefix

/-- A restoration key: an input and a salted prefix of that input's rounds. -/
abbrev Key (Input Salt : Type) (rounds : Input → List Round) :=
  (z : Input) × Prefix Salt (rounds z)

/-- The answer type of a key is the challenge alphabet of its round. -/
@[reducible] def Key.Challenge {Input Salt : Type} {rounds : Input → List Round}
    (key : Key Input Salt rounds) : Type :=
  key.2.Challenge

instance {Input Salt : Type} {rounds : Input → List Round} (key : Key Input Salt rounds) :
    Finite key.Challenge :=
  inferInstanceAs (Finite key.2.Challenge)

instance {Input Salt : Type} {rounds : Input → List Round} (key : Key Input Salt rounds) :
    Nonempty key.Challenge :=
  inferInstanceAs (Nonempty key.2.Challenge)

instance {Input Salt : Type} {rounds : Input → List Round} (key : Key Input Salt rounds) :
    SampleableType key.Challenge :=
  inferInstanceAs (SampleableType key.2.Challenge)

/-- A deterministic complete answer assignment on the prefixes of one round list. -/
abbrev PrefixTable (Salt : Type) (rounds : List Round) :=
  (pre : Prefix Salt rounds) → pre.Challenge

/-- A deterministic complete answer assignment, used to prove properties of cached execution. -/
abbrev Table (Input Salt : Type) (rounds : Input → List Round) :=
  (key : Key Input Salt rounds) → key.Challenge

/-- The answers of a complete table at the keys of one input. -/
abbrev Table.fibre {Input Salt : Type} {rounds : Input → List Round}
    (table : Table Input Salt rounds) (z : Input) : PrefixTable Salt (rounds z) :=
  fun pre => table ⟨z, pre⟩

/-- Updating a table at a key of input `z` updates the fibre of `z` at that key's prefix. -/
theorem Table.fibre_update {Input Salt : Type} {rounds : Input → List Round}
    [DecidableEq Input] [DecidableEq Salt]
    (table : Table Input Salt rounds) (z : Input) (pre : Prefix Salt (rounds z))
    (value : pre.Challenge) :
    Table.fibre (Function.update table ⟨z, pre⟩ value) z =
      Function.update (Table.fibre table z) pre value := by
  funext other
  by_cases h : other = pre
  · subst other
    simp [Table.fibre]
  · have hkey : (⟨z, other⟩ : Key Input Salt rounds) ≠ ⟨z, pre⟩ := by
      intro heq
      exact h (eq_of_heq (Sigma.mk.inj heq).2)
    simp only [Table.fibre, Function.update_of_ne hkey, Function.update_of_ne h]

universe w

/-- Reconstruct the pre-challenge extractor using this prefix's strict ancestor responses. -/
def prefixExtractor {Salt : Type} : {rounds : List Round} → {state : KnowledgeState.{w}} →
    RoundExtractor (protocol rounds).tree state → (pre : Prefix Salt rounds) →
    PrefixTable Salt rounds →
    (before : KnowledgeState.{w}) ×
      RoundExtractor (.public pre.Challenge (fun _ => (protocol pre.remaining).tree)) before
  | [], _, _, pre, _ => nomatch pre
  | _ :: _, _, extractor, .inl (message, _), _ =>
      ⟨(extractor message).1, (extractor message).2.2⟩
  | _ :: _, _, extractor, .inr (message, salt, pre), table =>
      let challenge := table (Prefix.here message salt)
      let afterMessage := (extractor message).2.2
      prefixExtractor (afterMessage challenge).2.2 pre
        (fun q => table (Prefix.later message salt q))

/-- Resampling a target prefix leaves its reconstructed pre-challenge extractor unchanged. -/
theorem prefixExtractor_update {Salt : Type} {rounds : List Round} [DecidableEq Salt]
    {state : KnowledgeState.{w}}
    (extractor : RoundExtractor (protocol rounds).tree state)
    (pre : Prefix Salt rounds) (table : PrefixTable Salt rounds) (value : pre.Challenge) :
    prefixExtractor extractor pre (Function.update table pre value) =
      prefixExtractor extractor pre table := by
  classical
  induction rounds generalizing state with
  | nil => exact pre.elim
  | cons round rounds ih =>
      cases pre with
      | inl data => rfl
      | inr data =>
          rcases data with ⟨message, salt, pre⟩
          simp only [prefixExtractor]
          have hhere : Function.update table (Prefix.later message salt pre) value
              (Prefix.here message salt) = table (Prefix.here message salt) := by
            apply Function.update_of_ne
            simp [Prefix.here, Prefix.later]
          rw [hhere]
          have htable : (fun q => Function.update table (Prefix.later message salt pre) value
                (Prefix.later message salt q)) =
              Function.update (fun q => table (Prefix.later message salt q)) pre value := by
            funext q
            by_cases hq : q = pre
            · subst q
              simp
            · simp [Function.update_of_ne hq, Function.update_of_ne
                (show Prefix.later message salt q ≠ Prefix.later message salt pre by
                  simpa [Prefix.later] using hq)]
          rw [htable]
          exact ih _ pre _ value

/-- Every receiver uses its round's uniform challenge and the same stated local error. -/
def uniformSchedule (error : ENNReal) : (rounds : List Round) →
    RoundExtractor.ChallengeSchedule (protocol rounds).tree (protocol rounds).roles
  | [] => PUnit.unit
  | round :: rounds => fun _ => ⟨⟨$ᵗ round.Challenge, error⟩,
      fun _ => uniformSchedule error rounds⟩

/-- An all-authored-prefix knowledge bound applies to every reconstructed salted prefix. -/
theorem prefixExtractor_local_bound {Salt : Type} {rounds : List Round}
    {state : KnowledgeState.{w}} (extractor : RoundExtractor (protocol rounds).tree state)
    (error : ENNReal)
    (bounded : RoundExtractor.IsLocallyBounded extractor (protocol rounds).roles
      (uniformSchedule error rounds))
    (pre : Prefix Salt rounds) (table : PrefixTable Salt rounds) :
    Pr{let response ← $ᵗ pre.Challenge}[
      RoundExtractor.badChallenge (prefixExtractor extractor pre table).2 response] ≤ error := by
  induction rounds generalizing state with
  | nil => exact pre.elim
  | cons round rounds ih =>
      cases pre with
      | inl data =>
          rcases data with ⟨message, salt⟩
          have h := (_root_.RoundByRound.GameFamily.isBounded_iff _ _).mp
            (bounded message).1 PUnit.unit PUnit.unit
          exact h
      | inr data =>
          rcases data with ⟨message, salt, pre⟩
          exact ih ((extractor message).2.2 (table (Prefix.here message salt))).2.2
            ((bounded message).2 (table (Prefix.here message salt))) pre
            (fun q => table (Prefix.later message salt q))

/-- The complete prover-message and salt sequence returned by a restoration adversary. -/
def Messages (Salt : Type) : List Round → Type
  | [] => PUnit
  | round :: rounds => round.Message × Salt × Messages Salt rounds

/-- The oracle on the salted prefixes of one round list. -/
abbrev prefixSpec (Salt : Type) (rounds : List Round) : OracleSpec (Prefix Salt rounds) :=
  OracleSpec.ofFn Prefix.Challenge

/-- The restoration oracle answers each key with its round's challenge type. -/
abbrev oracleSpec (Input Salt : Type) (rounds : Input → List Round) :
    OracleSpec (Key Input Salt rounds) :=
  OracleSpec.ofFn Key.Challenge

/-- Route a suffix prefix through the retained first prover message and salt. -/
def prependQuery {Salt : Type} {round : Round} {rounds : List Round}
    (message : round.Message) (salt : Salt) :
    QueryImpl (prefixSpec Salt rounds) (OracleComp (prefixSpec Salt (round :: rounds))) :=
  fun pre => liftM ((prefixSpec Salt (round :: rounds)).query (Prefix.later message salt pre))

/-- Route a prefix of input `z`'s rounds to its restoration key. -/
def inputQuery {Input Salt : Type} {rounds : Input → List Round} (z : Input) :
    QueryImpl (prefixSpec Salt (rounds z)) (OracleComp (oracleSpec Input Salt rounds)) :=
  fun pre => liftM ((oracleSpec Input Salt rounds).query ⟨z, pre⟩)

/-- Complete a message sequence by reading all challenges from the prefix oracle. -/
def completePrefix {Salt : Type} : (rounds : List Round) → Messages Salt rounds →
    OracleComp (prefixSpec Salt rounds) (protocol rounds).tree.ExecutionPath
  | [], _ => pure PUnit.unit
  | round :: rounds, (message, salt, messages) => do
      let challenge ← liftM ((prefixSpec Salt (round :: rounds)).query
        (Prefix.here message salt))
      let path ← simulateQ (prependQuery message salt) (completePrefix rounds messages)
      pure ⟨message, ⟨challenge, path⟩⟩

/-- Complete the selected transcript by reading all challenges from the same restoration oracle,
at the keys of the selected input. -/
def complete {Input Salt : Type} (rounds : Input → List Round) (z : Input)
    (messages : Messages Salt (rounds z)) :
    OracleComp (oracleSpec Input Salt rounds) (protocol (rounds z)).tree.ExecutionPath :=
  simulateQ (inputQuery z) (completePrefix (rounds z) messages)

/-- Prefix completion makes at most one access per protocol round, including repeated cached
prefixes. -/
theorem completePrefix_queryBound {Salt : Type} (rounds : List Round)
    (messages : Messages Salt rounds) :
    IsTotalQueryBound (completePrefix rounds messages) rounds.length := by
  induction rounds with
  | nil => trivial
  | cons round rounds ih =>
      rcases messages with ⟨message, salt, messages⟩
      simp only [completePrefix, List.length_cons, isTotalQueryBound_query_bind_iff,
        Nat.add_sub_cancel]
      refine ⟨by omega, fun challenge => ?_⟩
      have h := (ih messages).simulateQ_of_step_le (step := 1)
        (fun pre => show IsTotalQueryBound
          (prependQuery (Salt := Salt) (round := round) message salt pre) 1 from by
            change IsTotalQueryBound
              (liftM ((prefixSpec Salt (round :: rounds)).query
                (Prefix.later message salt pre)) >>= pure) 1
            exact ⟨by omega, fun _ => trivial⟩)
      have hb := isTotalQueryBound_bind h (fun path => show IsTotalQueryBound
        (pure (⟨message, ⟨challenge, path⟩⟩ : (protocol (round :: rounds)).tree.ExecutionPath) :
          OracleComp (prefixSpec Salt (round :: rounds)) _) 0 from trivial)
      simpa only [Nat.mul_one, Nat.add_zero, protocol, Protocol.oracleWith, Protocol.public]
        using hb

/-- Completion makes at most one access per round of the selected input. -/
theorem complete_queryBound {Input Salt : Type} (rounds : Input → List Round) (z : Input)
    (messages : Messages Salt (rounds z)) :
    IsTotalQueryBound (complete rounds z messages) (rounds z).length := by
  have h := (completePrefix_queryBound (rounds z) messages).simulateQ_of_step_le (step := 1)
    (impl := inputQuery (Input := Input) (rounds := rounds) z)
    (fun pre => show IsTotalQueryBound
      (inputQuery (Input := Input) (Salt := Salt) (rounds := rounds) z pre) 1 from by
        change IsTotalQueryBound
          (liftM ((oracleSpec Input Salt rounds).query ⟨z, pre⟩) >>= pure) 1
        exact ⟨by omega, fun _ => trivial⟩)
  rw [complete]
  simpa only [Nat.mul_one] using h

/-- The execution path reconstructed from a deterministic prefix challenge table. -/
def prefixPath {Salt : Type} : (rounds : List Round) →
    Messages Salt rounds → PrefixTable Salt rounds → (protocol rounds).tree.ExecutionPath
  | [], _, _ => PUnit.unit
  | _ :: rounds, (message, salt, messages), table =>
      ⟨message, ⟨table (Prefix.here message salt),
        prefixPath rounds messages (fun q => table (Prefix.later message salt q))⟩⟩

/-- The existing execution path reconstructed from a deterministic challenge table. -/
def completedPath {Input Salt : Type} (rounds : Input → List Round) (z : Input)
    (messages : Messages Salt (rounds z)) (table : Table Input Salt rounds) :
    (protocol (rounds z)).tree.ExecutionPath :=
  prefixPath (rounds z) messages (Table.fibre table z)

/-- The prefixes read when completing this message sequence. -/
def prefixKeys {Salt : Type} : (rounds : List Round) → Messages Salt rounds →
    List (Prefix Salt rounds)
  | [], _ => []
  | _ :: rounds, (message, salt, messages) =>
      Prefix.here message salt ::
        (prefixKeys rounds messages).map (Prefix.later message salt)

/-- The actual challenge keys read when completing this selected message sequence. -/
def completionKeys {Input Salt : Type} (rounds : Input → List Round) (z : Input)
    (messages : Messages Salt (rounds z)) : List (Key Input Salt rounds) :=
  (prefixKeys (rounds z) messages).map (Sigma.mk z)

/-- Deterministic execution of prefix completion returns exactly the reconstructed path. -/
theorem completePrefix_eval {Salt : Type} (rounds : List Round)
    (messages : Messages Salt rounds) (table : PrefixTable Salt rounds) :
    evalWithAnswerFn (QueryImpl.ofFn table) (completePrefix rounds messages) =
      prefixPath rounds messages table := by
  induction rounds with
  | nil => rfl
  | cons round rounds ih =>
      rcases messages with ⟨message, salt, messages⟩
      simp only [completePrefix, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query,
        QueryImpl.ofFn_apply, evalWithAnswerFn_simulateQ, prependQuery,
        prefixPath]
      exact congrArg (fun path => (⟨message, ⟨table (Prefix.here message salt), path⟩⟩ :
          (protocol (round :: rounds)).tree.ExecutionPath))
        (ih messages (fun q => table (Prefix.later message salt q)))

/-- Deterministic execution of completion returns exactly the reconstructed path. -/
theorem complete_eval {Input Salt : Type} (rounds : Input → List Round) (z : Input)
    (messages : Messages Salt (rounds z)) (table : Table Input Salt rounds) :
    evalWithAnswerFn (QueryImpl.ofFn table) (complete rounds z messages) =
      completedPath rounds z messages table := by
  simp only [complete, evalWithAnswerFn_simulateQ, inputQuery, evalWithAnswerFn_liftM_query,
    QueryImpl.ofFn_apply, completedPath]
  exact completePrefix_eval (rounds z) messages (Table.fibre table z)

/-- The prefix-key list is the projection of the actual prefix-oracle query log. -/
theorem completePrefix_log_keys {Salt : Type} (rounds : List Round)
    (messages : Messages Salt rounds) (table : PrefixTable Salt rounds) :
    (tableQueryLog (completePrefix rounds messages) table).map Sigma.fst =
      prefixKeys rounds messages := by
  induction rounds with
  | nil => simp [completePrefix, prefixKeys, protocol, Protocol.done]
  | cons round rounds ih =>
      rcases messages with ⟨message, salt, messages⟩
      simp only [completePrefix, protocol, Protocol.oracleWith, Protocol.public,
        tableQueryLog_bind, tableQueryLog_pure, List.append_nil, tableQueryLog_simulateQ,
        prependQuery, evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply, tableQueryLog_query,
        List.singleton_append, List.map_cons, ← List.map_eq_flatMap, List.map_map,
        Function.comp_def, prefixKeys]
      congr 1
      simpa only [List.flatMap_singleton, List.map_map, Function.comp_def] using
        congrArg (List.map (Prefix.later message salt))
          (ih messages (fun q => table (Prefix.later message salt q)))

/-- The completion-key list is the projection of the actual oracle query log. -/
theorem complete_log_keys {Input Salt : Type} (rounds : Input → List Round) (z : Input)
    (messages : Messages Salt (rounds z)) (table : Table Input Salt rounds) :
    (tableQueryLog (complete rounds z messages) table).map Sigma.fst =
      completionKeys rounds z messages := by
  simp only [complete, tableQueryLog_simulateQ, inputQuery, evalWithAnswerFn_liftM_query,
    QueryImpl.ofFn_apply, tableQueryLog_query, ← List.map_eq_flatMap, List.map_map,
    Function.comp_def, completionKeys]
  rw [← completePrefix_log_keys (rounds z) messages (Table.fibre table z), List.map_map]
  rfl

/-- A bad challenge on the reconstructed path is a bad prefix in its actual completion log. -/
theorem badChallengeOnPath_prefixPath {Salt : Type} {rounds : List Round}
    {state : KnowledgeState.{w}} (extractor : RoundExtractor (protocol rounds).tree state)
    (messages : Messages Salt rounds) (table : PrefixTable Salt rounds)
    (witness : (extractor.terminalState (prefixPath rounds messages table)).Witness)
    (bad : extractor.BadChallengeOnPath (protocol rounds).roles
      (prefixPath rounds messages table) witness) :
    ∃ pre ∈ prefixKeys rounds messages,
      RoundExtractor.badChallenge (prefixExtractor extractor pre table).2 (table pre) := by
  induction rounds generalizing state with
  | nil => exact bad.elim
  | cons round rounds ih =>
      rcases messages with ⟨message, salt, messages⟩
      rcases bad with bad | bad
      · refine ⟨Prefix.here message salt, List.mem_cons_self, ?_⟩
        exact ⟨_, bad.2.1, bad.2.2⟩
      · obtain ⟨pre, hpre, hb⟩ := ih
          ((extractor message).2.2 (table (Prefix.here message salt))).2.2
          messages (fun q => table (Prefix.later message salt q)) witness bad
        exact ⟨Prefix.later message salt pre,
          List.mem_cons_of_mem _ (List.mem_map.mpr ⟨pre, hpre, rfl⟩), hb⟩

/-- An adversary's selection: an input, a complete message sequence for that input's rounds,
and a terminal witness. -/
abbrev Selection (Input Salt W : Type) (rounds : Input → List Round) :=
  (z : Input) × Messages Salt (rounds z) × W

/-- A completed selection: an input, an execution path of that input's rounds, and a terminal
witness. -/
abbrev Outcome (Input W : Type) (rounds : Input → List Round) :=
  (z : Input) × (protocol (rounds z)).tree.ExecutionPath × W

/-- Run the adaptive adversary, then complete its selected transcript using the same oracle. -/
def restoredExecution {Input Salt W : Type} (rounds : Input → List Round)
    (adversary : OracleComp (oracleSpec Input Salt rounds) (Selection Input Salt W rounds)) :
    OracleComp (oracleSpec Input Salt rounds) (Outcome Input W rounds) := do
  let ⟨z, messages, witness⟩ ← adversary
  let path ← complete rounds z messages
  pure ⟨z, path, witness⟩

/-- The adversary and completion together make at most `Q + k` accesses when every input has at
most `k` rounds. -/
theorem restoredExecution_queryBound {Input Salt W : Type} (rounds : Input → List Round)
    (adversary : OracleComp (oracleSpec Input Salt rounds) (Selection Input Salt W rounds))
    (Q k : ℕ) (bounded : IsTotalQueryBound adversary Q)
    (length_le : ∀ z, (rounds z).length ≤ k) :
    IsTotalQueryBound (restoredExecution rounds adversary) (Q + k) := by
  apply isTotalQueryBound_bind bounded
  rintro ⟨z, messages, witness⟩
  have h := isTotalQueryBound_bind
    ((complete_queryBound rounds z messages).mono (length_le z))
    (fun path => show IsTotalQueryBound
      (pure (⟨z, path, witness⟩ : Outcome Input W rounds) :
        OracleComp (oracleSpec Input Salt rounds) _) 0 from trivial)
  simpa only [Nat.add_zero] using h

/-- A permitted-input key at which some later witness fails backward knowledge preservation. -/
def badKey {Input Salt : Type} {rounds : Input → List Round}
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol (rounds z)).tree (state z))
    (Z : Set Input) (key : Key Input Salt rounds) (table : Table Input Salt rounds) : Prop :=
  key.1 ∈ Z ∧ RoundExtractor.badChallenge
    (prefixExtractor (extractor key.1) key.2 (Table.fibre table key.1)).2 (table key)

/-- Resampling a key leaves its event a function of the fresh response alone. -/
theorem badKey_update_iff {Input Salt : Type} {rounds : Input → List Round}
    [DecidableEq Input] [DecidableEq Salt]
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol (rounds z)).tree (state z))
    (Z : Set Input) (key : Key Input Salt rounds) (table : Table Input Salt rounds)
    (response : key.Challenge) :
    badKey state extractor Z key (Function.update table key response) ↔
      key.1 ∈ Z ∧ RoundExtractor.badChallenge
        (prefixExtractor (extractor key.1) key.2 (Table.fibre table key.1)).2 response := by
  rcases key with ⟨z, pre⟩
  unfold badKey
  rw [Table.fibre_update, prefixExtractor_update, Function.update_self]

/-- All-prefix knowledge bounds hold when resampling each target in every background table. -/
theorem badKey_resample_bound {Input Salt : Type} {rounds : Input → List Round}
    [DecidableEq Input] [DecidableEq Salt]
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol (rounds z)).tree (state z))
    (Z : Set Input) (error : ENNReal)
    (bounded : ∀ z ∈ Z, RoundExtractor.IsLocallyBounded (extractor z) (protocol (rounds z)).roles
      (uniformSchedule error (rounds z)))
    (key : Key Input Salt rounds) (table : Table Input Salt rounds) :
    Pr{let response ← $ᵗ key.Challenge}[
      badKey state extractor Z key (Function.update table key response)] ≤ error := by
  simp_rw [badKey_update_iff]
  by_cases hz : key.1 ∈ Z
  · simp only [hz, true_and]
    exact prefixExtractor_local_bound (extractor key.1) error
      (bounded key.1 hz) key.2 (Table.fibre table key.1)
  · simp only [hz, false_and]
    simp

/-- A valid terminal witness whose backward extraction fails on the completed path of input `z`
identifies a bad key among that completion's keys. -/
theorem badKey_of_completedPath {Input Salt W : Type} {rounds : Input → List Round}
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol (rounds z)).tree (state z))
    (Z : Set Input)
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol (rounds z)).roles)
    (terminalWitness : (z : Input) → (path : (protocol (rounds z)).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (z : Input) (messages : Messages Salt (rounds z)) (witness : W)
    (table : Table Input Salt rounds)
    (hz : z ∈ Z)
    (holds : ((extractor z).terminalState (completedPath rounds z messages table)).holds
      (terminalWitness z (completedPath rounds z messages table) witness))
    (fails : ¬ (state z).holds ((extractor z).extractWitness
      (completedPath rounds z messages table)
      (terminalWitness z (completedPath rounds z messages table) witness))) :
    ∃ key ∈ completionKeys rounds z messages, badKey state extractor Z key table := by
  have hbad := RoundExtractor.extraction_failure_implies_bad_challenge (extractor z)
    (protocol (rounds z)).roles (preserving z hz) _ _ holds fails
  obtain ⟨pre, hpre, hb⟩ :=
    badChallengeOnPath_prefixPath (extractor z) messages (Table.fibre table z) _ hbad
  exact ⟨⟨z, pre⟩, List.mem_map.mpr ⟨pre, hpre, rfl⟩, hz, hb⟩

/-- Failed backward extraction from terminal knowledge identifies an actually accessed bad key. -/
theorem restored_bad_trace {Input Salt W : Type} {rounds : Input → List Round}
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol (rounds z)).tree (state z))
    (Z : Set Input)
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol (rounds z)).roles)
    (terminalWitness : (z : Input) → (path : (protocol (rounds z)).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (adversary : OracleComp (oracleSpec Input Salt rounds) (Selection Input Salt W rounds))
    (table : Table Input Salt rounds)
    (bad : let result :=
        evalWithAnswerFn (QueryImpl.ofFn table) (restoredExecution rounds adversary)
      result.1 ∈ Z ∧
      ((extractor result.1).terminalState result.2.1).holds
        (terminalWitness result.1 result.2.1 result.2.2) ∧
      ¬ (state result.1).holds ((extractor result.1).extractWitness result.2.1
        (terminalWitness result.1 result.2.1 result.2.2))) :
    ∃ q ∈ tableQueryLog (restoredExecution rounds adversary) table,
      badKey state extractor Z q.1 table := by
  let result := evalWithAnswerFn (QueryImpl.ofFn table) adversary
  rcases hresult : result with ⟨z, messages, witness⟩
  have heval : evalWithAnswerFn (QueryImpl.ofFn table) (restoredExecution rounds adversary) =
      ⟨z, completedPath rounds z messages table, witness⟩ := by
    simp only [restoredExecution, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
    change (⟨result.1,
      evalWithAnswerFn (QueryImpl.ofFn table) (complete rounds result.1 result.2.1),
        result.2.2⟩ : Outcome Input W rounds) = _
    rw [hresult, complete_eval]
  dsimp only at bad
  rw [heval] at bad
  obtain ⟨key, hkey, hb⟩ := badKey_of_completedPath state extractor Z preserving
    terminalWitness z messages witness table bad.1 bad.2.1 bad.2.2
  have hmem : key ∈ (tableQueryLog (complete rounds z messages) table).map Sigma.fst := by
    rwa [complete_log_keys]
  obtain ⟨q, hq, heq⟩ := List.mem_map.mp hmem
  refine ⟨q, ?_, heq ▸ hb⟩
  simp only [restoredExecution, tableQueryLog_bind]
  apply List.mem_append_right
  change q ∈ tableQueryLog (complete rounds result.1 result.2.1) table ++ _
  rw [hresult]
  exact List.mem_append_left _ hq

/-- All-prefix round-by-round knowledge bounds imply the `(Q + k) * error` extraction bound in
the actual cached restoration/completion experiment, where every input has at most `k` rounds.
The input is selected adaptively, the terminal witness is supplied by the adversary, and its
named carrier map is explicit data. -/
theorem restored_extraction_bound {Input Salt W : Type} {rounds : Input → List Round}
    [DecidableEq Input] [DecidableEq Salt]
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol (rounds z)).tree (state z))
    (Z : Set Input) (error : ENNReal)
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol (rounds z)).roles)
    (bounded : ∀ z ∈ Z, RoundExtractor.IsLocallyBounded (extractor z) (protocol (rounds z)).roles
      (uniformSchedule error (rounds z)))
    (terminalWitness : (z : Input) → (path : (protocol (rounds z)).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (adversary : OracleComp (oracleSpec Input Salt rounds) (Selection Input Salt W rounds))
    (Q k : ℕ) (queryBound : IsTotalQueryBound adversary Q)
    (length_le : ∀ z, (rounds z).length ≤ k) :
    Pr{let result ← (simulateQ randomOracle (restoredExecution rounds adversary)).run' ∅}[
      result.1 ∈ Z ∧
      ((extractor result.1).terminalState result.2.1).holds
        (terminalWitness result.1 result.2.1 result.2.2) ∧
      ¬ (state result.1).holds ((extractor result.1).extractWitness result.2.1
        (terminalWitness result.1 result.2.1 result.2.2))] ≤
      (Q + k) * error := by
  rw [← Nat.cast_add]
  apply prEvent_randomOracle_le_of_bad_queries _ (Q + k)
    (restoredExecution_queryBound rounds adversary Q k queryBound length_le) _
    (badKey state extractor Z) error
  · exact badKey_resample_bound state extractor Z error bounded
  · exact restored_bad_trace state extractor Z preserving terminalWitness adversary

end Interaction.Oracle.Security.StateRestoration
