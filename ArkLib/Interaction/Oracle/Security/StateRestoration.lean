/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude
-/
module

public import ArkLib.Interaction.Oracle.Security.Knowledge
public import ArkLib.Interaction.Oracle.PublicCoin
public import VCVio.OracleComp.QueryTracking.RandomOracle.FreshQuery

/-!
# Backward extraction in the state-restoration experiment

The protocol of input `z` is `protocol z`, presented as public-coin by `coin z`: after each
challenge its shape does not depend on the challenge, though it may depend on the input and on
the prover's public moves. A restoration key is an input `z` together with a salted prefix of
`coin z` ending at a challenge: the prover's public moves and oracle payloads up to that
challenge, and a salt at each challenge up to and including it, with the earlier challenges
erased. The input is the outermost component. A key's knowledge state reconstructs its strict
ancestors' challenges from the same table, and changing its own response cannot change that
state.

For an arbitrary adaptive adversary, completion reads the selected transcript's challenges from
the same cached oracle (`complete`), and a valid terminal knowledge witness whose backward
extraction fails identifies a bad key among the keys it read (`restored_bad_trace`). The
probability bounds that follow are in `StateRestorationBudget`. Inputs, salts and prover moves may
have infinite types; challenges have finite nonempty uniform samplers.

`Round` and `protocol` give the fixed-shape fragment of alternating oracle messages and
challenges, presented by `Round.coin`.
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
  finiteChallenge : Finite Challenge
  nonemptyChallenge : Nonempty Challenge
  sampleChallenge : SampleableType Challenge

attribute [instance] Round.decEqMessage Round.finiteChallenge Round.nonemptyChallenge
  Round.sampleChallenge

/-- The fixed presentation uses oracle-message and public-receiver nodes. -/
def protocol : List Round → Protocol
  | [] => .done
  | round :: rounds => .oracleWith round.Message round.interface
      (.public .receiver round.Challenge (fun _ => protocol rounds))

/-- Alternating oracle messages and challenges are public-coin. -/
def Round.coin : (rounds : List Round) → PublicCoin (protocol rounds)
  | [] => .done
  | _ :: rounds => .oracle (.challenge (Round.coin rounds))

/-! ### Keys -/

/-- A salted prefix ending at a challenge: the prover's moves and oracle payloads before it, and
a salt at each challenge up to and including it. No verifier challenge is part of a prefix. -/
@[reducible] def Prefix (Salt : Type) {protocol : Protocol} (coin : PublicCoin protocol) : Type :=
  PublicCoin.rec (motive := fun _ _ => Type) Empty
    (fun {Moves} _ _ _ prefixes => (move : Moves) × prefixes move)
    (fun {Messages} _ _ _ _ prefixes => Messages × prefixes)
    (fun _ prefixes => Salt ⊕ (Salt × prefixes)) coin

namespace Prefix

variable {Salt : Type}

instance instDecidableEq [DecidableEq Salt] :
    {protocol : Protocol} → (coin : PublicCoin protocol) → DecidableEq (Prefix Salt coin)
  | _, .done => fun pre => nomatch pre
  | _, @PublicCoin.sender Moves _ _ next =>
      letI := fun move => instDecidableEq (next move)
      inferInstanceAs (DecidableEq ((move : Moves) × Prefix Salt (next move)))
  | _, @PublicCoin.oracle Messages _ _ _ next =>
      letI := instDecidableEq next
      inferInstanceAs (DecidableEq (Messages × Prefix Salt next))
  | _, @PublicCoin.challenge _ _ _ _ _ next =>
      letI := instDecidableEq next
      inferInstanceAs (DecidableEq (Salt ⊕ (Salt × Prefix Salt next)))

/-- The answer type of a prefix is the alphabet of the challenge it ends at. -/
@[reducible] def Challenge {protocol : Protocol} {coin : PublicCoin protocol} :
    Prefix Salt coin → Type :=
  PublicCoin.rec (motive := fun _ coin => Prefix Salt coin → Type) (fun pre => nomatch pre)
    (fun _ challenge pre => challenge pre.1 pre.2) (fun _ challenge pre => challenge pre.2)
    (@fun Challenge _ _ _ _ _ challenge pre => Sum.casesOn pre (fun _ => Challenge)
      fun pre => challenge pre.2) coin

/-- The protocol following the challenge a prefix ends at. -/
@[reducible] noncomputable def rest {protocol : Protocol} {coin : PublicCoin protocol} :
    Prefix Salt coin → Protocol :=
  PublicCoin.rec (motive := fun _ coin => Prefix Salt coin → Protocol) (fun pre => nomatch pre)
    (fun _ rest pre => rest pre.1 pre.2) (fun _ rest pre => rest pre.2)
    (@fun _ _ _ _ restProtocol _ rest pre => Sum.casesOn pre (fun _ => restProtocol)
      fun pre => rest pre.2) coin

/-- The challenge node a prefix ends at, with its salts forgotten. -/
@[reducible] noncomputable def node {protocol : Protocol} {coin : PublicCoin protocol} :
    Prefix Salt coin → Prefix PUnit coin :=
  PublicCoin.rec (motive := fun _ coin => Prefix Salt coin → Prefix PUnit coin)
    (fun pre => nomatch pre)
    (fun _ node pre => ⟨pre.1, node pre.1 pre.2⟩) (fun _ node pre => ⟨pre.1, node pre.2⟩)
    (fun _ node pre => Sum.casesOn (motive := fun _ => PUnit ⊕ (PUnit × _)) pre
      (fun _ => .inl PUnit.unit) fun pre => .inr ⟨PUnit.unit, node pre.2⟩) coin

instance instFinite : {protocol : Protocol} → {coin : PublicCoin protocol} →
    (pre : Prefix Salt coin) → Finite pre.Challenge
  | _, .done, pre => nomatch pre
  | _, @PublicCoin.sender _ _ _ _, ⟨_, pre⟩ => instFinite pre
  | _, @PublicCoin.oracle _ _ _ _ _, ⟨_, pre⟩ => instFinite pre
  | _, @PublicCoin.challenge _ _ _ _ _ _, .inl _ => inferInstance
  | _, @PublicCoin.challenge _ _ _ _ _ _, .inr ⟨_, pre⟩ => instFinite pre

instance instNonempty : {protocol : Protocol} → {coin : PublicCoin protocol} →
    (pre : Prefix Salt coin) → Nonempty pre.Challenge
  | _, .done, pre => nomatch pre
  | _, @PublicCoin.sender _ _ _ _, ⟨_, pre⟩ => instNonempty pre
  | _, @PublicCoin.oracle _ _ _ _ _, ⟨_, pre⟩ => instNonempty pre
  | _, @PublicCoin.challenge _ _ _ _ _ _, .inl _ => inferInstance
  | _, @PublicCoin.challenge _ _ _ _ _ _, .inr ⟨_, pre⟩ => instNonempty pre

instance instSampleableType : {protocol : Protocol} → {coin : PublicCoin protocol} →
    (pre : Prefix Salt coin) → SampleableType pre.Challenge
  | _, .done, pre => nomatch pre
  | _, @PublicCoin.sender _ _ _ _, ⟨_, pre⟩ => instSampleableType pre
  | _, @PublicCoin.oracle _ _ _ _ _, ⟨_, pre⟩ => instSampleableType pre
  | _, @PublicCoin.challenge _ _ _ _ _ _, .inl _ => inferInstance
  | _, @PublicCoin.challenge _ _ _ _ _ _, .inr ⟨_, pre⟩ => instSampleableType pre

end Prefix

section

variable {Input : Type} {protocol : Input → Protocol}

/-- A restoration key: an input and a salted prefix of that input's protocol. -/
abbrev Key (Input Salt : Type) {protocol : Input → Protocol}
    (coin : (z : Input) → PublicCoin (protocol z)) :=
  (z : Input) × Prefix Salt (coin z)

/-- The answer type of a key is the challenge alphabet of its node. -/
@[reducible] def Key.Challenge {Salt : Type} {coin : (z : Input) → PublicCoin (protocol z)}
    (key : Key Input Salt coin) : Type :=
  key.2.Challenge

instance {Salt : Type} {coin : (z : Input) → PublicCoin (protocol z)}
    (key : Key Input Salt coin) : Finite key.Challenge :=
  inferInstanceAs (Finite key.2.Challenge)

instance {Salt : Type} {coin : (z : Input) → PublicCoin (protocol z)}
    (key : Key Input Salt coin) : Nonempty key.Challenge :=
  inferInstanceAs (Nonempty key.2.Challenge)

instance {Salt : Type} {coin : (z : Input) → PublicCoin (protocol z)}
    (key : Key Input Salt coin) : SampleableType key.Challenge :=
  inferInstanceAs (SampleableType key.2.Challenge)

end

/-- A deterministic complete answer assignment on the prefixes of one protocol. -/
abbrev PrefixTable (Salt : Type) {protocol : Protocol} (coin : PublicCoin protocol) :=
  (pre : Prefix Salt coin) → pre.Challenge

/-- A deterministic complete answer assignment, used to prove properties of cached execution. -/
abbrev Table (Input Salt : Type) {protocol : Input → Protocol}
    (coin : (z : Input) → PublicCoin (protocol z)) :=
  (key : Key Input Salt coin) → key.Challenge

/-- The answers of a complete table at the keys of one input. -/
abbrev Table.fibre {Input Salt : Type} {protocol : Input → Protocol}
    {coin : (z : Input) → PublicCoin (protocol z)}
    (table : Table Input Salt coin) (z : Input) : PrefixTable Salt (coin z) :=
  fun pre => table ⟨z, pre⟩

/-- Updating a table at a key of input `z` updates the fibre of `z` at that key's prefix. -/
theorem Table.fibre_update {Input Salt : Type} {protocol : Input → Protocol}
    {coin : (z : Input) → PublicCoin (protocol z)} [DecidableEq Input] [DecidableEq Salt]
    (table : Table Input Salt coin) (z : Input) (pre : Prefix Salt (coin z))
    (value : pre.Challenge) :
    Table.fibre (Function.update table ⟨z, pre⟩ value) z =
      Function.update (Table.fibre table z) pre value := by
  funext other
  by_cases h : other = pre
  · subst other
    simp [Table.fibre]
  · have hkey : (⟨z, other⟩ : Key Input Salt coin) ≠ ⟨z, pre⟩ := by
      intro heq
      exact h (eq_of_heq (Sigma.mk.inj heq).2)
    simp only [Table.fibre, Function.update_of_ne hkey, Function.update_of_ne h]

/-! ### Reindexed oracle access -/

/-- Answer queries at `q` by querying `f q`, whose answer type is the same. -/
def reindexQuery {D D' : Type} {R : D → Type} (f : D' → D) :
    QueryImpl (OracleSpec.ofFn fun q => R (f q)) (OracleComp (OracleSpec.ofFn R)) :=
  fun q => liftM ((OracleSpec.ofFn R).query (f q))

theorem evalWithAnswerFn_reindexQuery {D D' A : Type} {R : D → Type} (f : D' → D)
    (table : (d : D) → R d) (program : OracleComp (OracleSpec.ofFn fun q => R (f q)) A) :
    evalWithAnswerFn (QueryImpl.ofFn table) (simulateQ (reindexQuery f) program) =
      evalWithAnswerFn (QueryImpl.ofFn fun q => table (f q)) program := by
  simp only [evalWithAnswerFn_simulateQ, reindexQuery, evalWithAnswerFn_liftM_query,
    QueryImpl.ofFn_apply]
  rfl

theorem tableQueryLog_reindexQuery {D D' A : Type} {R : D → Type} (f : D' → D)
    (table : (d : D) → R d) (program : OracleComp (OracleSpec.ofFn fun q => R (f q)) A) :
    (tableQueryLog (simulateQ (reindexQuery f) program) table).map Sigma.fst =
      ((tableQueryLog program fun q => table (f q)).map Sigma.fst).map f := by
  simp only [tableQueryLog_simulateQ, reindexQuery, evalWithAnswerFn_liftM_query,
    QueryImpl.ofFn_apply, tableQueryLog_query, ← List.map_eq_flatMap, List.map_map,
    Function.comp_def]

theorem isTotalQueryBound_reindexQuery {D D' A : Type} {R : D → Type} (f : D' → D)
    (program : OracleComp (OracleSpec.ofFn fun q => R (f q)) A) (n : ℕ)
    (bounded : IsTotalQueryBound program n) :
    IsTotalQueryBound (simulateQ (reindexQuery f) program) n := by
  have h := bounded.simulateQ_of_step_le (step := 1) (impl := reindexQuery f)
    (fun q => show IsTotalQueryBound (reindexQuery (R := R) f q) 1 from by
      change IsTotalQueryBound (liftM ((OracleSpec.ofFn R).query (f q)) >>= pure) 1
      exact ⟨by omega, fun _ => trivial⟩)
  simpa only [Nat.mul_one] using h

/-! ### Backward extraction at a key -/

universe w

/-- Reconstruct the pre-challenge extractor using this prefix's strict ancestor responses. -/
def prefixExtractor {Salt : Type} : {protocol : Protocol} → (coin : PublicCoin protocol) →
    {state : KnowledgeState.{w}} → RoundExtractor protocol.tree state →
    (pre : Prefix Salt coin) → PrefixTable Salt coin →
    (before : KnowledgeState.{w}) ×
      RoundExtractor (.public pre.Challenge (fun _ => pre.rest.tree)) before
  | _, .done, _, _, pre, _ => nomatch pre
  | _, @PublicCoin.sender _ _ _ next, _, extractor, ⟨move, pre⟩, table =>
      prefixExtractor (next move) (extractor move).2.2 pre fun q => table ⟨move, q⟩
  | _, @PublicCoin.oracle _ _ _ _ next, _, extractor, ⟨message, pre⟩, table =>
      prefixExtractor next (extractor message).2.2 pre fun q => table ⟨message, q⟩
  | _, @PublicCoin.challenge _ _ _ _ _ _, state, extractor, .inl _, _ => ⟨state, extractor⟩
  | _, @PublicCoin.challenge _ _ _ _ _ next, _, extractor, .inr ⟨salt, pre⟩, table =>
      prefixExtractor next (extractor (table (.inl salt))).2.2 pre
        fun q => table (.inr ⟨salt, q⟩)

/-- Resampling a target prefix leaves its reconstructed pre-challenge extractor unchanged. -/
theorem prefixExtractor_update {Salt : Type} [DecidableEq Salt] {protocol : Protocol}
    (coin : PublicCoin protocol) {state : KnowledgeState.{w}}
    (extractor : RoundExtractor protocol.tree state)
    (pre : Prefix Salt coin) (table : PrefixTable Salt coin) (value : pre.Challenge) :
    prefixExtractor coin extractor pre (Function.update table pre value) =
      prefixExtractor coin extractor pre table := by
  induction coin generalizing state with
  | done => exact pre.elim
  | sender next ih =>
      rcases pre with ⟨move, pre⟩
      simp only [prefixExtractor]
      have htable : (fun q => Function.update table ⟨move, pre⟩ value ⟨move, q⟩) =
          Function.update (fun q => table ⟨move, q⟩) pre value := by
        funext q
        by_cases hq : q = pre
        · subst q
          simp
        · rw [Function.update_of_ne hq, Function.update_of_ne]
          simpa using hq
      rw [htable]
      exact ih move (extractor move).2.2 pre (fun q => table ⟨move, q⟩) value
  | oracle next ih =>
      rcases pre with ⟨message, pre⟩
      simp only [prefixExtractor]
      have htable : (fun q => Function.update table ⟨message, pre⟩ value ⟨message, q⟩) =
          Function.update (fun q => table ⟨message, q⟩) pre value := by
        funext q
        by_cases hq : q = pre
        · subst q
          simp
        · rw [Function.update_of_ne hq, Function.update_of_ne]
          simpa using hq
      rw [htable]
      exact ih (extractor message).2.2 pre (fun q => table ⟨message, q⟩) value
  | challenge next ih =>
      cases pre with
      | inl _ => rfl
      | inr data =>
          rcases data with ⟨salt, pre⟩
          simp only [prefixExtractor]
          have hhere : Function.update table (.inr ⟨salt, pre⟩) value (.inl salt) =
              table (.inl salt) :=
            Function.update_of_ne (by simp) _ _
          rw [hhere]
          have htable : (fun q => Function.update table (.inr ⟨salt, pre⟩) value
                (.inr ⟨salt, q⟩)) =
              Function.update (fun q => table (.inr ⟨salt, q⟩)) pre value := by
            funext q
            by_cases hq : q = pre
            · subst q
              simp
            · rw [Function.update_of_ne hq, Function.update_of_ne]
              simpa using hq
          rw [htable]
          exact ih (extractor (table (.inl salt))).2.2 pre (fun q => table (.inr ⟨salt, q⟩)) value

/-! ### Completion -/

/-- The prover's public moves, oracle payloads and salts along a complete path of the protocol:
an execution path with its challenges erased and a salt at each challenge. -/
@[reducible] def Messages (Salt : Type) {protocol : Protocol} (coin : PublicCoin protocol) :
    Type :=
  PublicCoin.rec (motive := fun _ _ => Type) PUnit
    (fun {Moves} _ _ _ messages => (move : Moves) × messages move)
    (fun {Messages} _ _ _ _ messages => Messages × messages)
    (fun _ messages => Salt × messages) coin

/-- The oracle on the salted prefixes of one protocol. -/
abbrev prefixSpec (Salt : Type) {protocol : Protocol} (coin : PublicCoin protocol) :
    OracleSpec (Prefix Salt coin) :=
  OracleSpec.ofFn Prefix.Challenge

/-- The restoration oracle answers each key with its node's challenge type. -/
abbrev oracleSpec (Input Salt : Type) {protocol : Input → Protocol}
    (coin : (z : Input) → PublicCoin (protocol z)) : OracleSpec (Key Input Salt coin) :=
  OracleSpec.ofFn Key.Challenge

/-- Route a prefix of input `z`'s protocol to its restoration key. -/
abbrev inputQuery {Input Salt : Type} {protocol : Input → Protocol}
    {coin : (z : Input) → PublicCoin (protocol z)} (z : Input) :
    QueryImpl (prefixSpec Salt (coin z)) (OracleComp (oracleSpec Input Salt coin)) :=
  reindexQuery (R := Key.Challenge) (Sigma.mk z)

/-- Complete a message sequence by reading all challenges from the prefix oracle. -/
def completePrefix {Salt : Type} : {protocol : Protocol} → (coin : PublicCoin protocol) →
    Messages Salt coin → OracleComp (prefixSpec Salt coin) protocol.tree.ExecutionPath
  | _, .done, _ => pure PUnit.unit
  | _, @PublicCoin.sender _ _ _ next, ⟨move, messages⟩ => do
      let path ← simulateQ (reindexQuery (R := Prefix.Challenge (coin := .sender next))
        (Sigma.mk move))
        (completePrefix (next move) messages)
      pure ⟨move, path⟩
  | _, @PublicCoin.oracle _ _ _ _ next, ⟨message, messages⟩ => do
      let path ← simulateQ (reindexQuery (R := Prefix.Challenge (coin := .oracle next))
        (Prod.mk message))
        (completePrefix next messages)
      pure ⟨message, path⟩
  | _, @PublicCoin.challenge Challenge _ _ _ _ next, ⟨salt, messages⟩ => do
      let challenge ← liftM ((prefixSpec Salt (@PublicCoin.challenge Challenge _ _ _ _ next)).query
        (Sum.inl salt))
      let path ← simulateQ (reindexQuery
        (R := Prefix.Challenge (coin := @PublicCoin.challenge Challenge _ _ _ _ next))
        (fun q : Prefix Salt next => Sum.inr ⟨salt, q⟩)) (completePrefix next messages)
      pure ⟨challenge, path⟩

/-- Complete the selected transcript by reading all challenges from the same restoration oracle,
at the keys of the selected input. -/
def complete {Input Salt : Type} {protocol : Input → Protocol}
    (coin : (z : Input) → PublicCoin (protocol z)) (z : Input)
    (messages : Messages Salt (coin z)) :
    OracleComp (oracleSpec Input Salt coin) (protocol z).tree.ExecutionPath :=
  simulateQ (inputQuery z) (completePrefix (coin z) messages)

/-- The execution path reconstructed from a deterministic prefix challenge table. -/
def prefixPath {Salt : Type} : {protocol : Protocol} → (coin : PublicCoin protocol) →
    Messages Salt coin → PrefixTable Salt coin → protocol.tree.ExecutionPath
  | _, .done, _, _ => PUnit.unit
  | _, @PublicCoin.sender _ _ _ next, ⟨move, messages⟩, table =>
      ⟨move, prefixPath (next move) messages fun q => table ⟨move, q⟩⟩
  | _, @PublicCoin.oracle _ _ _ _ next, ⟨message, messages⟩, table =>
      ⟨message, prefixPath next messages fun q => table ⟨message, q⟩⟩
  | _, @PublicCoin.challenge _ _ _ _ _ next, ⟨salt, messages⟩, table =>
      ⟨table (.inl salt), prefixPath next messages fun q => table (.inr ⟨salt, q⟩)⟩

/-- The existing execution path reconstructed from a deterministic challenge table. -/
def completedPath {Input Salt : Type} {protocol : Input → Protocol}
    (coin : (z : Input) → PublicCoin (protocol z)) (z : Input)
    (messages : Messages Salt (coin z)) (table : Table Input Salt coin) :
    (protocol z).tree.ExecutionPath :=
  prefixPath (coin z) messages (Table.fibre table z)

/-- The prefixes read when completing this message sequence. -/
def prefixKeys {Salt : Type} : {protocol : Protocol} → (coin : PublicCoin protocol) →
    Messages Salt coin → List (Prefix Salt coin)
  | _, .done, _ => []
  | _, @PublicCoin.sender _ _ _ next, ⟨move, messages⟩ =>
      (prefixKeys (next move) messages).map (Sigma.mk move)
  | _, @PublicCoin.oracle _ _ _ _ next, ⟨message, messages⟩ =>
      (prefixKeys next messages).map (Prod.mk message)
  | _, @PublicCoin.challenge _ _ _ _ _ next, ⟨salt, messages⟩ =>
      .inl salt :: (prefixKeys next messages).map (fun q => .inr ⟨salt, q⟩)

/-- The actual challenge keys read when completing this selected message sequence. -/
def completionKeys {Input Salt : Type} {protocol : Input → Protocol}
    (coin : (z : Input) → PublicCoin (protocol z)) (z : Input)
    (messages : Messages Salt (coin z)) : List (Key Input Salt coin) :=
  (prefixKeys (coin z) messages).map (Sigma.mk z)

/-- Deterministic execution of prefix completion returns exactly the reconstructed path. -/
theorem completePrefix_eval {Salt : Type} {protocol : Protocol} (coin : PublicCoin protocol)
    (messages : Messages Salt coin) (table : PrefixTable Salt coin) :
    evalWithAnswerFn (QueryImpl.ofFn table) (completePrefix coin messages) =
      prefixPath coin messages table := by
  induction coin with
  | done => rfl
  | sender next ih =>
      rcases messages with ⟨move, messages⟩
      simp only [completePrefix, evalWithAnswerFn_bind, evalWithAnswerFn_reindexQuery,
        prefixPath]
      simp only [ih]
      rfl
  | oracle next ih =>
      rcases messages with ⟨message, messages⟩
      simp only [completePrefix, evalWithAnswerFn_bind, evalWithAnswerFn_reindexQuery,
        prefixPath]
      simp only [ih]
      rfl
  | challenge next ih =>
      rcases messages with ⟨salt, messages⟩
      simp only [completePrefix, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query,
        QueryImpl.ofFn_apply, evalWithAnswerFn_reindexQuery, prefixPath]
      simp only [ih]
      rfl

/-- Deterministic execution of completion returns exactly the reconstructed path. -/
theorem complete_eval {Input Salt : Type} {protocol : Input → Protocol}
    (coin : (z : Input) → PublicCoin (protocol z)) (z : Input)
    (messages : Messages Salt (coin z)) (table : Table Input Salt coin) :
    evalWithAnswerFn (QueryImpl.ofFn table) (complete coin z messages) =
      completedPath coin z messages table := by
  rw [complete, evalWithAnswerFn_reindexQuery]
  exact completePrefix_eval (coin z) messages (Table.fibre table z)

/-- The prefix-key list is the projection of the actual prefix-oracle query log. -/
theorem completePrefix_log_keys {Salt : Type} {protocol : Protocol} (coin : PublicCoin protocol)
    (messages : Messages Salt coin) (table : PrefixTable Salt coin) :
    (tableQueryLog (completePrefix coin messages) table).map Sigma.fst =
      prefixKeys coin messages := by
  induction coin with
  | done => simp [completePrefix, prefixKeys]
  | sender next ih =>
      rcases messages with ⟨move, messages⟩
      simp only [completePrefix, tableQueryLog_bind, List.map_append]
      erw [tableQueryLog_pure, tableQueryLog_reindexQuery, ih move messages]
      simp only [List.map_nil, List.append_nil, prefixKeys]
  | oracle next ih =>
      rcases messages with ⟨message, messages⟩
      simp only [completePrefix, tableQueryLog_bind, List.map_append]
      erw [tableQueryLog_pure, tableQueryLog_reindexQuery, ih messages]
      simp only [List.map_nil, List.append_nil, prefixKeys]
  | challenge next ih =>
      rcases messages with ⟨salt, messages⟩
      simp only [completePrefix, tableQueryLog_bind, List.map_append]
      erw [tableQueryLog_pure, tableQueryLog_query, tableQueryLog_reindexQuery, ih messages]
      simp only [List.map_nil, List.append_nil, prefixKeys, List.map_cons, List.singleton_append]

/-- The completion-key list is the projection of the actual oracle query log. -/
theorem complete_log_keys {Input Salt : Type} {protocol : Input → Protocol}
    (coin : (z : Input) → PublicCoin (protocol z)) (z : Input)
    (messages : Messages Salt (coin z)) (table : Table Input Salt coin) :
    (tableQueryLog (complete coin z messages) table).map Sigma.fst =
      completionKeys coin z messages := by
  rw [complete, tableQueryLog_reindexQuery, completionKeys,
    completePrefix_log_keys (coin z) messages (Table.fibre table z)]

/-- A bad challenge on the reconstructed path is a bad prefix in its actual completion log. -/
theorem badChallengeOnPath_prefixPath {Salt : Type} {protocol : Protocol}
    (coin : PublicCoin protocol) {state : KnowledgeState.{w}}
    (extractor : RoundExtractor protocol.tree state)
    (messages : Messages Salt coin) (table : PrefixTable Salt coin)
    (witness : (extractor.terminalState (prefixPath coin messages table)).Witness)
    (bad : extractor.BadChallengeOnPath protocol.roles (prefixPath coin messages table) witness) :
    ∃ pre ∈ prefixKeys coin messages,
      RoundExtractor.badChallenge (prefixExtractor coin extractor pre table).2 (table pre) := by
  induction coin generalizing state with
  | done => exact bad.elim
  | sender next ih =>
      rcases messages with ⟨move, messages⟩
      rcases bad with bad | bad
      · exact absurd bad.1 (by simp [Protocol.public])
      · obtain ⟨pre, hpre, hb⟩ := ih move (extractor move).2.2 messages _ witness bad
        exact ⟨⟨move, pre⟩, List.mem_map.mpr ⟨pre, hpre, rfl⟩, hb⟩
  | oracle next ih =>
      rcases messages with ⟨message, messages⟩
      obtain ⟨pre, hpre, hb⟩ := ih (extractor message).2.2 messages _ witness bad
      exact ⟨⟨message, pre⟩, List.mem_map.mpr ⟨pre, hpre, rfl⟩, hb⟩
  | challenge next ih =>
      rcases messages with ⟨salt, messages⟩
      rcases bad with bad | bad
      · exact ⟨.inl salt, List.mem_cons_self, _, bad.2.1, bad.2.2⟩
      · obtain ⟨pre, hpre, hb⟩ := ih (extractor (table (.inl salt))).2.2 messages _ witness bad
        exact ⟨.inr ⟨salt, pre⟩, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨pre, hpre, rfl⟩), hb⟩

/-- An adversary's selection: an input, a complete message sequence for that input's protocol,
and a terminal witness. -/
abbrev Selection (Input Salt W : Type) {protocol : Input → Protocol}
    (coin : (z : Input) → PublicCoin (protocol z)) :=
  (z : Input) × Messages Salt (coin z) × W

/-- A completed selection: an input, an execution path of that input's protocol, and a terminal
witness. -/
abbrev Outcome (Input W : Type) (protocol : Input → Protocol) :=
  (z : Input) × (protocol z).tree.ExecutionPath × W

/-- Run the adaptive adversary, then complete its selected transcript using the same oracle. -/
def restoredExecution {Input Salt W : Type} {protocol : Input → Protocol}
    (coin : (z : Input) → PublicCoin (protocol z))
    (adversary : OracleComp (oracleSpec Input Salt coin) (Selection Input Salt W coin)) :
    OracleComp (oracleSpec Input Salt coin) (Outcome Input W protocol) := do
  let ⟨z, messages, witness⟩ ← adversary
  let path ← complete coin z messages
  pure ⟨z, path, witness⟩

/-- A permitted-input key at which some later witness fails backward knowledge preservation. -/
def badKey {Input Salt : Type} {protocol : Input → Protocol}
    {coin : (z : Input) → PublicCoin (protocol z)}
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol z).tree (state z))
    (Z : Set Input) (key : Key Input Salt coin) (table : Table Input Salt coin) : Prop :=
  key.1 ∈ Z ∧ RoundExtractor.badChallenge
    (prefixExtractor (coin key.1) (extractor key.1) key.2 (Table.fibre table key.1)).2 (table key)

/-- Resampling a key leaves its event a function of the fresh response alone. -/
theorem badKey_update_iff {Input Salt : Type} {protocol : Input → Protocol}
    {coin : (z : Input) → PublicCoin (protocol z)} [DecidableEq Input] [DecidableEq Salt]
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol z).tree (state z))
    (Z : Set Input) (key : Key Input Salt coin) (table : Table Input Salt coin)
    (response : key.Challenge) :
    badKey state extractor Z key (Function.update table key response) ↔
      key.1 ∈ Z ∧ RoundExtractor.badChallenge
        (prefixExtractor (coin key.1) (extractor key.1) key.2 (Table.fibre table key.1)).2
          response := by
  rcases key with ⟨z, pre⟩
  unfold badKey
  rw [Table.fibre_update, prefixExtractor_update, Function.update_self]

/-- A valid terminal witness whose backward extraction fails on the completed path of input `z`
identifies a bad key among that completion's keys. -/
theorem badKey_of_completedPath {Input Salt W : Type} {protocol : Input → Protocol}
    {coin : (z : Input) → PublicCoin (protocol z)}
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol z).tree (state z))
    (Z : Set Input)
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol z).roles)
    (terminalWitness : (z : Input) → (path : (protocol z).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (z : Input) (messages : Messages Salt (coin z)) (witness : W)
    (table : Table Input Salt coin)
    (hz : z ∈ Z)
    (holds : ((extractor z).terminalState (completedPath coin z messages table)).holds
      (terminalWitness z (completedPath coin z messages table) witness))
    (fails : ¬ (state z).holds ((extractor z).extractWitness
      (completedPath coin z messages table)
      (terminalWitness z (completedPath coin z messages table) witness))) :
    ∃ key ∈ completionKeys coin z messages, badKey state extractor Z key table := by
  have hbad := RoundExtractor.extraction_failure_implies_bad_challenge (extractor z)
    (protocol z).roles (preserving z hz) _ _ holds fails
  obtain ⟨pre, hpre, hb⟩ :=
    badChallengeOnPath_prefixPath (coin z) (extractor z) messages (Table.fibre table z) _ hbad
  exact ⟨⟨z, pre⟩, List.mem_map.mpr ⟨pre, hpre, rfl⟩, hz, hb⟩

/-- Failed backward extraction from terminal knowledge identifies an actually accessed bad key. -/
theorem restored_bad_trace {Input Salt W : Type} {protocol : Input → Protocol}
    {coin : (z : Input) → PublicCoin (protocol z)}
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol z).tree (state z))
    (Z : Set Input)
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol z).roles)
    (terminalWitness : (z : Input) → (path : (protocol z).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (adversary : OracleComp (oracleSpec Input Salt coin) (Selection Input Salt W coin))
    (table : Table Input Salt coin)
    (bad : let result :=
        evalWithAnswerFn (QueryImpl.ofFn table) (restoredExecution coin adversary)
      result.1 ∈ Z ∧
      ((extractor result.1).terminalState result.2.1).holds
        (terminalWitness result.1 result.2.1 result.2.2) ∧
      ¬ (state result.1).holds ((extractor result.1).extractWitness result.2.1
        (terminalWitness result.1 result.2.1 result.2.2))) :
    ∃ q ∈ tableQueryLog (restoredExecution coin adversary) table,
      badKey state extractor Z q.1 table := by
  let result := evalWithAnswerFn (QueryImpl.ofFn table) adversary
  rcases hresult : result with ⟨z, messages, witness⟩
  have heval : evalWithAnswerFn (QueryImpl.ofFn table) (restoredExecution coin adversary) =
      ⟨z, completedPath coin z messages table, witness⟩ := by
    simp only [restoredExecution, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
    change (⟨result.1,
      evalWithAnswerFn (QueryImpl.ofFn table) (complete coin result.1 result.2.1),
        result.2.2⟩ : Outcome Input W protocol) = _
    rw [hresult, complete_eval]
  dsimp only at bad
  rw [heval] at bad
  obtain ⟨key, hkey, hb⟩ := badKey_of_completedPath state extractor Z preserving
    terminalWitness z messages witness table bad.1 bad.2.1 bad.2.2
  have hmem : key ∈ (tableQueryLog (complete coin z messages) table).map Sigma.fst := by
    rwa [complete_log_keys]
  obtain ⟨q, hq, heq⟩ := List.mem_map.mp hmem
  refine ⟨q, ?_, heq ▸ hb⟩
  simp only [restoredExecution, tableQueryLog_bind]
  apply List.mem_append_right
  change q ∈ tableQueryLog (complete coin result.1 result.2.1) table ++ _
  rw [hresult]
  exact List.mem_append_left _ hq

end Interaction.Oracle.Security.StateRestoration
