/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.EncodedChallenges

/-!
# Stopped completion against the external encoded-domain oracle

The external adversary and stopped verifier execute in one oracle program. Every verifier
challenge at native key `key` queries the external oracle at `encode key` and maps the common
challenge back to that key's native challenge type. Thus both phases use one external cache.
-/

@[expose] public section

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec
open Interaction.Oracle.TypeTree

namespace Interaction.Oracle.Security.StateRestoration

variable {Input Salt C D W : Type} {protocol : Input → Protocol} {coin : (z : Input) → PublicCoin (protocol z)}

/-- The actual external verifier challenge call at an encoded native key. -/
def encodedCompletionQueries
    (common : CommonChallenge Input Salt C coin)
    (codec : StrictCodec (Key Input Salt coin) D) :
    QueryImpl (oracleSpec Input Salt coin)
      (OracleComp (unifSpec + (D →ₒ C))) :=
  fun key => (common.challengeEquiv key).symm <$>
    liftM ((unifSpec + (D →ₒ C)).query (.inr (codec.encode key)))

/-- Mapping a returned value leaves the routed external writer and off-image cache intact. -/
theorem StrictCodec.routeProgram_map
    (codec : StrictCodec (Key Input Salt coin) D)
    [DecidableEq D] [SampleableType C]
    {A B : Type} (f : A → B)
    (program : OracleComp (unifSpec + (D →ₒ C)) A)
    (off : (D →ₒ C).QueryCache) :
    codec.routeProgram (f <$> program) off =
      (fun result => ((f result.1.1, result.1.2), result.2)) <$>
        codec.routeProgram program off := by
  simp [StrictCodec.routeProgram, simulateQ_map, WriterT.run_map, StateT.run_map]

/-- One verifier image query routes to the corresponding common-carrier native hash key,
with no change to the off-image cache. -/
theorem encodedCompletionQuery_route
    (common : CommonChallenge Input Salt C coin)
    (codec : StrictCodec (Key Input Salt coin) D)
    [DecidableEq D] [SampleableType C]
    (key : Key Input Salt coin) (off : (D →ₒ C).QueryCache) :
    codec.routeProgram ((encodedCompletionQueries common codec) key) off =
      (fun answer => (((common.challengeEquiv key).symm answer,
        [⟨codec.encode key, answer⟩]), off)) <$>
        liftM ((unifSpec + (Key Input Salt coin →ₒ C)).query (.inr key)) := by
  rw [encodedCompletionQueries, codec.routeProgram_map]
  simp [StrictCodec.routeProgram, StrictCodec.encodedQueryImpl,
    codec.decode_encode, Functor.map_map]

/-- Native challenge queries interpreted through the common-carrier key oracle. -/
def commonCompletionQueries
    (common : CommonChallenge Input Salt C coin) :
    QueryImpl (oracleSpec Input Salt coin)
      (OracleComp (unifSpec + (Key Input Salt coin →ₒ C))) :=
  fun key => (common.challengeEquiv key).symm <$>
    liftM ((unifSpec + (Key Input Salt coin →ₒ C)).query (.inr key))

/-- Encode an ordered native completion log as the corresponding external hash calls. -/
def encodeCompletionLog
    (common : CommonChallenge Input Salt C coin)
    (codec : StrictCodec (Key Input Salt coin) D)
    (log : QueryLog (oracleSpec Input Salt coin)) : QueryLog (D →ₒ C) :=
  log.map fun entry => ⟨codec.encode entry.1, (common.challengeEquiv entry.1).toFun entry.2⟩

@[simp] theorem encodeCompletionLog_nil
    (common : CommonChallenge Input Salt C coin)
    (codec : StrictCodec (Key Input Salt coin) D) :
    encodeCompletionLog common codec [] = [] := rfl

@[simp] theorem encodeCompletionLog_append
    (common : CommonChallenge Input Salt C coin)
    (codec : StrictCodec (Key Input Salt coin) D)
    (first second : QueryLog (oracleSpec Input Salt coin)) :
    encodeCompletionLog common codec (first ++ second) =
      encodeCompletionLog common codec first ++ encodeCompletionLog common codec second := by
  simp [encodeCompletionLog]

/-- The entire stopped completion query program cancels through the strict codec. The external
writer contains exactly its encoded native challenge calls, and off-image cache stays unchanged. -/
theorem encodedCompletion_routeProgram
    (common : CommonChallenge Input Salt C coin)
    (codec : StrictCodec (Key Input Salt coin) D)
    [DecidableEq D] [SampleableType C]
    {A : Type} (program : OracleComp (oracleSpec Input Salt coin) A)
    (off : (D →ₒ C).QueryCache) :
    codec.routeProgram
      (simulateQ (encodedCompletionQueries common codec) program) off =
      (fun result => ((result.1, encodeCompletionLog common codec result.2), off)) <$>
        simulateQ (commonCompletionQueries common) program.withQueryLog := by
  induction program using OracleComp.inductionOn generalizing off with
  | pure value =>
      simp [StrictCodec.routeProgram, encodeCompletionLog]
  | query_bind key next ih =>
      rw [simulateQ_query_bind]
      rw [codec.routeProgram_bind]
      simp only [OracleQuery.input_query, OracleQuery.cont_query]
      change (codec.routeProgram ((encodedCompletionQueries common codec) key) off >>= _) = _
      rw [encodedCompletionQuery_route]
      rw [OracleComp.withQueryLog_bind, OracleComp.withQueryLog_query]
      simp only [simulateQ_bind, simulateQ_map, simulateQ_spec_query,
        commonCompletionQueries,
        bind_map_left, map_bind, bind_assoc, pure_bind, Functor.map_map]
      apply bind_congr
      intro answer
      simp only [id_eq]
      rw [ih ((common.challengeEquiv key).symm answer) off]
      simp only [Functor.map_map]
      congr 1
      funext result
      simp [encodeCompletionLog]

/-- The common-carrier translation and native challenge translation cancel on one verifier query. -/
theorem commonCompletionQuery_native
    (common : CommonChallenge Input Salt C coin)
    (key : Key Input Salt coin) :
    common.simulateNative ((commonCompletionQueries common) key) =
      (restorationQueries Input Salt coin) key := by
  simp [CommonChallenge.simulateNative, commonCompletionQueries,
    CommonChallenge.commonQueryImpl, restorationQueries]

/-- The translations cancel for an entire adaptive native challenge program. -/
theorem commonCompletion_native
    (common : CommonChallenge Input Salt C coin)
    {A : Type} (program : OracleComp (oracleSpec Input Salt coin) A) :
    common.simulateNative
      (simulateQ (commonCompletionQueries common) program) =
      simulateQ (restorationQueries Input Salt coin) program := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind key next ih =>
      simp only [CommonChallenge.simulateNative, simulateQ_bind]
      simp only [simulateQ_spec_query]
      change common.simulateNative ((commonCompletionQueries common) key) >>=
          (fun x => common.simulateNative
            (simulateQ (commonCompletionQueries common) (next x))) =
        (restorationQueries Input Salt coin) key >>=
          (fun x => simulateQ (restorationQueries Input Salt coin) (next x))
      rw [commonCompletionQuery_native]
      apply bind_congr
      intro answer
      exact ih answer

/-- Erasing the completion source log after the common/native round trip recovers the actual
native completion program exactly. -/
theorem commonCompletion_native_eraseLog
    (common : CommonChallenge Input Salt C coin)
    {A : Type} (program : OracleComp (oracleSpec Input Salt coin) A) :
    Prod.fst <$> common.simulateNative
      (simulateQ (commonCompletionQueries common) program.withQueryLog) =
        simulateQ (restorationQueries Input Salt coin) program := by
  calc
    _ = common.simulateNative
        (simulateQ (commonCompletionQueries common)
          (Prod.fst <$> program.withQueryLog)) := by
            simp [CommonChallenge.simulateNative, simulateQ_map]
    _ = common.simulateNative
        (simulateQ (commonCompletionQueries common) program) := by
          exact congrArg (fun p => common.simulateNative
            (simulateQ (commonCompletionQueries common) p))
            (loggingOracle.fst_map_run_simulateQ program)
    _ = _ := commonCompletion_native common program

/-- Reduction of an external encoded-domain adversary to the genuine dependent native oracle.
Off-image queries are sampled and memoized privately; image queries touch the native cache. -/
def encodedNativeAdversary
    (common : CommonChallenge Input Salt C coin)
    (codec : StrictCodec (Key Input Salt coin) D)
    [DecidableEq D] [SampleableType C]
    (external : OracleComp (unifSpec + (D →ₒ C))
      (Option (Selection Input Salt W coin))) :
    RandomizedRestorationAdversary Input Salt W coin :=
  (fun result => result.1.1) <$>
    common.simulateNative (codec.routeProgram external ∅)

/-- Complete a native selected transcript, retaining the selected witness but no source log. -/
def nativeStoppedCompletionAfter (coin : (z : Input) → PublicCoin (protocol z))
    (guards : (z : Input) → GuardSchedule Salt (coin z))
    (selected : Option (Selection Input Salt W coin)) :
    OracleComp (unifSpec + oracleSpec Input Salt coin)
      (Option (Outcome Input W protocol)) :=
  match selected with
  | none => pure none
  | some ⟨z, messages, witness⟩ =>
      (fun path => path.map (fun p => ⟨z, p, witness⟩)) <$>
        simulateQ (restorationQueries Input Salt coin)
          (stoppedComplete coin guards z messages)

/-- The same stopped native verifier without the auxiliary adversary source log. -/
def nativeStoppedExecution (coin : (z : Input) → PublicCoin (protocol z))
    (guards : (z : Input) → GuardSchedule Salt (coin z))
    (adversary : RandomizedRestorationAdversary Input Salt W coin) :
    OracleComp (unifSpec + oracleSpec Input Salt coin)
      (Option (Outcome Input W protocol)) :=
  adversary >>= nativeStoppedCompletionAfter coin guards

/-- Erasing the returned source log from the established stopped joint program recovers the
unlogged native stopped execution without changing any oracle effect. -/
theorem randomizedStoppedExecution_eraseSourceLog
    (coin : (z : Input) → PublicCoin (protocol z))
    (guards : (z : Input) → GuardSchedule Salt (coin z))
    (adversary : RandomizedRestorationAdversary Input Salt W coin) :
    Prod.fst <$>
      randomizedStoppedRestoredExecutionWithAdversaryLog coin guards adversary =
      nativeStoppedExecution coin guards adversary := by
  have herase : Prod.fst <$> adversary.withQueryLog = adversary :=
    loggingOracle.fst_map_run_simulateQ adversary
  calc
    _ = (Prod.fst <$> adversary.withQueryLog) >>=
          nativeStoppedCompletionAfter coin guards := by
      simp only [randomizedStoppedRestoredExecutionWithAdversaryLog,
        randomizedStoppedCompletionAfterAdversaryLog,
        nativeStoppedCompletionAfter, map_bind, bind_map_left]
      apply bind_congr
      intro phase
      rcases phase with ⟨selection, sourceLog⟩
      cases selection with
      | none => rfl
      | some selected =>
          rcases selected with ⟨z, messages, witness⟩
          simp
    _ = adversary >>= nativeStoppedCompletionAfter coin guards := by rw [herase]
    _ = _ := rfl

/-- Complete one selected transcript by querying only the encoded image of native keys. -/
def encodedExternalCompletionAfter (coin : (z : Input) → PublicCoin (protocol z))
    (common : CommonChallenge Input Salt C coin)
    (codec : StrictCodec (Key Input Salt coin) D)
    (guards : (z : Input) → GuardSchedule Salt (coin z))
    (selected : Option (Selection Input Salt W coin)) :
    OracleComp (unifSpec + (D →ₒ C))
      (Option (Outcome Input W protocol)) :=
  match selected with
  | none => pure none
  | some ⟨z, messages, witness⟩ =>
      (fun path => path.map (fun p => ⟨z, p, witness⟩)) <$>
        simulateQ (encodedCompletionQueries common codec)
          (stoppedComplete coin guards z messages)

/-- One external encoded-domain run: arbitrary adversary calls, then stopped completion on the
selected messages. Rejection and adversary failure retain their already executed oracle effects. -/
def encodedExternalStoppedExecution (coin : (z : Input) → PublicCoin (protocol z))
    (common : CommonChallenge Input Salt C coin)
    (codec : StrictCodec (Key Input Salt coin) D)
    (guards : (z : Input) → GuardSchedule Salt (coin z))
    (external : OracleComp (unifSpec + (D →ₒ C))
      (Option (Selection Input Salt W coin))) :
    OracleComp (unifSpec + (D →ₒ C))
      (Option (Outcome Input W protocol)) :=
  external >>= encodedExternalCompletionAfter coin common codec guards


/-- Erasing the routed external writer after a bind still threads its off-image cache through
both phases; the selected result is the second phase's result. -/
theorem encodedRoute_nativeValue_bind
    (common : CommonChallenge Input Salt C coin)
    (codec : StrictCodec (Key Input Salt coin) D)
    [DecidableEq D] [SampleableType C]
    {A B : Type} (program : OracleComp (unifSpec + (D →ₒ C)) A)
    (next : A → OracleComp (unifSpec + (D →ₒ C)) B)
    (off : (D →ₒ C).QueryCache) :
    (fun result => result.1.1) <$>
      common.simulateNative (codec.routeProgram (program >>= next) off) =
    common.simulateNative (codec.routeProgram program off) >>= fun first =>
      (fun result => result.1.1) <$>
        common.simulateNative (codec.routeProgram (next first.1.1) first.2) := by
  rw [codec.routeProgram_bind]
  simp only [CommonChallenge.simulateNative, simulateQ_bind, simulateQ_map,
    map_bind, Functor.map_map]

/-- The external completion branch has exactly the native stopped result after decoding its
image hash queries. This is program equality, including rejection and already sampled coins. -/
theorem encodedExternalCompletion_route_value (coin : (z : Input) → PublicCoin (protocol z))
    (common : CommonChallenge Input Salt C coin)
    (codec : StrictCodec (Key Input Salt coin) D)
    [DecidableEq D] [SampleableType C]
    (guards : (z : Input) → GuardSchedule Salt (coin z))
    (selected : Option (Selection Input Salt W coin))
    (off : (D →ₒ C).QueryCache) :
    (fun result => result.1.1) <$>
      common.simulateNative
        (codec.routeProgram
          (encodedExternalCompletionAfter coin common codec guards selected) off) =
      nativeStoppedCompletionAfter coin guards selected := by
  cases selected with
  | none =>
      simp [encodedExternalCompletionAfter, nativeStoppedCompletionAfter,
        StrictCodec.routeProgram, CommonChallenge.simulateNative]
  | some selected =>
      rcases selected with ⟨z, messages, witness⟩
      simp only [encodedExternalCompletionAfter, nativeStoppedCompletionAfter]
      rw [codec.routeProgram_map, encodedCompletion_routeProgram]
      simp only [CommonChallenge.simulateNative, simulateQ_map, Functor.map_map]
      simpa only [CommonChallenge.simulateNative, Functor.map_map,
        Function.comp_def] using (congrArg (fun program =>
        (fun path => path.map (fun p => (⟨z, p, witness⟩ : Outcome Input W protocol))) <$> program)
        (commonCompletion_native_eraseLog common
          (stoppedComplete coin guards z messages)))


/-- The *actual external* adversary and stopped verifier, sharing one encoded-domain cache,
have the same selected output as the translated native stopped game. This is a source-program
equality, not a postulated game correspondence. The full external log/cache remain available
from `StrictCodec.routedLoggedRun_eq_randomOracleLoggedRun`. -/
theorem encodedExternalStopped_route_nativeValue (coin : (z : Input) → PublicCoin (protocol z))
    (common : CommonChallenge Input Salt C coin)
    (codec : StrictCodec (Key Input Salt coin) D)
    [DecidableEq D] [SampleableType C]
    (guards : (z : Input) → GuardSchedule Salt (coin z))
    (external : OracleComp (unifSpec + (D →ₒ C))
      (Option (Selection Input Salt W coin))) :
    (fun result => result.1.1) <$>
      common.simulateNative
        (codec.routeProgram
          (encodedExternalStoppedExecution coin common codec guards external) ∅) =
      nativeStoppedExecution coin guards
        (encodedNativeAdversary common codec external) := by
  rw [encodedExternalStoppedExecution, encodedRoute_nativeValue_bind]
  simp only [encodedExternalCompletion_route_value,
    nativeStoppedExecution, encodedNativeAdversary, bind_map_left]

end Interaction.Oracle.Security.StateRestoration
