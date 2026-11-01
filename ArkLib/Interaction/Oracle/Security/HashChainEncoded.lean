/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.Interaction.Oracle.Security.HashChain
public import ArkLib.Interaction.Oracle.Security.EncodedSecurityEvent
public import ArkLib.Interaction.Oracle.Security.DecodedChallenges

/-!
# Fiat–Shamir with a hash chain

A Fiat–Shamir verifier on a hash chain (`HashChain.chainSpec S I O`) derives each challenge by
absorbing the challenge's erased prefix, encoded as a nonempty list of chain inputs, from the
initial state `s₀` (`HashChain.absorb`), and reads the challenge off the answer through the common
challenge carrier `S × O` (`CommonChallenge`). The encoding (`ChainCodec`) is any injective map of
restoration keys to nonempty input lists: the inputs absorbed for a key need not extend those of
its predecessor.

`HashChain.chainStopped_knowledge_soundness` bounds the probability that the verifier completes a
path with a valid terminal witness whose backward extraction fails, for an adversary on the chain,
by the collision-or-prediction error of the chain plus the encoded random oracle's bound
(`encodedExternalStopped_extraction_le_adversaryCount`):
`chainError S q + (maxError errors * q + sumError errors)`, `q` the chain queries of the adversary
and the verifier together. The chain answers coins, a state and an output, and a protocol's
challenges are drawn from them (`DecodedChallenges.lean`), after a prover witness and with a check
on the coins such as a proof of work: `KnowledgeCertificate.chainStopped_knowledge_soundness`
applies the bound to the decoded presentation of a protocol with a knowledge certificate,
`chainError S q` plus the certificate's `maxError * q + sumError` with every node's error
multiplied by its draw's ratio. A grinding draw's ratio carries its proof-of-work pass probability,
so grinding at a node divides that node's error, in both terms, by about `2 ^ bits`.

## Proof

The adversary is extended by the verifier's own completion (`chainAdversary`), so that the game
is the extended adversary's run, read off its output. The verifier's completion, run on a cache,
returns the same value when replayed from the final cache (`replay_of_mem_support_run`), so the
game's event is an event of the extended adversary's output and final chain cache. By
`HashChain.dominatedUntilBad`, that event is at most the same event read through the simulator's
`view`, plus `chainError S q`. Off a collision, replaying the completion through `view` is
replaying the encoded completion on the prefix oracle's cache (`replay_view_absorb`); and a
replay from a cache is the run from that cache (`run_of_replay`). The simulated extended adversary,
with the empty extra oracles dropped (`dropEmpty`), is the external adversary of the encoded
random-oracle theorem.
-/

@[expose] public section

open OracleComp OracleSpec Interaction.Oracle Interaction.Oracle.Security.StateRestoration
open MeasureTheory
open scoped ENNReal

namespace Interaction.Oracle.Security.HashChain

/-! ### Replaying a program from a cache -/

section Replay

variable {ι : Type} {hs : OracleSpec ι}

/-- Answer every oracle query from a cache: no answer on a miss or a private coin. -/
def cacheAnswers (c : hs.QueryCache) : QueryImpl (unifSpec + hs) Option
  | .inl _ => none
  | .inr t => c t

/-- A program's result with every oracle query answered by a cache, if the cache answers them
all and the program draws no private coin. -/
def replay (c : hs.QueryCache) {α : Type} (P : OracleComp (unifSpec + hs) α) : Option α :=
  simulateQ (cacheAnswers c) P

@[simp] theorem replay_pure (c : hs.QueryCache) {α : Type} (a : α) :
    replay c (pure a : OracleComp (unifSpec + hs) α) = some a := by
  simp [replay]

theorem replay_query_bind (c : hs.QueryCache) {α : Type} (t : (unifSpec + hs).Domain)
    (k : (unifSpec + hs).Range t → OracleComp (unifSpec + hs) α) :
    replay c (liftM ((unifSpec + hs).query t) >>= k) =
      cacheAnswers c t >>= fun u => replay c (k u) := by
  simp [replay]

theorem replay_bind (c : hs.QueryCache) {α β : Type} (P : OracleComp (unifSpec + hs) α)
    (k : α → OracleComp (unifSpec + hs) β) :
    replay c (P >>= k) = replay c P >>= fun a => replay c (k a) := by
  simp [replay]

theorem replay_map (c : hs.QueryCache) {α β : Type} (P : OracleComp (unifSpec + hs) α)
    (f : α → β) : replay c (f <$> P) = f <$> replay c P := by
  simp [replay]

/-- Whether a query is a private coin. -/
def isUnif {κ : Type} : ℕ ⊕ κ → Bool
  | .inl _ => true
  | .inr _ => false

variable [DecidableEq ι] [∀ t, SampleableType (hs.Range t)]

/-- A random-oracle step only adds to the cache. -/
theorem romImpl_step_le (q : (unifSpec + hs).Domain) (c : hs.QueryCache)
    (z : (unifSpec + hs).Range q × hs.QueryCache) (hz : z ∈ support ((hs.romImpl q).run c))
    (t : ι) (u : hs.Range t) (ht : c t = some u) : z.2 t = some u := by
  rcases q with n | x
  · rw [romImpl_run_unif, support_map] at hz
    obtain ⟨_, -, rfl⟩ := hz
    exact ht
  · cases hx : c x with
    | some v =>
      rw [romImpl_run_of_some hx, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
      exact ht
    | none =>
      rw [romImpl_run_of_none hx, support_map] at hz
      obtain ⟨v, -, rfl⟩ := hz
      have htx : t ≠ x := fun h => by subst h; rw [hx] at ht; cases ht
      rw [QueryCache.cacheQuery_of_ne _ _ htx]
      exact ht

/-- A random-oracle step caches its answer. -/
theorem romImpl_step_inr (x : ι) (c : hs.QueryCache) (z : hs.Range x × hs.QueryCache)
    (hz : z ∈ support ((hs.romImpl (.inr x)).run c)) : z.2 x = some z.1 := by
  cases hx : c x with
  | some v =>
    rw [romImpl_run_of_some hx, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    exact hx
  | none =>
    rw [romImpl_run_of_none hx, support_map] at hz
    obtain ⟨v, -, rfl⟩ := hz
    simp

/-- A random-oracle run only adds to its cache. -/
theorem cache_le_of_mem_support_run {α : Type} (P : OracleComp (unifSpec + hs) α)
    (c : hs.QueryCache) (z : α × hs.QueryCache)
    (hz : z ∈ support ((simulateQ hs.romImpl P).run c)) (t : ι) (u : hs.Range t)
    (ht : c t = some u) : z.2 t = some u := by
  induction P using OracleComp.inductionOn generalizing c with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    exact ht
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at hz
    obtain ⟨w, hw, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    exact ih w.1 w.2 hz (romImpl_step_le q c w hw t u ht)

/-- **Replaying a run.** A program drawing no private coin, run on a random oracle from any
cache, returns what its replay from the final cache returns. -/
theorem replay_of_mem_support_run {α : Type} (P : OracleComp (unifSpec + hs) α)
    (hP : IsQueryBoundP P (fun t => isUnif t = true) 0) (c : hs.QueryCache)
    (z : α × hs.QueryCache) (hz : z ∈ support ((simulateQ hs.romImpl P).run c)) :
    replay z.2 P = some z.1 := by
  induction P using OracleComp.inductionOn generalizing c with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    simp [hz]
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at hP
    rcases q with n | x
    · simp [isUnif] at hP
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at hz
    obtain ⟨w, hw, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    have hk := ih w.1 (hP.2 w.1) w.2 hz
    rw [replay_query_bind]
    change z.2 x >>= (fun u => replay z.2 (k u)) = _
    rw [cache_le_of_mem_support_run (k w.1) w.2 z hz x w.1 (romImpl_step_inr x c w hw)]
    exact hk

/-- **A replay is a run.** A program whose replay from a cache succeeds runs on a random oracle
from that cache to the replayed result, the cache unchanged. -/
theorem run_of_replay {α : Type} (P : OracleComp (unifSpec + hs) α) (c : hs.QueryCache) (a : α)
    (h : replay c P = some a) : (simulateQ hs.romImpl P).run c = pure (a, c) := by
  induction P using OracleComp.inductionOn with
  | pure b =>
    simp only [replay_pure, Option.some.injEq] at h
    simp [h]
  | query_bind q k ih =>
    rw [replay_query_bind] at h
    rcases q with n | x
    · simp [cacheAnswers] at h
    · cases hx : c x with
      | none => simp [cacheAnswers, hx] at h
      | some u =>
        simp only [cacheAnswers, hx] at h
        change replay c (k u) = some a at h
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
        rw [romImpl_run_of_some hx, pure_bind]
        exact ih u h

end Replay

/-! ### Absorbing a prefix -/

section Absorb

variable {S I O : Type} {ι : Type} {extra : OracleSpec ι}

/-- Absorb the inputs `x :: p`, latest first, through the chain from the initial state `s₀`: the
chain's answer at the query of `x`, made at the state answered to `p`. -/
def absorb (s₀ : S) : I → List I → OracleComp (unifSpec + (chainSpec S I O + extra)) (S × O)
  | x, [] => liftM ((unifSpec + (chainSpec S I O + extra)).query (.inr (.inl (s₀, x))))
  | x, y :: p => do
      let v ← absorb s₀ y p
      liftM ((unifSpec + (chainSpec S I O + extra)).query (.inr (.inl (v.1, x))))

/-- Absorbing makes chain queries only. -/
theorem isQueryBoundP_absorb (s₀ : S) (x : I) (p : List I) :
    IsQueryBoundP (absorb (O := O) (extra := extra) s₀ x p) (fun t => isUnif t = true) 0 := by
  induction p generalizing x with
  | nil => exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [isUnif])
  | cons y p ih =>
    rw [absorb]
    exact isQueryBoundP_bind (n := 0) (m := 0) (ih y) fun v _ =>
      (isQueryBoundP_query_iff _ (Sum.inr (Sum.inl (v.1, x))) 0).mpr (by simp [isUnif])

variable [DecidableEq S] [DecidableEq I]

/-- **Absorbing off a collision reads the prefix oracle.** Off a collision or prediction,
absorbing `x :: p` through the chain cache that a simulated run stands for (`view`) answers the
prefix oracle's cached answer at `x :: p`. -/
theorem replay_view_absorb (s₀ : S) {σ : IdealState S I O extra} (hI : Inv σ)
    (hG : Good s₀ σ.1) (x : I) (p : List I) (v : S × O)
    (h : replay (view s₀ σ) (absorb s₀ x p) = some v) : σ.2 (.inl (x :: p)) = some v := by
  induction p generalizing x v with
  | nil =>
    rw [← view_encode hI hG (k := [x]) (q := (s₀, x)) rfl]
    simpa [absorb, replay, cacheAnswers] using h
  | cons y p ih =>
    rw [absorb, replay_bind] at h
    cases hv' : replay (view s₀ σ) (absorb s₀ y p) with
    | none => rw [hv'] at h; cases h
    | some v' =>
    rw [hv'] at h
    change replay (view s₀ σ) (liftM ((unifSpec + (chainSpec S I O + extra)).query
      (.inr (.inl (v'.1, x))))) = some v at h
    have hp := ih y v' hv'
    have hkey : chainKey s₀ σ.1.prefixes (x :: y :: p) = some (v'.1, x) := by
      simp [chainKey, stateOf, ← hI.cache, hp]
    rw [← view_encode hI hG hkey]
    simpa [replay, cacheAnswers] using h

end Absorb

/-! ### Dropping the empty extra oracles -/

section Drop

variable {S I O : Type} [DecidableEq I] [SampleableType S] [SampleableType O]

instance : ∀ t : PEmpty, SampleableType (([]ₒ : OracleSpec PEmpty).Range t) := fun t => t.elim

/-- Prefix queries pass to the prefix oracle alone; there are no extra oracles to query. -/
def dropEmpty : QueryImpl (unifSpec + (prefixSpec S I O + []ₒ))
    (OracleComp (unifSpec + prefixSpec S I O))
  | .inl n => liftM ((unifSpec + prefixSpec S I O).query (.inl n))
  | .inr (.inl p) => liftM ((unifSpec + prefixSpec S I O).query (.inr p))
  | .inr (.inr e) => e.elim

/-- The prefix oracle's part of a cache. -/
def dropCache (c : (prefixSpec S I O + []ₒ).QueryCache) : (prefixSpec S I O).QueryCache :=
  QueryCache.ofFn fun p => c (.inl p)

omit [DecidableEq I] [SampleableType S] [SampleableType O] in
@[simp] theorem dropCache_apply (c : (prefixSpec S I O + []ₒ).QueryCache) (p : List I) :
    dropCache c p = c (.inl p) := rfl

omit [DecidableEq I] [SampleableType S] [SampleableType O] in
@[simp] theorem dropCache_empty : dropCache (∅ : (prefixSpec S I O + []ₒ).QueryCache) = ∅ :=
  QueryCache.ext fun _ => rfl

omit [SampleableType S] [SampleableType O] in
theorem dropCache_cacheQuery (c : (prefixSpec S I O + []ₒ).QueryCache) (p : List I)
    (u : S × O) : dropCache (c.cacheQuery (.inl p) u) = (dropCache c).cacheQuery p u := by
  refine QueryCache.ext fun p' => ?_
  by_cases h : p' = p
  · subst h
    simp [QueryCache.cacheQuery_self]
  · rw [dropCache_apply, QueryCache.cacheQuery_of_ne _ _ (by simpa using h),
      QueryCache.cacheQuery_of_ne _ _ h, dropCache_apply]

/-- The random oracle on the prefix oracle and no extra oracles is the random oracle on the prefix
oracle, through `dropEmpty`. -/
theorem map_run_dropEmpty {α : Type} (P : OracleComp (unifSpec + (prefixSpec S I O + []ₒ)) α)
    (c : (prefixSpec S I O + []ₒ).QueryCache) :
    (fun z => (z.1, dropCache z.2)) <$> (simulateQ (prefixSpec S I O + []ₒ).romImpl P).run c =
      (simulateQ (prefixSpec S I O).romImpl (simulateQ dropEmpty P)).run (dropCache c) := by
  induction P using OracleComp.inductionOn generalizing c with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rcases t with n | p | e
    · simp only [romImpl_run_unif, bind_map_left, ih]
      rfl
    · change _ = (simulateQ (prefixSpec S I O).romImpl
        (liftM ((unifSpec + prefixSpec S I O).query (.inr p)))).run (dropCache c) >>= _
      simp only [simulateQ_spec_query]
      cases hc : c (.inl p) with
      | some u =>
        rw [romImpl_run_of_some hc, romImpl_run_of_some (show dropCache c p = some u from hc),
          pure_bind, pure_bind, ih]
      | none =>
        rw [romImpl_run_of_none hc, romImpl_run_of_none (show dropCache c p = none from hc)]
        simp only [bind_map_left, ih, dropCache_cacheQuery]
        simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
        rfl
    · exact e.elim

end Drop

/-! ### The Fiat–Shamir game on a hash chain -/

/-- An encoding of restoration keys as nonempty lists of chain inputs, latest first: the inputs a
Fiat–Shamir verifier absorbs for a key's challenge. It is injective. -/
structure ChainCodec (K I : Type) where
  encode : K → I × List I
  injective : Function.Injective encode

namespace ChainCodec

variable {K I : Type}

/-- The encoding as a list of inputs. -/
def toList (codec : ChainCodec K I) (k : K) : List I := (codec.encode k).1 :: (codec.encode k).2

theorem toList_injective (codec : ChainCodec K I) : Function.Injective codec.toList :=
  fun _ _ h => codec.injective (Prod.ext (List.cons.inj h).1 (List.cons.inj h).2)

/-- The encoding as a strict codec into lists of inputs, decoding by inverting it. -/
noncomputable def strict (codec : ChainCodec K I) : StrictCodec K (List I) where
  encode := codec.toList
  decode d := open Classical in if h : ∃ k, codec.toList k = d then some h.choose else none
  decode_encode k := by
    have h : ∃ k', codec.toList k' = codec.toList k := ⟨k, rfl⟩
    simp only [h, ↓reduceDIte]
    exact congrArg some (codec.toList_injective h.choose_spec)
  encode_decode d k h := by
    split_ifs at h with hd
    cases h
    exact hd.choose_spec

end ChainCodec

section Game

variable {S I O : Type} [DecidableEq S] [DecidableEq I] [SampleableType S] [SampleableType O]
variable {Input Salt W : Type} {protocol : Input → Protocol}
  {coin : (z : Input) → PublicCoin (protocol z)}

/-- The Fiat–Shamir verifier's challenge at a key: absorb the key's encoding through the chain
from `s₀`, and read the challenge off the answer. -/
def chainCompletionQueries (s₀ : S) (common : CommonChallenge Input Salt (S × O) coin)
    (codec : ChainCodec (Key Input Salt coin) I) :
    QueryImpl (oracleSpec Input Salt coin) (OracleComp (unifSpec + (chainSpec S I O + []ₒ))) :=
  fun key => (common.challengeEquiv key).symm <$>
    absorb s₀ (codec.encode key).1 (codec.encode key).2

/-- Complete a selected transcript while its guards pass, each challenge from the chain. -/
def chainCompletionAfter (s₀ : S) (coin : (z : Input) → PublicCoin (protocol z))
    (common : CommonChallenge Input Salt (S × O) coin)
    (codec : ChainCodec (Key Input Salt coin) I)
    (guards : (z : Input) → GuardSchedule Salt (coin z))
    (selected : Option (Selection Input Salt W coin)) :
    OracleComp (unifSpec + (chainSpec S I O + []ₒ)) (Option (Outcome Input W protocol)) :=
  match selected with
  | none => pure none
  | some ⟨z, messages, witness⟩ =>
      (fun path => path.map (fun p => ⟨z, p, witness⟩)) <$>
        simulateQ (chainCompletionQueries s₀ common codec)
          (stoppedComplete coin guards z messages)

/-- The Fiat–Shamir game on a hash chain: the adversary queries the chain and selects a
transcript, and the verifier completes it, each challenge from the same chain. -/
def chainStoppedExecution (s₀ : S) (coin : (z : Input) → PublicCoin (protocol z))
    (common : CommonChallenge Input Salt (S × O) coin)
    (codec : ChainCodec (Key Input Salt coin) I)
    (guards : (z : Input) → GuardSchedule Salt (coin z))
    (adversary : OracleComp (unifSpec + (chainSpec S I O + []ₒ))
      (Option (Selection Input Salt W coin))) :
    OracleComp (unifSpec + (chainSpec S I O + []ₒ)) (Option (Outcome Input W protocol)) :=
  adversary >>= chainCompletionAfter s₀ coin common codec guards

end Game

/-! ### Query counts -/

section Count

variable {D : Type} {R : D → Type} [DecidableEq D] [∀ d, SampleableType (R d)]

/-- A logged random-oracle run of a program making at most `q` oracle queries logs at most `q`
queries. -/
theorem log_length_le_of_mem_support {α : Type} (P : OracleComp (unifSpec + ofFn R) α) {q : ℕ}
    (hP : IsQueryBoundP P (fun t => isUnif t = false) q) (c : (ofFn R).QueryCache)
    (z : (α × QueryLog (ofFn R)) × (ofFn R).QueryCache)
    (hz : z ∈ support (randomOracleLoggedRun P c)) : z.1.2.length ≤ q := by
  induction P using OracleComp.inductionOn generalizing c q z with
  | pure a =>
    simp only [randomOracleLoggedRun, QueryImpl.passthrough_add, simulateQ_pure,
      WriterT.run_pure, List.empty_eq, StateT.run_pure, MonadAttach.support_pure,
      Set.mem_singleton_iff] at hz
    rw [hz]
    simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hP
    rw [randomOracleLoggedRun_bind, mem_support_bind_iff] at hz
    obtain ⟨w, hw, hz⟩ := hz
    rw [support_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    have hk := ih w.1.1 (hP.2 w.1.1) w.2 y hy
    rcases t with n | x
    · rw [randomOracleLoggedRun_uniformQuery, support_map] at hw
      obtain ⟨u, -, rfl⟩ := hw
      simpa [isUnif] using hk
    · rw [randomOracleLoggedRun_hashQuery, support_map] at hw
      obtain ⟨u, -, rfl⟩ := hw
      have hq : 0 < q := by simpa [isUnif] using hP.1
      simp only [isUnif, ↓reduceIte] at hk
      simp only [List.length_append, List.length_singleton]
      omega

/-- A program making at most `q` oracle queries queries at most `q` distinct keys in expectation. -/
theorem expectedFreshQueryCharge_le {α : Type} (P : OracleComp (unifSpec + ofFn R) α) {q : ℕ}
    (hP : IsQueryBoundP P (fun t => isUnif t = false) q) :
    expectedFreshQueryCharge P (fun _ => 1) ≤ q := by
  let : MeasurableSpace ((α × QueryLog (ofFn R)) × (ofFn R).QueryCache) := ⊤
  have hae := evalDist.ae_of_forall_mem_support (randomOracleLoggedRun P ∅)
    (fun z => freshQueryCharge (fun _ => (1 : ENNReal)) z.1.2 ≤ q) MeasurableSet.of_discrete
    fun z hz => by
      simp only [freshQueryCharge, Finset.sum_const, nsmul_eq_mul, mul_one]
      exact Nat.cast_le.mpr (((List.toFinset_card_le _).trans (List.length_map _).le).trans
        (log_length_le_of_mem_support P hP ∅ z hz))
  calc expectedFreshQueryCharge P (fun _ => 1)
      ≤ ∫⁻ _, (q : ENNReal) ∂𝒟[randomOracleLoggedRun P ∅] := lintegral_mono_ae hae
    _ = q := by rw [lintegral_const, evalDist_apply_univ_eq_one, mul_one]

end Count

/-! ### The reduction to the encoded random oracle -/

section Reduction

variable {S I O : Type} [DecidableEq S] [DecidableEq I] [SampleableType S] [SampleableType O]
variable {Input Salt W : Type} {protocol : Input → Protocol}
  {coin : (z : Input) → PublicCoin (protocol z)}

/-- The adversary extended by the verifier's completion of its selection, returning both. -/
def chainAdversary (s₀ : S) (coin : (z : Input) → PublicCoin (protocol z))
    (common : CommonChallenge Input Salt (S × O) coin)
    (codec : ChainCodec (Key Input Salt coin) I)
    (guards : (z : Input) → GuardSchedule Salt (coin z))
    (adversary : OracleComp (unifSpec + (chainSpec S I O + []ₒ))
      (Option (Selection Input Salt W coin))) :
    OracleComp (unifSpec + (chainSpec S I O + []ₒ))
      (Option (Selection Input Salt W coin) × Option (Outcome Input W protocol)) :=
  adversary >>= fun selected =>
    (selected, ·) <$> chainCompletionAfter s₀ coin common codec guards selected

omit [DecidableEq S] [DecidableEq I] [SampleableType S] [SampleableType O] in
/-- The verifier's completion draws no private coin. -/
theorem isQueryBoundP_chainCompletionAfter (s₀ : S)
    (coin : (z : Input) → PublicCoin (protocol z))
    (common : CommonChallenge Input Salt (S × O) coin)
    (codec : ChainCodec (Key Input Salt coin) I)
    (guards : (z : Input) → GuardSchedule Salt (coin z))
    (selected : Option (Selection Input Salt W coin)) :
    IsQueryBoundP (chainCompletionAfter s₀ coin common codec guards selected)
      (fun t => isUnif t = true) 0 := by
  rcases selected with _ | ⟨z, messages, witness⟩
  · trivial
  · refine (isQueryBoundP_map_iff _ _ _).mpr (isQueryBoundP_simulateQ_zero _ fun key => ?_)
    exact (isQueryBoundP_map_iff _ _ _).mpr (isQueryBoundP_absorb s₀ _ _)

/-- Replaying two simulations of one program succeeds alike when each query's does. -/
theorem replay_simulateQ_of_forall {κ ι₁ ι₂ : Type} {native : OracleSpec κ}
    {hs₁ : OracleSpec ι₁} {hs₂ : OracleSpec ι₂} (c₁ : hs₁.QueryCache) (c₂ : hs₂.QueryCache)
    (impl₁ : QueryImpl native (OracleComp (unifSpec + hs₁)))
    (impl₂ : QueryImpl native (OracleComp (unifSpec + hs₂)))
    (h : ∀ t u, replay c₁ (impl₁ t) = some u → replay c₂ (impl₂ t) = some u) {α : Type}
    (P : OracleComp native α) (a : α) (hP : replay c₁ (simulateQ impl₁ P) = some a) :
    replay c₂ (simulateQ impl₂ P) = some a := by
  induction P using OracleComp.inductionOn with
  | pure b => simpa using hP
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, replay_bind] at hP ⊢
    cases hu : replay c₁ (impl₁ t) with
    | none => rw [hu] at hP; cases hP
    | some u =>
      rw [hu] at hP
      rw [h t u hu]
      exact ih u hP


omit [SampleableType S] [SampleableType O] in
/-- Off a collision, replaying the verifier's chain completion through `view` succeeds as replaying
the encoded completion on the prefix oracle's cache. -/
theorem replay_encodedCompletion (s₀ : S) (coin : (z : Input) → PublicCoin (protocol z))
    (common : CommonChallenge Input Salt (S × O) coin)
    (codec : ChainCodec (Key Input Salt coin) I)
    (guards : (z : Input) → GuardSchedule Salt (coin z))
    {σ : IdealState S I O []ₒ} (hI : Inv σ) (hG : Good s₀ σ.1)
    (selected : Option (Selection Input Salt W coin)) (r : Option (Outcome Input W protocol))
    (h : replay (view s₀ σ) (chainCompletionAfter s₀ coin common codec guards selected) =
      some r) :
    replay (dropCache σ.2) (encodedExternalCompletionAfter coin common codec.strict guards
      selected) = some r := by
  rcases selected with _ | ⟨z, messages, witness⟩
  · simpa [chainCompletionAfter, encodedExternalCompletionAfter] using h
  · simp only [chainCompletionAfter, encodedExternalCompletionAfter, replay_map] at h ⊢
    obtain ⟨path, hpath, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [replay_simulateQ_of_forall (view s₀ σ) (dropCache σ.2) _ _ (fun key u hu => ?_) _ path
      hpath]
    · rfl
    simp only [chainCompletionQueries, replay_map] at hu
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hu
    have hcache := replay_view_absorb s₀ hI hG _ _ v hv
    simp only [encodedCompletionQueries, replay_map]
    have hr : replay (dropCache σ.2) (liftM ((unifSpec + (List I →ₒ (S × O))).query
        (.inr (codec.strict.encode key)))) = some v := by
      simpa [replay, cacheAnswers, ChainCodec.strict, ChainCodec.toList] using hcache
    rw [hr]
    rfl

/-- The simulated extended adversary queries the prefix oracle at most as often as the extended
adversary queries the chain. -/
theorem isQueryBoundP_dropEmpty_simulate (s₀ : S) {α : Type}
    {A : OracleComp (unifSpec + (chainSpec S I O + []ₒ)) α} {q : ℕ}
    (hA : IsQueryBoundP A (fun t => isChain t = true) q) :
    IsQueryBoundP (simulateQ dropEmpty (simulate s₀ A)) (fun t => isUnif t = false) q := by
  refine (isQueryBoundP_simulate s₀ hA).simulateQ_of_step (fun t ht => ?_) (fun t ht => ?_)
  · rcases t with n | p | e
    · cases ht
    · exact (isQueryBoundP_query_iff _ _ _).mpr fun _ => Nat.one_pos
    · exact e.elim
  · rcases t with n | p | e
    · exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [isUnif])
    · exact absurd rfl ht
    · exact e.elim

/-- **Fiat–Shamir on a hash chain.** An adversary on a hash chain selects a transcript, and the
verifier completes it while its guards pass, absorbing each key's encoding through the chain from
`s₀` and reading the challenge off the answer. If the adversary and the verifier together make at
most `q` chain queries, the verifier completes a path with a valid terminal witness whose
backward extraction fails, for witness maps locally bounded by the node errors `errors`, with
probability at most the chain's collision-or-prediction error `chainError S q` plus the encoded
random oracle's bound `maxError errors * q + sumError errors`. -/
theorem chainStopped_knowledge_soundness (s₀ : S) (coin : (z : Input) → PublicCoin (protocol z))
    (common : CommonChallenge Input Salt (S × O) coin)
    (codec : ChainCodec (Key Input Salt coin) I)
    (guards : (z : Input) → GuardSchedule Salt (coin z))
    (errors : (z : Input) → Errors (coin z))
    (adversary : OracleComp (unifSpec + (chainSpec S I O + []ₒ))
      (Option (Selection Input Salt W coin)))
    {q : ℕ} (hq : IsQueryBoundP (chainStoppedExecution s₀ coin common codec guards adversary)
      (fun t => isChain t = true) q)
    (state : Input → KnowledgeState)
    (extractor : (z : Input) → RoundExtractor (protocol z).tree (state z))
    (Z : Set Input)
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol z).roles)
    (bounded : ∀ z ∈ Z, RoundExtractor.IsLocallyBounded (extractor z)
      (protocol z).roles (errorSchedule (coin z) (errors z))) :
    Pr{let result ← (simulateQ (chainSpec S I O + []ₒ).romImpl
        (chainStoppedExecution s₀ coin common codec guards adversary)).run' ∅}[
      stoppedExtractionFails state extractor Z result] ≤
      chainError S q + (maxError errors * q + sumError errors) := by
  classical
  let E := stoppedExtractionFails (W := W) state extractor Z
  let cc := chainCompletionAfter (W := W) s₀ coin common codec guards
  let enc := encodedExternalCompletionAfter (W := W) coin common codec.strict guards
  let Aplus := chainAdversary s₀ coin common codec guards adversary
  have hG : chainStoppedExecution s₀ coin common codec guards adversary = Prod.snd <$> Aplus := by
    simp only [chainStoppedExecution, Aplus, chainAdversary, map_bind, Functor.map_map]
    simp
  have hqA : IsQueryBoundP Aplus (fun t => isChain t = true) q := by
    rw [hG] at hq
    exact (isQueryBoundP_map_iff _ _ _).mp hq
  -- The game's event is an event of the extended adversary's output and final chain cache.
  have h1 : Pr{let result ← (simulateQ (chainSpec S I O + []ₒ).romImpl
      (chainStoppedExecution s₀ coin common codec guards adversary)).run' ∅}[E result] ≤
      Pr{let z ← (simulateQ (chainSpec S I O + []ₒ).romImpl Aplus).run ∅}[
        replay z.2 (cc z.1.1) = some z.1.2 ∧ E z.1.2] := by
    have e1 : (simulateQ (chainSpec S I O + []ₒ).romImpl
        (chainStoppedExecution s₀ coin common codec guards adversary)).run' ∅ =
        (fun z => z.1.2) <$> (simulateQ (chainSpec S I O + []ₒ).romImpl Aplus).run ∅ := by
      rw [hG]
      change Prod.fst <$> (simulateQ (chainSpec S I O + []ₒ).romImpl (Prod.snd <$> Aplus)).run ∅ = _
      rw [simulateQ_map, StateT.run_map, Functor.map_map]
    rw [e1, prEvent_map]
    refine prEvent_mono_of_support _ _ _ fun z hz hE => ⟨?_, hE⟩
    simp only [Aplus, chainAdversary, simulateQ_bind, StateT.run_bind] at hz
    obtain ⟨w, -, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    rw [simulateQ_map, StateT.run_map, support_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact replay_of_mem_support_run _ (isQueryBoundP_chainCompletionAfter s₀ coin common codec
      guards w.1) w.2 y hy
  -- Off a collision, it is the replay of the encoded completion in the simulated run.
  have h2 :=
    (dominatedUntilBad (I := I) (O := O) (extra := []ₒ) s₀).prEvent_simulateQ_run_le_map_or_bad
    (preservesInv_inv s₀) (preservesInv_bad s₀) Aplus (SimState.init, ∅) inv_init
    (fun z => replay z.2 (cc z.1.1) = some z.1.2 ∧ E z.1.2)
  rw [view_init] at h2
  have h3 : Pr{let z ← (simulateQ (idealImpl s₀) Aplus).run (SimState.init, ∅)}[
      (replay (view s₀ z.2) (cc z.1.1) = some z.1.2 ∧ E z.1.2) ∨ ¬ Good s₀ z.2.1] ≤
      Pr{let z ← (simulateQ (idealImpl s₀) Aplus).run (SimState.init, ∅)}[
        replay (dropCache z.2.2) (enc z.1.1) = some z.1.2 ∧ E z.1.2] + chainError S q := by
    refine (prEvent_mono_of_support _ _ _ fun z hz h => ?_).trans
      ((prEvent_or_le _ _ _).trans (add_le_add le_rfl (prEvent_bad_le s₀ Aplus hqA)))
    by_cases hgood : Good s₀ z.2.1
    · rcases h with ⟨hr, hE⟩ | hbad
      · exact .inl ⟨replay_encodedCompletion s₀ coin common codec guards
          (simulateQ_run_preservesInv _ _ (preservesInv_inv s₀) Aplus _ inv_init z hz) hgood
          _ _ hr, hE⟩
      · exact absurd hgood hbad
    · exact .inr hgood
  -- The simulated run is the prefix oracle's run of the simulated extended adversary.
  let X := simulateQ dropEmpty (simulate s₀ Aplus)
  have h4 : Pr{let z ← (simulateQ (idealImpl s₀) Aplus).run (SimState.init, ∅)}[
      replay (dropCache z.2.2) (enc z.1.1) = some z.1.2 ∧ E z.1.2] =
      Pr{let w ← (simulateQ (prefixSpec S I O).romImpl X).run ∅}[
        replay w.2 (enc w.1.1) = some w.1.2 ∧ E w.1.2] := by
    have e4 : (simulateQ (prefixSpec S I O).romImpl X).run ∅ =
        (fun z => (z.1, dropCache z.2.2)) <$>
          (simulateQ (idealImpl s₀) Aplus).run (SimState.init, ∅) := by
      have hsim := run_simulateQ_sim s₀ Aplus SimState.init ∅
      have hdrop := map_run_dropEmpty (simulate s₀ Aplus) ∅
      rw [dropCache_empty] at hdrop
      rw [← hdrop]
      change (fun z : (Option (Selection Input Salt W coin) × Option (Outcome Input W protocol)) ×
          (prefixSpec S I O + []ₒ).QueryCache => (z.1, dropCache z.2)) <$>
        (simulateQ (prefixSpec S I O + []ₒ).romImpl
          (Prod.fst <$> (simulateQ (sim s₀) Aplus).run SimState.init)).run ∅ = _
      rw [simulateQ_map, StateT.run_map, hsim, Functor.map_map, Functor.map_map]
    rw [e4, prEvent_map]
  -- A successful replay of the encoded completion is its run.
  let external := Prod.fst <$> X
  have h5 : Pr{let w ← (simulateQ (prefixSpec S I O).romImpl X).run ∅}[
      replay w.2 (enc w.1.1) = some w.1.2 ∧ E w.1.2] ≤
      Pr{let joint ← (randomOracleLoggedRun
        (encodedExternalStoppedExecution coin common codec.strict guards external) ∅)}[
        E joint.1.1] := by
    have e5 : Pr{let joint ← (randomOracleLoggedRun
        (encodedExternalStoppedExecution coin common codec.strict guards external) ∅)}[
        E joint.1.1] = Pr{let w ← (simulateQ (prefixSpec S I O).romImpl
          (external >>= enc)).run ∅}[E w.1] := by
      rw [← randomOracleLoggedRun_project, prEvent_map]
      rfl
    rw [e5, simulateQ_bind, StateT.run_bind, simulateQ_map, StateT.run_map, bind_map_left]
    conv_lhs => rw [← bind_pure ((simulateQ (prefixSpec S I O).romImpl X).run ∅)]
    refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun w => ?_
    by_cases hR : replay w.2 (enc w.1.1) = some w.1.2 ∧ E w.1.2
    · rw [run_of_replay _ w.2 w.1.2 hR.1, prEvent_pure, prEvent_pure]
      simp [hR]
    · rw [prEvent_pure]
      simp [hR]
  have h6 := encodedExternalStopped_extraction_le_adversaryCount coin common codec.strict
    guards errors external state extractor Z preserving bounded
  have h7 : expectedFreshQueryCharge external (fun _ => 1) ≤ q := by
    rw [OracleComp.expectedFreshQueryCharge_map]
    exact expectedFreshQueryCharge_le X (isQueryBoundP_dropEmpty_simulate s₀ hqA)
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ _ := h3
    _ = _ := by rw [h4]
    _ ≤ (maxError errors * q + sumError errors) + chainError S q := by
      refine add_le_add (h5.trans (h6.trans ?_)) le_rfl
      gcongr
    _ = _ := add_comm _ _

open PublicCoin in
/-- **Fiat–Shamir on a hash chain from knowledge certificates, with grinding.** The verifier
draws each challenge off the chain's answer, its state and output, through the draws `dec`: after
the prover's witness, absorbed into the key, it rejects the answers that fail the draw's check
(a grinding draw's proof of work) and decodes the challenge from the others. Each draw is bounded
by the ratio at its node (`ratio`). If every input's certificate samples its challenges uniformly
and the adversary and the verifier together make at most `q` chain queries, the verifier completes
a path whose answers all pass, decoding to a path of the protocol with a valid terminal witness
whose backward extraction fails, with probability at most `chainError S q` plus the
state-restoration bound `maxError * q + sumError` of the certificates' node errors, each
multiplied by its node's ratio. -/
theorem KnowledgeCertificate.chainStopped_knowledge_soundness (s₀ : S)
    (coin : (z : Input) → PublicCoin (protocol z)) (dec : (z : Input) → Decoder (S × O) (coin z))
    (ratio : (z : Input) → Errors (coin z)) (hdec : ∀ z, Decoder.Bounded (coin z) (dec z) (ratio z))
    (codec : ChainCodec (Key Input Salt fun z => decoded (S × O) (coin z) (dec z)) I)
    (guards : (z : Input) → GuardSchedule Salt (decoded (S × O) (coin z) (dec z)))
    (state : Input → KnowledgeState)
    (certificate : (z : Input) → KnowledgeCertificate (protocol z).tree (protocol z).roles
      (state z))
    (uniform : ∀ z, UniformChallenges (coin z) (certificate z).challenges)
    (adversary : OracleComp (unifSpec + (chainSpec S I O + []ₒ))
      (Option (Selection Input Salt W fun z => decoded (S × O) (coin z) (dec z))))
    {q : ℕ} (hq : IsQueryBoundP
      (chainStoppedExecution s₀ (fun z => decoded (S × O) (coin z) (dec z))
      (decodedCommon coin dec) codec guards adversary) (fun t => isChain t = true) q) :
    Pr{let result ← (simulateQ (chainSpec S I O + []ₒ).romImpl
        (chainStoppedExecution s₀ (fun z => decoded (S × O) (coin z) (dec z))
          (decodedCommon coin dec) codec guards adversary)).run' ∅}[
      ∃ z path seed, result = some ⟨z, path, seed⟩ ∧
        ∃ p, decodePath (coin z) (dec z) path = some p ∧
          ∃ witness, ((certificate z).extractor.terminalState p).holds witness ∧
            ¬ (state z).holds ((certificate z).extractor.extractWitness p witness)] ≤
      chainError S q + (maxError (fun z node => ratio z node *
          supErrors (coin z) (certificate z).challenges node) * q +
        sumError (fun z node => ratio z node *
          supErrors (coin z) (certificate z).challenges node)) := by
  classical
  let errors : (z : Input) → Errors (decoded (S × O) (coin z) (dec z)) := fun z node =>
    ratio z (Prefix.undecode (coin z) (dec z) node) *
      supErrors (coin z) (certificate z).challenges (Prefix.undecode (coin z) (dec z) node)
  have h := HashChain.chainStopped_knowledge_soundness
    (protocol := fun z => decodedProtocol (S × O) (coin z) (dec z)) s₀
    (fun z => decoded (S × O) (coin z) (dec z))
    (decodedCommon coin dec) codec guards errors adversary hq state
    (fun z => decodeExtractor (coin z) (dec z) (certificate z).extractor) Set.univ
    (fun z _ => isProverPreserving_decodeExtractor (coin z) (dec z) _
      (certificate z).prover_preserving)
    (fun z _ => isLocallyBounded_errorSchedule _ _ _
      (uniformChallenges_decodeSchedule (coin z) (dec z) (ratio z) (certificate z).challenges)
      (isLocallyBounded_decodeExtractor (coin z) (dec z) (ratio z) (hdec z) _ _ (uniform z)
        (certificate z).local_bound) _
      (supErrors_decodeSchedule_le (coin z) (dec z) (ratio z) (certificate z).challenges))
  refine (prEvent_mono _ _ _ fun result hresult => ?_).trans (h.trans (add_le_add le_rfl ?_))
  · obtain ⟨z, path, seed, rfl, bad⟩ := hresult
    exact ⟨Set.mem_univ z, (badTerminal_decode (coin z) (dec z) (certificate z).extractor path
      (fun w => ¬ (state z).holds w)).mpr bad⟩
  have hmax : maxError errors ≤ maxError (fun z node =>
      ratio z node * supErrors (coin z) (certificate z).challenges node) :=
    iSup_le fun z => iSup_le fun node =>
      le_iSup_of_le z (le_iSup (fun node => ratio z node *
        supErrors (coin z) (certificate z).challenges node) (Prefix.undecode (coin z) (dec z) node))
  have hsum : sumError errors ≤ sumError (fun z node =>
      ratio z node * supErrors (coin z) (certificate z).challenges node) :=
    iSup_mono fun z => pathError_undecode_le (coin z) (dec z) fun node =>
      ratio z node * supErrors (coin z) (certificate z).challenges node
  gcongr

end Reduction

end Interaction.Oracle.Security.HashChain
