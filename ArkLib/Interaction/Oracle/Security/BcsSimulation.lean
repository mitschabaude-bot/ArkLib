/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.Interaction.Oracle.Security.HashChainEncoded

/-!
# A hash chain beside a hash oracle, simulated by a chain over snapshot-encoded inputs

The real oracles are a chain oracle `HashChain.chainSpec S I O` and an auxiliary hash oracle
`hs`, run lazily with a log of their queries and answers (`Bcs.realImpl`): a query asked before is
answered by its logged answer, a fresh one by a uniform sample appended to the log. Mapping the
final log to the cache of its answers is the lazy random oracle's run
(`Bcs.map_run_simulateQ_realImpl`).

The simulator `Bcs.bcsSim enc` runs a program against the real oracles with an ideal chain oracle
`chainSpec S I' O` over encoded inputs. It keeps the same log: a fresh hash query is answered by a
private uniform sample, and a fresh chain query `(s, x)` is forwarded to the ideal chain at
`(s, enc T x)`, `T` the hash answers logged so far (`Bcs.hashCacheOf`). When the encoding
determines the input whatever the hash answers (`enc T x = enc T' x' → x = x'`), distinct chain
keys of the log are forwarded to distinct ideal keys, so every forwarded query is fresh for the
ideal oracle and the simulation is exact.

## Main statements

- `Bcs.map_run_simulateQ_realImpl`: the logged real run, its log mapped to a cache, is the lazy
  random oracle's run.
- `Bcs.prEvent_real_le_sim`: an event of the output and log of the real run is at most the same
  event of the simulated run against the ideal chain, together with `Bcs.Matches`: every chain
  entry `⟨(s, x), a⟩` of the log is cached by the ideal chain at `(s, enc T x)` with answer `a`,
  `T = Bcs.snapshotAt log (s, x)` the hash answers logged before the entry.

## Proof

The flat handler `Bcs.idealImpl` runs one simulator step against the ideal chain; its runs are the
ideal chain's runs of the simulated program (`Bcs.run_simulateQ_bcsSim`). Under the invariant
`Bcs.Inv` (the log's chain entries are cached at their forwarded keys, and the ideal cache holds
no other key), each step of `idealImpl`, read on its log, is a step of `realImpl`
(`Bcs.dominatedUntilBad`, with no bad event), and `QueryImpl.DominatedUntilBad` compares the runs.
-/

@[expose] public section

open OracleComp OracleSpec
open scoped ENNReal

namespace Interaction.Oracle.Security.Bcs

open HashChain

/-! ### The cache of a log -/

section Log

variable {κ : Type} [DecidableEq κ] {spec : OracleSpec κ}

/-- The cache of a log: each key answered by its first entry. -/
def cacheOf : QueryLog spec → spec.QueryCache
  | [] => ∅
  | e :: log => (cacheOf log).cacheQuery e.1 e.2

@[simp] theorem cacheOf_nil : cacheOf ([] : QueryLog spec) = ∅ := rfl

theorem cacheOf_cons (e : (t : κ) × spec.Range t) (log : QueryLog spec) :
    cacheOf (e :: log) = (cacheOf log).cacheQuery e.1 e.2 := rfl

theorem cacheOf_cons_eq_none {e : (t : κ) × spec.Range t} {log : QueryLog spec} {t : κ} :
    cacheOf (e :: log) t = none ↔ e.1 ≠ t ∧ cacheOf log t = none := by
  obtain ⟨t', u'⟩ := e
  by_cases h : t = t'
  · subst h
    simp [cacheOf_cons]
  · simp [cacheOf_cons, QueryCache.cacheQuery_of_ne _ _ h, Ne.symm h]

/-- A logged key is cached. -/
theorem cacheOf_ne_none_of_mem {log : QueryLog spec} {e : (t : κ) × spec.Range t}
    (h : e ∈ log) : cacheOf log e.1 ≠ none := by
  induction log with
  | nil => cases h
  | cons e' log ih =>
    intro hn
    rw [cacheOf_cons_eq_none] at hn
    rcases List.mem_cons.mp h with rfl | h
    · exact hn.1 rfl
    · exact ih h hn.2

/-- Appending an entry at an uncached key caches its answer. -/
theorem cacheOf_append_singleton {log : QueryLog spec} {t : κ} (h : cacheOf log t = none)
    (u : spec.Range t) : cacheOf (log ++ [⟨t, u⟩]) = (cacheOf log).cacheQuery t u := by
  induction log with
  | nil => rfl
  | cons e log ih =>
    obtain ⟨he, h⟩ := cacheOf_cons_eq_none.mp h
    rw [List.cons_append, cacheOf_cons, ih h, cacheOf_cons,
      QueryCache.cacheQuery_comm _ (Ne.symm he)]

/-- A list's longest prefix satisfying `p` is unchanged by appending, once an element of the
list fails `p`. -/
theorem takeWhile_append_of_mem {α : Type} {p : α → Bool} {l₁ : List α} {a : α} (ha : a ∈ l₁)
    (hp : p a = false) (l₂ : List α) : (l₁ ++ l₂).takeWhile p = l₁.takeWhile p := by
  induction l₁ with
  | nil => cases ha
  | cons b l ih =>
    cases hb : p b
    · simp [List.takeWhile, hb]
    · rcases List.mem_cons.mp ha with rfl | ha
      · rw [hp] at hb
        cases hb
      · simp [List.takeWhile, hb, ih ha]

end Log

variable {S I I' O ι : Type} [DecidableEq S] [DecidableEq I] [DecidableEq I'] [DecidableEq ι]
  [SampleableType S] [SampleableType O] {hs : OracleSpec ι} [∀ t, SampleableType (hs.Range t)]

/-! ### The real oracles with a log -/

/-- The real oracles answered lazily with a log: private coins pass through; a query is answered
by its first logged answer, or else by a uniform sample appended to the log. -/
def realImpl : QueryImpl (unifSpec + (chainSpec S I O + hs))
    (StateT (QueryLog (chainSpec S I O + hs)) ProbComp)
  | .inl n => StateT.mk fun log =>
      (fun u => (u, log)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) n)
  | .inr t => StateT.mk fun log => match cacheOf log t with
    | some u => pure (u, log)
    | none => (fun u => (u, log ++ [⟨t, u⟩])) <$> ($ᵗ (chainSpec S I O + hs).Range t)

omit [DecidableEq I'] in
theorem realImpl_run_unif (n : ℕ) (log : QueryLog (chainSpec S I O + hs)) :
    (realImpl (.inl n)).run log =
      (fun u => (u, log)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) n) := rfl

omit [DecidableEq I'] in
theorem realImpl_run_of_some {t : (chainSpec S I O + hs).Domain}
    {log : QueryLog (chainSpec S I O + hs)} {u : (chainSpec S I O + hs).Range t}
    (h : cacheOf log t = some u) : (realImpl (.inr t)).run log = pure (u, log) := by
  simp [realImpl, h]

omit [DecidableEq I'] in
theorem realImpl_run_of_none {t : (chainSpec S I O + hs).Domain}
    {log : QueryLog (chainSpec S I O + hs)} (h : cacheOf log t = none) :
    (realImpl (.inr t)).run log =
      (fun u => (u, log ++ [⟨t, u⟩])) <$> ($ᵗ (chainSpec S I O + hs).Range t) := by
  simp [realImpl, h]

omit [DecidableEq I'] in
/-- **The logged run is the lazy random oracle's run.** Mapping the final log to its cache gives
the lazy random oracle's run from the cache of the initial log. -/
theorem map_run_simulateQ_realImpl {α : Type}
    (P : OracleComp (unifSpec + (chainSpec S I O + hs)) α)
    (log : QueryLog (chainSpec S I O + hs)) :
    Prod.map id cacheOf <$> (simulateQ realImpl P).run log =
      (simulateQ (chainSpec S I O + hs).romImpl P).run (cacheOf log) := by
  refine map_run_simulateQ_eq_of_query_map_eq _ _ cacheOf (fun t log => ?_) P log
  rcases t with n | t
  · rw [realImpl_run_unif, romImpl_run_unif, Functor.map_map]
    rfl
  · cases h : cacheOf log t with
    | some u => rw [realImpl_run_of_some h, romImpl_run_of_some h, map_pure]; rfl
    | none =>
      rw [realImpl_run_of_none h, romImpl_run_of_none h, Functor.map_map]
      simp only [Prod.map, id, cacheOf_append_singleton h]

/-! ### Snapshots of the hash answers -/

/-- An entry of a log of the real oracles. -/
abbrev Entry (S I O : Type) (hs : OracleSpec ι) : Type :=
  (t : (chainSpec S I O + hs).Domain) × (chainSpec S I O + hs).Range t

/-- The hash answers of a log. -/
def hashCacheOf (log : QueryLog (chainSpec S I O + hs)) : hs.QueryCache := (cacheOf log).snd

/-- The hash answers of a log before its first entry at the chain key `q`. -/
def snapshotAt (log : QueryLog (chainSpec S I O + hs)) (q : S × I) : hs.QueryCache :=
  hashCacheOf (log.takeWhile fun e => decide (e.1 ≠ .inl q))

omit [DecidableEq I'] [SampleableType S] [SampleableType O] [∀ t, SampleableType (hs.Range t)] in
/-- The snapshot at a logged chain key is unchanged by appending. -/
theorem snapshotAt_append_of_mem {log : QueryLog (chainSpec S I O + hs)} {q : S × I}
    {a : S × O} (hmem : (⟨.inl q, a⟩ : Entry S I O hs) ∈ log)
    (l : QueryLog (chainSpec S I O + hs)) :
    snapshotAt (log ++ l) q = snapshotAt log q := by
  unfold snapshotAt
  rw [takeWhile_append_of_mem hmem (by simp)]

omit [DecidableEq I'] [SampleableType S] [SampleableType O] [∀ t, SampleableType (hs.Range t)] in
/-- The snapshot at a chain key appended fresh is the hash answers logged before it. -/
theorem snapshotAt_append_fresh {log : QueryLog (chainSpec S I O + hs)} {q : S × I}
    (h : cacheOf log (.inl q) = none) (u : S × O) :
    snapshotAt (log ++ [(⟨.inl q, u⟩ : Entry S I O hs)]) q = hashCacheOf log := by
  unfold snapshotAt
  rw [List.takeWhile_append_of_pos fun e he => ?_]
  · simp
  · simp only [ne_eq, decide_eq_true_eq]
    intro hq
    exact cacheOf_ne_none_of_mem he (hq ▸ h)

/-! ### The simulator -/

/-- One simulator step on a chain query `q = (s, x)`: the logged answer, or else the ideal chain's
answer at `(s, enc T x)`, `T` the hash answers logged so far, appended to the log. -/
def simChain (enc : hs.QueryCache → I → I') (q : S × I) (log : QueryLog (chainSpec S I O + hs)) :
    OracleComp (unifSpec + (chainSpec S I' O + []ₒ)) ((S × O) × QueryLog (chainSpec S I O + hs)) :=
  match cacheOf log (.inl q) with
  | some u => pure (u, log)
  | none => (fun u => (u, log ++ [⟨.inl q, u⟩])) <$>
      liftM ((unifSpec + (chainSpec S I' O + []ₒ)).query
        (.inr (.inl (q.1, enc (hashCacheOf log) q.2))))

/-- One simulator step on a hash query: the logged answer, or else a private uniform sample,
appended to the log. -/
def simHash (t : ι) (log : QueryLog (chainSpec S I O + hs)) :
    OracleComp (unifSpec + (chainSpec S I' O + []ₒ))
      (hs.Range t × QueryLog (chainSpec S I O + hs)) :=
  match cacheOf log (.inr t) with
  | some u => pure (u, log)
  | none => (fun u => (u, log ++ [⟨.inr t, u⟩])) <$>
      (liftM ($ᵗ hs.Range t : ProbComp (hs.Range t)) :
        OracleComp (unifSpec + (chainSpec S I' O + []ₒ)) (hs.Range t))

/-- The simulator: private coins pass through, chain and hash queries take a `simChain`,
respectively `simHash`, step. -/
def bcsSim (enc : hs.QueryCache → I → I') : QueryImpl (unifSpec + (chainSpec S I O + hs))
    (StateT (QueryLog (chainSpec S I O + hs)) (OracleComp (unifSpec + (chainSpec S I' O + []ₒ))))
  | .inl n => liftM (liftM ((unifSpec + (chainSpec S I' O + []ₒ)).query (.inl n)) :
      OracleComp (unifSpec + (chainSpec S I' O + []ₒ)) (Fin (n + 1)))
  | .inr (.inl q) => StateT.mk (simChain enc q)
  | .inr (.inr t) => StateT.mk (simHash t)

/-! ### The simulated run as one handler -/

/-- The state of the simulated run: the log and the ideal chain's cache. -/
abbrev IdealState (S I I' O : Type) (hs : OracleSpec ι) :=
  QueryLog (chainSpec S I O + hs) × (chainSpec S I' O + []ₒ).QueryCache

/-- One simulator step, run against the ideal chain. -/
def idealImpl (enc : hs.QueryCache → I → I') : QueryImpl (unifSpec + (chainSpec S I O + hs))
    (StateT (IdealState S I I' O hs) ProbComp) :=
  fun t => StateT.mk fun σ => (fun z => (z.1.1, (z.1.2, z.2))) <$>
    (simulateQ (chainSpec S I' O + []ₒ).romImpl ((bcsSim enc t).run σ.1)).run σ.2

/-- The ideal chain's run of the simulated program is the run of `idealImpl`. -/
theorem run_simulateQ_bcsSim (enc : hs.QueryCache → I → I') {α : Type}
    (P : OracleComp (unifSpec + (chainSpec S I O + hs)) α)
    (log : QueryLog (chainSpec S I O + hs)) (c : (chainSpec S I' O + []ₒ).QueryCache) :
    (simulateQ (chainSpec S I' O + []ₒ).romImpl ((simulateQ (bcsSim enc) P).run log)).run c =
      (fun z => ((z.1, z.2.1), z.2.2)) <$> (simulateQ (idealImpl enc) P).run (log, c) := by
  induction P using OracleComp.inductionOn generalizing log c with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, idealImpl, StateT.run_mk,
      map_bind, bind_map_left, ih]

/-! ### Step shapes -/

theorem idealImpl_run_unif (enc : hs.QueryCache → I → I') (n : ℕ)
    (σ : IdealState S I I' O hs) :
    (idealImpl enc (.inl n)).run σ =
      (fun u => (u, σ)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) n) := by
  simp [idealImpl, bcsSim]
  rfl

theorem idealImpl_run_chain (enc : hs.QueryCache → I → I') (q : S × I)
    (σ : IdealState S I I' O hs) :
    (idealImpl enc (.inr (.inl q))).run σ = (fun z => (z.1.1, (z.1.2, z.2))) <$>
      (simulateQ (chainSpec S I' O + []ₒ).romImpl (simChain enc q σ.1)).run σ.2 := by
  simp [idealImpl, bcsSim]

theorem idealImpl_run_hash (enc : hs.QueryCache → I → I') (t : ι)
    (σ : IdealState S I I' O hs) :
    (idealImpl enc (.inr (.inr t))).run σ = (fun z => (z.1.1, (z.1.2, z.2))) <$>
      (simulateQ (chainSpec S I' O + []ₒ).romImpl (simHash (I' := I') t σ.1)).run σ.2 := by
  simp [idealImpl, bcsSim]

theorem idealImpl_run_of_some (enc : hs.QueryCache → I → I')
    {t : (chainSpec S I O + hs).Domain} {σ : IdealState S I I' O hs}
    {u : (chainSpec S I O + hs).Range t} (h : cacheOf σ.1 t = some u) :
    (idealImpl enc (.inr t)).run σ = pure (u, σ) := by
  rcases t with q | t
  · rw [idealImpl_run_chain, simChain]
    simp [h]
  · rw [idealImpl_run_hash, simHash]
    simp [h]

theorem idealImpl_run_chain_of_none {enc : hs.QueryCache → I → I'} {q : S × I}
    {σ : IdealState S I I' O hs} (h : cacheOf σ.1 (.inl q) = none)
    (hc : σ.2 (.inl (q.1, enc (hashCacheOf σ.1) q.2)) = none) :
    (idealImpl enc (.inr (.inl q))).run σ = (fun u => (u, (σ.1 ++ [⟨.inl q, u⟩],
      σ.2.cacheQuery (.inl (q.1, enc (hashCacheOf σ.1) q.2)) u))) <$>
        ($ᵗ (S × O) : ProbComp (S × O)) := by
  rw [idealImpl_run_chain, simChain]
  simp [h, hc]

theorem idealImpl_run_hash_of_none (enc : hs.QueryCache → I → I') {t : ι}
    {σ : IdealState S I I' O hs} (h : cacheOf σ.1 (.inr t) = none) :
    (idealImpl enc (.inr (.inr t))).run σ =
      (fun u => (u, (σ.1 ++ [⟨.inr t, u⟩], σ.2))) <$> ($ᵗ hs.Range t) := by
  rw [idealImpl_run_hash, simHash]
  simp [h, roSim.run_liftM]

/-! ### The invariant -/

/-- Every chain entry `⟨(s, x), a⟩` of the log is cached with answer `a` by the ideal chain at
`(s, enc T x)`, `T` the snapshot of the hash answers before the entry. -/
def Matches (enc : hs.QueryCache → I → I') (log : QueryLog (chainSpec S I O + hs))
    (c : (chainSpec S I' O + []ₒ).QueryCache) : Prop :=
  ∀ s x a, (⟨.inl (s, x), a⟩ : Entry S I O hs) ∈ log →
    c (.inl (s, enc (snapshotAt log (s, x)) x)) = some a

/-- The invariant of the simulated run: the log matches the ideal cache, and the ideal cache holds
only the keys forwarded for the log's chain entries. -/
structure Inv (enc : hs.QueryCache → I → I') (σ : IdealState S I I' O hs) : Prop where
  cached : Matches enc σ.1 σ.2
  onlyLog : ∀ s y, σ.2 (.inl (s, y)) ≠ none → ∃ x a,
    (⟨.inl (s, x), a⟩ : Entry S I O hs) ∈ σ.1 ∧ y = enc (snapshotAt σ.1 (s, x)) x

omit [DecidableEq I'] [SampleableType S] [SampleableType O] [∀ t, SampleableType (hs.Range t)] in
theorem inv_init (enc : hs.QueryCache → I → I') :
    Inv enc (([], ∅) : IdealState S I I' O hs) where
  cached _ _ _ h := by cases h
  onlyLog _ _ h := absurd rfl h

omit [DecidableEq I'] [SampleableType S] [SampleableType O] [∀ t, SampleableType (hs.Range t)] in
/-- A chain key fresh for the log is forwarded to a key fresh for the ideal cache. -/
theorem ideal_fresh {enc : hs.QueryCache → I → I'}
    (henc : ∀ T T' x x', enc T x = enc T' x' → x = x') {σ : IdealState S I I' O hs}
    (hI : Inv enc σ) {q : S × I} (h : cacheOf σ.1 (.inl q) = none) :
    σ.2 (.inl (q.1, enc (hashCacheOf σ.1) q.2)) = none := by
  by_contra hc
  obtain ⟨x, a, hmem, hx⟩ := hI.onlyLog _ _ hc
  obtain rfl := henc _ _ _ _ hx
  exact cacheOf_ne_none_of_mem hmem h

omit [DecidableEq I'] [SampleableType S] [SampleableType O] [∀ t, SampleableType (hs.Range t)] in
theorem inv_hash_fresh {enc : hs.QueryCache → I → I'} {σ : IdealState S I I' O hs}
    (hI : Inv enc σ) (t : ι) (u : hs.Range t) :
    Inv enc ((σ.1 ++ [⟨.inr t, u⟩], σ.2) : IdealState S I I' O hs) where
  cached s x a hmem := by
    rcases List.mem_append.mp hmem with hmem | hmem
    · rw [snapshotAt_append_of_mem hmem]
      exact hI.cached s x a hmem
    · simp at hmem
  onlyLog s y hc := by
    obtain ⟨x, a, hmem, hy⟩ := hI.onlyLog s y hc
    exact ⟨x, a, List.mem_append_left _ hmem, by rw [snapshotAt_append_of_mem hmem]; exact hy⟩

omit [SampleableType S] [SampleableType O] [∀ t, SampleableType (hs.Range t)] in
theorem inv_chain_fresh {enc : hs.QueryCache → I → I'} {σ : IdealState S I I' O hs}
    (hI : Inv enc σ) {q : S × I} (h : cacheOf σ.1 (.inl q) = none)
    (hc : σ.2 (.inl (q.1, enc (hashCacheOf σ.1) q.2)) = none) (u : S × O) :
    Inv enc ((σ.1 ++ [⟨.inl q, u⟩], σ.2.cacheQuery (.inl (q.1, enc (hashCacheOf σ.1) q.2)) u) :
      IdealState S I I' O hs) where
  cached s x a hmem := by
    rcases List.mem_append.mp hmem with hmem | hmem
    · rw [snapshotAt_append_of_mem hmem]
      have ha := hI.cached s x a hmem
      have hsome : (σ.2 (.inl (s, enc (snapshotAt σ.1 (s, x)) x))).isSome := by rw [ha]; rfl
      rw [QueryCache.cacheQuery_of_ne _ _ fun heq => by rw [heq, hc] at hsome; cases hsome]
      exact ha
    · obtain ⟨s', x'⟩ := q
      simp only [List.mem_singleton, Sigma.mk.injEq, Sum.inl.injEq, Prod.mk.injEq] at hmem
      obtain ⟨⟨rfl, rfl⟩, ha⟩ := hmem
      obtain rfl := eq_of_heq ha
      rw [snapshotAt_append_fresh h, QueryCache.cacheQuery_self]
  onlyLog s y hc' := by
    by_cases hk : (Sum.inl (s, y) : (chainSpec S I' O + []ₒ).Domain) =
        .inl (q.1, enc (hashCacheOf σ.1) q.2)
    · obtain ⟨s', x'⟩ := q
      obtain ⟨rfl, rfl⟩ : s = s' ∧ y = enc (hashCacheOf σ.1) x' := by simpa using hk
      exact ⟨x', u, List.mem_append_right _ (List.mem_singleton_self _),
        by rw [snapshotAt_append_fresh h]⟩
    · rw [QueryCache.cacheQuery_of_ne _ _ hk] at hc'
      obtain ⟨x, a, hmem, hy⟩ := hI.onlyLog s y hc'
      exact ⟨x, a, List.mem_append_left _ hmem, by rw [snapshotAt_append_of_mem hmem]; exact hy⟩

/-- Every step preserves the invariant. -/
theorem preservesInv_inv {enc : hs.QueryCache → I → I'}
    (henc : ∀ T T' x x', enc T x = enc T' x' → x = x') :
    QueryImpl.PreservesInv (idealImpl (S := S) (O := O) enc) (Inv enc) := by
  intro t σ hI z hz
  rcases t with n | t
  · rw [idealImpl_run_unif, support_map] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact hI
  cases h : cacheOf σ.1 t with
  | some u =>
    rw [idealImpl_run_of_some enc h, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    exact hI
  | none =>
    rcases t with q | t
    · rw [idealImpl_run_chain_of_none h (ideal_fresh henc hI h), support_map] at hz
      obtain ⟨u, -, rfl⟩ := hz
      exact inv_chain_fresh hI h (ideal_fresh henc hI h) u
    · rw [idealImpl_run_hash_of_none enc h, support_map] at hz
      obtain ⟨u, -, rfl⟩ := hz
      exact inv_hash_fresh hI t u

/-! ### Exact simulation -/

/-- Under the invariant, each step of `idealImpl`, read on its log, is a step of `realImpl`. -/
theorem dominatedUntilBad {enc : hs.QueryCache → I → I'}
    (henc : ∀ T T' x x', enc T x = enc T' x' → x = x') :
    QueryImpl.DominatedUntilBad (idealImpl (S := S) (O := O) enc) realImpl Prod.fst (Inv enc)
      fun _ => False := by
  intro t σ hI _ Q
  rcases t with n | t
  · rw [idealImpl_run_unif, realImpl_run_unif]
    exact prEvent_map_le_of_eq _ (fun u => (u, σ)) (fun u => (u, σ.1)) Prod.fst (fun _ => False)
      (fun _ _ => rfl) Q
  cases h : cacheOf σ.1 t with
  | some u =>
    rw [idealImpl_run_of_some enc h, realImpl_run_of_some h]
    exact prEvent_pure_le_of_eq (u, σ) (u, σ.1) Prod.fst (fun _ => False) rfl Q
  | none =>
    rw [realImpl_run_of_none h]
    rcases t with q | t
    · rw [idealImpl_run_chain_of_none h (ideal_fresh henc hI h)]
      exact prEvent_map_le_of_eq ($ᵗ (S × O)) _ _ Prod.fst (fun _ => False) (fun _ _ => rfl) Q
    · rw [idealImpl_run_hash_of_none enc h]
      exact prEvent_map_le_of_eq ($ᵗ hs.Range t) _ _ Prod.fst (fun _ => False)
        (fun _ _ => rfl) Q

/-- **Exact simulation.** When the encoding determines the input whatever the hash answers, an
event of the output and log of the real run is at most the same event of the simulated run against
the ideal chain, together with `Matches`: every chain entry of the log is cached by the ideal chain
at the key the simulator forwarded it to. -/
theorem prEvent_real_le_sim {enc : hs.QueryCache → I → I'}
    (henc : ∀ T T' x x', enc T x = enc T' x' → x = x') {α : Type}
    (P : OracleComp (unifSpec + (chainSpec S I O + hs)) α)
    (E : α × QueryLog (chainSpec S I O + hs) → Prop) :
    Pr{let z ← (simulateQ realImpl P).run []}[E z] ≤
      Pr{let w ← (simulateQ (chainSpec S I' O + []ₒ).romImpl
          ((simulateQ (bcsSim enc) P).run [])).run ∅}[E w.1 ∧ Matches enc w.1.2 w.2] := by
  have hinv := preservesInv_inv (S := S) (O := O) henc
  have h := (dominatedUntilBad (S := S) (O := O) henc).prEvent_simulateQ_run_le_map_or_bad hinv
    (fun _ _ h _ _ => h) P ([], ∅) (inv_init enc) E
  rw [run_simulateQ_bcsSim, prEvent_map]
  refine h.trans (prEvent_mono_of_support _ _ _ fun z hz hE => ?_)
  exact ⟨hE.resolve_right id,
    (simulateQ_run_preservesInv _ _ hinv P _ (inv_init enc) z hz).cached⟩

end Interaction.Oracle.Security.Bcs
