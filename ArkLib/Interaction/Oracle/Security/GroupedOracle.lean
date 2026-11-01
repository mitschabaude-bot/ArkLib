/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.Interaction.Oracle.Security.HashChainEncoded

/-!
# A random oracle read in groups

Let the points `A` of a random oracle with answers `R` be in bijection `e : A ≃ B × Fin m` with
groups `B` of `m` points each. The grouped oracle `B →ₒ (Fin m → R)` answers a whole group at
once, a uniform function on its `m` points. A program against the oracle on `A` runs against the
grouped oracle by reading each point's answer off its group's (`ungroup e`), and its output has the
same distribution (`evalDist_run'_ungroup`): a group's answers are independent uniform values
whether they are drawn one by one or together.

## Proof

A query to the lazy random oracle commutes with any program against it
(`evalDist_run_query_bind_swap`), so a query whose answer is discarded does not change a run's
output (`evalDist_run'_query_bind_discard`). Hence the program that answers each point after
querying every point of its group (`prefetch e`) has the same output as the program itself. Its
caches hold every group whole or not at all, the caches of the grouped oracle read point by point
(`flatten e`), and its step at an uncached group draws the group's `m` answers one by one, a
uniform function on `Fin m`, which is the grouped oracle's step.
-/

@[expose] public section

open OracleComp OracleSpec MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Interaction.Oracle.Security.HashChain

section Commute

variable {ι : Type} [DecidableEq ι] {hs : OracleSpec ι} [∀ t, SampleableType (hs.Range t)]

/-- Two queries to the lazy random oracle commute: their answers and the final cache have the
same joint distribution in either order. -/
theorem evalDist_romImpl_run_bind_run_swap {γ : Type} [MeasurableSpace γ] (t t' : ι)
    (c : hs.QueryCache) (f : hs.Range t → hs.Range t' → hs.QueryCache → ProbComp γ) :
    𝒟[(hs.romImpl (.inr t)).run c >>= fun z =>
        (hs.romImpl (.inr t')).run z.2 >>= fun y => f z.1 y.1 y.2] =
      𝒟[(hs.romImpl (.inr t')).run c >>= fun y =>
        (hs.romImpl (.inr t)).run y.2 >>= fun z => f z.1 y.1 z.2] := by
  have hit : ∀ {t : ι} {c : hs.QueryCache} {z}, z ∈ support ((hs.romImpl (.inr t)).run c) →
      (hs.romImpl (.inr t)).run z.2 = pure z := fun {t c z} hz =>
    romImpl_run_of_some (romImpl_step_inr t c z hz)
  have keep : ∀ {t t' : ι} {c : hs.QueryCache} {v : hs.Range t'} {z},
      z ∈ support ((hs.romImpl (.inr t)).run c) → c t' = some v →
      (hs.romImpl (.inr t')).run z.2 = pure (v, z.2) := fun {t t' c v z} hz hv =>
    romImpl_run_of_some (romImpl_step_le (.inr t) c z hz t' v hv)
  by_cases htt : t = t'
  · subst htt
    calc _ = 𝒟[(hs.romImpl (.inr t)).run c >>= fun z => f z.1 z.1 z.2] :=
          evalDist_bind_congr_of_support _ _ _ fun z hz => by rw [hit hz, pure_bind]
      _ = _ := evalDist_bind_congr_of_support _ _ _ fun z hz => by rw [hit hz, pure_bind]
  cases ht : c t with
  | some v =>
    calc _ = 𝒟[(hs.romImpl (.inr t')).run c >>= fun y => f v y.1 y.2] := by
          rw [romImpl_run_of_some ht, pure_bind]
      _ = _ := evalDist_bind_congr_of_support _ _ _ fun z hz => by rw [keep hz ht, pure_bind]
  | none =>
    cases ht' : c t' with
    | some v' =>
      calc _ = 𝒟[(hs.romImpl (.inr t)).run c >>= fun z => f z.1 v' z.2] :=
            evalDist_bind_congr_of_support _ _ _ fun z hz => by rw [keep hz ht', pure_bind]
        _ = _ := by rw [romImpl_run_of_some ht', pure_bind]
    | none =>
      have h₁ : ∀ u, (c.cacheQuery t u) t' = none := fun u =>
        (QueryCache.cacheQuery_of_ne _ _ (Ne.symm htt)).trans ht'
      have h₂ : ∀ u', (c.cacheQuery t' u') t = none := fun u' =>
        (QueryCache.cacheQuery_of_ne _ _ htt).trans ht
      simp only [romImpl_run_of_none ht, romImpl_run_of_none ht', romImpl_run_of_none (h₁ _),
        romImpl_run_of_none (h₂ _), bind_map_left]
      rw [OracleComp.evalDist_bind_bind_swap]
      simp only [QueryCache.cacheQuery_comm _ htt]

/-- A query to the lazy random oracle commutes with any program run against it: the answer, the
program's output and the final cache have the same joint distribution in either order. -/
theorem evalDist_run_query_bind_swap {α γ : Type} [MeasurableSpace γ] (t : ι)
    (P : OracleComp (unifSpec + hs) α) (c : hs.QueryCache)
    (f : hs.Range t → α → hs.QueryCache → ProbComp γ) :
    𝒟[(hs.romImpl (.inr t)).run c >>= fun z =>
        (simulateQ hs.romImpl P).run z.2 >>= fun w => f z.1 w.1 w.2] =
      𝒟[(simulateQ hs.romImpl P).run c >>= fun w =>
        (hs.romImpl (.inr t)).run w.2 >>= fun z => f z.1 w.1 z.2] := by
  induction P using OracleComp.inductionOn generalizing c with
  | pure a => simp only [simulateQ_pure, StateT.run_pure, pure_bind]
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
    rcases q with n | t'
    · simp only [romImpl_run_unif, bind_map_left]
      calc _ = 𝒟[HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) n >>= fun u =>
            (hs.romImpl (.inr t)).run c >>= fun z =>
              (simulateQ hs.romImpl (k u)).run z.2 >>= fun w => f z.1 w.1 w.2] :=
            OracleComp.evalDist_bind_bind_swap _ _ _
        _ = _ := evalDist_bind_congr_of_support _ _ _ fun u _ => ih u c
    · rw [evalDist_romImpl_run_bind_run_swap t t' c fun u u' c =>
        (simulateQ hs.romImpl (k u')).run c >>= fun w => f u w.1 w.2]
      exact evalDist_bind_congr_of_support _ _ _ fun y _ => ih y.1 y.2

/-- A query to the lazy random oracle whose answer is discarded does not change the output
distribution of the program run after it. -/
theorem evalDist_run'_query_bind_discard {α : Type} [MeasurableSpace α] (t : ι)
    (X : OracleComp (unifSpec + hs) α) (c : hs.QueryCache) :
    𝒟[(simulateQ hs.romImpl
        (liftM ((unifSpec + hs).query (.inr t)) >>= fun _ => X)).run' c] =
      𝒟[(simulateQ hs.romImpl X).run' c] := by
  simp only [StateT.run'_eq, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc,
    ← bind_pure_comp]
  rw [evalDist_run_query_bind_swap t X c fun _ a _ => pure a]
  exact (evalDist_bind_congr_of_support _ _ _ fun w _ => OracleComp.evalDist_bind_const _ _)

/-- Programs with continuations of equal output distribution from every cache have equal output
distributions. -/
theorem evalDist_run'_bind_congr {α β : Type} [MeasurableSpace β]
    (P : OracleComp (unifSpec + hs) α) {K K' : α → OracleComp (unifSpec + hs) β}
    (h : ∀ a c, 𝒟[(simulateQ hs.romImpl (K a)).run' c] = 𝒟[(simulateQ hs.romImpl (K' a)).run' c])
    (c : hs.QueryCache) :
    𝒟[(simulateQ hs.romImpl (P >>= K)).run' c] = 𝒟[(simulateQ hs.romImpl (P >>= K')).run' c] := by
  simp only [StateT.run'_eq, simulateQ_bind, StateT.run_bind, map_bind]
  exact evalDist_bind_congr_of_support _ _ _ fun z _ => h z.1 z.2

end Commute

variable {A B R : Type} {m : ℕ} [DecidableEq A] [DecidableEq B] [SampleableType R]

/-- Answer a point from the grouped oracle: the component `(e a).2` of the answer at its group
`(e a).1`. Private coins pass through. -/
def ungroup (e : A ≃ B × Fin m) :
    QueryImpl (unifSpec + (A →ₒ R)) (OracleComp (unifSpec + (B →ₒ (Fin m → R))))
  | .inl n => liftM ((unifSpec + (B →ₒ (Fin m → R))).query (.inl n))
  | .inr a => (fun g => g (e a).2) <$>
      liftM ((unifSpec + (B →ₒ (Fin m → R))).query (.inr (e a).1))

/-- Query the oracle on `A` at the points `pts` in order, returning their answers. -/
def queryRow : {n : ℕ} → (Fin n → A) → OracleComp (unifSpec + (A →ₒ R)) (Fin n → R)
  | 0, _ => pure Fin.elim0
  | _ + 1, pts => do
    let u ← liftM ((unifSpec + (A →ₒ R)).query (.inr (pts 0)))
    let r ← queryRow (Fin.tail pts)
    pure (Fin.cons u r)

/-- Answer a point after querying every point of its group, in order. Private coins pass
through. -/
def prefetch (e : A ≃ B × Fin m) :
    QueryImpl (unifSpec + (A →ₒ R)) (OracleComp (unifSpec + (A →ₒ R)))
  | .inl n => liftM ((unifSpec + (A →ₒ R)).query (.inl n))
  | .inr a => (fun g => g (e a).2) <$> queryRow (R := R) fun j => e.symm ((e a).1, j)

/-- A cache of the grouped oracle, read point by point. -/
def flatten (e : A ≃ B × Fin m) (d : (B →ₒ (Fin m → R)).QueryCache) : (A →ₒ R).QueryCache :=
  QueryCache.ofFn fun a => (d (e a).1).map fun g => g (e a).2

/-- The cache after caching the answers `g` at the points `pts`, in order. -/
def writeRow : {n : ℕ} → (Fin n → A) → (Fin n → R) → (A →ₒ R).QueryCache →
    (A →ₒ R).QueryCache
  | 0, _, _, c => c
  | _ + 1, pts, g, c => writeRow (Fin.tail pts) (Fin.tail g) (c.cacheQuery (pts 0) (g 0))

/-- Draw `n` independent uniform values, in order. -/
def drawRow : (n : ℕ) → ProbComp (Fin n → R)
  | 0 => pure Fin.elim0
  | n + 1 => Fin.cons <$> ($ᵗ R) <*> drawRow n

/-- A row of queries whose answers are discarded does not change the output distribution of the
program run after it. -/
theorem evalDist_run'_queryRow_bind_discard {n : ℕ} {β : Type}
    [MeasurableSpace β] (pts : Fin n → A) (X : OracleComp (unifSpec + (A →ₒ R)) β)
    (c : (A →ₒ R).QueryCache) :
    𝒟[(simulateQ (A →ₒ R).romImpl (queryRow pts >>= fun _ => X)).run' c] =
      𝒟[(simulateQ (A →ₒ R).romImpl X).run' c] := by
  induction n generalizing c with
  | zero => simp only [queryRow, pure_bind]
  | succ n ih =>
    simp only [queryRow, bind_assoc, pure_bind]
    rw [evalDist_run'_query_bind_discard]
    exact ih _ c

/-- Reading one answer off a row of queries has the output of querying that point alone. -/
theorem evalDist_run'_queryRow_bind {n : ℕ} {β : Type}
    [MeasurableSpace β] (pts : Fin n → A) (i : Fin n) (K : R → OracleComp (unifSpec + (A →ₒ R)) β)
    (c : (A →ₒ R).QueryCache) :
    𝒟[(simulateQ (A →ₒ R).romImpl (queryRow pts >>= fun g => K (g i))).run' c] =
      𝒟[(simulateQ (A →ₒ R).romImpl
        (liftM ((unifSpec + (A →ₒ R)).query (.inr (pts i))) >>= K)).run' c] := by
  induction n generalizing c with
  | zero => exact i.elim0
  | succ n ih =>
    simp only [queryRow, bind_assoc, pure_bind]
    induction i using Fin.cases with
    | zero =>
      simp only [Fin.cons_zero]
      exact evalDist_run'_bind_congr _ (fun u c =>
        evalDist_run'_queryRow_bind_discard (Fin.tail pts) (K u) c) c
    | succ i =>
      simp only [Fin.cons_succ]
      rw [evalDist_run'_query_bind_discard]
      exact ih (Fin.tail pts) i c

omit [DecidableEq B] in
/-- Prefetching every group leaves a program's output distribution unchanged. -/
theorem evalDist_run'_prefetch (e : A ≃ B × Fin m) {α : Type} [MeasurableSpace α]
    (P : OracleComp (unifSpec + (A →ₒ R)) α) (c : (A →ₒ R).QueryCache) :
    𝒟[(simulateQ (A →ₒ R).romImpl (simulateQ (prefetch e) P)).run' c] =
      𝒟[(simulateQ (A →ₒ R).romImpl P).run' c] := by
  induction P using OracleComp.inductionOn generalizing c with
  | pure a => simp only [simulateQ_pure]
  | query_bind q k ih =>
    rw [simulateQ_bind, simulateQ_spec_query,
      evalDist_run'_bind_congr _ (fun u c => ih u c) c]
    rcases q with n | a
    · rfl
    · simp only [prefetch, bind_map_left]
      have ha : e.symm ((e a).1, (e a).2) = a := by simp
      rw [evalDist_run'_queryRow_bind _ (e a).2, ha]

/-- A row of cached points is answered from the cache. -/
theorem queryRow_run_of_cached {n : ℕ} (pts : Fin n → A) (g : Fin n → R)
    (c : (A →ₒ R).QueryCache) (h : ∀ i, c (pts i) = some (g i)) :
    (simulateQ (A →ₒ R).romImpl (queryRow pts)).run c = pure (g, c) := by
  induction n with
  | zero =>
    simp only [queryRow, simulateQ_pure, StateT.run_pure]
    congr 2
    funext i
    exact i.elim0
  | succ n ih =>
    simp only [queryRow, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind,
      StateT.run_pure]
    rw [romImpl_run_of_some (h 0), pure_bind, ih (Fin.tail pts) (Fin.tail g) fun i => h i.succ,
      pure_bind, Fin.cons_self_tail]

omit [SampleableType R] in
/-- Writing a row leaves the points off the row unchanged. -/
theorem writeRow_apply_of_forall_ne {n : ℕ} (pts : Fin n → A) (g : Fin n → R)
    (c : (A →ₒ R).QueryCache) (a : A) (h : ∀ i, pts i ≠ a) : writeRow pts g c a = c a := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [writeRow, ih (Fin.tail pts) (Fin.tail g) _ fun i => h i.succ,
      QueryCache.cacheQuery_of_ne _ _ (h 0).symm]

omit [SampleableType R] in
/-- Writing a row of distinct points caches its answers. -/
theorem writeRow_apply {n : ℕ} (pts : Fin n → A) (hinj : Function.Injective pts) (g : Fin n → R)
    (c : (A →ₒ R).QueryCache) (i : Fin n) : writeRow pts g c (pts i) = some (g i) := by
  induction n generalizing c with
  | zero => exact i.elim0
  | succ n ih =>
    rw [writeRow]
    induction i using Fin.cases with
    | zero =>
      rw [writeRow_apply_of_forall_ne (Fin.tail pts) _ _ _ fun i h => Fin.succ_ne_zero i (hinj h),
        QueryCache.cacheQuery_self]
    | succ i => exact ih (Fin.tail pts) (hinj.comp (Fin.succ_injective _)) (Fin.tail g) _ i

/-- A row of fresh distinct points draws its answers independently and caches them. -/
theorem queryRow_run_of_fresh {n : ℕ} (pts : Fin n → A) (hinj : Function.Injective pts)
    (c : (A →ₒ R).QueryCache) (h : ∀ i, c (pts i) = none) :
    (simulateQ (A →ₒ R).romImpl (queryRow pts)).run c =
      (fun g => (g, writeRow pts g c)) <$> drawRow n := by
  induction n generalizing c with
  | zero =>
    simp only [queryRow, drawRow, writeRow, simulateQ_pure, StateT.run_pure, map_pure]
  | succ n ih =>
    have h' : ∀ u i, (c.cacheQuery (pts 0) u) (Fin.tail pts i) = none := fun u i =>
      (QueryCache.cacheQuery_of_ne _ _ fun h => Fin.succ_ne_zero i (hinj h)).trans (h i.succ)
    simp only [queryRow, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind,
      StateT.run_pure, romImpl_run_of_none (h 0), bind_map_left,
      ih (Fin.tail pts) (hinj.comp (Fin.succ_injective _)) _ (h' _)]
    simp only [drawRow, writeRow, seq_eq_bind_map, map_bind, bind_map_left, Functor.map_map,
      Fin.tail_cons, Fin.cons_zero, bind_pure_comp]

omit [SampleableType R] in
/-- Writing a group's row into a flattened cache is flattening the cache with the group
cached. -/
theorem writeRow_flatten (e : A ≃ B × Fin m) (b : B) (g : Fin m → R)
    (d : (B →ₒ (Fin m → R)).QueryCache) :
    writeRow (fun j => e.symm (b, j)) g (flatten e d) = flatten e (d.cacheQuery b g) := by
  have hinj : Function.Injective fun j => e.symm (b, j) := fun j j' h => by simpa using h
  refine QueryCache.ext fun a => ?_
  by_cases hb : (e a).1 = b
  · have ha : e.symm (b, (e a).2) = a := by rw [← hb]; simp
    calc writeRow _ g (flatten e d) a = writeRow _ g (flatten e d) (e.symm (b, (e a).2)) := by
          rw [ha]
      _ = some (g (e a).2) := writeRow_apply _ hinj g _ (e a).2
      _ = ((d.cacheQuery b g) (e a).1).map fun g => g (e a).2 := by
        rw [hb, QueryCache.cacheQuery_self, Option.map_some]
  · rw [writeRow_apply_of_forall_ne _ _ _ _ fun j h => hb (by simp [← h])]
    simp [flatten, QueryCache.cacheQuery_of_ne _ _ hb]

/-- Drawing `n` values one by one is uniform on `Fin n → R`. -/
theorem evalDist_drawRow (n : ℕ) :
    ∀ [MeasurableSpace (Fin n → R)] [MeasurableSingletonClass (Fin n → R)],
      𝒟[drawRow n] = (uniformOn Set.univ : Measure (Fin n → R)) := by
  induction n with
  | zero =>
    intro _ _
    apply Measure.ext_of_singleton
    intro x
    rw [drawRow, evalDist_pure, Subsingleton.elim (Fin.elim0 : Fin 0 → R) x,
      uniformOn_univ_apply_singleton]
    simp
  | succ n ih =>
    intro _ _
    let : MeasurableSpace R := ⊤
    let : MeasurableSpace (Fin n → R) := ⊤
    have hbij : Function.Bijective
        (Function.uncurry (Fin.cons (α := fun _ => R) : R → (Fin n → R) → Fin (n + 1) → R)) :=
      ⟨fun x y h => Prod.ext (Fin.cons_injective2 h).1 (Fin.cons_injective2 h).2,
        fun x => ⟨(x 0, Fin.tail x), Fin.cons_self_tail x⟩⟩
    exact evalDist_seq_map_eq_uniformOn ($ᵗ R) (drawRow n) _
      SampleableType.evalDist_uniformSample ih Measurable.of_discrete hbij

/-- Drawing `n` values one by one has the distribution of a uniform function on `Fin n`. -/
theorem evalDist_drawRow_bind {n : ℕ} {γ : Type} [MeasurableSpace γ]
    (F : (Fin n → R) → ProbComp γ) : 𝒟[drawRow n >>= F] = 𝒟[$ᵗ (Fin n → R) >>= F] := by
  let : MeasurableSpace (Fin n → R) := ⊤
  rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete, evalDist_drawRow,
    SampleableType.evalDist_uniformSample]

/-- A program with every group prefetched, run from a flattened cache, has the output of the
program against the grouped oracle, run from the grouped cache. -/
theorem evalDist_run'_prefetch_flatten (e : A ≃ B × Fin m) {α : Type} [MeasurableSpace α]
    (P : OracleComp (unifSpec + (A →ₒ R)) α) (d : (B →ₒ (Fin m → R)).QueryCache) :
    𝒟[(simulateQ (A →ₒ R).romImpl (simulateQ (prefetch e) P)).run' (flatten e d)] =
      𝒟[(simulateQ (B →ₒ (Fin m → R)).romImpl (simulateQ (ungroup e) P)).run' d] := by
  induction P using OracleComp.inductionOn generalizing d with
  | pure a => simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind]
    rcases q with n | a
    · simp only [prefetch, ungroup, simulateQ_spec_query, romImpl_run_unif, bind_map_left]
      exact evalDist_bind_congr_of_support _ _ _ fun u _ => ih u d
    · simp only [prefetch, ungroup, simulateQ_map, simulateQ_spec_query, StateT.run_map,
        bind_map_left]
      have hinj : Function.Injective fun j => e.symm ((e a).1, j) := fun j j' h => by simpa using h
      have he : ∀ i, e (e.symm ((e a).1, i)) = ((e a).1, i) := fun i => e.apply_symm_apply _
      cases hb : d (e a).1 with
      | some g =>
        rw [queryRow_run_of_cached _ g _ fun i => by
          simp only [flatten, QueryCache.ofFn_apply]; rw [he i, hb]; rfl, romImpl_run_of_some hb,
          pure_bind, pure_bind]
        exact ih _ d
      | none =>
        rw [queryRow_run_of_fresh _ hinj _ fun i => by
          simp only [flatten, QueryCache.ofFn_apply]; rw [he i, hb]; rfl,
          romImpl_run_of_none hb, bind_map_left, bind_map_left]
        simp only [writeRow_flatten]
        rw [← evalDist_drawRow_bind]
        exact evalDist_bind_congr_of_support _ _ _ fun g _ => ih _ _

/-- A program reading the oracle on `A` has the same output against the grouped oracle, through
`ungroup e`. -/
theorem evalDist_run'_ungroup (e : A ≃ B × Fin m) {α : Type} [MeasurableSpace α]
    (P : OracleComp (unifSpec + (A →ₒ R)) α) :
    𝒟[(simulateQ (A →ₒ R).romImpl P).run' ∅] =
      𝒟[(simulateQ (B →ₒ (Fin m → R)).romImpl (simulateQ (ungroup e) P)).run' ∅] := by
  have h : flatten e (∅ : (B →ₒ (Fin m → R)).QueryCache) = ∅ := QueryCache.ext fun _ => rfl
  rw [← evalDist_run'_prefetch e, ← h]
  exact evalDist_run'_prefetch_flatten e P ∅

/-- An event of a program's output against the oracle on `A` has the same probability against
the grouped oracle. -/
theorem prEvent_run'_ungroup (e : A ≃ B × Fin m) {α : Type}
    (P : OracleComp (unifSpec + (A →ₒ R)) α) (E : α → Prop) :
    Pr{let a ← (simulateQ (A →ₒ R).romImpl P).run' ∅}[E a] =
      Pr{let a ← (simulateQ (B →ₒ (Fin m → R)).romImpl (simulateQ (ungroup e) P)).run' ∅}[E a] := by
  simp only [prEvent_def, map_eq_bind_pure_comp]
  rw [evalDist_bind_congr_left_of_forall (spec := unifSpec) (β := Prop)
    (fun {_} => evalDist_run'_ungroup e P)]

omit [DecidableEq A] [DecidableEq B] [SampleableType R] in
/-- Reading through `ungroup e` makes one grouped query per query of the oracle on `A`. -/
theorem isQueryBoundP_ungroup (e : A ≃ B × Fin m) {α : Type}
    {P : OracleComp (unifSpec + (A →ₒ R)) α} {q : ℕ}
    (hP : IsQueryBoundP P (fun t => isUnif t = false) q) :
    IsQueryBoundP (simulateQ (ungroup e) P) (fun t => isUnif t = false) q := by
  refine hP.simulateQ_of_step (fun t ht => ?_) (fun t ht => ?_)
  · rcases t with n | a
    · cases ht
    · exact (isQueryBoundP_map_iff _ _ _).mpr
        ((isQueryBoundP_query_iff _ _ _).mpr fun _ => Nat.one_pos)
  · rcases t with n | a
    · exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [isUnif])
    · exact absurd rfl ht

end Interaction.Oracle.Security.HashChain
