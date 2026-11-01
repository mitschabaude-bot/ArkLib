/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import VCVio.OracleComp.QueryTracking.RandomOracle.FreshAnswer
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.OracleComp.SimSemantics.StateT.UntilBad
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# A hash chain is a prefix-keyed random oracle until a state collision

A *chain oracle* `H : S × I → S × O` is run as a sponge or a duplex: a query takes a state and an
input and answers a new state and an output, and each answer's state is the state of the next
query, starting from a fixed initial state `s₀`. Absorbing the inputs `x₁, …, xₙ` in turn makes
the queries `(s₀, x₁), (s₁, x₂), …`, the state `sᵢ` answered at the query before. A *prefix* of
inputs is a list, its latest input first: the query `(sᵢ, xᵢ₊₁)` belongs to the prefix
`xᵢ₊₁ :: … :: x₁ :: []`.

This file compares a program against the lazy random oracle `chainSpec S I O` with a program
against the lazy random oracle `prefixSpec S I O`, keyed by whole prefixes. Both may also query
private coins (`unifSpec`) and further independent random oracles `extra`.

* The simulator `HashChain.sim s₀` answers a chain query at a state it has seen answered to a
  prefix `p` (the initial state for `[]`) and input `x` by the prefix oracle at `x :: p`, and
  memoizes it; any other chain query, at an unknown state, is answered by a memoized private
  uniform sample. A program `A` against the chain becomes the program `HashChain.simulate s₀ A`
  against the prefix oracle.
* The two runs differ only on a *state collision or prediction* (`HashChain.Good` fails): a prefix
  answer's state equal to the initial state or to another prefix answer's state, or a state that
  was queried before it was answered. Up to `Q` chain queries this has probability at most
  `chainError S Q = Q (Q + 1) / 2 / |S|`: a prefix answer at chain query `i` (from `0`) is fresh
  and uniform, and has at most `i + 1` states to avoid, the initial one included.

Off that event the simulator's state is a *strict prefix encoding*: the chain key of a prefix,
`(state of p, x)` for `x :: p`, and the prefix a known state decodes to, are mutually inverse
(`HashChain.decode_encode`, `HashChain.encode_of_decode`, the two laws of a strict codec), the
chain's answer at an encoded key is the prefix oracle's answer at the prefix
(`HashChain.view_encode`), and the chain's answer at any other key is a private sample
(`HashChain.view_of_decode_eq_none`).

A program's output may carry anything it observed, its own log of queries and answers included,
so the bounds compare logs as well.

## Main statements

- `HashChain.prEvent_chain_le`: an event of a program's output against the chain is at most the
  same event against the prefix oracle, through the simulator, plus `chainError S Q`.
- `HashChain.prEvent_prefix_le`: the converse bound.
- `HashChain.isQueryBoundP_simulate`: the simulated program makes at most `Q` prefix queries.
- `HashChain.prEvent_bad_le`: the collision-or-prediction bound in the simulated run.
- `HashChain.decode_encode`, `HashChain.encode_of_decode`, `HashChain.view_encode`,
  `HashChain.view_of_decode_eq_none`: the prefix encoding of chain keys off a collision.
- `HashChain.chainError_le`: `chainError S Q ≤ Q² / |S|`.

## Proof

The flat ideal handler `HashChain.idealImpl` runs one simulator step against the prefix oracle;
its runs are the prefix oracle's runs of the simulated program (`HashChain.run_simulateQ_sim`). The
chain cache it stands for is `HashChain.view`: a key at a known state reads the prefix answers,
any other key the private samples. Off a collision or prediction, each ideal step, read through
`view`, is the chain oracle's step (`HashChain.dominatedUntilBad`), so
`QueryImpl.DominatedUntilBad` bounds the two runs against each other by the probability of `¬Good`
in the ideal run. That probability is charged to the potential
`∑ i < m, (i + 1) / |S|` of the `m` memoized answers (`OracleComp.prEvent_and_le_of_potential`).
-/

@[expose] public section

open OracleComp OracleSpec
open scoped ENNReal

namespace Interaction.Oracle.Security.HashChain

/-- The chain oracle: a state and an input answer a new state and an output. -/
abbrev chainSpec (S I O : Type) : OracleSpec (S × I) := (S × I) →ₒ (S × O)

/-- The prefix oracle: a prefix of inputs, latest first, answers a state and an output. -/
abbrev prefixSpec (S I O : Type) : OracleSpec (List I) := List I →ₒ (S × O)

/-- The simulator's memory: the prefix answers it has drawn, and the private answers to chain
queries at unknown states, latest first. -/
structure SimState (S I O : Type) where
  prefixes : List (List I × (S × O))
  priv : List ((S × I) × (S × O))

/-- The simulator's empty memory. -/
def SimState.init {S I O : Type} : SimState S I O := ⟨[], []⟩

variable {S I O : Type}

/-- The number of memoized answers. -/
def SimState.size (st : SimState S I O) : ℕ := st.prefixes.length + st.priv.length

/-- The collision-or-prediction bound of `Q` chain queries: `Q (Q + 1) / 2` over the number of
states. -/
noncomputable def chainError (S : Type) (Q : ℕ) : ℝ≥0∞ :=
  ((Q * (Q + 1) / 2 : ℕ) : ℝ≥0∞) / Nat.card S

/-- The potential of `m` memoized answers: `∑ i < m, (i + 1)` over the number of states. -/
noncomputable def potential (S : Type) (m : ℕ) : ℝ≥0∞ :=
  ((∑ i ∈ Finset.range m, (i + 1) : ℕ) : ℝ≥0∞) / Nat.card S

theorem potential_zero (S : Type) : potential S 0 = 0 := by
  simp [potential]

theorem potential_succ (S : Type) (m : ℕ) :
    potential S (m + 1) = ((m + 1 : ℕ) : ℝ≥0∞) / Nat.card S + potential S m := by
  rw [potential, potential, Finset.sum_range_succ, Nat.cast_add, ENNReal.add_div, add_comm]

theorem potential_mono (S : Type) : Monotone (potential S) := fun a b h => by
  unfold potential
  gcongr

theorem potential_eq_chainError (S : Type) (Q : ℕ) : potential S Q = chainError S Q := by
  have h := Finset.sum_range_id_mul_two (Q + 1)
  rw [Finset.sum_range_succ'] at h
  simp only [add_zero, Nat.add_sub_cancel] at h
  rw [potential, chainError, Nat.div_eq_of_eq_mul_left (by norm_num) (by rw [h]; ring)]

theorem chainError_le (S : Type) (Q : ℕ) : chainError S Q ≤ ((Q ^ 2 : ℕ) : ℝ≥0∞) / Nat.card S := by
  unfold chainError
  gcongr
  calc Q * (Q + 1) / 2 ≤ Q * (Q + 1) / 2 + Q * (Q - 1) / 2 := Nat.le_add_right _ _
    _ ≤ (Q * (Q + 1) + Q * (Q - 1)) / 2 := Nat.div_add_div_le_add_div
    _ = Q ^ 2 := by
      rcases Q with _ | Q
      · rfl
      · rw [Nat.add_sub_cancel, show (Q + 1) * (Q + 1 + 1) + (Q + 1) * Q = (Q + 1) ^ 2 * 2 by
          ring, Nat.mul_div_cancel _ (by norm_num)]

/-- A uniform state lands in a list of states with probability at most its length over `|S|`. -/
theorem prEvent_fst_mem_le [SampleableType S] [SampleableType O] (L : List S) :
    Pr{let v ← ($ᵗ (S × O) : ProbComp (S × O))}[v.1 ∈ L] ≤ (L.length : ℝ≥0∞) / Nat.card S := by
  classical
  let := Fintype.ofFinite S
  let := Fintype.ofFinite O
  rw [SampleableType.prEvent_uniformSample, Fintype.card_prod, Nat.card_eq_fintype_card]
  have hc : (Finset.univ.filter fun v : S × O => v.1 ∈ L).card ≤ L.length * Fintype.card O := by
    calc _ ≤ (L.toFinset ×ˢ (Finset.univ : Finset O)).card :=
          Finset.card_le_card fun v hv => by simpa using hv
      _ = L.toFinset.card * Fintype.card O := by rw [Finset.card_product, Finset.card_univ]
      _ ≤ _ := Nat.mul_le_mul_right _ (List.toFinset_card_le L)
  have hO : (Fintype.card O : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc _ ≤ ((L.length * Fintype.card O : ℕ) : ℝ≥0∞) / ((Fintype.card S * Fintype.card O : ℕ)) := by
        push_cast
        gcongr
        exact_mod_cast hc
    _ = _ := by
      push_cast
      exact ENNReal.mul_div_mul_right _ _ hO (ENNReal.natCast_ne_top _)

/-! ### Known prefixes -/

/-- A run is *good* when no prefix answer's state is the initial state or another prefix answer's
state, and no private answer is at a state a prefix answer later took. -/
structure Good (s₀ : S) (st : SimState S I O) : Prop where
  ne_init : ∀ e ∈ st.prefixes, e.2.1 ≠ s₀
  nodup : (st.prefixes.map fun e => e.2.1).Nodup
  unpredicted : ∀ e ∈ st.prefixes, ∀ r ∈ st.priv, r.1.1 ≠ e.2.1

theorem Good.of_cons_prefixes {s₀ : S} {e : List I × (S × O)} {P : List (List I × (S × O))}
    {R : List ((S × I) × (S × O))} (h : Good s₀ ⟨e :: P, R⟩) : Good s₀ ⟨P, R⟩ where
  ne_init e' he' := h.ne_init e' (List.mem_cons_of_mem _ he')
  nodup := (List.nodup_cons.mp h.nodup).2
  unpredicted e' he' := h.unpredicted e' (List.mem_cons_of_mem _ he')

theorem Good.of_cons_priv {s₀ : S} {P : List (List I × (S × O))} {r : (S × I) × (S × O)}
    {R : List ((S × I) × (S × O))} (h : Good s₀ ⟨P, r :: R⟩) : Good s₀ ⟨P, R⟩ where
  ne_init := h.ne_init
  nodup := h.nodup
  unpredicted e he r' hr' := h.unpredicted e he r' (List.mem_cons_of_mem _ hr')

/-- The prefix memory's structure: the keys are distinct and nonempty, and each key's parent is a
key or `[]`. -/
structure WellFormed (P : List (List I × (S × O))) : Prop where
  ne_nil : ∀ e ∈ P, e.1 ≠ []
  parent : ∀ e ∈ P, e.1.tail = [] ∨ ∃ e' ∈ P, e'.1 = e.1.tail
  nodup : (P.map Prod.fst).Nodup

section Known

variable [DecidableEq S]

/-- The prefix a state is known for: `[]` for the initial state, otherwise the prefix of the
latest prefix answer with that state. -/
def knownPrefix (s₀ : S) (P : List (List I × (S × O))) (s : S) : Option (List I) :=
  if s = s₀ then some [] else (P.find? fun e => decide (e.2.1 = s)).map Prod.fst

theorem knownPrefix_eq_none_iff {s₀ s : S} {P : List (List I × (S × O))} :
    knownPrefix s₀ P s = none ↔ s ≠ s₀ ∧ ∀ e ∈ P, e.2.1 ≠ s := by
  unfold knownPrefix
  split_ifs with h
  · simp [h]
  · simp [h, List.find?_eq_none]

theorem knownPrefix_eq_some {s₀ s : S} {P : List (List I × (S × O))} {p : List I}
    (h : knownPrefix s₀ P s = some p) :
    (s = s₀ ∧ p = []) ∨ (s ≠ s₀ ∧ ∃ v, (p, v) ∈ P ∧ v.1 = s) := by
  unfold knownPrefix at h
  split_ifs at h with hs
  · exact .inl ⟨hs, (Option.some.inj h).symm⟩
  · right
    refine ⟨hs, ?_⟩
    obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨e.2, List.mem_of_find?_eq_some he, by simpa using List.find?_some he⟩

theorem knownPrefix_cons_of_ne {s₀ s : S} {e : List I × (S × O)} {P : List (List I × (S × O))}
    (h : e.2.1 ≠ s) : knownPrefix s₀ (e :: P) s = knownPrefix s₀ P s := by
  unfold knownPrefix
  simp [h]

theorem knownPrefix_cons_self {s₀ : S} {k : List I} {v : S × O} {P : List (List I × (S × O))}
    (h : v.1 ≠ s₀) : knownPrefix s₀ ((k, v) :: P) v.1 = some k := by
  unfold knownPrefix
  simp [h]

/-- In a well-formed memory, a prefix is known for at most one state. -/
theorem eq_of_knownPrefix {s₀ s s' : S} {P : List (List I × (S × O))} {p : List I}
    (hP : WellFormed P) (h : knownPrefix s₀ P s = some p) (h' : knownPrefix s₀ P s' = some p) :
    s = s' := by
  rcases knownPrefix_eq_some h with ⟨rfl, rfl⟩ | ⟨-, v, hv, rfl⟩ <;>
    rcases knownPrefix_eq_some h' with ⟨rfl, hp⟩ | ⟨-, v', hv', rfl⟩
  · rfl
  · exact absurd rfl (hP.ne_nil _ hv')
  · exact absurd hp (hP.ne_nil _ hv)
  · have := List.inj_on_of_nodup_map hP.nodup hv hv' rfl
    simp only [Prod.mk.injEq, true_and] at this
    rw [this]

end Known

section Lookup

variable [DecidableEq I]

/-- The value of the latest entry at a key. -/
def findVal {α β : Type} [DecidableEq α] (l : List (α × β)) (k : α) : Option β :=
  (l.find? fun e => decide (e.1 = k)).map Prod.snd

@[simp] theorem findVal_nil {α β : Type} [DecidableEq α] (k : α) :
    findVal ([] : List (α × β)) k = none := rfl

theorem findVal_cons {α β : Type} [DecidableEq α] (k k' : α) (v : β) (l : List (α × β)) :
    findVal ((k, v) :: l) k' = if k = k' then some v else findVal l k' := by
  unfold findVal
  by_cases h : k = k' <;> simp [h]

@[simp] theorem findVal_cons_self {α β : Type} [DecidableEq α] (k : α) (v : β)
    (l : List (α × β)) : findVal ((k, v) :: l) k = some v := by
  simp [findVal_cons]

theorem findVal_cons_of_ne {α β : Type} [DecidableEq α] {k k' : α} {v : β} {l : List (α × β)}
    (h : k ≠ k') : findVal ((k, v) :: l) k' = findVal l k' := by
  simp [findVal_cons, h]

theorem findVal_eq_none_iff {α β : Type} [DecidableEq α] {l : List (α × β)} {k : α} :
    findVal l k = none ↔ ∀ e ∈ l, e.1 ≠ k := by
  simp [findVal, List.find?_eq_none]

theorem mem_of_findVal_eq_some {α β : Type} [DecidableEq α] {l : List (α × β)} {k : α} {v : β}
    (h : findVal l k = some v) : (k, v) ∈ l := by
  unfold findVal at h
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
  have hk : e.1 = k := by simpa using List.find?_some he
  rw [← hk]
  exact List.mem_of_find?_eq_some he

/-- A key whose parent is no key is no key, in a well-formed memory. -/
theorem findVal_cons_eq_none {P : List (List I × (S × O))} (hP : WellFormed P) {k : List I}
    (hk : k ≠ []) (hnone : findVal P k = none) (x : I) : findVal P (x :: k) = none := by
  rw [findVal_eq_none_iff] at hnone ⊢
  intro e he hek
  rcases hP.parent e he with h | ⟨e', he', h⟩
  · rw [hek] at h
    exact hk h
  · rw [hek] at h
    exact hnone e' he' h

end Lookup

section View

variable [DecidableEq S] [DecidableEq I] {ι : Type} {extra : OracleSpec ι}

/-- The state of the simulated run: the simulator's memory and the prefix oracle's cache. -/
abbrev IdealState (S I O : Type) (extra : OracleSpec ι) :=
  SimState S I O × (prefixSpec S I O + extra).QueryCache

/-! ### The chain cache of a simulated run -/

/-- The invariant of the simulated run: the prefix oracle's cache holds exactly the prefix memory,
and the memory is well formed. -/
structure Inv (σ : IdealState S I O extra) : Prop where
  cache : ∀ k, σ.2 (.inl k) = findVal σ.1.prefixes k
  wf : WellFormed σ.1.prefixes

omit [DecidableEq S] in
theorem inv_init : Inv ((SimState.init, ∅) : IdealState S I O extra) where
  cache _ := rfl
  wf := ⟨by simp [SimState.init], by simp [SimState.init], by simp [SimState.init]⟩

/-- The chain cache a simulated run stands for: a chain key at a known state reads the prefix
memory, any other chain key the private memory, and the extra oracles their cache. -/
def view (s₀ : S) (σ : IdealState S I O extra) : (chainSpec S I O + extra).QueryCache :=
  QueryCache.ofFn fun t => match t with
    | .inl q => match knownPrefix s₀ σ.1.prefixes q.1 with
      | some p => findVal σ.1.prefixes (q.2 :: p)
      | none => findVal σ.1.priv q
    | .inr t => σ.2 (.inr t)

theorem view_inl_of_known {s₀ : S} {σ : IdealState S I O extra} {q : S × I} {p : List I}
    (hp : knownPrefix s₀ σ.1.prefixes q.1 = some p) :
    view s₀ σ (.inl q) = findVal σ.1.prefixes (q.2 :: p) := by
  simp [view, hp]

theorem view_inl_of_unknown {s₀ : S} {σ : IdealState S I O extra} {q : S × I}
    (hp : knownPrefix s₀ σ.1.prefixes q.1 = none) : view s₀ σ (.inl q) = findVal σ.1.priv q := by
  simp [view, hp]

@[simp] theorem view_inr (s₀ : S) (σ : IdealState S I O extra) (t : ι) :
    view s₀ σ (.inr t) = σ.2 (.inr t) := rfl

theorem view_init (s₀ : S) : view s₀ ((SimState.init, ∅) : IdealState S I O extra) = ∅ := by
  refine QueryCache.ext fun t => ?_
  rcases t with q | t
  · by_cases h : knownPrefix s₀ ([] : List (List I × (S × O))) q.1 = none
    · simp [view, SimState.init, h]
    · obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.mp h
      simp [view, SimState.init, hp]
  · rfl

theorem view_extra [DecidableEq ι] (s₀ : S) (σ : IdealState S I O extra) (t : ι)
    (u : extra.Range t) :
    view s₀ (σ.1, σ.2.cacheQuery (.inr t) u) = (view s₀ σ).cacheQuery (.inr t) u := by
  ext t'
  rcases t' with q | t'
  · rw [QueryCache.cacheQuery_of_ne _ _ (by simp)]
    rfl
  · by_cases h : t' = t
    · subst h
      simp
    · rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using h), view_inr, view_inr,
        QueryCache.cacheQuery_of_ne _ _ (by simpa using h)]

theorem view_unknown_fresh [DecidableEq ι] {s₀ : S} {σ : IdealState S I O extra} {q : S × I}
    (v : S × O)
    (hp : knownPrefix s₀ σ.1.prefixes q.1 = none) :
    view s₀ (⟨σ.1.prefixes, (q, v) :: σ.1.priv⟩, σ.2) = (view s₀ σ).cacheQuery (.inl q) v := by
  refine QueryCache.ext fun t => ?_
  rcases t with q' | t
  · by_cases h : q' = q
    · subst h
      simp [view, hp]
    · rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using h)]
      cases hp' : knownPrefix s₀ σ.1.prefixes q'.1 with
      | none => simp [view, hp', findVal_cons_of_ne (Ne.symm h)]
      | some p => simp [view, hp']
  · rfl

theorem view_known_fresh [DecidableEq ι] {s₀ : S} {σ : IdealState S I O extra} {q : S × I}
    {p : List I}
    {v : S × O} (hI : Inv σ) (hp : knownPrefix s₀ σ.1.prefixes q.1 = some p)
    (hv : findVal σ.1.prefixes (q.2 :: p) = none)
    (hG : Good s₀ ⟨(q.2 :: p, v) :: σ.1.prefixes, σ.1.priv⟩) :
    view s₀ (⟨(q.2 :: p, v) :: σ.1.prefixes, σ.1.priv⟩, σ.2.cacheQuery (.inl (q.2 :: p)) v) =
      (view s₀ σ).cacheQuery (.inl q) v := by
  have hv₀ : v.1 ≠ s₀ := hG.ne_init _ (List.mem_cons_self ..)
  have hfresh : ∀ e ∈ σ.1.prefixes, e.2.1 ≠ v.1 := by
    intro e he h
    have := hG.nodup
    rw [List.map_cons, List.nodup_cons] at this
    exact this.1 (List.mem_map.mpr ⟨e, he, h⟩)
  have hunk : knownPrefix s₀ σ.1.prefixes v.1 = none :=
    knownPrefix_eq_none_iff.mpr ⟨hv₀, hfresh⟩
  have hqv : q.1 ≠ v.1 := fun h => by rw [h, hunk] at hp; cases hp
  refine QueryCache.ext fun t => ?_
  rcases t with ⟨s₁, x₁⟩ | t
  · by_cases hs : s₁ = v.1
    · subst hs
      rw [QueryCache.cacheQuery_of_ne _ _ (by intro h; exact hqv (by cases h; rfl)),
        view_inl_of_unknown (σ := σ) hunk]
      simp only [view, QueryCache.ofFn_apply]
      rw [knownPrefix_cons_self hv₀]
      dsimp only
      rw [findVal_cons_of_ne (by simp), findVal_cons_eq_none hI.wf (by simp) hv]
      symm
      rw [findVal_eq_none_iff]
      intro r hr h
      exact hG.unpredicted _ (List.mem_cons_self ..) r hr (by rw [h])
    · simp only [view, QueryCache.ofFn_apply]
      rw [knownPrefix_cons_of_ne (Ne.symm hs)]
      cases hp₁ : knownPrefix s₀ σ.1.prefixes s₁ with
      | none =>
        have hne : (s₁, x₁) ≠ q := fun h => by
          rw [← h] at hp
          rw [hp] at hp₁
          cases hp₁
        rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using hne)]
        simp [hp₁]
      | some p₁ =>
        dsimp only
        by_cases hk : x₁ :: p₁ = q.2 :: p
        · obtain ⟨rfl, rfl⟩ := List.cons.inj hk
          have hs₁ : s₁ = q.1 := eq_of_knownPrefix hI.wf hp₁ hp
          subst hs₁
          simp
        · have hne : (s₁, x₁) ≠ q := fun h => by
            subst h
            rw [hp] at hp₁
            cases hp₁
            exact hk rfl
          rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using hne), findVal_cons_of_ne (Ne.symm hk)]
          simp [hp₁]
  · rw [view_inr, QueryCache.cacheQuery_of_ne _ _ (by simp), QueryCache.cacheQuery_of_ne _ _
      (by simp), view_inr]

/-! ### The prefix encoding of chain keys -/

/-- The state of a prefix: the initial state for `[]`, its prefix answer's state otherwise. -/
def stateOf (s₀ : S) (P : List (List I × (S × O))) : List I → Option S
  | [] => some s₀
  | k => (findVal P k).map Prod.fst

/-- The chain key of a prefix `x :: p` whose prefix `p` has a state: that state, and `x`. -/
def chainKey (s₀ : S) (P : List (List I × (S × O))) : List I → Option (S × I)
  | [] => none
  | x :: p => (stateOf s₀ P p).map (·, x)

/-- The prefix a chain key `(s, x)` decodes to: `x :: p`, for the prefix `p` known for `s`. -/
def decodeKey (s₀ : S) (P : List (List I × (S × O))) (q : S × I) : Option (List I) :=
  (knownPrefix s₀ P q.1).map (q.2 :: ·)

omit [DecidableEq S] in
theorem findVal_eq_some_of_mem {P : List (List I × (S × O))} (hP : WellFormed P) {k : List I}
    {v : S × O} (h : (k, v) ∈ P) : findVal P k = some v := by
  cases hf : findVal P k with
  | none => exact absurd rfl ((findVal_eq_none_iff.mp hf) _ h)
  | some w =>
    have := List.inj_on_of_nodup_map hP.nodup (mem_of_findVal_eq_some hf) h rfl
    simp only [Prod.mk.injEq, true_and] at this
    rw [this]

/-- **Decoding inverts encoding**, off a collision: the chain key of a prefix decodes to it. -/
theorem decode_encode {s₀ : S} {st : SimState S I O} (hG : Good s₀ st) {k : List I} {q : S × I}
    (h : chainKey s₀ st.prefixes k = some q) :
    decodeKey s₀ st.prefixes q = some k := by
  rcases k with _ | ⟨x, p⟩
  · cases h
  obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp h
  simp only [decodeKey, Option.map_eq_some_iff, List.cons.injEq, true_and, exists_eq_right]
  rcases p with _ | ⟨y, p⟩
  · cases hs
    simp [knownPrefix]
  · obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hs
    have hmem := mem_of_findVal_eq_some hv
    unfold knownPrefix
    rw [ite_eq_right_of_eq_false _ _ (eq_false (hG.ne_init _ hmem))]
    obtain ⟨e, he, he'⟩ : ∃ e, (st.prefixes.find? fun e => decide (e.2.1 = v.1)) = some e ∧
        e = (y :: p, v) := by
      cases hf : st.prefixes.find? fun e => decide (e.2.1 = v.1) with
      | none => exact absurd (List.find?_eq_none.mp hf _ hmem) (by simp)
      | some e =>
        refine ⟨e, rfl, List.inj_on_of_nodup_map hG.nodup (List.mem_of_find?_eq_some hf) hmem ?_⟩
        simpa using List.find?_some hf
    rw [he, he']
    rfl

/-- **Encoding inverts decoding**: a chain key that decodes to a prefix is its chain key. -/
theorem encode_of_decode {s₀ : S} {P : List (List I × (S × O))} (hP : WellFormed P)
    {q : S × I} {k : List I} (h : decodeKey s₀ P q = some k) : chainKey s₀ P k = some q := by
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
  rcases knownPrefix_eq_some hp with ⟨hs, rfl⟩ | ⟨-, v, hv, hvs⟩
  · simp [chainKey, stateOf, ← hs]
  · rcases p with _ | ⟨y, p⟩
    · exact absurd rfl (hP.ne_nil _ hv)
    · simp [chainKey, stateOf, findVal_eq_some_of_mem hP hv, hvs]

/-- Off a collision, the chain's answer at the chain key of a prefix is the prefix oracle's answer
at the prefix. -/
theorem view_encode {s₀ : S} {σ : IdealState S I O extra} (hI : Inv σ)
    (hG : Good s₀ σ.1) {k : List I} {q : S × I} (h : chainKey s₀ σ.1.prefixes k = some q) :
    view s₀ σ (.inl q) = σ.2 (.inl k) := by
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp (decode_encode hG h)
  rw [view_inl_of_known hp, hI.cache]

/-- The chain's answer at a key that decodes to no prefix is a private answer. -/
theorem view_of_decode_eq_none {s₀ : S} {σ : IdealState S I O extra} {q : S × I}
    (h : decodeKey s₀ σ.1.prefixes q = none) : view s₀ σ (.inl q) = findVal σ.1.priv q :=
  view_inl_of_unknown (Option.map_eq_none_iff.mp h)

end View

variable [DecidableEq S] [DecidableEq I] [SampleableType S] [SampleableType O] {ι : Type}
  {extra : OracleSpec ι}

/-- One simulator step on a chain query. -/
def simChain (s₀ : S) (q : S × I) (st : SimState S I O) :
    OracleComp (unifSpec + (prefixSpec S I O + extra)) ((S × O) × SimState S I O) :=
  match knownPrefix s₀ st.prefixes q.1 with
  | some p =>
    match findVal st.prefixes (q.2 :: p) with
    | some v => pure (v, st)
    | none => (fun v => (v, { st with prefixes := (q.2 :: p, v) :: st.prefixes })) <$>
        liftM ((unifSpec + (prefixSpec S I O + extra)).query (.inr (.inl (q.2 :: p))))
  | none =>
    match findVal st.priv q with
    | some v => pure (v, st)
    | none => (fun v => (v, { st with priv := (q, v) :: st.priv })) <$>
        (liftM ($ᵗ (S × O) : ProbComp (S × O)) :
          OracleComp (unifSpec + (prefixSpec S I O + extra)) (S × O))

/-- The simulator: private coins and the extra oracles pass through, chain queries take a
`simChain` step. -/
def sim (s₀ : S) : QueryImpl (unifSpec + (chainSpec S I O + extra))
    (StateT (SimState S I O) (OracleComp (unifSpec + (prefixSpec S I O + extra))))
  | .inl n => liftM (liftM ((unifSpec + (prefixSpec S I O + extra)).query (.inl n)) :
      OracleComp (unifSpec + (prefixSpec S I O + extra)) (Fin (n + 1)))
  | .inr (.inl q) => StateT.mk (simChain s₀ q)
  | .inr (.inr t) => liftM (liftM ((unifSpec + (prefixSpec S I O + extra)).query (.inr (.inr t))) :
      OracleComp (unifSpec + (prefixSpec S I O + extra)) (extra.Range t))

/-- A program against the chain oracle, run against the prefix oracle by the simulator. -/
def simulate (s₀ : S) {α : Type} (A : OracleComp (unifSpec + (chainSpec S I O + extra)) α) :
    OracleComp (unifSpec + (prefixSpec S I O + extra)) α :=
  (simulateQ (sim s₀) A).run' SimState.init

/-- Whether a query is a chain query. -/
def isChain {κ : Type} : ℕ ⊕ ((S × I) ⊕ κ) → Bool
  | .inr (.inl _) => true
  | _ => false

/-! ### The simulated run as one handler -/

section Ideal

variable [DecidableEq ι] [∀ t, SampleableType (extra.Range t)]

/-- One simulator step, run against the prefix oracle. -/
def idealImpl (s₀ : S) : QueryImpl (unifSpec + (chainSpec S I O + extra))
    (StateT (IdealState S I O extra) ProbComp) :=
  fun t => StateT.mk fun σ => (fun z => (z.1.1, (z.1.2, z.2))) <$>
    (simulateQ (prefixSpec S I O + extra).romImpl ((sim s₀ t).run σ.1)).run σ.2

/-- The prefix oracle's run of the simulated program is the run of `idealImpl`. -/
theorem run_simulateQ_sim (s₀ : S) {α : Type}
    (A : OracleComp (unifSpec + (chainSpec S I O + extra)) α) (st : SimState S I O)
    (c : (prefixSpec S I O + extra).QueryCache) :
    (simulateQ (prefixSpec S I O + extra).romImpl ((simulateQ (sim s₀) A).run st)).run c =
      (fun z => ((z.1, z.2.1), z.2.2)) <$> (simulateQ (idealImpl s₀) A).run (st, c) := by
  induction A using OracleComp.inductionOn generalizing st c with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, idealImpl, StateT.run_mk,
      map_bind, bind_map_left, ih]

/-- The prefix oracle's run of `simulate s₀ A`, as the run of `idealImpl`. -/
theorem run'_simulate (s₀ : S) {α : Type}
    (A : OracleComp (unifSpec + (chainSpec S I O + extra)) α) :
    (simulateQ (prefixSpec S I O + extra).romImpl (simulate s₀ A)).run' ∅ =
      Prod.fst <$> (simulateQ (idealImpl s₀) A).run (SimState.init, ∅) := by
  have h := run_simulateQ_sim s₀ A SimState.init ∅
  change Prod.fst <$> (simulateQ (prefixSpec S I O + extra).romImpl
    (Prod.fst <$> (simulateQ (sim s₀) A).run SimState.init)).run ∅ = _
  rw [simulateQ_map, StateT.run_map, h]
  simp only [Functor.map_map]

/-! ### Step shapes -/

theorem idealImpl_run_unif (s₀ : S) (n : ℕ) (σ : IdealState S I O extra) :
    (idealImpl s₀ (.inl n)).run σ =
      (fun u => (u, σ)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) n) := by
  simp [idealImpl, sim]
  rfl

theorem idealImpl_run_extra (s₀ : S) (t : ι) (σ : IdealState S I O extra) :
    (idealImpl s₀ (.inr (.inr t))).run σ =
      (fun z => (z.1, (σ.1, z.2))) <$>
        ((prefixSpec S I O + extra).randomOracle (.inr t)).run σ.2 := by
  simp [idealImpl, sim]

theorem idealImpl_run_chain (s₀ : S) (q : S × I) (σ : IdealState S I O extra) :
    (idealImpl s₀ (.inr (.inl q))).run σ = (fun z => (z.1.1, (z.1.2, z.2))) <$>
      (simulateQ (prefixSpec S I O + extra).romImpl (simChain s₀ q σ.1)).run σ.2 := by
  simp [idealImpl, sim]

theorem idealImpl_run_known_cached {s₀ : S} {q : S × I} {σ : IdealState S I O extra}
    {p : List I} {v : S × O} (hp : knownPrefix s₀ σ.1.prefixes q.1 = some p)
    (hv : findVal σ.1.prefixes (q.2 :: p) = some v) :
    (idealImpl s₀ (.inr (.inl q))).run σ = pure (v, σ) := by
  rw [idealImpl_run_chain, simChain, hp]
  simp [hv]

theorem idealImpl_run_known_fresh {s₀ : S} {q : S × I} {σ : IdealState S I O extra}
    {p : List I} (hp : knownPrefix s₀ σ.1.prefixes q.1 = some p)
    (hv : findVal σ.1.prefixes (q.2 :: p) = none) (hc : σ.2 (.inl (q.2 :: p)) = none) :
    (idealImpl s₀ (.inr (.inl q))).run σ = (fun v => (v, (⟨(q.2 :: p, v) :: σ.1.prefixes,
      σ.1.priv⟩, σ.2.cacheQuery (.inl (q.2 :: p)) v))) <$> ($ᵗ (S × O) : ProbComp (S × O)) := by
  rw [idealImpl_run_chain, simChain, hp]
  simp [hv, hc]

theorem idealImpl_run_unknown_cached {s₀ : S} {q : S × I} {σ : IdealState S I O extra}
    {v : S × O} (hp : knownPrefix s₀ σ.1.prefixes q.1 = none) (hv : findVal σ.1.priv q = some v) :
    (idealImpl s₀ (.inr (.inl q))).run σ = pure (v, σ) := by
  rw [idealImpl_run_chain, simChain, hp]
  simp [hv]

theorem idealImpl_run_unknown_fresh {s₀ : S} {q : S × I} {σ : IdealState S I O extra}
    (hp : knownPrefix s₀ σ.1.prefixes q.1 = none) (hv : findVal σ.1.priv q = none) :
    (idealImpl s₀ (.inr (.inl q))).run σ = (fun v => (v, (⟨σ.1.prefixes, (q, v) :: σ.1.priv⟩,
      σ.2))) <$> ($ᵗ (S × O) : ProbComp (S × O)) := by
  rw [idealImpl_run_chain, simChain, hp]
  simp [hv, roSim.run_liftM]

/-- A step only adds memoized answers: none off chain queries, one at most on a chain query. -/
theorem mem_support_idealImpl {s₀ : S} {t : (unifSpec + (chainSpec S I O + extra)).Domain}
    {σ : IdealState S I O extra} {z} (hz : z ∈ support ((idealImpl s₀ t).run σ)) :
    z.2.1 = σ.1 ∨ isChain t ∧ ((∃ e, z.2.1 = ⟨e :: σ.1.prefixes, σ.1.priv⟩) ∨
      ∃ r, z.2.1 = ⟨σ.1.prefixes, r :: σ.1.priv⟩) := by
  rcases t with n | q | t
  · rw [idealImpl_run_unif, support_map] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact .inl rfl
  · rw [idealImpl_run_chain, support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    unfold simChain at hw
    split at hw
    · split at hw
      · simp at hw
        simp [hw]
      · simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hw
        obtain ⟨_, -, rfl⟩ := hw
        simp [isChain]
    · split at hw
      · simp at hw
        simp [hw]
      · simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hw
        obtain ⟨_, -, rfl⟩ := hw
        simp [isChain]
  · rw [idealImpl_run_extra, support_map] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact .inl rfl


/-! ### Invariants -/

theorem mem_support_randomOracle_run {κ : Type} [DecidableEq κ] {spec : OracleSpec κ}
    [∀ t, SampleableType (spec.Range t)] (t : κ) (c : spec.QueryCache) {z}
    (hz : z ∈ support ((spec.randomOracle t).run c)) : z.2 = c ∨ z.2 = c.cacheQuery t z.1 := by
  rw [randomOracle.run_eq] at hz
  split at hz
  · simp only [support_pure, Set.mem_singleton_iff] at hz
    exact .inl (by rw [hz])
  · simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact .inr rfl

omit [SampleableType S] [SampleableType O] [∀ t, SampleableType (extra.Range t)] in
theorem inv_known_fresh {s₀ : S} {σ : IdealState S I O extra} {q : S × I} {p : List I}
    (hI : Inv σ) (hp : knownPrefix s₀ σ.1.prefixes q.1 = some p)
    (hv : findVal σ.1.prefixes (q.2 :: p) = none) (v : S × O) :
    Inv ((⟨(q.2 :: p, v) :: σ.1.prefixes, σ.1.priv⟩, σ.2.cacheQuery (.inl (q.2 :: p)) v) :
      IdealState S I O extra) where
  cache k := by
    by_cases hk : k = q.2 :: p
    · subst hk
      simp
    · rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using hk), findVal_cons_of_ne (Ne.symm hk)]
      exact hI.cache k
  wf := by
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · simp
      · exact hI.wf.ne_nil e he
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · rcases knownPrefix_eq_some hp with ⟨-, rfl⟩ | ⟨-, w, hw, -⟩
        · exact .inl rfl
        · exact .inr ⟨(p, w), List.mem_cons_of_mem _ hw, rfl⟩
      · rcases hI.wf.parent e he with h | ⟨e', he', h⟩
        · exact .inl h
        · exact .inr ⟨e', List.mem_cons_of_mem _ he', h⟩
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨fun h => ?_, hI.wf.nodup⟩
      obtain ⟨e, he, hek⟩ := List.mem_map.mp h
      exact (findVal_eq_none_iff.mp hv) e he hek

/-- Every step preserves the invariant. -/
theorem preservesInv_inv (s₀ : S) :
    QueryImpl.PreservesInv (idealImpl (I := I) (O := O) (extra := extra) s₀) Inv := by
  intro t σ hI z hz
  rcases t with n | q | t
  · rw [idealImpl_run_unif, support_map] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact hI
  · cases hp : knownPrefix s₀ σ.1.prefixes q.1 with
    | some p =>
      cases hv : findVal σ.1.prefixes (q.2 :: p) with
      | some v =>
        rw [idealImpl_run_known_cached hp hv, support_pure, Set.mem_singleton_iff] at hz
        rw [hz]
        exact hI
      | none =>
        rw [idealImpl_run_known_fresh hp hv (by rw [hI.cache]; exact hv), support_map] at hz
        obtain ⟨v, -, rfl⟩ := hz
        exact inv_known_fresh hI hp hv v
    | none =>
      cases hv : findVal σ.1.priv q with
      | some v =>
        rw [idealImpl_run_unknown_cached hp hv, support_pure, Set.mem_singleton_iff] at hz
        rw [hz]
        exact hI
      | none =>
        rw [idealImpl_run_unknown_fresh hp hv, support_map] at hz
        obtain ⟨v, -, rfl⟩ := hz
        exact ⟨hI.cache, hI.wf⟩
  · rw [idealImpl_run_extra, support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    refine ⟨fun k => ?_, hI.wf⟩
    rcases mem_support_randomOracle_run _ _ hw with h | h <;> rw [h]
    · exact hI.cache k
    · rw [QueryCache.cacheQuery_of_ne _ _ (by simp)]
      exact hI.cache k

/-- A collision or prediction, once it happens, persists. -/
theorem preservesInv_bad (s₀ : S) :
    QueryImpl.PreservesInv (idealImpl (I := I) (O := O) (extra := extra) s₀)
      fun σ => ¬ Good s₀ σ.1 := by
  intro t σ hσ z hz hG
  rcases mem_support_idealImpl hz with h | ⟨-, ⟨e, h⟩ | ⟨r, h⟩⟩
  · exact hσ (h ▸ hG)
  · rw [h] at hG
    exact hσ hG.of_cons_prefixes
  · rw [h] at hG
    exact hσ hG.of_cons_priv

/-! ### The simulated run follows the chain until a collision or prediction -/

theorem prEvent_map_le_of_eq {β γ σ' τ : Type} (samp : ProbComp β) (f : β → γ × σ')
    (g : β → γ × τ) (vw : σ' → τ) (bad : σ' → Prop)
    (h : ∀ u, ¬ bad (f u).2 → ((f u).1, vw (f u).2) = g u) (Q : γ × τ → Prop) :
    Pr{let z ← f <$> samp}[Q (z.1, vw z.2) ∧ ¬ bad z.2] ≤ Pr{let z ← g <$> samp}[Q z] := by
  rw [prEvent_map, prEvent_map]
  exact prEvent_mono _ _ _ fun u hu => (h u hu.2) ▸ hu.1

theorem prEvent_pure_le_of_eq {γ σ' τ : Type} (a : γ × σ') (b : γ × τ) (vw : σ' → τ)
    (bad : σ' → Prop) (h : (a.1, vw a.2) = b) (Q : γ × τ → Prop) :
    Pr{let z ← (pure a : ProbComp (γ × σ'))}[Q (z.1, vw z.2) ∧ ¬ bad z.2] ≤
      Pr{let z ← (pure b : ProbComp (γ × τ))}[Q z] := by
  simpa using prEvent_map_le_of_eq (pure ()) (fun _ => a) (fun _ => b) vw bad (fun _ _ => h) Q

theorem romImpl_run_unif {κ : Type} [DecidableEq κ] {hs : OracleSpec κ}
    [∀ t, SampleableType (hs.Range t)] (n : ℕ) (c : hs.QueryCache) :
    (hs.romImpl (.inl n)).run c =
      (fun u => (u, c)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) n) := rfl

theorem romImpl_run_of_some {κ : Type} [DecidableEq κ] {hs : OracleSpec κ}
    [∀ t, SampleableType (hs.Range t)] {x : κ} {c : hs.QueryCache} {u : hs.Range x}
    (h : c x = some u) : (hs.romImpl (.inr x)).run c = pure (u, c) := by
  rw [romImpl_apply_inr, randomOracle.run_eq, h]

theorem romImpl_run_of_none {κ : Type} [DecidableEq κ] {hs : OracleSpec κ}
    [∀ t, SampleableType (hs.Range t)] {x : κ} {c : hs.QueryCache} (h : c x = none) :
    (hs.romImpl (.inr x)).run c = (fun u => (u, c.cacheQuery x u)) <$> ($ᵗ hs.Range x) := by
  rw [romImpl_apply_inr, randomOracle.run_eq, h, bind_pure_comp]

/-- Off a collision or prediction, a simulated chain step, read through `view`, is a step of the
chain oracle. -/
theorem dominated_chain (s₀ : S) (q : S × I) (σ : IdealState S I O extra) (hI : Inv σ)
    (Q : (S × O) × (chainSpec S I O + extra).QueryCache → Prop) :
    Pr{let z ← (idealImpl s₀ (.inr (.inl q))).run σ}[Q (z.1, view s₀ z.2) ∧
        ¬ (fun σ : IdealState S I O extra => ¬ Good s₀ σ.1) z.2] ≤
      Pr{let z ← ((chainSpec S I O + extra).romImpl (.inr (.inl q))).run (view s₀ σ)}[Q z] := by
  cases hp : knownPrefix s₀ σ.1.prefixes q.1 with
  | some p =>
    cases hv : findVal σ.1.prefixes (q.2 :: p) with
    | some v =>
      rw [idealImpl_run_known_cached hp hv, romImpl_run_of_some ((view_inl_of_known hp).trans hv)]
      exact prEvent_pure_le_of_eq (γ := S × O) (v, σ) (v, view s₀ σ) (view s₀)
        (fun σ => ¬ Good s₀ σ.1) rfl Q
    | none =>
      rw [idealImpl_run_known_fresh hp hv (by rw [hI.cache]; exact hv),
        romImpl_run_of_none ((view_inl_of_known hp).trans hv)]
      exact prEvent_map_le_of_eq (γ := S × O) ($ᵗ (S × O))
        (fun v => (v, (⟨(q.2 :: p, v) :: σ.1.prefixes, σ.1.priv⟩,
          σ.2.cacheQuery (.inl (q.2 :: p)) v)))
        (fun v => (v, (view s₀ σ).cacheQuery (.inl q) v)) (view s₀) (fun σ => ¬ Good s₀ σ.1)
        (fun v hG => by rw [view_known_fresh hI hp hv (not_not.mp hG)]) Q
  | none =>
    cases hv : findVal σ.1.priv q with
    | some v =>
      rw [idealImpl_run_unknown_cached hp hv,
        romImpl_run_of_some ((view_inl_of_unknown hp).trans hv)]
      exact prEvent_pure_le_of_eq (γ := S × O) (v, σ) (v, view s₀ σ) (view s₀)
        (fun σ => ¬ Good s₀ σ.1) rfl Q
    | none =>
      rw [idealImpl_run_unknown_fresh hp hv,
        romImpl_run_of_none ((view_inl_of_unknown hp).trans hv)]
      exact prEvent_map_le_of_eq (γ := S × O) ($ᵗ (S × O))
        (fun v => (v, (⟨σ.1.prefixes, (q, v) :: σ.1.priv⟩, σ.2)))
        (fun v => (v, (view s₀ σ).cacheQuery (.inl q) v)) (view s₀) (fun σ => ¬ Good s₀ σ.1)
        (fun v _ => by rw [view_unknown_fresh v hp]) Q

/-- A simulated step on an extra oracle, read through `view`, is a step of the chain oracle. -/
theorem dominated_extra (s₀ : S) (t : ι) (σ : IdealState S I O extra)
    (Q : extra.Range t × (chainSpec S I O + extra).QueryCache → Prop) :
    Pr{let z ← (idealImpl (I := I) (O := O) s₀ (.inr (.inr t))).run σ}[Q (z.1, view s₀ z.2) ∧
        ¬ (fun σ : IdealState S I O extra => ¬ Good s₀ σ.1) z.2] ≤
      Pr{let z ← ((chainSpec S I O + extra).romImpl (.inr (.inr t))).run (view s₀ σ)}[Q z] := by
  rw [idealImpl_run_extra]
  cases hc : σ.2 (.inr t) with
  | some u =>
    rw [romImpl_run_of_some ((view_inr s₀ σ t).trans hc), randomOracle.run_eq, hc, map_pure]
    exact prEvent_pure_le_of_eq (γ := extra.Range t) (u, σ) (u, view s₀ σ) (view s₀)
      (fun σ => ¬ Good s₀ σ.1) rfl Q
  | none =>
    rw [romImpl_run_of_none ((view_inr s₀ σ t).trans hc), randomOracle.run_eq, hc]
    dsimp only
    rw [bind_pure_comp, prEvent_map, prEvent_map, prEvent_map]
    refine prEvent_mono (m := ProbComp) ($ᵗ extra.Range t) _ _ fun u hu => ?_
    have h := hu.1
    dsimp only at h
    rwa [view_extra] at h

/-- Off a collision or prediction, each simulated step, read through `view`, is a step of the
chain oracle. -/
theorem dominatedUntilBad (s₀ : S) :
    QueryImpl.DominatedUntilBad (idealImpl (I := I) (O := O) (extra := extra) s₀)
      (chainSpec S I O + extra).romImpl (view s₀) Inv fun σ => ¬ Good s₀ σ.1 := by
  intro t (σ : IdealState S I O extra) hI _ Q
  rcases t with n | q | t
  · rw [idealImpl_run_unif, romImpl_run_unif]
    exact prEvent_map_le_of_eq _ (fun u => (u, σ)) (fun u => (u, view s₀ σ)) _
      (fun σ => ¬ Good s₀ σ.1) (fun _ _ => rfl) Q
  · exact dominated_chain s₀ q σ hI Q
  · exact dominated_extra s₀ t σ Q

/-! ### The collision-or-prediction bound -/

omit [DecidableEq S] [DecidableEq I] [SampleableType S] [SampleableType O] in
/-- A fresh prefix answer keeps the run good unless its state is the initial state, a prefix
answer's state or a private answer's state. -/
theorem good_known_fresh {s₀ : S} {st : SimState S I O} (hG : Good s₀ st) (k : List I)
    (v : S × O) (hv : v.1 ∉ s₀ :: (st.prefixes.map fun e => e.2.1) ++ st.priv.map fun r => r.1.1) :
    Good s₀ ⟨(k, v) :: st.prefixes, st.priv⟩ where
  ne_init e he := by
    rcases List.mem_cons.mp he with rfl | he
    · exact fun h => hv (List.mem_cons.mpr (.inl h))
    · exact hG.ne_init e he
  nodup := by
    rw [List.map_cons, List.nodup_cons]
    exact ⟨fun h => hv (by simp_all), hG.nodup⟩
  unpredicted e he r hr := by
    rcases List.mem_cons.mp he with rfl | he
    · exact fun h => hv (List.mem_append_right _ (List.mem_map.mpr ⟨r, hr, h⟩))
    · exact hG.unpredicted e he r hr

omit [DecidableEq I] [SampleableType S] [SampleableType O] in
/-- A private answer at an unknown state keeps the run good. -/
theorem good_unknown_fresh {s₀ : S} {st : SimState S I O} (hG : Good s₀ st) {q : S × I}
    (hp : knownPrefix s₀ st.prefixes q.1 = none) (v : S × O) :
    Good s₀ ⟨st.prefixes, (q, v) :: st.priv⟩ where
  ne_init := hG.ne_init
  nodup := hG.nodup
  unpredicted e he r hr := by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact fun h => (knownPrefix_eq_none_iff.mp hp).2 e he h.symm
    · exact hG.unpredicted e he r hr

/-- The bad event of the potential argument: a collision or prediction, or a broken invariant. -/
def Fired (s₀ : S) (σ : IdealState S I O extra) : Prop := ¬ Good s₀ σ.1 ∨ ¬ Inv σ

/-- A chain step fires at most the share of states its fresh prefix answer must avoid, which the
potential pays. -/
theorem potentialStep_chain (s₀ : S) (q : S × I) (σ : IdealState S I O extra)
    (hσ : ¬ Fired s₀ σ) :
    (∃ a s', (idealImpl s₀ (.inr (.inl q))).run σ = pure (a, s') ∧ ¬ Fired s₀ s') ∨
      (∃ (samp : ProbComp (S × O)) (upd : S × O → IdealState S I O extra) (w : ℝ≥0∞),
        (idealImpl s₀ (.inr (.inl q))).run σ = (fun u => (u, upd u)) <$> samp ∧
        Pr{let u ← samp}[Fired s₀ (upd u)] ≤ w ∧
        ∀ u, w + potential S σ.1.size ≤ potential S (upd u).1.size) := by
  obtain ⟨hG, hI⟩ := not_or.mp hσ
  rw [not_not] at hG hI
  cases hp : knownPrefix s₀ σ.1.prefixes q.1 with
  | some p =>
    cases hv : findVal σ.1.prefixes (q.2 :: p) with
    | some v => exact .inl ⟨v, σ, idealImpl_run_known_cached hp hv, hσ⟩
    | none =>
      refine .inr ⟨$ᵗ (S × O), fun v => (⟨(q.2 :: p, v) :: σ.1.prefixes, σ.1.priv⟩,
        σ.2.cacheQuery (.inl (q.2 :: p)) v), ((σ.1.size + 1 : ℕ) : ℝ≥0∞) / Nat.card S,
        idealImpl_run_known_fresh hp hv (by rw [hI.cache]; exact hv), ?_, fun v => ?_⟩
      · refine (prEvent_mono _ _ (fun v => v.1 ∈ s₀ :: (σ.1.prefixes.map fun e => e.2.1) ++
          σ.1.priv.map fun r => r.1.1) fun v hv' => ?_).trans ((prEvent_fst_mem_le _).trans ?_)
        · rcases hv' with hv' | hv'
          · by_contra hmem
            exact hv' (good_known_fresh hG _ v hmem)
          · exact absurd (inv_known_fresh hI hp hv v) hv'
        · simp [SimState.size]
      · simp only [SimState.size, List.length_cons]
        rw [show σ.1.prefixes.length + 1 + σ.1.priv.length = σ.1.size + 1 by
          simp [SimState.size]; omega, potential_succ]
        exact le_rfl
  | none =>
    cases hv : findVal σ.1.priv q with
    | some v => exact .inl ⟨v, σ, idealImpl_run_unknown_cached hp hv, hσ⟩
    | none =>
      refine .inr ⟨$ᵗ (S × O), fun v => (⟨σ.1.prefixes, (q, v) :: σ.1.priv⟩, σ.2), 0,
        idealImpl_run_unknown_fresh hp hv, ?_, fun v => ?_⟩
      · refine le_of_eq (prEvent_eq_zero_of_forall_not _ _ fun v hv' => ?_)
        rcases hv' with hv' | hv'
        · exact hv' (good_unknown_fresh hG hp v)
        · exact hv' ⟨hI.cache, hI.wf⟩
      · rw [zero_add]
        exact potential_mono S (by simp [SimState.size])

theorem potentialStep_extra (s₀ : S) (t : ι) (σ : IdealState S I O extra)
    (hσ : ¬ Fired s₀ σ) :
    (∃ a s', (idealImpl (I := I) (O := O) s₀ (.inr (.inr t))).run σ = pure (a, s') ∧
        ¬ Fired s₀ s') ∨
      (∃ (samp : ProbComp (extra.Range t)) (upd : extra.Range t → IdealState S I O extra)
        (w : ℝ≥0∞), (idealImpl s₀ (.inr (.inr t))).run σ = (fun u => (u, upd u)) <$> samp ∧
        Pr{let u ← samp}[Fired s₀ (upd u)] ≤ w ∧
        ∀ u, w + potential S σ.1.size ≤ potential S (upd u).1.size) := by
  obtain ⟨hG, hI⟩ := not_or.mp hσ
  rw [not_not] at hG hI
  rw [idealImpl_run_extra, randomOracle.run_eq]
  cases hc : σ.2 (.inr t) with
  | some u =>
    refine .inl ⟨u, σ, ?_, hσ⟩
    dsimp only
    rw [map_pure]
  | none =>
    refine .inr ⟨$ᵗ extra.Range t, fun u => (σ.1, σ.2.cacheQuery (.inr t) u), 0, ?_, ?_,
      fun _ => by rw [zero_add]⟩
    · dsimp only
      rw [bind_pure_comp, Functor.map_map]
      rfl
    · refine le_of_eq (prEvent_eq_zero_of_forall_not _ _ fun u hu => ?_)
      rcases hu with hu | hu
      · exact hu hG
      · refine hu ⟨fun k => ?_, hI.wf⟩
        rw [QueryCache.cacheQuery_of_ne _ _ (by simp)]
        exact hI.cache k

/-- **The collision-or-prediction bound.** A program making at most `Q` chain queries, run against
the prefix oracle by the simulator, ends with a collision or prediction with probability at most
`chainError S Q`. -/
theorem prEvent_bad_le (s₀ : S) {α : Type}
    (A : OracleComp (unifSpec + (chainSpec S I O + extra)) α) {Q : ℕ}
    (hQ : IsQueryBoundP A (fun t => isChain t = true) Q) :
    Pr{let z ← (simulateQ (idealImpl s₀) A).run (SimState.init, ∅)}[¬ Good s₀ z.2.1] ≤
      chainError S Q := by
  have hsize : ∀ z ∈ support ((simulateQ (idealImpl s₀) A).run (SimState.init, ∅)),
      z.2.1.size ≤ Q := by
    intro z hz
    have := hQ.cost_le_of_mem_support_run_simulateQ (impl := idealImpl s₀) (fun σ => σ.1.size)
      (fun t ht σ w hw => ?_) (fun t ht σ w hw => ?_) (SimState.init, ∅) z hz
    · simpa [SimState.size, SimState.init] using this
    · rcases mem_support_idealImpl hw with h | ⟨-, ⟨e, h⟩ | ⟨r, h⟩⟩ <;>
        simp [h, SimState.size] <;> omega
    · rcases mem_support_idealImpl hw with h | ⟨h', -⟩
      · rw [h]
      · exact absurd h' ht
  have hmono : ∀ (t : (unifSpec + (chainSpec S I O + extra)).Domain) (σ : IdealState S I O extra),
      ∀ z ∈ support ((idealImpl s₀ t).run σ),
        potential S σ.1.size ≤ potential S z.2.1.size := by
    intro t σ z hz
    refine potential_mono S ?_
    rcases mem_support_idealImpl hz with h | ⟨-, ⟨e, h⟩ | ⟨r, h⟩⟩ <;>
      simp [h, SimState.size]
  have hS : (Nat.card S : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
  have key := prEvent_and_le_of_potential (idealImpl (I := I) (O := O) (extra := extra) s₀)
    (Fired s₀) (fun σ => potential S σ.1.size) hmono (fun t σ hσ => ?_) A (potential S Q)
    (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hS) (SimState.init, ∅)
    (not_or.mpr ⟨not_not.mpr ⟨by simp [SimState.init], by simp [SimState.init],
      by simp [SimState.init]⟩, not_not.mpr inv_init⟩)
  · rw [← potential_eq_chainError]
    refine (prEvent_mono_of_support _ _ _ fun z hz h =>
      ⟨.inl h, potential_mono S (hsize z hz)⟩).trans (key.trans ?_)
    simp [SimState.size, SimState.init, potential_zero]
  · rcases t with n | q | t
    · refine .inr ⟨_, fun _ => σ, 0, idealImpl_run_unif s₀ n σ,
        le_of_eq (prEvent_eq_zero_of_forall_not _ _ fun _ => hσ), fun _ => by rw [zero_add]⟩
    · exact potentialStep_chain s₀ q σ hσ
    · exact potentialStep_extra s₀ t σ hσ

/-! ### The chain and the prefix oracle -/

/-- **A hash chain is a prefix-keyed random oracle until a collision or prediction.** An event of
the output of a program making at most `Q` chain queries against the chain oracle is at most the
same event against the prefix oracle, through the simulator, plus `chainError S Q`. -/
theorem prEvent_chain_le (s₀ : S) {α : Type}
    (A : OracleComp (unifSpec + (chainSpec S I O + extra)) α) {Q : ℕ}
    (hQ : IsQueryBoundP A (fun t => isChain t = true) Q) (E : α → Prop) :
    Pr{let a ← (simulateQ (chainSpec S I O + extra).romImpl A).run' ∅}[E a] ≤
      Pr{let a ← (simulateQ (prefixSpec S I O + extra).romImpl (simulate s₀ A)).run' ∅}[E a] +
        chainError S Q := by
  have h := (dominatedUntilBad s₀).prEvent_simulateQ_run_le_map_or_bad (preservesInv_inv s₀)
    (preservesInv_bad s₀) A (SimState.init, ∅) inv_init fun z => E z.1
  rw [view_init] at h
  rw [run'_simulate, prEvent_map]
  simp only [StateT.run', prEvent_map]
  exact h.trans ((prEvent_or_le _ _ _).trans (add_le_add le_rfl (prEvent_bad_le s₀ A hQ)))

/-- **The converse bound.** An event of the output of the simulated program against the prefix
oracle is at most the same event of the program against the chain oracle, plus
`chainError S Q`. -/
theorem prEvent_prefix_le (s₀ : S) {α : Type}
    (A : OracleComp (unifSpec + (chainSpec S I O + extra)) α) {Q : ℕ}
    (hQ : IsQueryBoundP A (fun t => isChain t = true) Q) (E : α → Prop) :
    Pr{let a ← (simulateQ (prefixSpec S I O + extra).romImpl (simulate s₀ A)).run' ∅}[E a] ≤
      Pr{let a ← (simulateQ (chainSpec S I O + extra).romImpl A).run' ∅}[E a] +
        chainError S Q := by
  have h := (dominatedUntilBad s₀).prEvent_simulateQ_run_map_and_not_bad_le (preservesInv_inv s₀)
    (preservesInv_bad s₀) A (SimState.init, ∅) inv_init fun z => E z.1
  rw [view_init] at h
  rw [run'_simulate, prEvent_map]
  simp only [StateT.run', prEvent_map]
  refine (prEvent_mono _ _ (fun z => (E z.1 ∧ ¬¬Good s₀ z.2.1) ∨ ¬Good s₀ z.2.1)
    fun z hz => ?_).trans ((prEvent_or_le _ _ _).trans (add_le_add h (prEvent_bad_le s₀ A hQ)))
  by_cases hg : Good s₀ z.2.1
  · exact .inl ⟨hz, not_not.mpr hg⟩
  · exact .inr hg

/-! ### The simulated program's prefix queries -/

/-- Whether a query of the simulated program is a prefix query. -/
def isPrefix {κ : Type} : ℕ ⊕ (List I ⊕ κ) → Bool
  | .inr (.inl _) => true
  | _ => false

omit [DecidableEq S] [DecidableEq I] [SampleableType S] [SampleableType O] [DecidableEq ι]
  [∀ t, SampleableType (extra.Range t)] in
theorem isQueryBoundP_liftM_probComp {α : Type} (oa : ProbComp α) :
    IsQueryBoundP (liftM oa : OracleComp (unifSpec + (prefixSpec S I O + extra)) α)
      (fun t => isPrefix t = true) 0 := by
  change IsQueryBoundP (liftComp oa _) _ 0
  rw [liftComp_def]
  refine isQueryBoundP_simulateQ_zero oa fun t => ?_
  change IsQueryBoundP (liftM ((unifSpec + (prefixSpec S I O + extra)).query (.inl t))) _ 0
  rw [isQueryBoundP_query_iff]
  simp [isPrefix]

omit [DecidableEq ι] [∀ t, SampleableType (extra.Range t)] in
/-- **The simulated program's queries.** A program making at most `Q` chain queries becomes, by
the simulator, a program making at most `Q` prefix queries. -/
theorem isQueryBoundP_simulate (s₀ : S) {α : Type}
    {A : OracleComp (unifSpec + (chainSpec S I O + extra)) α} {Q : ℕ}
    (hQ : IsQueryBoundP A (fun t => isChain t = true) Q) :
    IsQueryBoundP (simulate s₀ A) (fun t => isPrefix t = true) Q := by
  rw [simulate, StateT.run', isQueryBoundP_map_iff]
  refine hQ.simulateQ_run_of_step (fun t ht st => ?_) (fun t ht st => ?_) _
  · rcases t with n | q | t
    · cases ht
    · change IsQueryBoundP (simChain s₀ q st) _ 1
      unfold simChain
      split
      · split
        · trivial
        · rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
          exact fun _ => Nat.one_pos
      · split
        · trivial
        · rw [isQueryBoundP_map_iff]
          exact (isQueryBoundP_liftM_probComp _).mono (Nat.zero_le _)
    · cases ht
  · rcases t with n | q | t
    · simp [sim, isPrefix]
    · exact absurd rfl ht
    · simp [sim, isPrefix]

end Ideal

end Interaction.Oracle.Security.HashChain
