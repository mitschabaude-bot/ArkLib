/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.Interaction.Oracle.Security.RoundByRound
public import ArkLib.Interaction.Oracle.Security.StateRestoration

/-!
# Deterministic Fiat–Shamir soundness from correlation intractability

Challenges are supplied by a fixed deterministic restoration table with trivial salts.
The reduction reads the selected path's challenge-erased keys in order, without inspecting
an ordinary state. The security bound charges a false accepting proof to one rank's CI game.

An erased key's concrete prefix is reconstructed using the table's strict ancestor answers.
Consequently `Bad` is explicitly parameterized by that table. `ChallengeSchedule` is paired
with a zero root rank so that the list index selected by the reduction equals the supplied rank.
-/

@[expose] public section

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec
open Interaction.Oracle.TypeTree
open scoped ENNReal

namespace Interaction.Oracle.Security.CorrelationIntractable

open StateRestoration

/-- A claimed statement together with a complete concrete execution path. -/
abbrev FSProof (Statement : Type) (protocol : Statement → Protocol) :=
  (statement : Statement) × (protocol statement).tree.ExecutionPath

/-- A probabilistic proof producer, which may be chosen with arbitrary dependence on `h`. -/
abbrev FSAdversary (Statement : Type) (protocol : Statement → Protocol) :=
  ProbComp (FSProof Statement protocol)

/-- A probabilistic key producer for the existing restoration keys with trivial salts. -/
abbrev CIAdversary (Statement : Type) {protocol : Statement → Protocol}
    (coin : (statement : Statement) → PublicCoin (protocol statement)) :=
  ProbComp (Option (Key Statement PUnit coin))

/-- The CI experiment samples a key and tests the relation against its deterministic answer. -/
noncomputable def ciGame {Statement : Type} {protocol : Statement → Protocol}
    {coin : (statement : Statement) → PublicCoin (protocol statement)}
    (h : Table Statement PUnit coin)
    (relation : (key : Key Statement PUnit coin) → key.Challenge → Prop)
    (adversary : CIAdversary Statement coin) : ProbComp Bool := by
  classical
  exact (fun selected => match selected with
    | none => false
    | some key => decide (relation key (h key))) <$> adversary

/-- Winning probability of the deterministic-table CI game, with subprobability semantics. -/
noncomputable def ciWinProb {Statement : Type} {protocol : Statement → Protocol}
    {coin : (statement : Statement) → PublicCoin (protocol statement)}
    (h : Table Statement PUnit coin)
    (relation : (key : Key Statement PUnit coin) → key.Challenge → Prop)
    (adversary : CIAdversary Statement coin) : ℝ≥0∞ :=
  Pr{let won ← ciGame h relation adversary}[won = true]

/-- The CI game's probability is the event probability on the key producer itself. -/
theorem ciWinProb_eq_probEvent {Statement : Type} {protocol : Statement → Protocol}
    {coin : (statement : Statement) → PublicCoin (protocol statement)}
    (h : Table Statement PUnit coin)
    (relation : (key : Key Statement PUnit coin) → key.Challenge → Prop)
    (adversary : CIAdversary Statement coin) :
    ciWinProb h relation adversary =
      Pr{let selected ← adversary}[∃ key, selected = some key ∧ relation key (h key)] := by
  classical
  rw [ciWinProb, ciGame, prEvent_map]
  apply prEvent_congr
  intro selected
  cases selected <;> simp only [Bool.false_eq_true,
    reduceCtorEq, false_and, exists_false, Option.some.injEq, exists_eq_left', decide_eq_true_eq]

/-- Erase every verifier challenge of a concrete path, retaining trivial challenge salts. -/
def erasePath : {protocol : Protocol} → (coin : PublicCoin protocol) →
    protocol.tree.ExecutionPath → Messages PUnit coin
  | _, .done, _ => PUnit.unit
  | _, @PublicCoin.sender _ _ _ next, path => ⟨path.1, erasePath (next path.1) path.2⟩
  | _, @PublicCoin.oracle _ _ _ _ next, path => ⟨path.1, erasePath next path.2⟩
  | _, @PublicCoin.challenge _ _ _ next, path => ⟨PUnit.unit, erasePath next path.2⟩

/-- Every verifier move on the concrete path equals the table answer at its erased key. -/
def Consistent : {protocol : Protocol} → (coin : PublicCoin protocol) →
    PrefixTable PUnit coin → protocol.tree.ExecutionPath → Prop
  | _, .done, _, _ => True
  | _, @PublicCoin.sender _ _ _ next, table, path =>
      Consistent (next path.1) (fun q => table ⟨path.1, q⟩) path.2
  | _, @PublicCoin.oracle _ _ _ _ next, table, path =>
      Consistent next (fun q => table ⟨path.1, q⟩) path.2
  | _, @PublicCoin.challenge _ _ _ next, table, path =>
      path.1 = table (.inl PUnit.unit) ∧
        Consistent next (fun q => table (.inr ⟨PUnit.unit, q⟩)) path.2

/-- Deterministic Fiat–Shamir acceptance checks challenge consistency and the terminal relation. -/
def verify {Statement : Type} {protocol : Statement → Protocol}
    (coin : (statement : Statement) → PublicCoin (protocol statement))
    (h : Table Statement PUnit coin)
    (output : (statement : Statement) → (protocol statement).tree.ExecutionPath → Prop)
    (proof : FSProof Statement protocol) : Prop :=
  Consistent (coin proof.1) (Table.fibre h proof.1) proof.2 ∧ output proof.1 proof.2

/-- Probability that the adversary produces an accepted proof of a false statement. -/
noncomputable def fsSuccessProb {Statement : Type} {protocol : Statement → Protocol}
    (coin : (statement : Statement) → PublicCoin (protocol statement))
    (h : Table Statement PUnit coin) (lang : Statement → Prop)
    (output : (statement : Statement) → (protocol statement).tree.ExecutionPath → Prop)
    (adversary : FSAdversary Statement protocol) : ℝ≥0∞ :=
  Pr{let proof ← adversary}[verify coin h output proof ∧ ¬ lang proof.1]

/-- Challenge consistency is exactly reconstruction from the erased path using the same table. -/
theorem consistent_iff_prefixPath {protocol : Protocol} (coin : PublicCoin protocol)
    (table : PrefixTable PUnit coin) (path : protocol.tree.ExecutionPath) :
    Consistent coin table path ↔ prefixPath coin (erasePath coin path) table = path := by
  induction coin with
  | done => exact ⟨fun _ => rfl, fun _ => True.intro⟩
  | sender next ih =>
      rcases path with ⟨move, tail⟩
      constructor
      · intro consistent
        exact Sigma.ext rfl (heq_of_eq ((ih move _ tail).mp consistent))
      · intro equal
        exact (ih move _ tail).mpr (eq_of_heq (Sigma.mk.inj equal).2)
  | oracle next ih =>
      rcases path with ⟨message, tail⟩
      constructor
      · intro consistent
        exact Sigma.ext rfl (heq_of_eq ((ih _ tail).mp consistent))
      · intro equal
        exact (ih _ tail).mpr (eq_of_heq (Sigma.mk.inj equal).2)
  | challenge next ih =>
      rcases path with ⟨value, tail⟩
      constructor
      · rintro ⟨equal, consistent⟩
        change value = _ at equal
        subst value
        exact Sigma.ext rfl (heq_of_eq ((ih _ tail).mp consistent))
      · intro equal
        obtain ⟨head, tailEqual⟩ := Sigma.mk.inj equal
        exact ⟨head.symm, (ih _ tail).mpr (eq_of_heq tailEqual)⟩

/-- Reconstruct the concrete prefix before a key, using only strict ancestor table answers. -/
def prefixBefore : {protocol : Protocol} → (coin : PublicCoin protocol) →
    (pre : Prefix PUnit coin) → PrefixTable PUnit coin → ExecutionPrefix protocol.tree
  | _, .done, pre, _ => nomatch pre
  | _, @PublicCoin.sender _ _ _ next, ⟨move, pre⟩, table =>
      .prependPublic move (prefixBefore (next move) pre fun q => table ⟨move, q⟩)
  | _, @PublicCoin.oracle _ _ _ _ next, ⟨message, pre⟩, table =>
      .prependOracle message (prefixBefore next pre fun q => table ⟨message, q⟩)
  | _, @PublicCoin.challenge _ _ _ _, .inl _, _ => .root _
  | _, @PublicCoin.challenge _ _ _ next, .inr ⟨salt, pre⟩, table =>
      .prependPublic (table (.inl salt))
        (prefixBefore next pre fun q => table (.inr ⟨salt, q⟩))

/-- Reconstruct the prefix after the target challenge, using a supplied answer at that key. -/
def prefixAfter : {protocol : Protocol} → (coin : PublicCoin protocol) →
    (pre : Prefix PUnit coin) → PrefixTable PUnit coin →
    pre.Challenge → ExecutionPrefix protocol.tree
  | _, .done, pre, _, _ => nomatch pre
  | _, @PublicCoin.sender _ _ _ next, ⟨move, pre⟩, table, value =>
      .prependPublic move (prefixAfter (next move) pre (fun q => table ⟨move, q⟩) value)
  | _, @PublicCoin.oracle _ _ _ _ next, ⟨message, pre⟩, table, value =>
      .prependOracle message (prefixAfter next pre (fun q => table ⟨message, q⟩) value)
  | _, @PublicCoin.challenge _ _ _ _, .inl _, _, value =>
      .prependPublic value (.root _)
  | _, @PublicCoin.challenge _ _ _ next, .inr ⟨salt, pre⟩, table, value =>
      .prependPublic (table (.inl salt))
        (prefixAfter next pre (fun q => table (.inr ⟨salt, q⟩)) value)

/-- The challenge-erased keys of the strict ancestor challenges, in path order. -/
def strictAncestors : {protocol : Protocol} → (coin : PublicCoin protocol) →
    Prefix PUnit coin → List (Prefix PUnit coin)
  | _, .done, pre => nomatch pre
  | _, @PublicCoin.sender _ _ _ next, ⟨move, pre⟩ =>
      (strictAncestors (next move) pre).map (Sigma.mk move)
  | _, @PublicCoin.oracle _ _ _ _ next, ⟨message, pre⟩ =>
      (strictAncestors next pre).map (Prod.mk message)
  | _, @PublicCoin.challenge _ _ _ _, .inl _ => []
  | _, @PublicCoin.challenge _ _ _ next, .inr ⟨salt, pre⟩ =>
      .inl salt :: (strictAncestors next pre).map (fun q => .inr ⟨salt, q⟩)

/-- A strict ancestor has fewer ancestor challenges than its descendant. -/
theorem strictAncestors_length_lt {protocol : Protocol} (coin : PublicCoin protocol)
    (pre ancestor : Prefix PUnit coin) (member : ancestor ∈ strictAncestors coin pre) :
    (strictAncestors coin ancestor).length < (strictAncestors coin pre).length := by
  induction coin with
  | done => exact pre.elim
  | sender next ih =>
      rcases pre with ⟨move, pre⟩
      simp only [strictAncestors, List.mem_map] at member
      obtain ⟨ancestor, member, rfl⟩ := member
      simpa only [strictAncestors, List.length_map] using ih move pre ancestor member
  | oracle next ih =>
      rcases pre with ⟨message, pre⟩
      simp only [strictAncestors, List.mem_map] at member
      obtain ⟨ancestor, member, rfl⟩ := member
      simpa only [strictAncestors, List.length_map] using ih pre ancestor member
  | challenge next ih =>
      cases pre with
      | inl salt => exact (List.not_mem_nil member).elim
      | inr data =>
          rcases data with ⟨salt, pre⟩
          simp only [strictAncestors, List.mem_cons, List.mem_map] at member
          rcases member with rfl | ⟨ancestor, member, rfl⟩
          · simp only [strictAncestors, List.length_nil, List.length_cons, List.length_map]
            omega
          · have smaller := ih pre ancestor member
            simpa only [strictAncestors, List.length_cons, List.length_map,
              Nat.add_lt_add_iff_right] using smaller

/-- The strict ancestor relation is well founded by its number of earlier challenges. -/
theorem strictAncestors_wellFounded {protocol : Protocol} (coin : PublicCoin protocol) :
    WellFounded (fun ancestor pre => ancestor ∈ strictAncestors coin pre) :=
  (measure (fun pre => (strictAncestors coin pre).length)).wf.mono
    (fun ancestor pre member => strictAncestors_length_lt coin pre ancestor member)

/-- A key is not one of its own strict ancestors. -/
theorem not_mem_strictAncestors {protocol : Protocol} (coin : PublicCoin protocol)
    (pre : Prefix PUnit coin) : pre ∉ strictAncestors coin pre :=
  fun member => Nat.lt_irrefl _ (strictAncestors_length_lt coin pre pre member)

/-- Strict ancestor agreement determines the reconstructed prefix before and after a key. -/
theorem prefixes_congr {protocol : Protocol} (coin : PublicCoin protocol)
    (pre : Prefix PUnit coin) (table other : PrefixTable PUnit coin)
    (agree : ∀ ancestor ∈ strictAncestors coin pre, table ancestor = other ancestor) :
    prefixBefore coin pre table = prefixBefore coin pre other ∧
      ∀ value, prefixAfter coin pre table value = prefixAfter coin pre other value := by
  induction coin with
  | done => exact pre.elim
  | sender next ih =>
      rcases pre with ⟨move, pre⟩
      obtain ⟨before, after⟩ := ih move pre (fun q => table ⟨move, q⟩)
        (fun q => other ⟨move, q⟩)
        (fun q hq => agree ⟨move, q⟩ (List.mem_map.mpr ⟨q, hq, rfl⟩))
      exact ⟨congrArg (ExecutionPrefix.prependPublic move) before,
        fun value => congrArg (ExecutionPrefix.prependPublic move) (after value)⟩
  | oracle next ih =>
      rcases pre with ⟨message, pre⟩
      obtain ⟨before, after⟩ := ih pre (fun q => table ⟨message, q⟩)
        (fun q => other ⟨message, q⟩)
        (fun q hq => agree ⟨message, q⟩ (List.mem_map.mpr ⟨q, hq, rfl⟩))
      exact ⟨congrArg (ExecutionPrefix.prependOracle message) before,
        fun value => congrArg (ExecutionPrefix.prependOracle message) (after value)⟩
  | challenge next ih =>
      cases pre with
      | inl salt => exact ⟨rfl, fun _ => rfl⟩
      | inr data =>
          rcases data with ⟨salt, pre⟩
          have root := agree (.inl salt) List.mem_cons_self
          obtain ⟨before, after⟩ := ih pre (fun q => table (.inr ⟨salt, q⟩))
            (fun q => other (.inr ⟨salt, q⟩))
            (fun q hq => agree (.inr ⟨salt, q⟩)
              (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q, hq, rfl⟩)))
          constructor
          · simp only [prefixBefore, root, before]
            rfl
          · intro value
            simp only [prefixAfter, root, after value]
            rfl

/-- The concrete prefix before a key reads its table only at strict ancestor keys. -/
theorem prefixBefore_congr {protocol : Protocol} (coin : PublicCoin protocol)
    (pre : Prefix PUnit coin) (table other : PrefixTable PUnit coin)
    (agree : ∀ ancestor ∈ strictAncestors coin pre, table ancestor = other ancestor) :
    prefixBefore coin pre table = prefixBefore coin pre other :=
  (prefixes_congr coin pre table other agree).1

/-- The concrete prefix after a supplied challenge reads the table only at strict ancestors. -/
theorem prefixAfter_congr {protocol : Protocol} (coin : PublicCoin protocol)
    (pre : Prefix PUnit coin) (table other : PrefixTable PUnit coin)
    (agree : ∀ ancestor ∈ strictAncestors coin pre, table ancestor = other ancestor)
    (value : pre.Challenge) :
    prefixAfter coin pre table value = prefixAfter coin pre other value :=
  (prefixes_congr coin pre table other agree).2 value

/-- A key reconstructed from a public-coin presentation always ends at a verifier node. -/
theorem prefixBefore_isVerifier {protocol : Protocol} (coin : PublicCoin protocol)
    (pre : Prefix PUnit coin) (table : PrefixTable PUnit coin) :
    IsVerifierPrefix protocol.roles (prefixBefore coin pre table) := by
  induction coin with
  | done => exact pre.elim
  | sender next ih =>
      rcases pre with ⟨move, pre⟩
      exact ih move pre (fun q => table ⟨move, q⟩)
  | oracle next ih =>
      rcases pre with ⟨message, pre⟩
      exact ih pre (fun q => table ⟨message, q⟩)
  | challenge next ih =>
      cases pre with
      | inl salt => rfl
      | inr data =>
          rcases data with ⟨salt, pre⟩
          exact ih pre (fun q => table (.inr ⟨salt, q⟩))

/-- On a consistent path, verifier escapes are precisely false-to-true edges at its erased keys. -/
theorem verifierEscape_iff_exists_prefix {protocol : Protocol} (coin : PublicCoin protocol)
    (state : ExecutionPrefix protocol.tree → Prop) (table : PrefixTable PUnit coin)
    (path : protocol.tree.ExecutionPath) (consistent : Consistent coin table path) :
    VerifierEscapeOnPath protocol.tree protocol.roles state path ↔
      ∃ pre ∈ prefixKeys coin (erasePath coin path),
        ¬ state (prefixBefore coin pre table) ∧
          state (prefixAfter coin pre table (table pre)) := by
  induction coin with
  | done => exact ⟨False.elim, fun ⟨_, member, _⟩ => (List.not_mem_nil member).elim⟩
  | sender next ih =>
      rcases path with ⟨move, tail⟩
      have tailLaw := ih move (fun pfx => state (.prependPublic move pfx))
        (fun q => table ⟨move, q⟩) tail consistent
      constructor
      · rintro (⟨impossible, _⟩ | escape)
        · cases impossible
        · obtain ⟨pre, member, bad⟩ := tailLaw.mp escape
          exact ⟨⟨move, pre⟩, List.mem_map.mpr ⟨pre, member, rfl⟩, bad⟩
      · rintro ⟨pre, member, bad⟩
        simp only [erasePath, prefixKeys, List.mem_map] at member
        obtain ⟨pre, member, rfl⟩ := member
        exact Or.inr (tailLaw.mpr ⟨pre, member, bad⟩)
  | oracle next ih =>
      rcases path with ⟨message, tail⟩
      have tailLaw := ih (fun pfx => state (.prependOracle message pfx))
        (fun q => table ⟨message, q⟩) tail consistent
      constructor
      · intro escape
        obtain ⟨pre, member, bad⟩ := tailLaw.mp escape
        exact ⟨⟨message, pre⟩, List.mem_map.mpr ⟨pre, member, rfl⟩, bad⟩
      · rintro ⟨pre, member, bad⟩
        simp only [erasePath, prefixKeys, List.mem_map] at member
        obtain ⟨pre, member, rfl⟩ := member
        exact tailLaw.mpr ⟨pre, member, bad⟩
  | challenge next ih =>
      rcases path with ⟨value, tail⟩
      rcases consistent with ⟨equal, consistent⟩
      change value = _ at equal
      subst value
      have tailLaw := ih (fun pfx => state (.prependPublic (table (.inl PUnit.unit)) pfx))
        (fun q => table (.inr ⟨PUnit.unit, q⟩)) tail consistent
      constructor
      · rintro (⟨_, bad⟩ | escape)
        · exact ⟨.inl PUnit.unit, List.mem_cons_self, bad⟩
        · obtain ⟨pre, member, bad⟩ := tailLaw.mp escape
          exact ⟨.inr ⟨PUnit.unit, pre⟩,
            List.mem_cons_of_mem _ (List.mem_map.mpr ⟨pre, member, rfl⟩), bad⟩
      · rintro ⟨pre, member, bad⟩
        simp only [erasePath, prefixKeys, List.mem_cons, List.mem_map] at member
        rcases member with rfl | ⟨pre, member, rfl⟩
        · exact Or.inl ⟨rfl, bad⟩
        · exact Or.inr (tailLaw.mpr ⟨pre, member, bad⟩)

/-- The rank-`r` bad-challenge relation reads `h` only at strict ancestors of its key;
`Bad_congr` makes this independence of the target answer explicit. -/
def Bad {Statement : Type} {protocol : Statement → Protocol}
    {coin : (statement : Statement) → PublicCoin (protocol statement)}
    (h : Table Statement PUnit coin)
    (state : (statement : Statement) → ExecutionPrefix (protocol statement).tree → Prop)
    (rank : (statement : Statement) → ExecutionPrefix (protocol statement).tree → ℕ)
    (r : ℕ) (key : Key Statement PUnit coin) (value : key.Challenge) : Prop :=
  let before := prefixBefore (coin key.1) key.2 (Table.fibre h key.1)
  rank key.1 before = r ∧ ¬ state key.1 before ∧
    state key.1 (prefixAfter (coin key.1) key.2 (Table.fibre h key.1) value)

/-- Tables agreeing at a key's strict ancestors give the same bad-challenge relation there. -/
theorem Bad_congr {Statement : Type} {protocol : Statement → Protocol}
    {coin : (statement : Statement) → PublicCoin (protocol statement)}
    (h other : Table Statement PUnit coin)
    (state : (statement : Statement) → ExecutionPrefix (protocol statement).tree → Prop)
    (rank : (statement : Statement) → ExecutionPrefix (protocol statement).tree → ℕ)
    (r : ℕ) (key : Key Statement PUnit coin) (value : key.Challenge)
    (agree : ∀ ancestor ∈ strictAncestors (coin key.1) key.2,
      h ⟨key.1, ancestor⟩ = other ⟨key.1, ancestor⟩) :
    Bad h state rank r key value ↔ Bad other state rank r key value := by
  obtain ⟨before, after⟩ := prefixes_congr (coin key.1) key.2
    (Table.fibre h key.1) (Table.fibre other key.1) agree
  simp only [Bad, before, after value]

/-- The erased challenge keys of a complete proof in path order. -/
def proofKeys {Statement : Type} {protocol : Statement → Protocol}
    (coin : (statement : Statement) → PublicCoin (protocol statement))
    (proof : FSProof Statement protocol) : List (Key Statement PUnit coin) :=
  completionKeys coin proof.1 (erasePath (coin proof.1) proof.2)

/-- The reduction runs `A` and reads its path; it never evaluates `h`, `state`, or `rank`. -/
def reductionAdversary {Statement : Type} {protocol : Statement → Protocol}
    (coin : (statement : Statement) → PublicCoin (protocol statement))
    (r : ℕ) (A : FSAdversary Statement protocol) : CIAdversary Statement coin :=
  (fun proof => (proofKeys coin proof)[r]?) <$> A

/-- The index of a completion key adds to the starting rank, and stays below the schedule cap. -/
theorem prefixKeys_rank {protocol : Protocol} (coin : PublicCoin protocol)
    (messages : Messages PUnit coin) (table : PrefixTable PUnit coin)
    (rank : ExecutionPrefix protocol.tree → ℕ) (count : ℕ)
    (schedule : ChallengeSchedule protocol.tree protocol.roles rank count)
    (r : ℕ) (pre : Prefix PUnit coin)
    (selected : (prefixKeys coin messages)[r]? = some pre) :
    rank (prefixBefore coin pre table) = rank (.root _) + r ∧
      rank (prefixBefore coin pre table) < count := by
  induction coin generalizing r with
  | done => exact pre.elim
  | sender next ih =>
      rcases messages with ⟨move, messages⟩
      simp only [prefixKeys, List.getElem?_map, Option.map_eq_some_iff] at selected
      obtain ⟨pre, selected, rfl⟩ := selected
      have result := ih move messages (fun q => table ⟨move, q⟩)
        (fun pfx => rank (.prependPublic move pfx)) (schedule.2 move) r pre selected
      exact ⟨result.1.trans (congrArg (fun n => n + r) (schedule.1 move)), result.2⟩
  | oracle next ih =>
      rcases messages with ⟨message, messages⟩
      simp only [prefixKeys, List.getElem?_map, Option.map_eq_some_iff] at selected
      obtain ⟨pre, selected, rfl⟩ := selected
      have result := ih messages (fun q => table ⟨message, q⟩)
        (fun pfx => rank (.prependOracle message pfx)) (schedule.2 message) r pre selected
      exact ⟨result.1.trans (congrArg (fun n => n + r) (schedule.1 message)), result.2⟩
  | challenge next ih =>
      rcases messages with ⟨salt, messages⟩
      cases r with
      | zero =>
          simp only [prefixKeys, List.getElem?_cons_zero, Option.some.injEq] at selected
          subst pre
          exact ⟨(Nat.add_zero _).symm, schedule.1.1⟩
      | succ r =>
          simp only [prefixKeys, List.getElem?_cons_succ, List.getElem?_map,
            Option.map_eq_some_iff] at selected
          obtain ⟨pre, selected, rfl⟩ := selected
          have result := ih messages (fun q => table (.inr ⟨salt, q⟩))
            (fun pfx => rank (.prependPublic (table (.inl salt)) pfx))
            (schedule.2 (table (.inl salt))) r pre selected
          refine ⟨result.1.trans ?_, result.2⟩
          exact (congrArg (fun n => n + r) (schedule.1.2 (table (.inl salt)))).trans
            (Nat.add_right_comm _ _ _)

/-- The list position of a reached verifier key equals its normalized challenge rank. -/
theorem proofKeys_rank {Statement : Type} {protocol : Statement → Protocol}
    (coin : (statement : Statement) → PublicCoin (protocol statement))
    (h : Table Statement PUnit coin)
    (rank : (statement : Statement) → ExecutionPrefix (protocol statement).tree → ℕ)
    (count : ℕ)
    (schedule : ∀ statement, ChallengeSchedule (protocol statement).tree
      (protocol statement).roles (rank statement) count)
    (rootRank : ∀ statement, rank statement (.root _) = 0)
    (proof : FSProof Statement protocol)
    (r : ℕ) (key : Key Statement PUnit coin)
    (selected : (proofKeys coin proof)[r]? = some key) :
    r < count ∧ rank key.1
      (prefixBefore (coin key.1) key.2 (Table.fibre h key.1)) = r := by
  simp only [proofKeys, completionKeys, List.getElem?_map, Option.map_eq_some_iff] at selected
  obtain ⟨pre, selected, rfl⟩ := selected
  obtain ⟨equal, bounded⟩ := prefixKeys_rank (coin proof.1) (erasePath (coin proof.1) proof.2)
    (Table.fibre h proof.1) (rank proof.1) count (schedule proof.1) r pre selected
  rw [rootRank, Nat.zero_add] at equal
  exact ⟨equal ▸ bounded, equal⟩

/-- An accepting false proof makes one path-selected key win its rank's CI game. -/
theorem exists_bad_selectedKey {Statement : Type} {protocol : Statement → Protocol}
    (coin : (statement : Statement) → PublicCoin (protocol statement))
    (h : Table Statement PUnit coin) (lang : Statement → Prop)
    (output : (statement : Statement) → (protocol statement).tree.ExecutionPath → Prop)
    (certificate : (statement : Statement) →
      OrdinaryState (protocol statement) (lang statement) (output statement))
    (rank : (statement : Statement) → ExecutionPrefix (protocol statement).tree → ℕ)
    (count : ℕ)
    (schedule : ∀ statement, ChallengeSchedule (protocol statement).tree
      (protocol statement).roles (rank statement) count)
    (rootRank : ∀ statement, rank statement (.root _) = 0)
    (proof : FSProof Statement protocol)
    (accepted : verify coin h output proof) (falseStatement : ¬ lang proof.1) :
    ∃ r ∈ Finset.range count, ∃ key,
      (proofKeys coin proof)[r]? = some key ∧
        Bad h (fun statement => (certificate statement).state) rank r key (h key) := by
  have escape := (certificate proof.1).exists_verifier_escape proof.2 falseStatement accepted.2
  obtain ⟨pre, member, before, after⟩ :=
    (verifierEscape_iff_exists_prefix (coin proof.1) (certificate proof.1).state
      (Table.fibre h proof.1) proof.2 accepted.1).mp escape
  obtain ⟨r, selected⟩ := List.mem_iff_getElem?.mp member
  have selectedKey : (proofKeys coin proof)[r]? = some ⟨proof.1, pre⟩ := by
    simp only [proofKeys, completionKeys, List.getElem?_map, selected, Option.map_some]
  obtain ⟨bounded, rankEqual⟩ := proofKeys_rank coin h rank count schedule rootRank
    proof r ⟨proof.1, pre⟩ selectedKey
  exact ⟨r, Finset.mem_range.mpr bounded, ⟨proof.1, pre⟩, selectedKey, rankEqual, before, after⟩

/-- The reduction's CI probability is the corresponding event on the original proof producer. -/
theorem reductionAdversary_winProb {Statement : Type} {protocol : Statement → Protocol}
    (coin : (statement : Statement) → PublicCoin (protocol statement))
    (h : Table Statement PUnit coin)
    (relation : (key : Key Statement PUnit coin) → key.Challenge → Prop)
    (r : ℕ) (A : FSAdversary Statement protocol) :
    ciWinProb h relation (reductionAdversary coin r A) =
      Pr{let proof ← A}[∃ key, (proofKeys coin proof)[r]? = some key ∧
        relation key (h key)] := by
  rw [ciWinProb_eq_probEvent, reductionAdversary, prEvent_map]

/-- Standard-model Fiat–Shamir soundness is bounded by the sum of the explicit reductions'
CI winning probabilities. The fixed table and the adversary may depend on each other arbitrarily. -/
theorem soundness {Statement : Type} {protocol : Statement → Protocol}
    (coin : (statement : Statement) → PublicCoin (protocol statement))
    (h : Table Statement PUnit coin) (lang : Statement → Prop)
    (output : (statement : Statement) → (protocol statement).tree.ExecutionPath → Prop)
    (certificate : (statement : Statement) →
      OrdinaryState (protocol statement) (lang statement) (output statement))
    (rank : (statement : Statement) → ExecutionPrefix (protocol statement).tree → ℕ)
    (count : ℕ)
    (schedule : ∀ statement, ChallengeSchedule (protocol statement).tree
      (protocol statement).roles (rank statement) count)
    (rootRank : ∀ statement, rank statement (.root _) = 0)
    (A : FSAdversary Statement protocol) :
    fsSuccessProb coin h lang output A ≤
      ∑ r ∈ Finset.range count,
        ciWinProb h (Bad h (fun statement => (certificate statement).state) rank r)
          (reductionAdversary coin r A) := by
  unfold fsSuccessProb
  calc
    _ ≤ Pr{let proof ← A}[∃ r ∈ Finset.range count, ∃ key,
        (proofKeys coin proof)[r]? = some key ∧
          Bad h (fun statement => (certificate statement).state) rank r key (h key)] :=
      prEvent_mono A _ _ (fun proof bad =>
        exists_bad_selectedKey coin h lang output certificate rank count schedule rootRank
          proof bad.1 bad.2)
    _ ≤ ∑ r ∈ Finset.range count, Pr{let proof ← A}[∃ key,
        (proofKeys coin proof)[r]? = some key ∧
          Bad h (fun statement => (certificate statement).state) rank r key (h key)] :=
      prEvent_exists_finset_le (Finset.range count) A _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      exact (reductionAdversary_winProb coin h _ r A).symm

end Interaction.Oracle.Security.CorrelationIntractable
