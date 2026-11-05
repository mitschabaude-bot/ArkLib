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
  ProbComp (Key Statement PUnit coin)

/-- The CI experiment samples a key and tests the relation against its deterministic answer. -/
noncomputable def ciGame {Statement : Type} {protocol : Statement → Protocol}
    {coin : (statement : Statement) → PublicCoin (protocol statement)}
    (h : Table Statement PUnit coin)
    (relation : (key : Key Statement PUnit coin) → key.Challenge → Prop)
    (adversary : CIAdversary Statement coin) : ProbComp Bool := by
  classical
  exact (fun key => decide (relation key (h key))) <$> adversary

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
      Pr{let key ← adversary}[relation key (h key)] := by
  sorry

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
  sorry

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

/-- A key reconstructed from a public-coin presentation always ends at a verifier node. -/
theorem prefixBefore_isVerifier {protocol : Protocol} (coin : PublicCoin protocol)
    (pre : Prefix PUnit coin) (table : PrefixTable PUnit coin) :
    IsVerifierPrefix protocol.roles (prefixBefore coin pre table) := by
  sorry

/-- On a consistent path, verifier escapes are precisely false-to-true edges at its erased keys. -/
theorem verifierEscape_iff_exists_prefix {protocol : Protocol} (coin : PublicCoin protocol)
    (state : ExecutionPrefix protocol.tree → Prop) (table : PrefixTable PUnit coin)
    (path : protocol.tree.ExecutionPath) (consistent : Consistent coin table path) :
    VerifierEscapeOnPath protocol.tree protocol.roles state path ↔
      ∃ pre ∈ prefixKeys coin (erasePath coin path),
        ¬ state (prefixBefore coin pre table) ∧
          state (prefixAfter coin pre table (table pre)) := by
  sorry

/-- The bad-challenge relation at rank `r`, with earlier challenges reconstructed from `h`. -/
def Bad {Statement : Type} {protocol : Statement → Protocol}
    {coin : (statement : Statement) → PublicCoin (protocol statement)}
    (h : Table Statement PUnit coin)
    (state : (statement : Statement) → ExecutionPrefix (protocol statement).tree → Prop)
    (rank : (statement : Statement) → ExecutionPrefix (protocol statement).tree → ℕ)
    (r : ℕ) (key : Key Statement PUnit coin) (value : key.Challenge) : Prop :=
  let before := prefixBefore (coin key.1) key.2 (Table.fibre h key.1)
  rank key.1 before = r ∧ ¬ state key.1 before ∧
    state key.1 (prefixAfter (coin key.1) key.2 (Table.fibre h key.1) value)

/-- The erased challenge keys of a complete proof in path order. -/
def proofKeys {Statement : Type} {protocol : Statement → Protocol}
    (coin : (statement : Statement) → PublicCoin (protocol statement))
    (proof : FSProof Statement protocol) : List (Key Statement PUnit coin) :=
  completionKeys coin proof.1 (erasePath (coin proof.1) proof.2)

/-- Select the `r`th verifier key on the path, or the fixed default when the path has none. -/
def selectKey {Statement : Type} {protocol : Statement → Protocol}
    (coin : (statement : Statement) → PublicCoin (protocol statement))
    (defaultKey : Key Statement PUnit coin) (r : ℕ)
    (proof : FSProof Statement protocol) : Key Statement PUnit coin :=
  ((proofKeys coin proof)[r]?).getD defaultKey

/-- The reduction runs `A` and reads its path; it never evaluates `h`, `state`, or `rank`. -/
def reductionAdversary {Statement : Type} {protocol : Statement → Protocol}
    (coin : (statement : Statement) → PublicCoin (protocol statement))
    (defaultKey : Key Statement PUnit coin) (r : ℕ)
    (A : FSAdversary Statement protocol) : CIAdversary Statement coin :=
  selectKey coin defaultKey r <$> A

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
    (consistent : Consistent (coin proof.1) (Table.fibre h proof.1) proof.2)
    (r : ℕ) (key : Key Statement PUnit coin)
    (selected : (proofKeys coin proof)[r]? = some key) :
    r < count ∧ rank key.1
      (prefixBefore (coin key.1) key.2 (Table.fibre h key.1)) = r := by
  sorry

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
    (defaultKey : Key Statement PUnit coin) (proof : FSProof Statement protocol)
    (accepted : verify coin h output proof) (falseStatement : ¬ lang proof.1) :
    ∃ r ∈ Finset.range count,
      Bad h (fun statement => (certificate statement).state) rank r
        (selectKey coin defaultKey r proof) (h (selectKey coin defaultKey r proof)) := by
  sorry

/-- The reduction's CI probability is the corresponding event on the original proof producer. -/
theorem reductionAdversary_winProb {Statement : Type} {protocol : Statement → Protocol}
    (coin : (statement : Statement) → PublicCoin (protocol statement))
    (h : Table Statement PUnit coin)
    (relation : (key : Key Statement PUnit coin) → key.Challenge → Prop)
    (defaultKey : Key Statement PUnit coin) (r : ℕ)
    (A : FSAdversary Statement protocol) :
    ciWinProb h relation (reductionAdversary coin defaultKey r A) =
      Pr{let proof ← A}[relation (selectKey coin defaultKey r proof)
        (h (selectKey coin defaultKey r proof))] := by
  sorry

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
    (defaultKey : Key Statement PUnit coin) (A : FSAdversary Statement protocol) :
    fsSuccessProb coin h lang output A ≤
      ∑ r ∈ Finset.range count,
        ciWinProb h (Bad h (fun statement => (certificate statement).state) rank r)
          (reductionAdversary coin defaultKey r A) := by
  sorry

end Interaction.Oracle.Security.CorrelationIntractable
