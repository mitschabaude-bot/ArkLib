/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.Interaction.Oracle.Security.CorrelationIntractable

/-!
# Standard-model BCS knowledge soundness

Oracle messages are compiled to public commitments. A coin-aware message extractor supplies the
oracle messages on the selected compiled path, and a knowledge certificate transports a supplied
terminal witness backward. Binding is isolated as a disagreement event and an acceptance-transfer
hypothesis. Challenges come from a deterministic table on the compiled challenge-erased keys.

The local escape event checks table consistency only through its target challenge. Its knowledge
failure is existential over the later witness, as in `RoundExtractor.badChallenge`; it never
reads a witness extracted from the future suffix. This makes its table dependence local to the
strict ancestor keys and the target answer.
-/

@[expose] public section

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec
open Interaction.Oracle.TypeTree
open scoped ENNReal

namespace Interaction.Oracle.Security.StandardBcs

open StateRestoration
open CorrelationIntractable (Consistent erasePath strictAncestors)

/-- Replace each oracle message by a public sender commitment; preserve all other moves. -/
def compile (Com : Type) : {protocol : Protocol} → PublicCoin protocol → Protocol
  | _, .done => .done
  | _, @PublicCoin.sender Moves _ _ next =>
      .public .sender Moves (fun move => compile Com (next move))
  | _, @PublicCoin.oracle _ _ _ _ next =>
      .public .sender Com (fun _ => compile Com next)
  | _, @PublicCoin.challenge Challenge _ _ next =>
      .public .receiver Challenge (fun _ => compile Com next)

/-- The commitment compilation retains the public-coin presentation and its challenge types. -/
def compiledCoin (Com : Type) [DecidableEq Com] :
    {protocol : Protocol} → (coin : PublicCoin protocol) → PublicCoin (compile Com coin)
  | _, .done => .done
  | _, @PublicCoin.sender _ _ _ next => .sender (fun move => compiledCoin Com (next move))
  | _, @PublicCoin.oracle _ _ _ _ next => .sender (fun _ => compiledCoin Com next)
  | _, @PublicCoin.challenge _ _ _ next => .challenge (compiledCoin Com next)

/-- Oracle occurrences on one compiled path. The left summand names the current commitment;
the right summand names an occurrence in its tail. Public moves select the dependent tail. -/
@[reducible] def MessageIndex {Com : Type} : {protocol : Protocol} → (coin : PublicCoin protocol) →
    (compile Com coin).tree.ExecutionPath → Type
  | _, .done, _ => Empty
  | _, @PublicCoin.sender _ _ _ next, path => MessageIndex (next path.1) path.2
  | _, @PublicCoin.oracle _ _ _ _ next, path => Unit ⊕ MessageIndex next path.2
  | _, @PublicCoin.challenge _ _ _ next, path => MessageIndex next path.2

/-- The original oracle-message carrier at a selected occurrence, including dependent tails. -/
@[reducible] def MessageType {Com : Type} : {protocol : Protocol} → (coin : PublicCoin protocol) →
    (path : (compile Com coin).tree.ExecutionPath) → MessageIndex coin path → Type
  | _, .done, _, index => nomatch index
  | _, @PublicCoin.sender _ _ _ next, path, index => MessageType (next path.1) path.2 index
  | _, @PublicCoin.oracle Messages _ _ _ next, path, index =>
      match index with
      | .inl _ => Messages
      | .inr index => MessageType next path.2 index
  | _, @PublicCoin.challenge _ _ _ next, path, index => MessageType next path.2 index

/-- One extracted oracle message for every commitment occurrence on the selected path. -/
abbrev ExtractedMessages {Com : Type} {protocol : Protocol} (coin : PublicCoin protocol)
    (path : (compile Com coin).tree.ExecutionPath) :=
  (index : MessageIndex coin path) → MessageType coin path index

/-- Replace commitments by the supplied messages, retaining every public move and challenge. -/
def extractedPath {Com : Type} : {protocol : Protocol} → (coin : PublicCoin protocol) →
    (path : (compile Com coin).tree.ExecutionPath) →
    ExtractedMessages coin path → protocol.tree.ExecutionPath
  | _, .done, _, _ => PUnit.unit
  | _, @PublicCoin.sender _ _ _ next, path, messages =>
      ⟨path.1, extractedPath (next path.1) path.2 messages⟩
  | _, @PublicCoin.oracle _ _ _ _ next, path, messages =>
      ⟨messages (.inl ()), extractedPath next path.2 (fun index => messages (.inr index))⟩
  | _, @PublicCoin.challenge _ _ _ next, path, messages =>
      ⟨path.1, extractedPath next path.2 messages⟩

/-- A compiled Fiat–Shamir proof retains abstract verifier opening data beside the full path. -/
abbrev FSProof (Statement Com Openings : Type) {protocol : Statement → Protocol}
    (coin : (statement : Statement) → PublicCoin (protocol statement)) :=
  (statement : Statement) × ((compile Com (coin statement)).tree.ExecutionPath × Openings)

/-- The underlying compiled statement and path, with the opening data forgotten. -/
def FSProof.toCI {Statement Com Openings : Type} {protocol : Statement → Protocol}
    {coin : (statement : Statement) → PublicCoin (protocol statement)}
    (proof : FSProof Statement Com Openings coin) :
    CorrelationIntractable.FSProof Statement (fun statement => compile Com (coin statement)) :=
  ⟨proof.1, proof.2.1⟩

/-- Acceptance checks the compiled challenge table and the verifier's abstract opening predicate. -/
def verify {Statement Com Openings : Type} [DecidableEq Com]
    {protocol : Statement → Protocol}
    (coin : (statement : Statement) → PublicCoin (protocol statement))
    (h : Table Statement PUnit (fun statement => compiledCoin Com (coin statement)))
    (accept : FSProof Statement Com Openings coin → Prop)
    (proof : FSProof Statement Com Openings coin) : Prop :=
  Consistent (compiledCoin Com (coin proof.1)) (Table.fibre h proof.1) proof.2.1 ∧
    accept proof

/-- The rank-`r` existential knowledge escape on a concrete IOP path; rank counts verifier moves.
The later witness is local to the edge and is not extracted from the future suffix. -/
def pathEscapeAt : {protocol : Protocol} → (coin : PublicCoin protocol) →
    {state : KnowledgeState} → RoundExtractor protocol.tree state →
    protocol.tree.ExecutionPath → ℕ → Prop
  | _, .done, _, _, _, _ => False
  | _, @PublicCoin.sender _ _ _ next, _, extractor, path, r =>
      pathEscapeAt (next path.1) (extractor path.1).2.2 path.2 r
  | _, @PublicCoin.oracle _ _ _ _ next, _, extractor, path, r =>
      pathEscapeAt next (extractor path.1).2.2 path.2 r
  | _, @PublicCoin.challenge _ _ _ _, _, extractor, path, 0 =>
      RoundExtractor.badChallenge extractor path.1
  | _, @PublicCoin.challenge _ _ _ next, _, extractor, path, r + 1 =>
      pathEscapeAt next (extractor path.1).2.2 path.2 r

/-- The extracted IOP path escapes at rank `r`, with its compiled challenges equal to the table
through that rank. Only the strict ancestors and target key are read, never the later suffix. -/
def escapeAt {Com : Type} [DecidableEq Com] :
    {protocol : Protocol} → (coin : PublicCoin protocol) →
    {state : KnowledgeState} → RoundExtractor protocol.tree state →
    (path : (compile Com coin).tree.ExecutionPath) → ExtractedMessages coin path →
    PrefixTable PUnit (compiledCoin Com coin) → ℕ → Prop
  | _, .done, _, _, _, _, _, _ => False
  | _, @PublicCoin.sender _ _ _ next, _, extractor, path, messages, table, r =>
      escapeAt (next path.1) (extractor path.1).2.2 path.2 messages
        (fun pre => table ⟨path.1, pre⟩) r
  | _, @PublicCoin.oracle _ _ _ _ next, _, extractor, path, messages, table, r =>
      escapeAt next (extractor (messages (.inl ()))).2.2 path.2
        (fun index => messages (.inr index)) (fun pre => table ⟨path.1, pre⟩) r
  | _, @PublicCoin.challenge _ _ _ _, _, extractor, path, _, table, 0 =>
      path.1 = table (.inl PUnit.unit) ∧ RoundExtractor.badChallenge extractor path.1
  | _, @PublicCoin.challenge _ _ _ next, _, extractor, path, messages, table, r + 1 =>
      path.1 = table (.inl PUnit.unit) ∧
        escapeAt next (extractor path.1).2.2 path.2 messages
          (fun pre => table (.inr ⟨PUnit.unit, pre⟩)) r

/-- For a table-consistent proof the local CI event is exactly its extracted path's escape. -/
theorem escapeAt_iff_pathEscapeAt {Com : Type} [DecidableEq Com] {protocol : Protocol}
    (coin : PublicCoin protocol) {state : KnowledgeState}
    (extractor : RoundExtractor protocol.tree state)
    (path : (compile Com coin).tree.ExecutionPath) (messages : ExtractedMessages coin path)
    (table : PrefixTable PUnit (compiledCoin Com coin))
    (consistent : Consistent (compiledCoin Com coin) table path) (r : ℕ) :
    escapeAt coin extractor path messages table r ↔
      pathEscapeAt coin extractor (extractedPath coin path messages) r := by
  induction coin generalizing state r with
  | done => exact Iff.rfl
  | sender next ih =>
      exact ih path.1 (extractor path.1).2.2 path.2 messages _ consistent r
  | oracle next ih =>
      exact ih (extractor (messages (.inl ()))).2.2 path.2
        (fun index => messages (.inr index)) _ consistent r
  | challenge next ih =>
      cases r with
      | zero => exact and_iff_right consistent.1
      | succ r =>
          exact (and_iff_right consistent.1).trans
            (ih (extractor path.1).2.2 path.2 messages _ consistent.2 r)

/-- At a selected rank, table dependence is confined to strict ancestors and the target answer.
The compiled key, path, extracted words and witness maps are held fixed in this comparison.
`CorrelationIntractable.prefixes_congr` supplies the compiled-prefix reconstruction law. -/
theorem escapeAt_congr {Com : Type} [DecidableEq Com] {protocol : Protocol}
    (coin : PublicCoin protocol) {state : KnowledgeState}
    (extractor : RoundExtractor protocol.tree state)
    (path : (compile Com coin).tree.ExecutionPath) (messages : ExtractedMessages coin path)
    (table other : PrefixTable PUnit (compiledCoin Com coin))
    (r : ℕ) (pre : Prefix PUnit (compiledCoin Com coin))
    (selected : (prefixKeys (compiledCoin Com coin)
      (erasePath (compiledCoin Com coin) path))[r]? = some pre)
    (ancestors : ∀ ancestor ∈ strictAncestors (compiledCoin Com coin) pre,
      table ancestor = other ancestor)
    (answer : table pre = other pre) :
    escapeAt coin extractor path messages table r ↔
      escapeAt coin extractor path messages other r := by
  induction coin generalizing state r with
  | done => exact pre.elim
  | sender next ih =>
      simp only [compiledCoin, erasePath, prefixKeys] at selected
      erw [List.getElem?_map, Option.map_eq_some_iff] at selected
      obtain ⟨pre, selected, rfl⟩ := selected
      exact ih path.1 (extractor path.1).2.2 path.2 messages _ _ r pre selected
        (fun ancestor member => ancestors ⟨path.1, ancestor⟩
          (List.mem_map.mpr ⟨ancestor, member, rfl⟩)) answer
  | oracle next ih =>
      simp only [compiledCoin, erasePath, prefixKeys] at selected
      erw [List.getElem?_map, Option.map_eq_some_iff] at selected
      obtain ⟨pre, selected, rfl⟩ := selected
      exact ih (extractor (messages (.inl ()))).2.2 path.2
        (fun index => messages (.inr index)) _ _ r pre selected
        (fun ancestor member => ancestors ⟨path.1, ancestor⟩
          (List.mem_map.mpr ⟨ancestor, member, rfl⟩)) answer
  | challenge next ih =>
      cases r with
      | zero =>
          simp only [compiledCoin, erasePath, prefixKeys] at selected
          erw [List.getElem?_cons_zero, Option.some.injEq] at selected
          subst pre
          simp only [escapeAt, answer]
      | succ r =>
          simp only [compiledCoin, erasePath, prefixKeys] at selected
          erw [List.getElem?_cons_succ, List.getElem?_map, Option.map_eq_some_iff] at selected
          obtain ⟨pre, selected, rfl⟩ := selected
          have head := ancestors (.inl PUnit.unit) List.mem_cons_self
          exact and_congr (congrArg (fun value => path.1 = value) head).to_iff
            (ih (extractor path.1).2.2 path.2 messages _ _ r pre selected
              (fun ancestor member => ancestors (.inr ⟨PUnit.unit, ancestor⟩)
                (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨ancestor, member, rfl⟩))) answer)

/-- The compiled strict-ancestor relation is well founded by the number of earlier challenges. -/
theorem strictAncestors_wellFounded {Com : Type} [DecidableEq Com] {protocol : Protocol}
    (coin : PublicCoin protocol) :
    WellFounded (fun ancestor pre => ancestor ∈ strictAncestors (compiledCoin Com coin) pre) :=
  CorrelationIntractable.strictAncestors_wellFounded (compiledCoin Com coin)

/-- A bad challenge with its actual suffix-extracted witness gives an existential local escape
at some challenge rank on the same IOP path. -/
theorem badChallengeOnPath_implies_exists_pathEscapeAt {protocol : Protocol}
    (coin : PublicCoin protocol) {state : KnowledgeState}
    (extractor : RoundExtractor protocol.tree state) (path : protocol.tree.ExecutionPath)
    (witness : (extractor.terminalState path).Witness)
    (bad : extractor.BadChallengeOnPath protocol.roles path witness) :
    ∃ r, pathEscapeAt coin extractor path r := by
  induction coin generalizing state with
  | done => exact bad.elim
  | sender next ih =>
      rcases bad with ⟨impossible, _, _⟩ | bad
      · cases impossible
      · exact ih path.1 (extractor path.1).2.2 path.2 witness bad
  | oracle next ih =>
      exact ih (extractor path.1).2.2 path.2 witness bad
  | challenge next ih =>
      rcases bad with ⟨_, before, after⟩ | bad
      · exact ⟨0, ⟨_, before, after⟩⟩
      · obtain ⟨r, escape⟩ := ih (extractor path.1).2.2 path.2 witness bad
        exact ⟨r + 1, escape⟩

/-- An extracted path's escape rank is smaller than its compiled path's challenge-key count. -/
theorem pathEscapeAt_rank_lt {Com : Type} [DecidableEq Com] {protocol : Protocol}
    (coin : PublicCoin protocol) {state : KnowledgeState}
    (extractor : RoundExtractor protocol.tree state)
    (path : (compile Com coin).tree.ExecutionPath) (messages : ExtractedMessages coin path)
    (r : ℕ) (escape : pathEscapeAt coin extractor (extractedPath coin path messages) r) :
    r < (prefixKeys (compiledCoin Com coin)
      (erasePath (compiledCoin Com coin) path)).length := by
  induction coin generalizing state r with
  | done => exact escape.elim
  | sender next ih =>
      simpa only [compiledCoin, erasePath, prefixKeys, List.length_map] using
        ih path.1 (extractor path.1).2.2 path.2 messages r escape
  | oracle next ih =>
      simpa only [compiledCoin, erasePath, prefixKeys, List.length_map] using
        ih (extractor (messages (.inl ()))).2.2 path.2
          (fun index => messages (.inr index)) r escape
  | challenge next ih =>
      cases r with
      | zero =>
          exact Nat.zero_lt_succ _
      | succ r =>
          simpa only [compiledCoin, erasePath, prefixKeys, List.length_cons, List.length_map]
            using Nat.succ_lt_succ (ih (extractor path.1).2.2 path.2 messages r escape)

/-- A valid terminal witness whose backward extraction fails produces a rank-local escape.
The rank is the zero-based position of a challenge in the compiled path's key list. -/
theorem extraction_failure_implies_escapeAt {Com : Type} [DecidableEq Com]
    {protocol : Protocol} (coin : PublicCoin protocol) {state : KnowledgeState}
    (certificate : KnowledgeCertificate protocol.tree protocol.roles state)
    (path : (compile Com coin).tree.ExecutionPath) (messages : ExtractedMessages coin path)
    (table : PrefixTable PUnit (compiledCoin Com coin))
    (consistent : Consistent (compiledCoin Com coin) table path)
    (witness : (certificate.extractor.terminalState (extractedPath coin path messages)).Witness)
    (terminal : (certificate.extractor.terminalState (extractedPath coin path messages)).holds
      witness)
    (failure : ¬ state.holds
      (certificate.extractor.extractWitness (extractedPath coin path messages) witness)) :
    ∃ r < (prefixKeys (compiledCoin Com coin)
      (erasePath (compiledCoin Com coin) path)).length,
      escapeAt coin certificate.extractor path messages table r := by
  have bad := certificate.extractor.extraction_failure_implies_bad_challenge protocol.roles
    certificate.prover_preserving (extractedPath coin path messages) witness terminal failure
  obtain ⟨r, escape⟩ := badChallengeOnPath_implies_exists_pathEscapeAt coin
    certificate.extractor (extractedPath coin path messages) witness bad
  exact ⟨r, pathEscapeAt_rank_lt coin certificate.extractor path messages r escape,
    (escapeAt_iff_pathEscapeAt coin certificate.extractor path messages table consistent r).mpr
      escape⟩

/-- The compiled protocol has at most `count` challenges along every complete path.
Ranks are key-list positions, so no separately normalized rank function is required. -/
def ChallengeBound {Statement Com : Type} [DecidableEq Com]
    {protocol : Statement → Protocol}
    (coin : (statement : Statement) → PublicCoin (protocol statement)) (count : ℕ) : Prop :=
  ∀ statement (path : (compile Com (coin statement)).tree.ExecutionPath),
    (prefixKeys (compiledCoin Com (coin statement))
      (erasePath (compiledCoin Com (coin statement)) path)).length ≤ count

section Extraction

variable {Statement Com Openings Coins : Type} {protocol : Statement → Protocol}
    (coin : (statement : Statement) → PublicCoin (protocol statement))
    (state : Statement → KnowledgeState)
    (certificate : (statement : Statement) →
      KnowledgeCertificate (protocol statement).tree (protocol statement).roles (state statement))
    (extractor : (statement : Statement) →
      RoundExtractor (protocol statement).tree (state statement))
    (A : Coins → FSProof Statement Com Openings coin)
    (ext : (c : Coins) → ExtractedMessages (coin (A c).1) (A c).2.1)

/-- Run `A` on its explicit coins, then extract each committed message, then run the supplied
    extractor's
backward witness maps on that extracted IOP path and the supplied terminal witness. -/
def compositeExtractor
    (terminalWitness : (c : Coins) → ((extractor (A c).1).terminalState
      (extractedPath (coin (A c).1) (A c).2.1 (ext c))).Witness)
    (c : Coins) : (state (A c).1).Witness :=
  let proof := A c
  let messages := ext c
  let path := extractedPath (coin proof.1) proof.2.1 messages
  (extractor proof.1).extractWitness path (terminalWitness c)

/-- The per-round CI game relative to the message extractor: the compiled path is consistent
with `h` through rank `r`, and the challenge `h` of its compiled key escapes on the extracted
prefix. The relation is fixed by the IOP certificate, and the oracle messages come from `ext`.
The existential later witness is inside the event. -/
noncomputable def ciRel [DecidableEq Com] [SampleableType Coins]
    (h : Table Statement PUnit (fun statement => compiledCoin Com (coin statement)))
    (r : ℕ) : ℝ≥0∞ :=
  Pr{let c ← ($ᵗ Coins : ProbComp Coins)}[
    escapeAt (coin (A c).1) (certificate (A c).1).extractor
      (A c).2.1 (ext c) (Table.fibre h (A c).1) r]

/-- Accepted extraction failure is contained in disagreement or a bounded-rank CI escape.
The transfer hypothesis asserts the certificate's terminal relation for the supplied witness. -/
theorem failure_implies_disagree_or_escape [DecidableEq Com]
    (h : Table Statement PUnit (fun statement => compiledCoin Com (coin statement)))
    (accept : FSProof Statement Com Openings coin → Prop)
    (terminalWitness : (c : Coins) → ((certificate (A c).1).extractor.terminalState
      (extractedPath (coin (A c).1) (A c).2.1 (ext c))).Witness)
    (Disagree : Coins → Prop)
    (transfer : ∀ c, verify coin h accept (A c) → ¬ Disagree c →
      ((certificate (A c).1).extractor.terminalState
        (extractedPath (coin (A c).1) (A c).2.1 (ext c))).holds (terminalWitness c))
    (count : ℕ) (bound : ChallengeBound (Com := Com) coin count)
    (c : Coins) (accepted : verify coin h accept (A c))
    (failure : ¬ (state (A c).1).holds
      (compositeExtractor coin state (fun s => (certificate s).extractor) A ext terminalWitness
        c)) :
    Disagree c ∨ ∃ r ∈ Finset.range count,
      escapeAt (coin (A c).1) (certificate (A c).1).extractor
        (A c).2.1 (ext c) (Table.fibre h (A c).1) r := by
  by_cases disagree : Disagree c
  · exact Or.inl disagree
  · obtain ⟨r, bounded, escape⟩ := extraction_failure_implies_escapeAt
      (coin (A c).1) (certificate (A c).1) (A c).2.1 (ext c)
      (Table.fibre h (A c).1) accepted.1 (terminalWitness c)
      (transfer c accepted disagree) failure
    exact Or.inr ⟨r, Finset.mem_range.mpr (bounded.trans_le (bound (A c).1 (A c).2.1)),
      escape⟩

/-- A single same-coins game combines disagreement and all compiled CI ranks. -/
theorem knowledgeSoundness_union [DecidableEq Com] [SampleableType Coins]
    (h : Table Statement PUnit (fun statement => compiledCoin Com (coin statement)))
    (accept : FSProof Statement Com Openings coin → Prop)
    (terminalWitness : (c : Coins) → ((certificate (A c).1).extractor.terminalState
      (extractedPath (coin (A c).1) (A c).2.1 (ext c))).Witness)
    (Disagree : Coins → Prop)
    (transfer : ∀ c, verify coin h accept (A c) → ¬ Disagree c →
      ((certificate (A c).1).extractor.terminalState
        (extractedPath (coin (A c).1) (A c).2.1 (ext c))).holds (terminalWitness c))
    (count : ℕ) (bound : ChallengeBound (Com := Com) coin count) :
    Pr{let c ← ($ᵗ Coins : ProbComp Coins)}[
      verify coin h accept (A c) ∧ ¬ (state (A c).1).holds
        (compositeExtractor coin state (fun s => (certificate s).extractor) A ext terminalWitness
          c)] ≤
      Pr{let c ← ($ᵗ Coins : ProbComp Coins)}[
        Disagree c ∨ ∃ r ∈ Finset.range count,
          escapeAt (coin (A c).1) (certificate (A c).1).extractor
            (A c).2.1 (ext c) (Table.fibre h (A c).1) r] := by
  exact prEvent_mono _ _ _ (fun c bad => failure_implies_disagree_or_escape
    coin state certificate A ext h accept terminalWitness Disagree transfer count bound
    c bad.1 bad.2)

/-- The disagreement and rank sum follows from the same-coins union game. -/
theorem knowledgeSoundness [DecidableEq Com] [SampleableType Coins]
    (h : Table Statement PUnit (fun statement => compiledCoin Com (coin statement)))
    (accept : FSProof Statement Com Openings coin → Prop)
    (terminalWitness : (c : Coins) → ((certificate (A c).1).extractor.terminalState
      (extractedPath (coin (A c).1) (A c).2.1 (ext c))).Witness)
    (Disagree : Coins → Prop)
    (transfer : ∀ c, verify coin h accept (A c) → ¬ Disagree c →
      ((certificate (A c).1).extractor.terminalState
        (extractedPath (coin (A c).1) (A c).2.1 (ext c))).holds (terminalWitness c))
    (count : ℕ) (bound : ChallengeBound (Com := Com) coin count) :
    Pr{let c ← ($ᵗ Coins : ProbComp Coins)}[
      verify coin h accept (A c) ∧ ¬ (state (A c).1).holds
        (compositeExtractor coin state (fun s => (certificate s).extractor) A ext terminalWitness
          c)] ≤
      Pr{let c ← ($ᵗ Coins : ProbComp Coins)}[Disagree c] +
        ∑ r ∈ Finset.range count, ciRel coin state certificate A ext h r := by
  let escape := fun r c => escapeAt (coin (A c).1) (certificate (A c).1).extractor
    (A c).2.1 (ext c) (Table.fibre h (A c).1) r
  calc
    _ ≤ Pr{let c ← ($ᵗ Coins : ProbComp Coins)}[
        Disagree c ∨ ∃ r ∈ Finset.range count, escape r c] :=
      knowledgeSoundness_union coin state certificate A ext h accept terminalWitness Disagree
        transfer count bound
    _ ≤ Pr{let c ← ($ᵗ Coins : ProbComp Coins)}[Disagree c] +
        Pr{let c ← ($ᵗ Coins : ProbComp Coins)}[∃ r ∈ Finset.range count, escape r c] :=
      prEvent_or_le _ _ _
    _ ≤ _ := add_le_add le_rfl
      (prEvent_exists_finset_le (Finset.range count) ($ᵗ Coins : ProbComp Coins) escape)

end Extraction


/-- Extracted oracle messages and actual earlier challenge answers, with no future suffix. -/
@[reducible] def PrefixMessages {Com : Type} [DecidableEq Com] :
    {protocol : Protocol} → (coin : PublicCoin protocol) →
    Prefix PUnit (compiledCoin Com coin) → Type
  | _, .done, pre => nomatch pre
  | _, @PublicCoin.sender _ _ _ next, pre => PrefixMessages (next pre.1) pre.2
  | _, @PublicCoin.oracle Messages _ _ _ next, pre => Messages × PrefixMessages next pre.2
  | _, @PublicCoin.challenge Challenge _ _ next, pre => match pre with
      | .inl _ => PUnit
      | .inr ⟨_, pre⟩ => Challenge × PrefixMessages next pre

/-- Select a challenge key and only the extracted oracle prefix preceding that key. -/
def selectedPrefix {Com : Type} [DecidableEq Com] :
    {protocol : Protocol} → (coin : PublicCoin protocol) →
    (path : (compile Com coin).tree.ExecutionPath) → ExtractedMessages coin path → ℕ →
    Option ((pre : Prefix PUnit (compiledCoin Com coin)) × PrefixMessages coin pre)
  | _, .done, _, _, _ => none
  | _, @PublicCoin.sender _ _ _ next, path, messages, r =>
      (selectedPrefix (next path.1) path.2 messages r).map fun ⟨pre, words⟩ =>
        ⟨⟨path.1, pre⟩, words⟩
  | _, @PublicCoin.oracle _ _ _ _ next, path, messages, r =>
      (selectedPrefix next path.2 (fun i => messages (.inr i)) r).map fun ⟨pre, words⟩ =>
        ⟨⟨path.1, pre⟩, messages (.inl ()) , words⟩
  | _, @PublicCoin.challenge _ _ _ _, _, _, 0 => some ⟨.inl PUnit.unit, PUnit.unit⟩
  | _, @PublicCoin.challenge _ _ _ next, path, messages, r + 1 =>
      (selectedPrefix next path.2 messages r).map fun ⟨pre, words⟩ =>
        ⟨.inr ⟨PUnit.unit, pre⟩, path.1, words⟩

/-- Every local escape has a selected compiled key and an extracted strict prefix. -/
theorem selectedPrefix_some_of_escape {Com : Type} [DecidableEq Com] {protocol : Protocol}
    (coin : PublicCoin protocol) {state : KnowledgeState}
    (extractor : RoundExtractor protocol.tree state)
    (path : (compile Com coin).tree.ExecutionPath) (messages : ExtractedMessages coin path)
    (table : PrefixTable PUnit (compiledCoin Com coin)) (r : ℕ)
    (escape : escapeAt coin extractor path messages table r) :
    ∃ selected, selectedPrefix coin path messages r = some selected := by
  induction coin generalizing state r with
  | done => exact escape.elim
  | sender next ih =>
      obtain ⟨selected, hs⟩ := ih path.1 (extractor path.1).2.2 path.2 messages _ r escape
      simp only [selectedPrefix, hs, Option.map_some]
      exact ⟨_, rfl⟩
  | oracle next ih =>
      obtain ⟨selected, hs⟩ := ih (extractor (messages (.inl ()))).2.2 path.2
        (fun i => messages (.inr i)) _ r escape
      simp only [selectedPrefix, hs, Option.map_some]
      exact ⟨_, rfl⟩
  | challenge next ih =>
      cases r with
      | zero => exact ⟨_, rfl⟩
      | succ r =>
          obtain ⟨selected, hs⟩ := ih (extractor path.1).2.2 path.2 messages _ r escape.2
          simp only [selectedPrefix, hs, Option.map_some]
          exact ⟨_, rfl⟩

/-- Check earlier witness challenges against the table using executable equality. -/
def prefixConsistent {Com : Type} [DecidableEq Com] :
    {protocol : Protocol} → (coin : PublicCoin protocol) →
    (pre : Prefix PUnit (compiledCoin Com coin)) → PrefixMessages coin pre →
    PrefixTable PUnit (compiledCoin Com coin) →
    ((pre : Prefix PUnit (compiledCoin Com coin)) → DecidableEq pre.Challenge) → Bool
  | _, .done, pre, _, _, _ => nomatch pre
  | _, @PublicCoin.sender _ _ _ next, pre, words, table, equality =>
      prefixConsistent (next pre.1) pre.2 words (fun q => table ⟨pre.1, q⟩)
        (fun q => equality ⟨pre.1, q⟩)
  | _, @PublicCoin.oracle _ _ _ _ next, pre, words, table, equality =>
      prefixConsistent next pre.2 words.2 (fun q => table ⟨pre.1, q⟩)
        (fun q => equality ⟨pre.1, q⟩)
  | _, @PublicCoin.challenge _ _ _ next, pre, words, table, equality =>
      match pre with
      | .inl _ => true
      | .inr ⟨salt, pre⟩ =>
          @decide _ (equality (.inl salt) words.1 (table (.inl salt))) &&
            prefixConsistent next pre words.2 (fun q => table (.inr ⟨salt, q⟩))
              (fun q => equality (.inr ⟨salt, q⟩))

/-- A selected escaping prefix carries table-consistent earlier challenges on the same coins. -/
theorem prefixConsistent_of_escape {Com : Type} [DecidableEq Com] {protocol : Protocol}
    (coin : PublicCoin protocol) {state : KnowledgeState}
    (extractor : RoundExtractor protocol.tree state)
    (path : (compile Com coin).tree.ExecutionPath) (messages : ExtractedMessages coin path)
    (table : PrefixTable PUnit (compiledCoin Com coin))
    (equality : (pre : Prefix PUnit (compiledCoin Com coin)) → DecidableEq pre.Challenge)
    (r : ℕ) selected (hs : selectedPrefix coin path messages r = some selected)
    (escape : escapeAt coin extractor path messages table r) :
    prefixConsistent coin selected.1 selected.2 table equality = true := by
  induction coin generalizing state r with
  | done => exact escape.elim
  | sender next ih =>
      simp only [selectedPrefix, Option.map_eq_some_iff] at hs
      obtain ⟨⟨pre, words⟩, hs, heq⟩ := hs
      cases heq
      exact ih path.1 (extractor path.1).2.2 path.2 messages _ _ r _ hs escape
  | oracle next ih =>
      simp only [selectedPrefix, Option.map_eq_some_iff] at hs
      obtain ⟨⟨pre, words⟩, hs, heq⟩ := hs
      cases heq
      exact ih (extractor (messages (.inl ()))).2.2 path.2
        (fun i => messages (.inr i)) _ _ r _ hs escape
  | challenge next ih =>
      cases r with
      | zero =>
          simp only [selectedPrefix, Option.some.injEq] at hs
          cases hs
          rfl
      | succ r =>
          simp only [selectedPrefix, Option.map_eq_some_iff] at hs
          obtain ⟨⟨pre, words⟩, hs, heq⟩ := hs
          cases heq
          simp only [prefixConsistent, Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨escape.1, ih (extractor path.1).2.2 path.2 messages _ _ r _ hs escape.2⟩

/-- A falsifiable relation authenticates masked prefixes and classifies query keys. A query key's
event is monotone only on complete prefixes, whose committed words reveal every column. -/
structure WitnessCIRelation {Statement Com : Type} [DecidableEq Com]
    {protocol : Statement → Protocol}
    (coin : (statement : Statement) → PublicCoin (protocol statement)) where
  /-- Executable challenge equality is supplied for every typed compiled key. -/
  challengeEq : (key : Key Statement PUnit (fun s => compiledCoin Com (coin s))) →
    DecidableEq key.Challenge
  /-- Query keys enter the witness game only on complete prefixes. -/
  isQuery : Key Statement PUnit (fun s => compiledCoin Com (coin s)) → Bool
  /-- Every committed word read by this key's event reveals all of its columns. -/
  complete : (key : Key Statement PUnit (fun s => compiledCoin Com (coin s))) →
    PrefixMessages (coin key.1) key.2 → Bool
  /-- The Merkle authentication carrier for this key's strict prefix. -/
  Authentication : Key Statement PUnit (fun s => compiledCoin Com (coin s)) → Type
  /-- Authentication checks the revealed columns against the commitments encoded in the key. -/
  authenticate : (key : Key Statement PUnit (fun s => compiledCoin Com (coin s))) →
    PrefixMessages (coin key.1) key.2 → Authentication key → Bool
  /-- Hiding columns retains their known values throughout the strict prefix. -/
  MaskLE : (key : Key Statement PUnit (fun s => compiledCoin Com (coin s))) →
    PrefixMessages (coin key.1) key.2 → PrefixMessages (coin key.1) key.2 → Prop
  /-- The mathematical bad event depends only on a masked prefix and target answer. -/
  Bad : (key : Key Statement PUnit (fun s => compiledCoin Com (coin s))) →
    PrefixMessages (coin key.1) key.2 → key.Challenge → Prop
  /-- The bad-event checker is executable and reads no extractor. -/
  check : (key : Key Statement PUnit (fun s => compiledCoin Com (coin s))) →
    PrefixMessages (coin key.1) key.2 → key.Challenge → Bool
  /-- The executable checker decides the mathematical bad event. -/
  check_iff : ∀ key words α, check key words α = true ↔ Bad key words α
  /-- Hiding columns cannot create a bad event at an algebraic key or a complete query prefix. -/
  monotone : ∀ key small large, MaskLE key small large →
    (isQuery key = true → complete key small = true) → ∀ α, Bad key small α → Bad key large α
  /-- The existing per-word error, without a mask or rate penalty. -/
  error : Key Statement PUnit (fun s => compiledCoin Com (coin s)) → Erased ℝ≥0∞
  /-- Each fixed masked prefix has its original uniform challenge bound. -/
  bad_bound : ∀ key words,
    Pr{let α ← ($ᵗ key.Challenge : ProbComp key.Challenge)}[Bad key words α] ≤ (error key).out

/-- A knowledge certificate whose local escapes lie in the authenticated bad events. -/
structure WitnessKnowledgeCertificate {Statement Com : Type} [DecidableEq Com]
    {protocol : Statement → Protocol}
    (coin : (statement : Statement) → PublicCoin (protocol statement))
    (state : Statement → KnowledgeState)
    (certificate : (s : Statement) → KnowledgeCertificate
      (protocol s).tree (protocol s).roles (state s))
    extends WitnessCIRelation (Com := Com) coin where
  /-- Every local escape is contained in the prefix's bad event on the same table. -/
  escape_subset : ∀ s (path : (compile Com (coin s)).tree.ExecutionPath)
    (messages : ExtractedMessages (coin s) path)
    (table : PrefixTable PUnit (compiledCoin Com (coin s))) r selected,
    selectedPrefix (coin s) path messages r = some selected →
    escapeAt (coin s) (certificate s).extractor path messages table r →
    Bad ⟨s, selected.1⟩ selected.2 (table selected.1)

/-- A witness-CI adversary outputs a statement-key, masked prefix, and its authentication. -/
abbrev WitnessCIOutput {Statement Com : Type} [DecidableEq Com]
    {protocol : Statement → Protocol}
    {coin : (s : Statement) → PublicCoin (protocol s)}
    (relation : WitnessCIRelation (Com := Com) coin) :=
  (key : Key Statement PUnit (fun s => compiledCoin Com (coin s))) ×
    PrefixMessages (coin key.1) key.2 × relation.Authentication key

/-- Check the authenticated masked witness and earlier-challenge consistency at one compiled key;
a query key additionally needs a complete prefix. -/
def witnessCheck {Statement Com : Type} [DecidableEq Com]
    {protocol : Statement → Protocol} {coin : (s : Statement) → PublicCoin (protocol s)}
    (relation : WitnessCIRelation (Com := Com) coin)
    (h : Table Statement PUnit (fun s => compiledCoin Com (coin s)))
    (output : Option (WitnessCIOutput relation)) : Bool :=
  match output with
    | none => false
    | some ⟨key, words, auth⟩ => (!relation.isQuery key || relation.complete key words) &&
        prefixConsistent (coin key.1) key.2 words (Table.fibre h key.1)
          (fun pre => relation.challengeEq ⟨key.1, pre⟩) &&
        relation.authenticate key words auth && relation.check key words (h key)

/-- The witness game checks authentication and the monotone bad set at the hash of the key. -/
def witnessCIGame {Statement Com Coins : Type} [DecidableEq Com] [SampleableType Coins]
    {protocol : Statement → Protocol} {coin : (s : Statement) → PublicCoin (protocol s)}
    (relation : WitnessCIRelation (Com := Com) coin)
    (h : Table Statement PUnit (fun s => compiledCoin Com (coin s)))
    (B : Coins → Option (WitnessCIOutput relation)) : ProbComp Bool := do
  let c ← $ᵗ Coins
  return witnessCheck relation h (B c)

/-- Winning probability of the executable witness-CI experiment. -/
noncomputable def witnessCI {Statement Com Coins : Type} [DecidableEq Com] [SampleableType Coins]
    {protocol : Statement → Protocol} {coin : (s : Statement) → PublicCoin (protocol s)}
    (relation : WitnessCIRelation (Com := Com) coin)
    (h : Table Statement PUnit (fun s => compiledCoin Com (coin s)))
    (B : Coins → Option (WitnessCIOutput relation)) : ℝ≥0∞ :=
  Pr{let won ← witnessCIGame relation h B}[won = true]

/-- Run the proof adversary and its same-coins authenticated masked extractor at a selected rank. -/
def reductionAdversary {Statement Com Openings Coins : Type} [DecidableEq Com]
    {protocol : Statement → Protocol} {coin : (s : Statement) → PublicCoin (protocol s)}
    (relation : WitnessCIRelation (Com := Com) coin)
    (A : Coins → FSProof Statement Com Openings coin)
    (ext : (c : Coins) → ExtractedMessages (coin (A c).1) (A c).2.1)
    (auth : (c : Coins) → (pre : Prefix PUnit (compiledCoin Com (coin (A c).1))) →
      relation.Authentication ⟨(A c).1, pre⟩) (r : ℕ) (c : Coins) :
    Option (WitnessCIOutput relation) :=
  (selectedPrefix (coin (A c).1) (A c).2.1 (ext c) r).map fun ⟨pre, words⟩ =>
    ⟨⟨(A c).1, pre⟩, words, auth c pre⟩

/-- Residual extractor-relative CI is restricted to query keys with an incomplete prefix. -/
def QueryEscape {Statement Com Openings Coins : Type} [DecidableEq Com]
    {protocol : Statement → Protocol} {coin : (s : Statement) → PublicCoin (protocol s)}
    (relation : WitnessCIRelation (Com := Com) coin)
    (state : Statement → KnowledgeState)
    (certificate : (s : Statement) → KnowledgeCertificate
      (protocol s).tree (protocol s).roles (state s))
    (A : Coins → FSProof Statement Com Openings coin)
    (ext : (c : Coins) → ExtractedMessages (coin (A c).1) (A c).2.1)
    (h : Table Statement PUnit (fun s => compiledCoin Com (coin s))) (r : ℕ) (c : Coins) : Prop :=
  (∃ selected, selectedPrefix (coin (A c).1) (A c).2.1 (ext c) r = some selected ∧
    relation.isQuery ⟨(A c).1, selected.1⟩ = true ∧
    relation.complete ⟨(A c).1, selected.1⟩ selected.2 = false) ∧
  escapeAt (coin (A c).1) (certificate (A c).1).extractor (A c).2.1 (ext c)
    (Table.fibre h (A c).1) r

/-- Only query escapes on incomplete prefixes contribute to the extractor-relative residual. -/
noncomputable def queryRel {Statement Com Openings Coins : Type} [DecidableEq Com]
    [SampleableType Coins] {protocol : Statement → Protocol}
    {coin : (s : Statement) → PublicCoin (protocol s)}
    (relation : WitnessCIRelation (Com := Com) coin)
    (state : Statement → KnowledgeState)
    (certificate : (s : Statement) → KnowledgeCertificate
      (protocol s).tree (protocol s).roles (state s))
    (A : Coins → FSProof Statement Com Openings coin)
    (ext : (c : Coins) → ExtractedMessages (coin (A c).1) (A c).2.1)
    (h : Table Statement PUnit (fun s => compiledCoin Com (coin s))) (r : ℕ) : ℝ≥0∞ :=
  Pr{let c ← ($ᵗ Coins : ProbComp Coins)}[QueryEscape relation state certificate A ext h r c]

section WitnessDecomposition

variable {Statement Com Openings Coins : Type} [DecidableEq Com] [SampleableType Coins]
    {protocol : Statement → Protocol} (coin : (s : Statement) → PublicCoin (protocol s))
    (state : Statement → KnowledgeState)
    (certificate : (s : Statement) → KnowledgeCertificate
      (protocol s).tree (protocol s).roles (state s))
    (refinement : WitnessKnowledgeCertificate (Com := Com) coin state certificate)
    (A : Coins → FSProof Statement Com Openings coin)
    (ext : (c : Coins) → ExtractedMessages (coin (A c).1) (A c).2.1)
    (auth : (c : Coins) → (pre : Prefix PUnit (compiledCoin Com (coin (A c).1))) →
      refinement.Authentication ⟨(A c).1, pre⟩)
    (h : Table Statement PUnit (fun s => compiledCoin Com (coin s)))
    (accept : FSProof Statement Com Openings coin → Prop)
    (terminalWitness : (c : Coins) → ((certificate (A c).1).extractor.terminalState
      (extractedPath (coin (A c).1) (A c).2.1 (ext c))).Witness)
    (Disagree : Coins → Prop)
    (transfer : ∀ c, verify coin h accept (A c) → ¬ Disagree c →
      ((certificate (A c).1).extractor.terminalState
        (extractedPath (coin (A c).1) (A c).2.1 (ext c))).holds (terminalWitness c))
    (authenticated : ∀ c r selected,
      selectedPrefix (coin (A c).1) (A c).2.1 (ext c) r = some selected →
      refinement.authenticate ⟨(A c).1, selected.1⟩ selected.2 (auth c selected.1) = true)
    (count : ℕ) (bound : ChallengeBound (Com := Com) coin count)

include transfer authenticated bound in
/-- Accepted extraction failure lies in disagreement, the authenticated witness game, or a query
escape on an incomplete prefix. -/
theorem knowledgeSoundness_witness_union :
    Pr{let c ← ($ᵗ Coins : ProbComp Coins)}[
      verify coin h accept (A c) ∧ ¬ (state (A c).1).holds
        (compositeExtractor coin state (fun s => (certificate s).extractor) A ext terminalWitness
          c)] ≤
    Pr{let c ← ($ᵗ Coins : ProbComp Coins)}[
      Disagree c ∨ (∃ r ∈ Finset.range count,
        witnessCheck refinement.toWitnessCIRelation h
          (reductionAdversary refinement.toWitnessCIRelation A ext auth r c) = true) ∨
      ∃ r ∈ Finset.range count,
        QueryEscape refinement.toWitnessCIRelation state certificate A ext h r c] := by
  apply prEvent_mono
  rintro c ⟨accepted, failure⟩
  obtain disagree | ⟨r, hr, escape⟩ := failure_implies_disagree_or_escape coin state certificate
    A ext h accept terminalWitness Disagree transfer count bound c accepted failure
  · exact Or.inl disagree
  · by_cases hd : Disagree c
    · exact Or.inl hd
    obtain ⟨selected, hs⟩ := selectedPrefix_some_of_escape (coin (A c).1)
      (certificate (A c).1).extractor (A c).2.1 (ext c) _ r escape
    by_cases residual : refinement.isQuery ⟨(A c).1, selected.1⟩ = true ∧
        refinement.complete ⟨(A c).1, selected.1⟩ selected.2 = false
    · exact Or.inr (Or.inr ⟨r, hr, ⟨⟨selected, hs, residual⟩, escape⟩⟩)
    · have admitted : (!refinement.isQuery ⟨(A c).1, selected.1⟩ ||
          refinement.complete ⟨(A c).1, selected.1⟩ selected.2) = true := by
        cases hq : refinement.isQuery ⟨(A c).1, selected.1⟩ <;>
          cases hc : refinement.complete ⟨(A c).1, selected.1⟩ selected.2 <;>
          simp_all
      refine Or.inr (Or.inl ⟨r, hr, ?_⟩)
      have consistent := prefixConsistent_of_escape (coin (A c).1)
        (certificate (A c).1).extractor (A c).2.1 (ext c) _
        (fun pre => refinement.challengeEq ⟨(A c).1, pre⟩) r selected hs escape
      have bad := refinement.escape_subset _ _ _ _ r selected hs escape
      simp only [reductionAdversary, hs, Option.map_some, witnessCheck, admitted, consistent,
        authenticated c r selected hs, Bool.true_and, refinement.check_iff]
      exact bad

include transfer authenticated bound in
/-- The rank sum has no algebraic mask penalty and leaves only incomplete query escapes
extractor-relative. -/
theorem knowledgeSoundness_witness :
    Pr{let c ← ($ᵗ Coins : ProbComp Coins)}[
      verify coin h accept (A c) ∧ ¬ (state (A c).1).holds
        (compositeExtractor coin state (fun s => (certificate s).extractor) A ext terminalWitness
          c)] ≤
    Pr{let c ← ($ᵗ Coins : ProbComp Coins)}[Disagree c] +
      (∑ r ∈ Finset.range count, witnessCI refinement.toWitnessCIRelation h
        (reductionAdversary refinement.toWitnessCIRelation A ext auth r)) +
      ∑ r ∈ Finset.range count,
        queryRel refinement.toWitnessCIRelation state certificate A ext h r := by
  let won := fun r c => witnessCheck refinement.toWitnessCIRelation h
    (reductionAdversary refinement.toWitnessCIRelation A ext auth r c) = true
  have game (r : ℕ) : Pr{let c ← ($ᵗ Coins : ProbComp Coins)}[won r c] =
      witnessCI refinement.toWitnessCIRelation h
        (reductionAdversary refinement.toWitnessCIRelation A ext auth r) := by
    simp only [won, witnessCI, witnessCIGame, bind_pure_comp, prEvent_map]
  refine (knowledgeSoundness_witness_union coin state certificate refinement A ext auth h
    accept terminalWitness Disagree transfer authenticated count bound).trans ?_
  refine (prEvent_or_le _ _ _).trans ?_
  refine (add_le_add le_rfl (prEvent_or_le _ _ _)).trans ?_
  rw [← add_assoc]
  apply add_le_add
  · apply add_le_add le_rfl
    simpa only [game] using
      prEvent_exists_finset_le (Finset.range count) ($ᵗ Coins : ProbComp Coins) won
  · exact prEvent_exists_finset_le (Finset.range count) ($ᵗ Coins : ProbComp Coins) _

end WitnessDecomposition

end Interaction.Oracle.Security.StandardBcs
