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
full words on the selected compiled path, and a knowledge certificate transports a supplied
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

/-- One full extracted oracle message for every commitment occurrence on the selected path. -/
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
prefix. The relation is fixed by the IOP certificate, and the full oracle words come from `ext`.
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

end Interaction.Oracle.Security.StandardBcs
