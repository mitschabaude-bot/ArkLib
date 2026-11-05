/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.Interaction.Oracle.Security.StandardBcs

/-!
# Recursive knowledge soundness from explicit-coins bounds

A recursive witness contains the statements and proofs checked by its step. Extraction follows
those children using the root adversary's coins throughout. At depth `d`, the extracted tree has
witnesses at levels `0` through `d`; even its leaves satisfy the one-level relation, including
verification of their own children. The error sums one-level bounds at all bounded index paths.
-/

@[expose] public section

open OracleComp OracleSpec
open scoped ENNReal

namespace Interaction.Oracle.Security.Recursion

universe u v w

/-- An abstract argument whose step witnesses contain the child statements and proofs it checks. -/
structure RecursiveRelation (S : Type u) (Proof : Type v) (W : Type w) where
  /-- Acceptance of a statement and its proof. -/
  verify : S → Proof → Prop
  /-- The step's constraints apart from verification of child proofs. -/
  localCheck : S → W → Prop
  /-- The ordered child statements and proofs carried by a step witness. -/
  children : W → List (S × Proof)

/-- A valid step satisfies its local constraints and verifies every child proof it carries. -/
def RecursiveRelation.Relation {S : Type u} {Proof : Type v} {W : Type w}
    (argument : RecursiveRelation S Proof W) (s : S) (witness : W) : Prop :=
  argument.localCheck s witness ∧
    ∀ child ∈ argument.children witness, argument.verify child.1 child.2

/-- A single-level extractor and error for every explicit-coins adversary. Coins live in `Type`,
while statements, proofs, and witnesses may live in independent universes. -/
structure KnowledgeBound {S : Type u} {Proof : Type v} {W : Type w}
    (argument : RecursiveRelation S Proof W) where
  /-- Extract a step witness from the adversary and the same coins used to run it. -/
  ext : {Coins : Type} → [SampleableType Coins] → (Coins → S × Proof) → Coins → W
  /-- The adversary-dependent one-level extraction error. -/
  err : {Coins : Type} → [SampleableType Coins] → (Coins → S × Proof) → ℝ≥0∞
  /-- Acceptance with an invalid extracted step has probability at most the assigned error. -/
  sound : ∀ {Coins : Type} [SampleableType Coins] (A : Coins → S × Proof),
    Pr{let c ← ($ᵗ Coins : ProbComp Coins)}[
      argument.verify (A c).1 (A c).2 ∧ ¬ argument.Relation (A c).1 (ext A c)] ≤ err A

/-- A finite tree of step witnesses, with an ordered statement and subtree for each child. -/
inductive WitnessTree (S : Type u) (W : Type w) : Type (max u w) where
  /-- A step witness together with the ordered statements and extracted subtrees of its children. -/
  | node (witness : W) (subtrees : List (S × WitnessTree S W)) : WitnessTree S W

/-- The step witness at the root of an extracted tree. -/
def WitnessTree.rootWitness {S : Type u} {W : Type w} : WitnessTree S W → W
  | .node witness _ => witness

/-- Every node through depth `depth` satisfies the one-level relation. At internal levels,
`Forall₂` pairs the witness's child list with exactly the subtree list, in order and with equal
statements. At depth zero only the one-level relation is required, including verification of
child proofs; no claim is made about further subtrees. -/
def Deep {S : Type u} {Proof : Type v} {W : Type w}
    (argument : RecursiveRelation S Proof W) : ℕ → S → WitnessTree S W → Prop
  | 0, s, .node witness _ => argument.Relation s witness
  | depth + 1, s, .node witness subtrees =>
      argument.Relation s witness ∧
        List.Forall₂ (fun child subtree =>
          child.1 = subtree.1 ∧ Deep argument depth child.1 subtree.2)
          (argument.children witness) subtrees

/-- The bounded paths through level `depth`, including the empty root path. Absent children
remain in this index set and are handled by the fixed default adversary output. -/
def paths (fanout : ℕ) : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | depth + 1 => insert [] ((Finset.range fanout).biUnion fun i =>
      (paths fanout depth).image (List.cons i))

/-- Path membership means length at most the depth and every child index below the fanout. -/
theorem mem_paths (fanout depth : ℕ) (p : List ℕ) :
    p ∈ paths fanout depth ↔ p.length ≤ depth ∧ ∀ i ∈ p, i < fanout := by
  induction depth generalizing p with
  | zero => cases p <;> simp [paths]
  | succ depth ih =>
      cases p with
      | nil => simp [paths]
      | cons i p =>
          simp [paths, ih, and_assoc, and_left_comm]

/-- The empty path names the root at every extraction depth. -/
theorem nil_mem_paths (fanout depth : ℕ) : [] ∈ paths fanout depth := by
  cases depth with
  | zero => exact Finset.mem_singleton_self _
  | succ depth => exact Finset.mem_insert_self _ _

/-- Prefixing a bounded child index extends a bounded path by one level. -/
theorem cons_mem_paths {fanout depth i : ℕ} {p : List ℕ} (index : i < fanout)
    (member : p ∈ paths fanout depth) : i :: p ∈ paths fanout (depth + 1) := by
  exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
    ⟨i, Finset.mem_range.mpr index, Finset.mem_image.mpr ⟨p, member, rfl⟩⟩)

/-- Pairing a list with a mapped indexed copy checks the relation at each indexed element. -/
private theorem forall₂_zipIdx_map {α : Type u} {β : Type v} (R : α → β → Prop)
    (xs : List α) (f : α × ℕ → β) :
    List.Forall₂ R xs (xs.zipIdx.map f) ↔ ∀ x ∈ xs.zipIdx, R x.1 (f x) := by
  calc
    _ ↔ List.Forall₂ R (xs.zipIdx.map Prod.fst) (xs.zipIdx.map f) := by
      rw [List.zipIdx_map_fst]
    _ ↔ _ := by
      rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]

section Extraction

variable {S : Type u} {Proof : Type v} {W : Type w} {Coins : Type}
    {argument : RecursiveRelation S Proof W} [SampleableType Coins]

/-- Extract one step and return its selected child, or the fixed default if that index is absent.
This uses the same coins for the adversary and extraction. -/
def childAdversary (K : KnowledgeBound argument) (fallback : S × Proof)
    (A : Coins → S × Proof) (i : ℕ) (c : Coins) : S × Proof :=
  ((argument.children (K.ext A c))[i]?).getD fallback

/-- Follow child indices from the root in list order. At length `k`, this adversary runs the
root followed by `k` single-level extractors, all on the same coins. -/
def derivedAdversary (K : KnowledgeBound argument) (fallback : S × Proof) :
    (Coins → S × Proof) → List ℕ → Coins → S × Proof
  | A, [] => A
  | A, i :: p => derivedAdversary K fallback (childAdversary K fallback A i) p

/-- The empty path denotes the root adversary. -/
theorem derivedAdversary_nil (K : KnowledgeBound argument) (fallback : S × Proof)
    (A : Coins → S × Proof) : derivedAdversary K fallback A [] = A := by
  rfl

/-- Appending one index extracts the adversary at the prefix and selects its indexed child. -/
theorem derivedAdversary_append (K : KnowledgeBound argument) (fallback : S × Proof)
    (A : Coins → S × Proof) (p : List ℕ) (i : ℕ) :
    derivedAdversary K fallback A (p ++ [i]) =
      childAdversary K fallback (derivedAdversary K fallback A p) i := by
  induction p generalizing A with
  | nil => rfl
  | cons j p ih => exact ih (childAdversary K fallback A j)

/-- Extract every actual child recursively, retaining its statement and original list position.
The final level contains a step witness but no subtrees. No additional coins are sampled. -/
def treeExtractor (K : KnowledgeBound argument) (fallback : S × Proof) :
    (depth : ℕ) → (Coins → S × Proof) → Coins → WitnessTree S W
  | 0, A, c => .node (K.ext A c) []
  | depth + 1, A, c =>
      .node (K.ext A c) ((argument.children (K.ext A c)).zipIdx.map fun (child, i) =>
        (child.1, treeExtractor K fallback depth (childAdversary K fallback A i) c))

/-- The tree extractor places the current adversary's step witness at its root. -/
theorem treeExtractor_rootWitness (K : KnowledgeBound argument) (fallback : S × Proof)
    (depth : ℕ) (A : Coins → S × Proof) (c : Coins) :
    (treeExtractor K fallback depth A c).rootWitness = K.ext A c := by
  cases depth <;> rfl

/-- An indexed child carried by the extracted witness is the selected adversary output. -/
theorem childAdversary_of_mem_zipIdx (K : KnowledgeBound argument) (fallback : S × Proof)
    (A : Coins → S × Proof) (c : Coins) (child : (S × Proof) × ℕ)
    (member : child ∈ (argument.children (K.ext A c)).zipIdx) :
    childAdversary K fallback A child.2 c = child.1 := by
  simp only [childAdversary, List.mem_zipIdx_iff_getElem?.mp member, Option.getD_some]

/-- Deep validity of an extracted successor tree is root validity and deep validity of each
actual indexed child subtree, with the child statement read from the root witness. -/
theorem deep_succ_treeExtractor (K : KnowledgeBound argument) (fallback : S × Proof)
    (depth : ℕ) (A : Coins → S × Proof) (c : Coins) :
    Deep argument (depth + 1) (A c).1 (treeExtractor K fallback (depth + 1) A c) ↔
      argument.Relation (A c).1 (K.ext A c) ∧
        ∀ child ∈ (argument.children (K.ext A c)).zipIdx,
          Deep argument depth child.1.1
            (treeExtractor K fallback depth (childAdversary K fallback A child.2) c) := by
  simp only [treeExtractor, Deep, forall₂_zipIdx_map, true_and]

/-- Acceptance with a failed one-level extraction at a fixed explicit coin. -/
def Bad (K : KnowledgeBound argument) (A : Coins → S × Proof) (c : Coins) : Prop :=
  argument.verify (A c).1 (A c).2 ∧ ¬ argument.Relation (A c).1 (K.ext A c)

/-- Depth zero for the extracted tree is exactly the original one-level relation. -/
theorem deep_zero_treeExtractor (K : KnowledgeBound argument) (fallback : S × Proof)
    (A : Coins → S × Proof) (c : Coins) :
    Deep argument 0 (A c).1 (treeExtractor K fallback 0 A c) ↔
      argument.Relation (A c).1 (K.ext A c) := by
  rfl

/-- A failed deep extraction from an accepting root has a bounded path whose proof verifies
but whose one-level extraction fails. Only valid parent relations need satisfy the fanout bound. -/
theorem failure_implies_badNode (K : KnowledgeBound argument) (fallback : S × Proof)
    (A : Coins → S × Proof) (depth fanout : ℕ) (c : Coins)
    (fanoutBound : ∀ s w, argument.Relation s w →
      (argument.children w).length ≤ fanout)
    (accepted : argument.verify (A c).1 (A c).2)
    (failure : ¬ Deep argument depth (A c).1 (treeExtractor K fallback depth A c)) :
    ∃ p ∈ paths fanout depth, Bad K (derivedAdversary K fallback A p) c := by
  classical
  induction depth generalizing A with
  | zero =>
      exact ⟨[], nil_mem_paths fanout 0, accepted, failure⟩
  | succ depth ih =>
      by_cases valid : argument.Relation (A c).1 (K.ext A c)
      · have childFailure : ∃ child ∈ (argument.children (K.ext A c)).zipIdx,
            ¬ Deep argument depth child.1.1
              (treeExtractor K fallback depth (childAdversary K fallback A child.2) c) := by
          by_contra noFailure
          apply failure
          apply (deep_succ_treeExtractor K fallback depth A c).mpr
          exact ⟨valid, fun child member => Classical.byContradiction
            (fun bad => noFailure ⟨child, member, bad⟩)⟩
        obtain ⟨child, member, childFailure⟩ := childFailure
        have selected := childAdversary_of_mem_zipIdx K fallback A c child member
        have childAccepted : argument.verify (childAdversary K fallback A child.2 c).1
            (childAdversary K fallback A child.2 c).2 := by
          rw [selected]
          exact valid.2 child.1 (List.fst_mem_of_mem_zipIdx member)
        rw [← selected] at childFailure
        obtain ⟨p, pathMember, bad⟩ := ih (childAdversary K fallback A child.2)
          childAccepted childFailure
        have indexBound : child.2 < fanout :=
          (List.snd_lt_of_mem_zipIdx member).trans_le (fanoutBound _ _ valid)
        exact ⟨child.2 :: p, cons_mem_paths indexBound pathMember, bad⟩
      · exact ⟨[], nil_mem_paths fanout (depth + 1), accepted, valid⟩

/-- Recursive knowledge soundness through any depth: sum the one-level errors at every bounded
path, including the root. The recursion relation bounds the children of valid witnesses;
no independence between nodes, adversaries, or extraction events is assumed. -/
theorem knowledgeSoundness (K : KnowledgeBound argument) (fallback : S × Proof)
    (A : Coins → S × Proof) (depth fanout : ℕ)
    (fanoutBound : ∀ s w, argument.Relation s w →
      (argument.children w).length ≤ fanout) :
    Pr{let c ← ($ᵗ Coins : ProbComp Coins)}[
      argument.verify (A c).1 (A c).2 ∧
        ¬ Deep argument depth (A c).1 (treeExtractor K fallback depth A c)] ≤
      ∑ p ∈ paths fanout depth, K.err (derivedAdversary K fallback A p) := by
  calc
    _ ≤ Pr{let c ← ($ᵗ Coins : ProbComp Coins)}[
        ∃ p ∈ paths fanout depth, Bad K (derivedAdversary K fallback A p) c] :=
      prEvent_mono _ _ _ (fun c bad => failure_implies_badNode K fallback A depth fanout c
        fanoutBound bad.1 bad.2)
    _ ≤ ∑ p ∈ paths fanout depth,
        Pr{let c ← ($ᵗ Coins : ProbComp Coins)}[
          Bad K (derivedAdversary K fallback A p) c] :=
      prEvent_exists_finset_le (paths fanout depth) ($ᵗ Coins : ProbComp Coins) _
    _ ≤ _ := Finset.sum_le_sum fun p _ => K.sound (derivedAdversary K fallback A p)

end Extraction

section StandardBcs

variable {S Proof W Com Openings : Type}

/-- View the recursive one-level relation as the input knowledge state of a BCS certificate. -/
def RecursiveRelation.knowledgeState (argument : RecursiveRelation S Proof W) (s : S) :
    KnowledgeState :=
  ⟨W, argument.Relation s⟩

/-- Uniform BCS extraction data give a recursive one-level bound. The encoding retains the
statement; the certificate's input state is exactly the recursive relation. Message extraction,
terminal witnesses, disagreement and acceptance transfer are supplied for every adversary and
coin type, so the resulting bound can also be applied to derived child adversaries. -/
noncomputable def KnowledgeBound.of_standardBcs (argument : RecursiveRelation S Proof W)
    [DecidableEq Com] {protocol : S → Protocol}
    (coin : (s : S) → PublicCoin (protocol s))
    (certificate : (s : S) →
      KnowledgeCertificate (protocol s).tree (protocol s).roles (argument.knowledgeState s))
    (h : StateRestoration.Table S PUnit (fun s => StandardBcs.compiledCoin Com (coin s)))
    (accept : StandardBcs.FSProof S Com Openings coin → Prop)
    (toProof : S × Proof → StandardBcs.FSProof S Com Openings coin)
    (statement_eq : ∀ pair, (toProof pair).1 = pair.1)
    (verify_iff : ∀ pair,
      StandardBcs.verify coin h accept (toProof pair) ↔ argument.verify pair.1 pair.2)
    (messages : ∀ {Coins : Type} [SampleableType Coins] (A : Coins → S × Proof) (c : Coins),
      StandardBcs.ExtractedMessages (coin (toProof (A c)).1) (toProof (A c)).2.1)
    (terminalWitness : ∀ {Coins : Type} [SampleableType Coins] (A : Coins → S × Proof) (c : Coins),
      ((certificate (toProof (A c)).1).extractor.terminalState
        (StandardBcs.extractedPath (coin (toProof (A c)).1)
          (toProof (A c)).2.1 (messages A c))).Witness)
    (Disagree : {Coins : Type} → [SampleableType Coins] → (Coins → S × Proof) → Coins → Prop)
    (transfer : ∀ {Coins : Type} [SampleableType Coins] (A : Coins → S × Proof) (c : Coins),
      StandardBcs.verify coin h accept (toProof (A c)) → ¬ Disagree A c →
        ((certificate (toProof (A c)).1).extractor.terminalState
          (StandardBcs.extractedPath (coin (toProof (A c)).1)
            (toProof (A c)).2.1 (messages A c))).holds (terminalWitness A c))
    (count : ℕ) (bound : StandardBcs.ChallengeBound (Com := Com) coin count) :
    KnowledgeBound argument where
  ext A := StandardBcs.compositeExtractor coin argument.knowledgeState certificate
    (fun c => toProof (A c)) (messages A) (terminalWitness A)
  err A := Pr{let c ← ($ᵗ _ : ProbComp _)}[Disagree A c] +
    ∑ r ∈ Finset.range count, StandardBcs.ciRel coin argument.knowledgeState certificate
      (fun c => toProof (A c)) (messages A) h r
  sound := by
    intro Coins _ A
    have singleLevel := StandardBcs.knowledgeSoundness coin argument.knowledgeState certificate
      (fun c => toProof (A c)) (messages A) h accept (terminalWitness A) (Disagree A)
      (transfer A) count bound
    calc
      _ = Pr{let c ← ($ᵗ Coins : ProbComp Coins)}[
          StandardBcs.verify coin h accept (toProof (A c)) ∧
            ¬ (argument.knowledgeState (toProof (A c)).1).holds
              (StandardBcs.compositeExtractor coin argument.knowledgeState certificate
                (fun c => toProof (A c)) (messages A) (terminalWitness A) c)] := by
        apply prEvent_congr
        intro c
        simp only [verify_iff, RecursiveRelation.knowledgeState, statement_eq]
      _ ≤ _ := singleLevel

end StandardBcs

end Interaction.Oracle.Security.Recursion
