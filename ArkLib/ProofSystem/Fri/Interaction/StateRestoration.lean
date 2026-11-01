/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.ProofSystem.Fri.Interaction.Soundness
public import ArkLib.Interaction.Oracle.Security.StateRestorationOracle

/-!
# State-restoration knowledge soundness of FRI

The verifier's checks as a program of the branch (`terminal`): with the folding challenges, the
final polynomial and the query positions read off the branch, the checks of `verifier` at every
queried position. When they pass on a complete execution, its terminal knowledge state holds
(`terminal_holds_of_eval`), as for the verifier's own run (`terminal_holds_of_accepts`).

In the state-restoration game of FRI's public-coin presentation (`publicCoin`), the adversary
chooses the inputs and every prover message, querying a random oracle for the challenges at their
erased prefixes, and the game runs `terminal` on the completed branch. `stateRestoration_le`
bounds the probability that the checks pass while the inputs are far from their codes by
`Q * maxError + sumError` of the node errors `nodeErrors`: each fold's lossy MCA error and the
query error `(1 - δ + m · loss) ^ t`, `m` folds (`supErrors_certificate`). The path sum of the node
errors is FRI's error at the proximity loss (`sumError_nodeErrors`).
-/

@[expose] public section

open Interaction Interaction.Oracle Interaction.Oracle.Security OracleComp OracleSpec Domain
open Interaction.Oracle.Security.StateRestoration Interaction.Oracle.TypeTree
open ReedSolomon
open scoped ProbabilityTheory NNReal

namespace Fri.Interaction

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] [SampleableType K]
variable (top d t : ℕ)

/-- The verifier's terminal program on a branch of FRI from a layer of log height `n`: the checks
of `verifier` at the query positions, with the folding challenges, the final polynomial and the
positions read off the branch. -/
def terminal : {n : ℕ} → (ω : SmoothCosetFftDomain n K) → (A : PFunctor) →
    Reader (K := K) top A n → (s : Schedule n) → (p : (protocol K top d t s).tree.BranchPath) →
      OracleComp (OracleSpec.ofPFunctor (accessAfter (protocol K top d t s).tree
        (protocol K top d t s).oracles A p)) Bool
  | _, ω, _, r, .final, p => r.checkAll ω p.1 p.2.1
  | _, ω, _, r, .fold k hk inject rest, p =>
      terminal (ω.subdomain k) _ (r.fold ω k hk inject p.1) rest p.2.2

variable (inputs : (m : ℕ) → Fin (2 ^ m) → K) (δ loss : ℝ)

set_option backward.isDefEq.respectTransparency false in
/-- When the terminal checks pass on a complete execution, closed with its messages, the
certificate's terminal state holds: every query lands in the final consistent set. -/
theorem terminal_holds_of_eval (hd : 0 < d) (hloss : 0 ≤ loss) :
    ∀ {n : ℕ} (s : Schedule n) (hn : n ≤ top) (ω : SmoothCosetFftDomain n K) (A : PFunctor)
      (impl : QueryImpl (OracleSpec.ofPFunctor A) Id) (r : Reader (K := K) top A n) (j : ℕ)
      (f : Word K n) (C : Finset (Fin (2 ^ top))),
      r.Reads impl inputs f → (∀ x, simulateQ impl (r.check x) = decide (x ∈ C)) →
      ∀ path : (protocol K top d t s).tree.ExecutionPath,
        evalWithAnswerFn (path.closingImpl (protocol K top d t s).oracles A impl)
          (terminal top d t ω A r s path.toBranchPath) = true →
        ∃ w, ((certificate top d t inputs δ loss hd hloss hn ω s j f C).extractor.terminalState
          path).holds w := by
  intro n s
  induction s with
  | final =>
    intro hn ω A impl r j f C hr hcheck path hacc
    have hacc' : simulateQ impl (r.checkAll ω path.1 path.2.1) = true := hacc
    rw [Reader.simulateQ_checkAll impl inputs hr, decide_eq_true_eq] at hacc'
    refine ⟨finalConsistent top ω f path.1 C, rfl, fun i => ?_⟩
    have hi := hacc' i
    rw [hcheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hi
    exact Finset.mem_filter.mpr hi
  | @fold m k hk inject rest ih =>
    intro hn ω A impl r j f C hr hcheck path hacc
    obtain ⟨β, next, path⟩ := path
    exact ih ((Nat.sub_le m k).trans hn) (ω.subdomain k) _ _ _ (j + 1) next
      (foldConsistent top hk ω f β (injected inputs (m - k) inject) next C)
      (Reader.reads_fold impl inputs hr ω k hk inject β next)
      (fun x => by
        rw [Reader.simulateQ_fold_check impl inputs hr, hcheck, Bool.eq_iff_iff]
        simp [foldConsistent, Finset.mem_filter])
      path hacc

/-- The node errors of FRI's public-coin presentation from a layer of log height `n`, `j` folds
done: each fold's lossy MCA error, and the query error `(1 - δ + m · loss) ^ t` after `m` folds. -/
noncomputable def nodeErrors : {n : ℕ} → (ω : SmoothCosetFftDomain n K) → (s : Schedule n) →
    (j : ℕ) → Errors (publicCoin K top d t s)
  | _, _, .final, j => fun _ => ENNReal.ofReal (threshold δ loss j) ^ t
  | n, ω, .fold k _ inject rest, j => fun node =>
      Sum.elim (fun _ => Schedule.roundError ω k (rest.degree d) δ loss inject)
        (fun node => nodeErrors (ω.subdomain k) rest (j + 1) node.2.2)
        (node : PUnit ⊕ (PUnit × (Word K (n - k) × Prefix PUnit (publicCoin K top d t rest))))

/-- The certificate's error at each node of the public-coin presentation is the node error. -/
theorem supErrors_certificate (hd : 0 < d) (hloss : 0 ≤ loss) :
    ∀ {n : ℕ} (hn : n ≤ top) (ω : SmoothCosetFftDomain n K) (s : Schedule n) (j : ℕ)
      (f : Word K n) (C : Finset (Fin (2 ^ top))) (node : Prefix PUnit (publicCoin K top d t s)),
      supErrors (publicCoin K top d t s)
        (certificate top d t inputs δ loss hd hloss hn ω s j f C).challenges node =
      nodeErrors top d t δ loss ω s j node
  | _, _, _, .final, _, _, _, node => by
    obtain ⟨c, _ | ⟨_, node⟩⟩ := (node : (_ : Fin d → K) × (PUnit ⊕ (PUnit × Empty)))
    · rfl
    · exact node.elim
  | n, hn, ω, .fold k hk inject rest, j, f, C, node => by
    obtain _ | ⟨_, word, node⟩ :=
      (node : PUnit ⊕ (PUnit × (Word K (n - k) × Prefix PUnit (publicCoin K top d t rest))))
    · rfl
    · exact (iSup_congr fun β => supErrors_certificate hd hloss ((Nat.sub_le n k).trans hn)
        (ω.subdomain k) rest (j + 1) word
        (foldConsistent top hk ω f β (injected inputs (n - k) inject) word C) node).trans
          iSup_const

/-- The path sum of the node errors is FRI's error at the proximity loss: the folds' errors and
the query error. -/
theorem pathError_nodeErrors :
    ∀ {n : ℕ} (ω : SmoothCosetFftDomain n K) (s : Schedule n) (j : ℕ),
      pathError (publicCoin K top d t s) (nodeErrors top d t δ loss ω s j) =
        s.foldError d δ loss ω + ENNReal.ofReal (threshold δ loss (j + s.numFolds)) ^ t
  | _, _, .final, j => by
    change (⨆ _ : Fin d → K, ENNReal.ofReal (threshold δ loss j) ^ t + 0) = _
    simp [Schedule.foldError, Schedule.numFolds]
  | n, ω, .fold k hk inject rest, j => by
    change Schedule.roundError ω k (rest.degree d) δ loss inject +
      (⨆ _ : Word K (n - k), pathError (publicCoin K top d t rest)
        (nodeErrors top d t δ loss (ω.subdomain k) rest (j + 1))) = _
    rw [iSup_const, pathError_nodeErrors (ω.subdomain k) rest (j + 1), Schedule.foldError,
      Schedule.numFolds, add_assoc, Nat.add_comm 1 rest.numFolds]
    exact (add_assoc _ _ _).symm

/-- **FRI's state-restoration knowledge soundness.** In the state-restoration game of FRI's
public-coin presentation on a domain `ω` of `2 ^ top` points, where an adversary making at most
`Q` queries chooses the statement, whose inputs are `inputs z`, and every prover message, the
verifier's checks pass while the tallest input is `δ`-far from its code or some injected input is
`δ`-far from its code with probability at most `Q * maxError + sumError` of the node errors: each
fold's lossy MCA error and the query error at the proximity loss `loss`. The path sum is FRI's
error at that loss (`pathError_nodeErrors`). -/
theorem stateRestoration_le {Input Salt W : Type} [DecidableEq Input] [DecidableEq Salt]
    (inputs : Input → (m : ℕ) → Fin (2 ^ m) → K) (hd : 0 < d) (hloss : 0 ≤ loss)
    (ω : SmoothCosetFftDomain top K) (s : Schedule top)
    (adversary : OracleComp (oracleSpec Input Salt fun _ => publicCoin K top d t s)
      (Selection Input Salt W fun _ => publicCoin K top d t s))
    (Q : ℕ) (queryBound : IsTotalQueryBound adversary Q) :
    Pr{let result ← (simulateQ randomOracle (verificationGame (fun _ => publicCoin K top d t s)
        (inputAccess K) (fun z => inputImpl K (inputs z)) (fun _ _ => Bool)
        (fun _ => terminal top d t ω (inputAccess K) (Reader.root top) s) adversary)).run' ∅}[
      result.2.2.1 = true ∧ ¬ (Agrees ω (s.degree d) (1 - δ) (inputs result.1 top) ∧
        s.InputsAgree (inputs result.1) d (1 - δ) ω)] ≤
      Q * maxError (fun _ : Input => nodeErrors top d t δ loss ω s 0) +
        sumError (fun _ : Input => nodeErrors top d t δ loss ω s 0) := by
  have h := KnowledgeCertificate.stateRestoration_extraction_le (fun _ => publicCoin K top d t s)
    (fun z => levelState top d (inputs z) δ loss ω s 0 (inputs z top) Finset.univ)
    (fun z => certificate top d t (inputs z) δ loss hd hloss le_rfl ω s 0 (inputs z top)
      Finset.univ)
    (fun z => uniformChallenges_certificate top d t (inputs z) δ loss hd hloss le_rfl ω s 0 _ _)
    (inputAccess K) (fun z => inputImpl K (inputs z)) (fun _ _ => Bool)
    (fun _ => terminal top d t ω (inputAccess K) (Reader.root top) s) adversary Q queryBound
  have herr : (fun z : Input => supErrors (publicCoin K top d t s)
      (certificate top d t (inputs z) δ loss hd hloss le_rfl ω s 0 (inputs z top)
        Finset.univ).challenges) = fun _ => nodeErrors top d t δ loss ω s 0 :=
    funext fun z => funext fun node => supErrors_certificate top d t (inputs z) δ loss hd hloss
      le_rfl ω s 0 _ _ node
  rw [herr, verificationGame_eq, simulateQ_map] at h
  rw [verificationGame_eq, simulateQ_map]
  simp only [StateT.run'_map', prEvent_map] at h ⊢
  refine (prEvent_mono _ _ _ fun result hres => ?_).trans h
  obtain ⟨hacc, hfar⟩ := hres
  obtain ⟨w, hw⟩ := terminal_holds_of_eval top d t (inputs result.1) δ loss hd hloss s le_rfl ω
    (inputAccess K) (inputImpl K (inputs result.1)) (Reader.root top) 0 (inputs result.1 top)
    Finset.univ (Reader.reads_root (inputs result.1) top)
    (fun x => by simp only [Finset.mem_univ, decide_true]; rfl) result.2.1 hacc
  exact ⟨w, hw, fun hroot => hfar (agrees_of_root_holds top d (inputs result.1) δ loss ω s _
    hroot)⟩

end Fri.Interaction
