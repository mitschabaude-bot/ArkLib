/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.ProofSystem.Fri.Interaction.QueryKnowledge
public import ArkLib.Interaction.Oracle.Security.KnowledgeSoundness
public import ArkLib.ProofSystem.Fri.Interaction.Plonky3

/-!
# Knowledge soundness of FRI on the interaction layer

`certificate` composes FRI's knowledge certificate from its rounds with
`KnowledgeCertificate.append`: each fold round's (`foldRoundCertificate`), then the final message's
and the query phase's (`finalCertificate`). At the first layer its state holds exactly when the
inputs are close to their codes (`agrees_of_root_holds`); its largest path error is the folds'
lossy MCA errors and `(1 - δ + m · loss) ^ t` for the queries (`maxError_certificate`).

The verifier meets the certificate: it samples the challenges uniformly
(`samplesChallenges_verifier`), and when it accepts, the terminal state holds
(`terminal_holds_of_accepts`), its checks computing the consistent sets of the knowledge states.
`KnowledgeCertificate.executeStrategies_extraction_le` then bounds acceptance of far inputs:
`acceptance_le`, at most `error ω s d t δ`, the folds' errors and the query term minimized over
the proximity loss. That is CompStark's `FriGame.error`, the error of `friErrorWith`, on the
schedule's shape.
-/

@[expose] public section

open Interaction Interaction.Oracle Interaction.Oracle.Security OracleComp OracleSpec Domain
open ReedSolomon
open scoped ProbabilityTheory NNReal

namespace Fri.Interaction

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] [SampleableType K]
variable (top d t : ℕ) (inputs : (m : ℕ) → Fin (2 ^ m) → K) (δ loss : ℝ)

/-- **FRI's knowledge certificate** from a layer of log height `n ≤ top`, after `j` folds with
current word `f` and consistent set `C`: each fold round's certificate, then the final message
and the query phase, appended. -/
noncomputable def certificate (hd : 0 < d) (hloss : 0 ≤ loss) :
    {n : ℕ} → n ≤ top → (ω : SmoothCosetFftDomain n K) → (s : Schedule n) → (j : ℕ) →
      (f : Word K n) → (C : Finset (Fin (2 ^ top))) →
      KnowledgeCertificate (protocol K top d t s).tree (protocol K top d t s).roles
        (levelState top d inputs δ loss ω s j f C)
  | _, _, ω, .final, j, f, C => finalCertificate top t δ loss d inputs ω j f C
  | n, hn, ω, .fold k hk inject rest, j, f, C =>
      (foldRoundCertificate top d inputs δ loss hd hloss hn hk ω inject rest j f C).append
        (fun _ => (protocol K top d t rest).tree) (fun _ => (protocol K top d t rest).roles)
        fun path => certificate hd hloss (n := n - k) ((Nat.sub_le n k).trans hn)
          (ω.subdomain k) rest (j + 1) path.2.1
          (foldConsistent top hk ω f path.1 (injected inputs (n - k) inject) path.2.1 C)

/-- The certificate's largest path error is the folds' errors and the query term. -/
theorem maxError_certificate (hd : 0 < d) (hloss : 0 ≤ loss) :
    ∀ {n : ℕ} (hn : n ≤ top) (ω : SmoothCosetFftDomain n K) (s : Schedule n) (j : ℕ)
      (f : Word K n) (C : Finset (Fin (2 ^ top))),
      (certificate top d t inputs δ loss hd hloss hn ω s j f C).challenges.maxError
        (protocol K top d t s).roles ≤
      s.foldError d δ loss ω + ENNReal.ofReal (threshold δ loss (j + s.numFolds)) ^ t
  | _, _, ω, .final, j, f, C => by
    refine iSup_le fun c => ?_
    change ENNReal.ofReal (threshold δ loss j) ^ t + ⨆ _ : Fin t → Fin (2 ^ top), (0 : ENNReal) ≤ _
    simp [Schedule.foldError, Schedule.numFolds]
  | n, hn, ω, .fold k hk inject rest, j, f, C => by
    change Schedule.roundError ω k (rest.degree d) δ loss inject +
        (⨆ β : K, ⨆ next : Word K (n - k), (certificate top d t inputs δ loss hd hloss
          ((Nat.sub_le n k).trans hn) (ω.subdomain k) rest (j + 1) next
          (foldConsistent top hk ω f β (injected inputs (n - k) inject) next C)).challenges.maxError
          (protocol K top d t rest).roles) ≤ _
    rw [Schedule.foldError, Schedule.numFolds, add_assoc]
    refine add_le_add le_rfl (iSup_le fun β => iSup_le fun next => ?_)
    refine (maxError_certificate hd hloss _ _ rest (j + 1) next _).trans (le_of_eq ?_)
    rw [show j + 1 + rest.numFolds = j + (rest.numFolds + 1) by omega]

omit [Fintype K] [DecidableEq K] [SampleableType K] in
/-- At the first layer, the state holds only if the inputs are close to their codes. -/
theorem agrees_of_root_holds (ω : SmoothCosetFftDomain top K) (s : Schedule top)
    (w : (levelState top d inputs δ loss ω s 0 (inputs top) Finset.univ).Witness)
    (hw : (levelState top d inputs δ loss ω s 0 (inputs top) Finset.univ).holds w) :
    Agrees ω (s.degree d) (1 - δ) (inputs top) ∧ s.InputsAgree inputs d (1 - δ) ω := by
  obtain ⟨hu, -, hagree, hcard, hin⟩ := hw
  have hproj (x : Fin (2 ^ top)) : proj top x = x := Fin.ext (Nat.mod_eq_of_lt x.isLt)
  refine ⟨⟨w.1, ?_, w.2, hu, fun x hx => ?_⟩, hin⟩
  · simpa [threshold] using hcard
  · simpa only [hproj] using hagree x hx

/-! ### The verifier's terminal and challenge laws -/

/-- Lifting a sampler beside the sources and running it reads no source. -/
@[simp]
theorem simulateQ_liftAccessImpl_liftComp {ι : Type} (ambient : OracleSpec ι) (A : PFunctor)
    (impl : QueryImpl (OracleSpec.ofPFunctor A) Id) {α : Type} (oa : OracleComp ambient α) :
    simulateQ (Verifier.liftAccessImpl ambient A impl)
      (liftComp oa (ambient + OracleSpec.ofPFunctor A)) = oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind q k ih =>
    simp only [liftComp_bind, simulateQ_bind, ih, liftComp_liftM_query]
    rfl

variable {ι : Type} (ambient : OracleSpec ι)

set_option backward.isDefEq.respectTransparency false in
/-- An accepting execution reaches a terminal state that holds: the verifier accepts exactly when
every query lands in the final consistent set, which its checks compute. -/
theorem terminal_holds_of_accepts (hd : 0 < d) (hloss : 0 ≤ loss)
    (sample : OracleComp ambient K) (sampleQueries : OracleComp ambient (Fin t → Fin (2 ^ top))) :
    ∀ {n : ℕ} (s : Schedule n) (hn : n ≤ top) (ω : SmoothCosetFftDomain n K) (A : PFunctor)
      (impl : QueryImpl (OracleSpec.ofPFunctor A) Id) (r : Reader (K := K) top A n) (j : ℕ)
      (f : Word K n) (C : Finset (Fin (2 ^ top)))
      {OutP : (protocol K top d t s).tree.ExecutionPath → Type}
      (prover : Prover.Strategy ambient (protocol K top d t s).tree (protocol K top d t s).roles
        OutP),
      r.Reads impl inputs f → (∀ x, simulateQ impl (r.check x) = decide (x ∈ C)) →
      ∀ result ∈ support (executeStrategies ambient (protocol K top d t s).tree
        (protocol K top d t s).roles (protocol K top d t s).oracles A impl prover
        (verifier ambient top d t sample sampleQueries ω A r s)), result.2.2 = true →
      ∃ w, ((certificate top d t inputs δ loss hd hloss hn ω s j f C).extractor.terminalState
        result.1).holds w := by
  intro n s
  induction s with
  | final =>
    intro hn ω A impl r j f C OutP prover hr hcheck result hresult hacc
    rw [executeStrategies_final] at hresult
    obtain ⟨chosen, -, hresult⟩ := support_bind_exists hresult
    obtain ⟨next, hnext, hresult⟩ := support_bind_exists hresult
    rw [verifier, simulateQ_pure, mem_support_pure_iff] at hnext
    subst hnext
    obtain ⟨picked, hpicked, hresult⟩ := support_bind_exists hresult
    rw [simulateQ_bind] at hpicked
    obtain ⟨xs, -, hpicked⟩ := support_bind_exists hpicked
    rw [simulateQ_pure, mem_support_pure_iff] at hpicked
    subst hpicked
    obtain ⟨outP, -, hresult⟩ := support_bind_exists hresult
    obtain ⟨outV, houtV, hresult⟩ := support_bind_exists hresult
    rw [mem_support_pure_iff] at hresult
    subst hresult
    rw [simulateQ_withAmbient, mem_support_pure_iff, Reader.simulateQ_checkAll impl inputs hr]
      at houtV
    change outV = true at hacc
    rw [hacc, eq_comm, decide_eq_true_eq] at houtV
    refine ⟨finalConsistent top ω f chosen.1 C, rfl, fun i => ?_⟩
    have hi := houtV i
    rw [hcheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hi
    exact Finset.mem_filter.mpr hi
  | @fold m k hk inject rest ih =>
    intro hn ω A impl r j f C OutP prover hr hcheck result hresult hacc
    rw [executeStrategies_fold] at hresult
    obtain ⟨chosen, hchosen, hresult⟩ := support_bind_exists hresult
    rw [verifier, simulateQ_bind] at hchosen
    obtain ⟨β, -, hchosen⟩ := support_bind_exists hchosen
    rw [simulateQ_pure, mem_support_pure_iff] at hchosen
    subst hchosen
    obtain ⟨next, -, hresult⟩ := support_bind_exists hresult
    obtain ⟨sent, -, hresult⟩ := support_bind_exists hresult
    obtain ⟨after, hafter, hresult⟩ := support_bind_exists hresult
    rw [simulateQ_pure, mem_support_pure_iff] at hafter
    subst hafter
    obtain ⟨res, hres, hresult⟩ := support_bind_exists hresult
    rw [mem_support_pure_iff] at hresult
    subst hresult
    exact ih (OutP := fun path => OutP ⟨β, sent.1, path⟩) ((Nat.sub_le m k).trans hn)
      (ω.subdomain k) _ _ _ (j + 1) sent.1
      (foldConsistent top hk ω f β (injected inputs (m - k) inject) sent.1 C) sent.2
      (Reader.reads_fold impl inputs hr ω k hk inject β sent.1)
      (fun x => by
        rw [Reader.simulateQ_fold_check impl inputs hr, hcheck, Bool.eq_iff_iff]
        simp [foldConsistent, Finset.mem_filter])
      res hres hacc

set_option backward.isDefEq.respectTransparency false in
/-- The verifier samples its challenges as the certificate's challenge programs: the folding
challenges and the query positions are uniform. -/
theorem samplesChallenges_verifier (hd : 0 < d) (hloss : 0 ≤ loss) :
    ∀ {n : ℕ} (s : Schedule n) (hn : n ≤ top) (ω : SmoothCosetFftDomain n K) (A : PFunctor)
      (impl : QueryImpl (OracleSpec.ofPFunctor A) Id) (r : Reader (K := K) top A n) (j : ℕ)
      (f : Word K n) (C : Finset (Fin (2 ^ top))),
      SamplesChallenges unifSpec (QueryImpl.id' unifSpec) (protocol K top d t s).tree
        (protocol K top d t s).roles (protocol K top d t s).oracles A impl _
        (verifier unifSpec top d t ($ᵗ K) ($ᵗ (Fin t → Fin (2 ^ top))) ω A r s)
        (certificate top d t inputs δ loss hd hloss hn ω s j f C).challenges := by
  intro n s
  induction s with
  | final =>
    intro hn ω A impl r j f C c after hafter
    rw [simulateQ_id', verifier, simulateQ_pure, mem_support_pure_iff] at hafter
    subst hafter
    refine ⟨fun event => ?_, fun _ _ => trivial⟩
    simp only [simulateQ_id', simulateQ_bind, simulateQ_liftAccessImpl_liftComp, simulateQ_pure]
    rw [bind_pure_comp, prEvent_map]
    rfl
  | @fold m k hk inject rest ih =>
    intro hn ω A impl r j f C
    refine ⟨fun event => ?_, fun chosen hchosen => ?_⟩
    · simp only [simulateQ_id', verifier, simulateQ_bind, simulateQ_liftAccessImpl_liftComp,
        simulateQ_pure]
      rw [bind_pure_comp, prEvent_map]
      rfl
    · simp only [simulateQ_id', verifier, simulateQ_bind, simulateQ_liftAccessImpl_liftComp,
        simulateQ_pure] at hchosen
      obtain ⟨β, -, hchosen⟩ := support_bind_exists hchosen
      rw [mem_support_pure_iff] at hchosen
      subst hchosen
      intro message after hafter
      rw [simulateQ_id', simulateQ_pure, mem_support_pure_iff] at hafter
      subst hafter
      exact ih ((Nat.sub_le m k).trans hn) (ω.subdomain k) _ _ _ (j + 1) message
        (foldConsistent top hk ω f β (injected inputs (m - k) inject) message C)

/-- **FRI is knowledge sound.** Against any prover, the verifier accepts the inputs `inputs` with
probability at most `error ω s d t δ` unless the tallest input is `δ`-close to the code before
the folds and every injected input is `δ`-close to its code: for every proximity loss, at most
the folds' lossy MCA errors and `(1 - δ + m · loss) ^ t`, `m` folds. -/
theorem acceptance_le (hd : 0 < d) (ω : SmoothCosetFftDomain top K) (s : Schedule top)
    (hfar : ¬ (Agrees ω (s.degree d) (1 - δ) (inputs top) ∧ s.InputsAgree inputs d (1 - δ) ω))
    {OutP : (protocol K top d t s).tree.ExecutionPath → Type}
    (prover : Prover.Strategy unifSpec (protocol K top d t s).tree (protocol K top d t s).roles
      OutP) :
    Pr{let result ← (executeStrategies unifSpec (protocol K top d t s).tree
      (protocol K top d t s).roles (protocol K top d t s).oracles (inputAccess K)
      (inputImpl K inputs) prover
      (verifier unifSpec top d t ($ᵗ K) ($ᵗ (Fin t → Fin (2 ^ top))) ω (inputAccess K)
        (Reader.root top) s))}[result.2.2 = true] ≤ error ω s d t δ := by
  refine le_iInf fun loss => ?_
  let cert := certificate top d t inputs δ loss hd loss.coe_nonneg le_rfl ω s 0 (inputs top)
    Finset.univ
  have key := cert.executeStrategies_extraction_le unifSpec (QueryImpl.id' unifSpec)
    (protocol K top d t s).oracles (inputAccess K) (inputImpl K inputs) prover
    (verifier unifSpec top d t ($ᵗ K) ($ᵗ (Fin t → Fin (2 ^ top))) ω (inputAccess K)
      (Reader.root top) s)
    (samplesChallenges_verifier top d t inputs δ loss hd loss.coe_nonneg s le_rfl ω _ _ _ 0
      (inputs top) Finset.univ)
  rw [simulateQ_id'] at key
  refine (prEvent_mono_of_support _ _ _ fun result hresult hacc => ?_).trans (key.trans
    ((maxError_certificate top d t inputs δ loss hd loss.coe_nonneg le_rfl ω s 0 (inputs top)
      Finset.univ).trans (le_of_eq ?_)))
  · obtain ⟨w, hw⟩ := terminal_holds_of_accepts top d t inputs δ loss unifSpec hd
      loss.coe_nonneg _ _ s le_rfl ω _ _ _ 0 (inputs top) Finset.univ prover
      (Reader.reads_root inputs top) (fun x => by simp only [Finset.mem_univ, decide_true]; rfl)
      result hresult hacc
    exact ⟨w, hw, fun hroot => hfar (agrees_of_root_holds top d inputs δ loss ω s _ hroot)⟩
  · simp [threshold]

/-- **FRI with Plonky3's schedule is knowledge sound.** For input heights that fit below the
tallest and above the final height `logFinal`, if the tallest input is `δ`-far from its code or
some input is `δ`-far from its code on every domain with a property `P` that the folds keep, the
verifier accepts with probability at most the schedule's error. -/
theorem acceptance_le_plonky3 {maxLogArity logFinal : ℕ} (ha : 0 < maxLogArity) (hd : 0 < d)
    (ω : SmoothCosetFftDomain top K) (heights : List ℕ) (hlog : logFinal ≤ top)
    (hfit : Schedule.Fits logFinal top heights)
    (P : ∀ {m : ℕ}, SmoothCosetFftDomain m K → Prop)
    (hP : ∀ {m : ℕ} (D : SmoothCosetFftDomain m K) (k : ℕ), P D → P (D.subdomain k)) (hω : P ω)
    (hfar : ¬ Agrees ω (2 ^ (top - logFinal) * d) (1 - δ) (inputs top) ∨
      ∃ m ∈ heights, ∀ D : SmoothCosetFftDomain m K, P D →
        ¬ Agrees D (2 ^ (m - logFinal) * d) (1 - δ) (inputs m))
    {OutP : (protocol K top d t
      (Schedule.plonky3 maxLogArity logFinal top top heights)).tree.ExecutionPath → Type}
    (prover : Prover.Strategy unifSpec
      (protocol K top d t (Schedule.plonky3 maxLogArity logFinal top top heights)).tree
      (protocol K top d t (Schedule.plonky3 maxLogArity logFinal top top heights)).roles OutP) :
    Pr{let result ← (executeStrategies unifSpec
      (protocol K top d t (Schedule.plonky3 maxLogArity logFinal top top heights)).tree
      (protocol K top d t (Schedule.plonky3 maxLogArity logFinal top top heights)).roles
      (protocol K top d t (Schedule.plonky3 maxLogArity logFinal top top heights)).oracles
      (inputAccess K) (inputImpl K inputs) prover
      (verifier unifSpec top d t ($ᵗ K) ($ᵗ (Fin t → Fin (2 ^ top))) ω (inputAccess K)
        (Reader.root top) (Schedule.plonky3 maxLogArity logFinal top top heights)))}[
      result.2.2 = true] ≤
      error ω (Schedule.plonky3 maxLogArity logFinal top top heights) d t δ := by
  refine acceptance_le top d t inputs δ hd ω _ (fun ⟨hword, hin⟩ => ?_) prover
  rcases hfar with hfar | ⟨m, hm, hfar⟩
  · rw [Schedule.degree_plonky3 ha d top top heights hlog (Nat.sub_le _ _) hfit] at hword
    exact hfar hword
  · obtain ⟨D, hD, hagree⟩ := Schedule.agrees_of_inputsAgree ha inputs d (1 - δ) P hP top top ω
      heights hlog (Nat.sub_le _ _) hfit hω hin m hm
    exact hfar D hD hagree

end Fri.Interaction
