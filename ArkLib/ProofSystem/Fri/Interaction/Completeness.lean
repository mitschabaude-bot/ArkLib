/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.ProofSystem.Fri.Interaction.Protocol

/-!
# Completeness of FRI on the interaction layer

`perfectCompleteness`: if the tallest input is a codeword of the code before the folds and every
injected input is a codeword of its code, the verifier accepts the honest prover with probability
one, for folds by `2 ^ k` with `k ≥ 1` (`Schedule.ArityPos`).

The verifier's programs are read under the actual source handler (`Reader.Reads`): a program
lifted past an oracle message reads the earlier sources as before (`simulateQ_extendAccess`), a
committed word's check passes at a top position exactly when it agrees with the verifier's word at
the point the position reduces to (`Reader.simulateQ_commit_check`), and after a fold the
verifier's word is the fold of the committed one (`Reader.reads_fold`). The honest prover commits
the verifier's words, so it passes every check; a fold is ArkLib's folded word plus the injected
input (`foldNext_apply`), a codeword of the folded code (`foldNext_mem_code`); the final
coefficients interpolate the last word (`evalCoeffs_finalCoeffs`). `honest_accepts` follows the
execution round by round.
-/

@[expose] public section

open Interaction Interaction.Oracle OracleComp OracleSpec Domain

namespace Fri.Interaction

variable {K : Type}

/-! ### The verifier's query programs under a source handler -/

section Semantics

variable {A : PFunctor} (impl : QueryImpl (OracleSpec.ofPFunctor A) Id)

/-- A lifted program reads the earlier sources as before the oracle message. -/
@[simp]
theorem simulateQ_extendAccess {M : Type} (I : OracleInterface M) (message : M) {α : Type}
    (oa : OracleComp (OracleSpec.ofPFunctor A) α) :
    simulateQ (Access.extendImpl A I impl message) (extendAccess I oa) = simulateQ impl oa :=
  QueryImpl.simulateQ_simulateQ_eq_of_apply
    (fun q => Access.eval_queryPrior A I impl message q) oa

/-- A query program beside the ambient oracles makes no ambient query. -/
@[simp]
theorem simulateQ_withAmbient {ι : Type} (ambient : OracleSpec ι) {α : Type}
    (oa : OracleComp (OracleSpec.ofPFunctor A) α) :
    simulateQ (Verifier.liftAccessImpl ambient A impl) (withAmbient ambient oa) =
      pure (simulateQ impl oa) := by
  rw [withAmbient, ← QueryImpl.simulateQ_compose]
  induction oa using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.apply_compose, ih]
    simp only [Verifier.liftAccessImpl_source, pure_bind]
    rfl

/-- Reading values reads each of them. -/
theorem simulateQ_readAll {ι : Type} {spec : OracleSpec ι} (impl : QueryImpl spec Id)
    {α : Type} : ∀ (m : ℕ) (read : Fin m → OracleComp spec α) (v : Fin m → α),
      (∀ q, simulateQ impl (read q) = v q) → simulateQ impl (readAll m read) = v
  | 0, _, v, _ => funext fun q => q.elim0
  | m + 1, read, v, h => by
    simp only [readAll, simulateQ_bind, simulateQ_pure, h]
    rw [simulateQ_readAll impl m (fun i => read i.succ) (fun i => v i.succ) (fun i => h i.succ)]
    exact Fin.cons_self_tail v

end Semantics

/-! ### Honest folds -/

section Fold

variable [Field K] [DecidableEq K]

/-- The fiber's points reduce to the point they are above. -/
theorem sqFoldMapGen_fiberPoint {n k : ℕ} (hk : k ≤ n) (y : Fin (2 ^ (n - k)))
    (q : Fin (2 ^ k)) : CosetFftDomainClass.sqFoldMapGen (i := k) (fiberPoint hk y q) = y := by
  apply Fin.ext
  simp only [CosetFftDomainClass.sqFoldMapGen, fiberPoint, Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt y.isLt

omit [DecidableEq K] in
/-- The `2 ^ k`th powers of the fiber's points are the point they are above. -/
theorem pow_fiberPoint {n k : ℕ} (hk : k ≤ n) (ω : SmoothCosetFftDomain n K)
    (y : Fin (2 ^ (n - k))) (q : Fin (2 ^ k)) :
    ω (fiberPoint hk y q) ^ 2 ^ k = ω.subdomain k y := by
  rw [← CosetFftDomainClass.pow_eq_subdomain_sqFoldMapGen (ω := ω) (i := k),
    sqFoldMapGen_fiberPoint]

theorem fiberPoint_injective {n k : ℕ} (hk : k ≤ n) (y : Fin (2 ^ (n - k))) :
    Function.Injective (fiberPoint hk y) := by
  intro q q' h
  have h' := congrArg Fin.val h
  simp only [fiberPoint, add_right_inj] at h'
  exact Fin.ext (Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos _) h')

/-- The folded value from the fiber is ArkLib's folded word. -/
theorem foldFiber_eq_foldWord {n k : ℕ} (hk : k ≤ n) (ω : SmoothCosetFftDomain n K)
    (f : Word K n) (β : K) (y : Fin (2 ^ (n - k))) :
    foldFiber hk ω y β (fun q => f (fiberPoint hk y q)) = ProximityGap.foldWord ω f k β y := by
  have h := (RoundConsistency.roundConsistencyCheck_eq_foldValue ω f
    ⟨fiberPoint hk y, fiberPoint_injective hk y⟩ (ω.subdomain k y) β
    (foldFiber hk ω y β (fun q => f (fiberPoint hk y q))) (pow_fiberPoint hk ω y)).mp
    (by simp [RoundConsistency.roundConsistencyCheck, foldFiber])
  exact h.symm

/-- The fold is the folded word plus `β ^ 2 ^ k g`. -/
theorem foldNext_apply {n k : ℕ} (hk : k ≤ n) (ω : SmoothCosetFftDomain n K) (f : Word K n)
    (β : K) (g : Word K (n - k)) (y : Fin (2 ^ (n - k))) :
    foldNext hk ω f β g y = ProximityGap.foldWord ω f k β y + β ^ 2 ^ k * g y := by
  rw [foldNext, foldFiber_eq_foldWord]

/-- Folding a codeword by `2 ^ k`, `k ≥ 1`, gives a codeword of the folded code. -/
theorem foldWord_mem_code {n k D : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n) (hD : 0 < D)
    (ω : SmoothCosetFftDomain n K) {f : Word K n}
    (hf : f ∈ ReedSolomon.code (ω : Fin (2 ^ n) ↪ K) (2 ^ k * D)) (β : K) :
    ProximityGap.foldWord ω f k β ∈
      ReedSolomon.code (ω.subdomain k : Fin (2 ^ (n - k)) ↪ K) D := by
  have : ProximityGap.FoldingContextMiddle k n := ⟨hk1, hk⟩
  obtain ⟨p, hp, rfl⟩ := ReedSolomon.mem_code_iff_exists_polynomial'.mp hf
  have hpn : p.degree < 2 ^ n := by
    refine hp.trans_le ?_
    rw [Fintype.card_fin]
    exact_mod_cast min_le_right _ _
  rw [ProximityGap.foldWord_evalOnPoints hpn]
  refine ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval _ ?_ fun _ => rfl
  refine Polynomial.FoldingPolynomial.polyFold_natDegree_le.trans_lt ?_
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)]
  by_cases hp0 : p = 0
  · rw [hp0, Polynomial.natDegree_zero]
    positivity
  · have := hp.trans_le (WithBot.coe_le_coe.mpr (min_le_left _ _))
    rw [Polynomial.degree_eq_natDegree hp0] at this
    calc p.natDegree < 2 ^ k * D := WithBot.coe_lt_coe.mp this
      _ = D * 2 ^ k := mul_comm _ _

/-- An honest fold of a codeword, injecting a codeword, is a codeword. -/
theorem foldNext_mem_code {n k D : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n) (hD : 0 < D)
    (ω : SmoothCosetFftDomain n K) {f : Word K n}
    (hf : f ∈ ReedSolomon.code (ω : Fin (2 ^ n) ↪ K) (2 ^ k * D)) (β : K) {g : Word K (n - k)}
    (hg : g ∈ ReedSolomon.code (ω.subdomain k : Fin (2 ^ (n - k)) ↪ K) D) :
    foldNext hk ω f β g ∈ ReedSolomon.code (ω.subdomain k : Fin (2 ^ (n - k)) ↪ K) D := by
  have h : foldNext hk ω f β g = ProximityGap.foldWord ω f k β + (β ^ 2 ^ k) • g :=
    funext fun y => by rw [foldNext_apply]; rfl
  rw [h]
  exact Submodule.add_mem _ (foldWord_mem_code hk1 hk hD ω hf β) (Submodule.smul_mem _ _ hg)

/-- The final coefficients of a codeword evaluate to it. -/
theorem evalCoeffs_finalCoeffs {n d : ℕ} (ω : SmoothCosetFftDomain n K) {f : Word K n}
    (hf : f ∈ ReedSolomon.code (ω : Fin (2 ^ n) ↪ K) d) (y : Fin (2 ^ n)) :
    evalCoeffs (finalCoeffs ω f d) (ω y) = f y := by
  obtain ⟨p, hp, rfl⟩ := ReedSolomon.mem_code_iff_exists_polynomial'.mp hf
  have hinterp : (CompPoly.CPolynomial.CLagrange.interpolate Finset.univ (fun x => ω x)
      (ReedSolomon.evalOnPoints (ω : Fin (2 ^ n) ↪ K) p)).toPoly = p := by
    rw [CompPoly.CPolynomial.CLagrange.cinterpolate_eq_interpolate]
    refine (Lagrange.eq_interpolate_of_eval_eq _ ?_ ?_ fun x _ => rfl).symm
    · exact CosetFftDomain.injOn
    · refine hp.trans_le ?_
      rw [Finset.card_univ]
      exact_mod_cast min_le_right _ _
  have hdeg : p.natDegree < d ∨ p = 0 := by
    by_cases hp0 : p = 0
    · exact Or.inr hp0
    · left
      have := hp.trans_le (WithBot.coe_le_coe.mpr (min_le_left _ _))
      rw [Polynomial.degree_eq_natDegree hp0] at this
      exact WithBot.coe_lt_coe.mp this
  simp only [evalCoeffs, finalCoeffs, CompPoly.CPolynomial.coeff_toPoly, hinterp]
  change _ = p.eval (ω y)
  rcases hdeg with hdeg | rfl
  · rw [Polynomial.eval_eq_sum_range' hdeg, ← Fin.sum_univ_eq_sum_range
      (fun i => p.coeff i * ω y ^ i)]
  · simp

end Fold

/-! ### The reader's programs under a source handler -/

namespace Reader

variable [Field K] [DecidableEq K] {top : ℕ} {A : PFunctor}
  (impl : QueryImpl (OracleSpec.ofPFunctor A) Id) (inputs : (m : ℕ) → Fin (2 ^ m) → K)

/-- The reader reads the inputs `inputs` and the verifier's word `f`. -/
structure Reads {n : ℕ} (r : Reader (K := K) top A n) (f : Word K n) : Prop where
  input : ∀ m x, simulateQ impl (r.input m x) = inputs m x
  word : ∀ y, simulateQ impl (r.word y) = f y

omit [Field K] [DecidableEq K] in
theorem reads_root (top : ℕ) :
    (Reader.root (K := K) top).Reads (inputImpl K inputs) inputs (inputs top) :=
  ⟨fun _ _ => rfl, fun _ => rfl⟩

omit [DecidableEq K] in
theorem simulateQ_readInjected {n : ℕ} {r : Reader (K := K) top A n} {f : Word K n}
    (hr : r.Reads impl inputs f) (m : ℕ) (y : Fin (2 ^ m)) :
    ∀ inject, simulateQ impl (r.readInjected m y inject) = injected inputs m inject y
  | true => hr.input m y
  | false => rfl

omit [Field K] in
/-- After the prover's word `f`, the reader reads `f`. -/
theorem reads_commit {n : ℕ} {r : Reader (K := K) top A n} {v : Word K n}
    (hr : r.Reads impl inputs v) (f : Word K n) :
    r.commit.Reads (Access.extendImpl A _ impl f) inputs f where
  input m x := by simp only [Reader.commit, simulateQ_extendAccess, hr.input]
  word y := Access.eval_queryLatest A _ impl f y

omit [Field K] in
/-- After the prover's word `f`, a top position passes the checks if it passed them before and
`f` agrees with the verifier's word at the point it reduces to. -/
theorem simulateQ_commit_check {n : ℕ} {r : Reader (K := K) top A n} {v : Word K n}
    (hr : r.Reads impl inputs v) (f : Word K n) (x : Fin (2 ^ top)) :
    simulateQ (Access.extendImpl A _ impl f) (r.commit.check x) =
      (simulateQ impl (r.check x) && v (proj n x) == f (proj n x)) := by
  simp only [Reader.commit, simulateQ_bind, simulateQ_extendAccess, hr.word]
  rfl

/-- A fold keeps the checks. -/
theorem fold_check {n : ℕ} (r : Reader (K := K) top A n) (ω : SmoothCosetFftDomain n K) (k : ℕ)
    (hk : k ≤ n) (inject : Bool) (β : K) : (r.fold ω k hk inject β).check = r.check :=
  rfl

/-- After a fold by `2 ^ k` at `β`, the verifier's word is the fold of the word before it. -/
theorem reads_fold {n : ℕ} {r : Reader (K := K) top A n} {f : Word K n}
    (hr : r.Reads impl inputs f) (ω : SmoothCosetFftDomain n K) (k : ℕ) (hk : k ≤ n)
    (inject : Bool) (β : K) :
    (r.fold ω k hk inject β).Reads impl inputs
      (foldNext hk ω f β (injected inputs (n - k) inject)) where
  input := hr.input
  word y := by
    simp only [Reader.fold, simulateQ_bind,
      simulateQ_readAll impl _ _ _ (fun q => hr.word (fiberPoint hk y q)),
      simulateQ_readInjected impl inputs hr]
    rfl

/-- With the final polynomial `c`, a top position passes if it passed the folds and the current
word agrees with `c` at it. -/
theorem simulateQ_finalCheck {n d : ℕ} {r : Reader (K := K) top A n} {f : Word K n}
    (hr : r.Reads impl inputs f) (ω : SmoothCosetFftDomain n K) (c : Fin d → K)
    (x : Fin (2 ^ top)) :
    simulateQ impl (r.finalCheck ω c x) =
      (simulateQ impl (r.check x) && f (proj n x) == evalCoeffs c (ω (proj n x))) := by
  simp only [Reader.finalCheck, simulateQ_bind, hr.word, simulateQ_pure]
  rfl

/-- The queries pass if every queried position passes. -/
theorem simulateQ_checkAll {n d t : ℕ} {r : Reader (K := K) top A n} {f : Word K n}
    (hr : r.Reads impl inputs f) (ω : SmoothCosetFftDomain n K) (c : Fin d → K)
    (xs : Fin t → Fin (2 ^ top)) :
    simulateQ impl (r.checkAll ω c xs) =
      decide (∀ i, (simulateQ impl (r.check (xs i)) &&
        f (proj n (xs i)) == evalCoeffs c (ω (proj n (xs i)))) = true) := by
  simp only [Reader.checkAll, simulateQ_bind,
    simulateQ_readAll impl _ _ _ (fun i => simulateQ_finalCheck impl inputs hr ω c (xs i)),
    simulateQ_pure]
  rfl

end Reader

end Fri.Interaction

namespace Fri.Interaction

variable {K : Type} [Field K] [DecidableEq K]
variable {ι : Type} (ambient : OracleSpec ι) (top d t : ℕ)

set_option backward.isDefEq.respectTransparency false in
/-- Every supported honest execution from a layer accepts, when the verifier's word and the
injected inputs are codewords and the reader reads them. -/
theorem honest_accepts (sample : OracleComp ambient K)
    (sampleQueries : OracleComp ambient (Fin t → Fin (2 ^ top)))
    (inputs : (m : ℕ) → Fin (2 ^ m) → K) (hd : 0 < d) :
    ∀ {n : ℕ} (s : Schedule n) (ω : SmoothCosetFftDomain n K) (A : PFunctor)
      (impl : QueryImpl (OracleSpec.ofPFunctor A) Id) (r : Reader (K := K) top A n)
      (f : Word K n), s.ArityPos → s.InputsInCode inputs d ω →
      f ∈ ReedSolomon.code (ω : Fin (2 ^ n) ↪ K) (s.degree d) → r.Reads impl inputs f →
      (∀ x, simulateQ impl (r.check x) = true) →
      ∀ result ∈ support (executeStrategies ambient (protocol K top d t s).tree
        (protocol K top d t s).roles (protocol K top d t s).oracles A impl
        (honestProver ambient top d t inputs ω f s)
        (verifier ambient top d t sample sampleQueries ω A r s)), result.2.2 = true := by
  intro n s
  induction s with
  | final =>
    intro ω A impl r f _ _ hf hr hcheck result hresult
    rw [executeStrategies_final] at hresult
    obtain ⟨chosen, hchosen, hresult⟩ := support_bind_exists hresult
    rw [honestProver, mem_support_pure_iff] at hchosen
    subst hchosen
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
    rw [houtV, decide_eq_true_eq]
    intro i
    rw [hcheck, Bool.true_and, beq_iff_eq]
    exact (evalCoeffs_finalCoeffs ω hf _).symm
  | @fold m k hk inject rest ih =>
    intro ω A impl r f hpos hin hf hr hcheck result hresult
    rw [executeStrategies_fold] at hresult
    obtain ⟨sent, hsent, hresult⟩ := support_bind_exists hresult
    rw [honestProver, mem_support_pure_iff] at hsent
    subst hsent
    obtain ⟨next, hnext, hresult⟩ := support_bind_exists hresult
    rw [verifier, simulateQ_pure, mem_support_pure_iff] at hnext
    subst hnext
    obtain ⟨chosen, hchosen, hresult⟩ := support_bind_exists hresult
    rw [simulateQ_bind] at hchosen
    obtain ⟨β, -, hchosen⟩ := support_bind_exists hchosen
    rw [simulateQ_pure, mem_support_pure_iff] at hchosen
    subst hchosen
    obtain ⟨after, hafter, hresult⟩ := support_bind_exists hresult
    rw [mem_support_pure_iff] at hafter
    subst hafter
    obtain ⟨res, hres, hresult⟩ := support_bind_exists hresult
    rw [mem_support_pure_iff] at hresult
    subst hresult
    have hg : injected inputs (m - k) inject ∈
        ReedSolomon.code (ω.subdomain k : Fin (2 ^ (m - k)) ↪ K) (rest.degree d) := by
      cases inject
      · exact Submodule.zero_mem _
      · exact hin.1
    have hin' : rest.InputsInCode inputs d (ω.subdomain k) := by
      cases inject
      · exact hin
      · exact hin.2
    have hr' := Reader.reads_fold _ inputs (Reader.reads_commit impl inputs hr f) ω k hk inject β
    exact ih _ _ _ _ _ hpos.2 hin'
      (foldNext_mem_code hpos.1 hk (Schedule.degree_pos hd rest) ω hf β hg) hr'
      (fun x => by
        rw [Reader.fold_check, Reader.simulateQ_commit_check impl inputs hr]
        simp [hcheck])
      res hres

/-- **Completeness.** If the tallest input is a codeword of the code before the folds and every
injected input is a codeword of its code, the honest prover's execution accepts with probability
one. -/
theorem perfectCompleteness [SampleableType K] (hd : 0 < d) (ω : SmoothCosetFftDomain top K)
    (s : Schedule top) (inputs : (m : ℕ) → Fin (2 ^ m) → K) (hpos : s.ArityPos)
    (hin : s.InputsInCode inputs d ω)
    (hword : inputs top ∈ ReedSolomon.code (ω : Fin (2 ^ top) ↪ K) (s.degree d)) :
    Pr{let result ← (executeStrategies unifSpec (protocol K top d t s).tree
      (protocol K top d t s).roles (protocol K top d t s).oracles (inputAccess K)
      (inputImpl K inputs) (honestProver unifSpec top d t inputs ω (inputs top) s)
      (verifier unifSpec top d t ($ᵗ K) ($ᵗ (Fin t → Fin (2 ^ top))) ω (inputAccess K)
        (Reader.root top) s))}[result.2.2 = true] = 1 :=
  prEvent_eq_one_of_forall_mem_support _ _
    (honest_accepts unifSpec top d t _ _ inputs hd s ω _ _ _ _ hpos hin hword
      (Reader.reads_root inputs top) fun _ => rfl)

end Fri.Interaction
