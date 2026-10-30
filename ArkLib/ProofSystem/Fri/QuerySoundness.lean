/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoichi Hirai, Pietro Monticone, Aristotle (Harmonic), Alexander Hicks
-/

module

public import ArkLib.ProofSystem.Fri.Projection
public import ArkLib.Data.CodingTheory.ListDecodability.AgreementRadius

/-!
# FRI query soundness

A typed trace of successive applications of ArkLib's folding operation records the words
and challenges used by the query checks. It permits a different folding factor at every
step. This is an algebraic view of a fixed commitment transcript, not a new interactive
protocol: it contains no prover strategy or sampling procedure.

The key induction lifts agreement on any sufficiently large subset of accepting queries.
In particular, it retains the actual accepting positions, as required by the binding and
erasure-detection interpretation in the March 27, 2026 revision of [GMW25].
`FoldTrace.exists_codeword_of_query_probability` gives the algebraic conclusions of
Corollary 5.6 with separate distance and tradeoff parameters. Interpolation is proved
for every subset of accepting positions of the required size; no complexity bound is asserted.

## Lossy MCA

With lossy MCA (`IsLossyMCA`), agreement no longer propagates upward through the whole green
subgraph of [GMW25, §5.1], only through all but a `loss` fraction of each layer. A fold is
exploitable (`LossyFoldingAgreementFailure`) when the folded word agrees with a codeword on a set
`T` of at least `(1 - θ)` of its domain `L'`, yet the previous word agrees with a codeword on the
blocks above no `T' ⊆ T` with `|T \ T'| ≤ loss · |L'|`. Its probability is at most the lossy MCA
error of the coefficient words (`lossyFoldingAgreementFailure_prob_le`).

Every point of `L'` has `|L| / |L'|` preimages in the domain `L` of the previous word, so the
blocks above `T \ T'` cover at most `loss · |L|` points: the loss is the same fraction of every
layer. On the original domain `L₀` with `N = |L₀|`, take the accepting set `S` and `m` folds,
none of them exploitable. Going down from the final word (which agrees with its code on all of
`S`), the fold into layer `j` receives agreement on the projection of `S_j ⊆ S`, where `S_j`
has lost at most `(m - j) · loss · N` points of `S` to the folds below. A projection never
shrinks density, so the fold applies once `|S_j| ≥ (1 - θ) N`; this holds for every fold if
`|S| ≥ (1 - θ + (m - 1) · loss) N`, the outermost fold receiving the smallest set. It returns
agreement on `S_{j-1} ⊆ S_j` with `|S_j \ S_{j-1}| ≤ loss · N`. After all `m` folds, a codeword
of the original code agrees with `f₀` on `S₀ ⊆ S` with `|S \ S₀| ≤ m · loss · N`
(`exists_codeword_agree_on_lossy`).

If `f₀` has distance at least `δ` from its code, then `|S₀| ≤ (1 - δ) N`. Hence either
`|S| < (1 - θ + (m - 1) · loss) N` or `|S| ≤ (1 - δ + m · loss) N`, so the accepting density
is at most `1 - min (θ - (m - 1) · loss) (δ - m · loss)` (`accepting_density_le_lossy`), and
`t` independent queries all accept with probability at most its `t`-th power
(`query_soundness_lossy`). This is at most `(1 - min θ δ + m · loss)^t`. With the `k + 1` folds
of `Fri.Spec`, the query term is `(1 - min (θ - k · loss) (δ - (k + 1) · loss))^l`. At
`loss = 0` everything reduces to the lossless statements.

## References

* [Garreta, A., Mohnblatt, N., Wagner, B., *A Simplified Round-by-round Soundness Proof
  of FRI*][GMW25]

The proof strategy is also informed by
[zkSecurity's formalization](https://github.com/zksecurity/simple-rbr-fri), by Yoichi Hirai
and Harmonic's Aristotle, with subsequent work by Pietro Monticone. The author list credits
that source formalization and Alexander Hicks's ArkLib adaptation.
-/

@[expose] public section

namespace Fri

open Polynomial Domain ProximityGap ReedSolomon LinearCode
open CosetFftDomainClass (sqFoldMapGen)
open OracleComp
open scoped BigOperators ProbabilityTheory

variable {F : Type} [Field F] [DecidableEq F]

/-! ## Fixed commitment traces -/

/-- The algebraic data read by FRI's query phase. At each step the degree bound and domain
shrink by the folding factor; the last word is checked for membership in its RS code. -/
inductive FoldTrace : {n : ℕ} → SmoothCosetFftDomain n F → ℕ → Type
  | terminal {n : ℕ} {domain : SmoothCosetFftDomain n F} {d : ℕ}
      (f : Fin (2 ^ n) → F) : FoldTrace domain d
  | step {n k d : ℕ} {domain : SmoothCosetFftDomain n F}
      (hk : k ≤ n) (hd : 0 < d) (f : Fin (2 ^ n) → F) (α : F)
      (tail : FoldTrace (domain.subdomain k) d) : FoldTrace domain (2 ^ k * d)

namespace FoldTrace

variable {n d : ℕ} {domain : SmoothCosetFftDomain n F}

/-- The word at the beginning of a folding trace. -/
def initial : FoldTrace domain d → (Fin (2 ^ n) → F)
  | .terminal f => f
  | .step _ _ f _ _ => f

/-- The final code-membership check. -/
def FinalInCode : {n d : ℕ} → {domain : SmoothCosetFftDomain n F} →
    FoldTrace domain d → Prop
  | _, d, domain, .terminal f => f ∈ code domain d
  | _, _, _, .step _ _ _ _ tail => tail.FinalInCode

/-- None of the folding challenges has lost the ability to lift large agreement sets. -/
def Safe (θ : ℝ) : {n d : ℕ} → {domain : SmoothCosetFftDomain n F} →
    FoldTrace domain d → Prop
  | _, _, _, .terminal _ => True
  | _, _, domain, .step (k := k) (d := d) _ _ f α tail =>
      ¬ FoldingAgreementFailure domain f k d θ α ∧ tail.Safe θ

/-- The number of folding steps. -/
def numFolds : {n d : ℕ} → {domain : SmoothCosetFftDomain n F} → FoldTrace domain d → ℕ
  | _, _, _, .terminal _ => 0
  | _, _, _, .step _ _ _ _ tail => tail.numFolds + 1

/-- No folding challenge is lossily bad: every large agreement set of each fold lifts to the
preimage of a subset missing at most a `loss` fraction of the folded domain. -/
def SafeLossy (θ loss : ℝ) : {n d : ℕ} → {domain : SmoothCosetFftDomain n F} →
    FoldTrace domain d → Prop
  | _, _, _, .terminal _ => True
  | _, _, domain, .step (k := k) (d := d) _ _ f α tail =>
      ¬ LossyFoldingAgreementFailure domain f k d θ loss α ∧ tail.SafeLossy θ loss

/-- Initial positions at which every local folding check accepts. -/
noncomputable def accepting : {n d : ℕ} → {domain : SmoothCosetFftDomain n F} →
    FoldTrace domain d → Finset (Fin (2 ^ n))
  | _, _, _, .terminal _ => Finset.univ
  | _, _, domain, .step (k := k) _ _ f α tail => by
      classical
      exact Finset.univ.filter fun i ↦
        let x := sqFoldMapGen (i := k) i
        foldWord domain f k α x = tail.initial x ∧ x ∈ tail.accepting

/-- Acceptance of a fixed query vector, including the final code-membership check. -/
def Accepts (tr : FoldTrace domain d) {t : ℕ} (xs : Fin t → Fin (2 ^ n)) : Prop :=
  tr.FinalInCode ∧ ∀ j, xs j ∈ tr.accepting

/-! ## Query probability and agreement lifting -/

/-- For a valid final word, independent uniform repetitions accept with probability equal
to the accepting density raised to the number of repetitions. -/
theorem query_acceptance_probability (tr : FoldTrace domain d) (t : ℕ)
    (hfinal : tr.FinalInCode) :
    Pr{let xs ←$ᵗ (Fin t → Fin (2 ^ n))}[tr.Accepts xs] =
      ((tr.accepting.card : ENNReal) / (2 ^ n : ENNReal)) ^ t := by
  classical
  rw [prEvent_congr _ _ (fun xs ↦ ∀ j, xs j ∈ tr.accepting)
    (fun xs ↦ by simp only [Accepts, hfinal, true_and])]
  simpa using Probability.prob_uniform_pi_mem_finset_eq tr.accepting t

/-- A lower bound on repeated-query acceptance implies the corresponding density bound.
The positive repetition count is essential; no safety assumption is needed here. -/
theorem accepting_card_ge_of_query_probability (tr : FoldTrace domain d)
    (θ : ℝ) {t : ℕ} (ht : 0 < t) (hfinal : tr.FinalInCode)
    (hprob : ENNReal.ofReal (1 - θ) ^ t ≤ Pr{
      let xs ← $ᵗ (Fin t → Fin (2 ^ n))}[tr.Accepts xs]) :
    (2 ^ n : ℝ) * (1 - θ) ≤ tr.accepting.card := by
  rw [tr.query_acceptance_probability t hfinal] at hprob
  have hbase := (ENNReal.pow_le_pow_left_iff ht.ne').mp hprob
  have hreal : 1 - θ ≤ (tr.accepting.card : ℝ) / 2 ^ n := by
    have hcast : (tr.accepting.card : ENNReal) / (2 ^ n : ENNReal) =
        ENNReal.ofReal ((tr.accepting.card : ℝ) / 2 ^ n) := by
      simp [ENNReal.ofReal_div_of_pos, show (0 : ℝ) < 2 ^ n by positivity]
    rw [hcast] at hbase
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hbase
  have := (le_div_iff₀ (show (0 : ℝ) < 2 ^ n by positivity)).mp hreal
  simpa [mul_comm] using this

/-- Without loss, lossy safety is safety. -/
theorem safeLossy_zero_iff (tr : FoldTrace domain d) (θ : ℝ) :
    tr.SafeLossy θ 0 ↔ tr.Safe θ := by
  induction tr with
  | terminal f => exact Iff.rfl
  | step hk hd f α tail ih =>
    simp only [SafeLossy, Safe, lossyFoldingAgreementFailure_zero_iff, ih]

/-- On a lossily safe trace with a valid final word, a large subset `S` of accepting queries
agrees with one original codeword off at most `numFolds · loss · 2 ^ n` of its positions. Every
fold loses `loss` relative to its domain, which is the same fraction of the initial domain. The
size threshold accounts for the losses of all but the outermost fold. -/
theorem exists_codeword_agree_on_lossy (tr : FoldTrace domain d) (θ loss : ℝ)
    (hloss : 0 ≤ loss) (hsafe : tr.SafeLossy θ loss) (hfinal : tr.FinalInCode)
    (S : Finset (Fin (2 ^ n))) (hS : S ⊆ tr.accepting)
    (hlarge : (2 ^ n : ℝ) * (1 - θ) + ((tr.numFolds : ℝ) - 1) * loss * 2 ^ n ≤ S.card) :
    ∃ u ∈ code domain d, ∃ S' ⊆ S, (S.card : ℝ) ≤ S'.card + tr.numFolds * loss * 2 ^ n ∧
      ∀ i ∈ S', u i = tr.initial i := by
  classical
  induction tr with
  | terminal f => exact ⟨f, hfinal, S, subset_rfl, by simp [numFolds], fun _ _ ↦ rfl⟩
  | @step n k d domain hk hd f α tail ih =>
    simp only [numFolds, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hlarge ⊢
    set m : ℝ := (tail.numFolds : ℝ)
    let T := S.image (sqFoldMapGen (i := k))
    have hT : T ⊆ tail.accepting := by
      rintro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp (hS hi)).2.2
    set N : ℝ := 2 ^ (n - k)
    have hn : (2 : ℝ) ^ n = 2 ^ k * N := by
      rw [← pow_add, Nat.add_sub_of_le hk]
    have hkpos : (0 : ℝ) < 2 ^ k := by positivity
    have hTlarge : N * (1 - θ) + m * loss * N ≤ T.card := by
      have hc : (S.card : ℝ) ≤ 2 ^ k * (T.card : ℝ) := by
        exact_mod_cast card_le_mul_card_sqFoldMapGen_image domain k S
      rw [hn] at hlarge
      have : 2 ^ k * (N * (1 - θ) + m * loss * N) ≤ 2 ^ k * T.card := by linarith
      exact le_of_mul_le_mul_left this hkpos
    have hmloss : 0 ≤ loss * N := by positivity
    obtain ⟨u, hu, T₂, hT₂, hT₂card, hagree⟩ := ih hsafe.2 hfinal T hT (by nlinarith)
    have hfold : projectedWord (foldWord domain f k α) T₂ ∈
        projectedCodeSubmod (code (domain.subdomain k) d) T₂ := by
      rw [mem_projectedCodeSubmod_iff]
      refine ⟨u, hu, ?_⟩
      funext x
      obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp (hT₂ x.property)
      have hcheck := (Finset.mem_filter.mp (hS hi)).2.1
      exact (hix ▸ hcheck).trans (hagree x x.property).symm
    obtain ⟨T₃, hT₃, hT₃card, v, hv, hvagree⟩ : ∃ T₃ ⊆ T₂,
        (T₃.card : ℝ) ≥ T₂.card - loss * Fintype.card (Fin (2 ^ (n - k))) ∧
        ∃ v ∈ code domain (2 ^ k * d),
          ∀ i x, x ∈ T₃ → domain i ^ (2 ^ k) = domain.subdomain k x → v i = f i := by
      by_contra h
      exact hsafe.1 ⟨T₂, by simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]; linarith,
        hfold, fun T' hT' hc hex ↦ h ⟨T', hT', hc, hex⟩⟩
    simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] at hT₃card
    refine ⟨v, hv, S.filter fun i ↦ sqFoldMapGen (i := k) i ∈ T₃, Finset.filter_subset _ _,
      ?_, fun i hi ↦ hvagree i _ (Finset.mem_filter.mp hi).2
        (CosetFftDomainClass.pow_eq_subdomain_sqFoldMapGen (ω := domain) i).symm⟩
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := S) (fun i ↦ sqFoldMapGen (i := k) i ∈ T₃)
    have hrest : (S.filter fun i ↦ ¬ sqFoldMapGen (i := k) i ∈ T₃).card ≤
        2 ^ k * (T \ T₃).card := by
      refine le_trans (Finset.card_le_card ?_) (card_filter_sqFoldMapGen_mem_le domain k S _)
      intro i hi
      obtain ⟨hiS, hiT⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_filter.mpr ⟨hiS, Finset.mem_sdiff.mpr
        ⟨Finset.mem_image_of_mem _ hiS, hiT⟩⟩
    have hsdiff : ((T \ T₃).card : ℝ) = T.card - T₃.card := by
      rw [Finset.card_sdiff_of_subset (hT₃.trans hT₂)]
      exact Nat.cast_sub (Finset.card_le_card (hT₃.trans hT₂))
    have hrest' : ((S.filter fun i ↦ ¬ sqFoldMapGen (i := k) i ∈ T₃).card : ℝ) ≤
        2 ^ k * (T.card - T₃.card) := by
      rw [← hsdiff]
      exact_mod_cast hrest
    have hsplit' : (S.card : ℝ) = (S.filter fun i ↦ sqFoldMapGen (i := k) i ∈ T₃).card +
        (S.filter fun i ↦ ¬ sqFoldMapGen (i := k) i ∈ T₃).card := by
      exact_mod_cast hsplit.symm
    rw [hn]
    have : 2 ^ k * ((T.card : ℝ) - T₃.card) ≤ 2 ^ k * ((m + 1) * loss * N) :=
      mul_le_mul_of_nonneg_left (by linarith) hkpos.le
    nlinarith

/-- On a safe trace with a valid final word, any sufficiently large subset of accepting
queries agrees with one original codeword. This also covers zero folding steps. -/
theorem exists_codeword_agree_on (tr : FoldTrace domain d) (θ : ℝ)
    (hsafe : tr.Safe θ) (hfinal : tr.FinalInCode)
    (S : Finset (Fin (2 ^ n))) (hS : S ⊆ tr.accepting)
    (hlarge : (2 ^ n : ℝ) * (1 - θ) ≤ S.card) :
    ∃ u ∈ code domain d, ∀ i ∈ S, u i = tr.initial i := by
  obtain ⟨u, hu, S', hS', hcard, hagree⟩ := tr.exists_codeword_agree_on_lossy θ 0 le_rfl
    ((tr.safeLossy_zero_iff θ).mpr hsafe) hfinal S hS (by simpa using hlarge)
  rw [Finset.eq_of_subset_of_card_le hS' (by simpa using hcard)] at hagree
  exact ⟨u, hu, hagree⟩

/-- On a lossily safe trace, the accepting-query density is at most
`1 - min (θ - (numFolds - 1) · loss) (δ - numFolds · loss)`, where `δ` is any lower bound on the
initial word's distance to its code. -/
theorem accepting_density_le_lossy (tr : FoldTrace domain d) (θ δ loss : ℝ) (hloss : 0 ≤ loss)
    (hsafe : tr.SafeLossy θ loss) (hfinal : tr.FinalInCode)
    (hdist : ∀ u ∈ code domain d, δ ≤ (Code.relHammingDist tr.initial u : ℝ)) :
    (tr.accepting.card : ℝ) / 2 ^ n ≤
      1 - min (θ - ((tr.numFolds : ℝ) - 1) * loss) (δ - tr.numFolds * loss) :=
  accepting_density_le_of_lossy_agreement domain tr.initial tr.accepting θ δ _ _
    (fun h ↦ tr.exists_codeword_agree_on_lossy θ loss hloss hsafe hfinal tr.accepting
      (fun _ h ↦ h) (by linarith)) hdist

/-- The accepting-query density is bounded by the tradeoff threshold or by the initial
word's agreement with its code, whichever is larger. `δ` may be any lower bound on distance. -/
theorem accepting_density_le (tr : FoldTrace domain d) (θ δ : ℝ)
    (hsafe : tr.Safe θ) (hfinal : tr.FinalInCode)
    (hdist : ∀ u ∈ code domain d, δ ≤ (Code.relHammingDist tr.initial u : ℝ)) :
    (tr.accepting.card : ℝ) / 2 ^ n ≤ 1 - min θ δ := by
  simpa using tr.accepting_density_le_lossy θ δ 0 le_rfl ((tr.safeLossy_zero_iff θ).mpr hsafe)
    hfinal hdist

/-- A lossily safe trace accepts independent uniform queries with probability at most
`(1 - min (θ - (numFolds - 1) · loss) (δ - numFolds · loss))^t`, where `δ` is a lower bound on
the initial word's distance to its code. -/
theorem query_soundness_lossy (tr : FoldTrace domain d) (θ δ loss : ℝ) (t : ℕ)
    (hloss : 0 ≤ loss) (hsafe : tr.SafeLossy θ loss)
    (hdist : ∀ u ∈ code domain d, δ ≤ (Code.relHammingDist tr.initial u : ℝ)) :
    Pr{let xs ←$ᵗ (Fin t → Fin (2 ^ n))}[tr.Accepts xs] ≤
      ENNReal.ofReal (1 - min (θ - ((tr.numFolds : ℝ) - 1) * loss)
        (δ - tr.numFolds * loss)) ^ t := by
  classical
  by_cases hfinal : tr.FinalInCode
  · rw [tr.query_acceptance_probability t hfinal]
    apply pow_le_pow_left' _ t
    have h := ENNReal.ofReal_le_ofReal
      (tr.accepting_density_le_lossy θ δ loss hloss hsafe hfinal hdist)
    simpa [ENNReal.ofReal_div_of_pos, show (0 : ℝ) < 2 ^ n by positivity] using h
  · rw [prEvent_congr _ _ (fun _ ↦ False)
      (fun xs ↦ by simp only [Accepts, hfinal, false_and])]
    rw [prEvent_const_of_not _ not_false]
    exact zero_le

/-- A safe trace accepts independent uniform queries with probability at most
`(1 - min θ δ)^t`, where `δ` is a lower bound on the initial word's distance to its code. -/
theorem query_soundness (tr : FoldTrace domain d) (θ δ : ℝ) (t : ℕ)
    (hsafe : tr.Safe θ)
    (hdist : ∀ u ∈ code domain d, δ ≤ (Code.relHammingDist tr.initial u : ℝ)) :
    Pr{let xs ←$ᵗ (Fin t → Fin (2 ^ n))}[tr.Accepts xs] ≤
      ENNReal.ofReal (1 - min θ δ) ^ t := by
  simpa using tr.query_soundness_lossy θ δ 0 t le_rfl ((tr.safeLossy_zero_iff θ).mpr hsafe) hdist

/-- The query bound at the actual relative distance to the original Reed–Solomon code. -/
theorem query_soundness_distance (tr : FoldTrace domain d) (θ : ℝ) (t : ℕ)
    (hsafe : tr.Safe θ) :
    Pr{let xs ←$ᵗ (Fin t → Fin (2 ^ n))}[tr.Accepts xs] ≤
      ENNReal.ofReal (1 - min θ
        (Code.relDistFromCode tr.initial
          (code (domain : Fin (2 ^ n) ↪ F) d : Set (Fin (2 ^ n) → F))).toReal) ^ t := by
  apply tr.query_soundness θ _ t hsafe
  intro u hu
  have h := Code.relDistFromCode_le_relDist_to_mem tr.initial u hu
  have hfinite : (Code.relHammingDist tr.initial u : ENNReal) ≠ ⊤ := by
    rw [ENNReal.coe_NNRat_coe_NNReal]
    exact ENNReal.coe_ne_top
  simpa [Code.relHammingDist, ENNReal.coe_NNRat_coe_NNReal] using
    ENNReal.toReal_mono hfinite h

/-! ## Binding and interpolation -/

/-- On a safe trace with a valid final word, an accepting set meeting the agreement-lifting
threshold and containing at least `d` positions determines a unique original codeword. -/
theorem exists_unique_codeword_agree (tr : FoldTrace domain d) (θ : ℝ)
    (hsafe : tr.Safe θ) (hfinal : tr.FinalInCode)
    (hlarge : (2 ^ n : ℝ) * (1 - θ) ≤ tr.accepting.card)
    (hrate : d ≤ tr.accepting.card) :
    ∃! u, u ∈ code domain d ∧ ∀ i ∈ tr.accepting, u i = tr.initial i := by
  classical
  obtain ⟨u, hu, hagree⟩ := tr.exists_codeword_agree_on θ hsafe hfinal
    tr.accepting (fun _ h ↦ h) hlarge
  refine ⟨u, ⟨hu, hagree⟩, ?_⟩
  rintro v ⟨hv, hvagree⟩
  by_contra hne
  have hlt := ReedSolomon.agree_lt_of_mem_code hv hu hne
  have hcard : tr.accepting.card ≤ Code.agree v u := by
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hvagree i hi).trans (hagree i hi).symm⟩
  omega

/-- For a safe trace with a valid final word, acceptance probability at least `(1 - δ)^t`
with `t > 0`, `δ ≤ θ`, and `δ ≤ 1 - d / 2^n` determines a unique codeword on accepting positions. -/
theorem exists_unique_codeword_agree_of_query_probability (tr : FoldTrace domain d)
    (θ δ : ℝ) {t : ℕ} (ht : 0 < t) (hsafe : tr.Safe θ) (hfinal : tr.FinalInCode)
    (hδθ : δ ≤ θ) (hrate : δ ≤ 1 - (d : ℝ) / 2 ^ n)
    (hprob : ENNReal.ofReal (1 - δ) ^ t ≤ Pr{
      let xs ← $ᵗ (Fin t → Fin (2 ^ n))}[tr.Accepts xs]) :
    ∃! u, u ∈ code domain d ∧ ∀ i ∈ tr.accepting, u i = tr.initial i := by
  have hcard := tr.accepting_card_ge_of_query_probability δ ht hfinal hprob
  have hlarge : (2 ^ n : ℝ) * (1 - θ) ≤ tr.accepting.card :=
    (mul_le_mul_of_nonneg_left (sub_le_sub_left hδθ 1) (by positivity)).trans hcard
  have hdegree : (d : ℝ) ≤ (2 ^ n : ℝ) * (1 - δ) := by
    have h := (div_le_iff₀ (show (0 : ℝ) < 2 ^ n by positivity)).mp
      (show (d : ℝ) / 2 ^ n ≤ 1 - δ by linarith)
    simpa [mul_comm] using h
  apply tr.exists_unique_codeword_agree θ hsafe hfinal hlarge
  exact_mod_cast hdegree.trans hcard

/-- For a safe trace with a valid final word and accepting density at least `1 - θ`,
interpolation on any `d` accepting positions has degree less than `d` and agrees with the
initial word on every accepting position. -/
theorem interpolate_accepting_agrees (tr : FoldTrace domain d) (θ : ℝ)
    (hsafe : tr.Safe θ) (hfinal : tr.FinalInCode)
    (hlarge : (2 ^ n : ℝ) * (1 - θ) ≤ tr.accepting.card)
    (S : Finset (Fin (2 ^ n))) (hS : S ⊆ tr.accepting) (hcard : S.card = d) :
    let p := Lagrange.interpolate S domain tr.initial
    p.degree < d ∧ ∀ i ∈ tr.accepting, p.eval (domain i) = tr.initial i := by
  obtain ⟨u, hu, hagree⟩ := tr.exists_codeword_agree_on θ hsafe hfinal
    tr.accepting (fun _ h ↦ h) hlarge
  obtain ⟨p, hp, heval⟩ := ReedSolomon.mem_code_iff_eval.mp hu
  have heq : p = Lagrange.interpolate S domain tr.initial := by
    apply Lagrange.eq_interpolate_of_eval_eq _ Domain.CosetFftDomain.injOn
    · simpa [hcard] using hp
    · intro i hi
      exact (heval i).trans (hagree i (hS hi))
  rw [← heq]
  exact ⟨hp, fun i hi ↦ (heval i).trans (hagree i hi)⟩

/-- A query at a disagreement with a word agreeing on all accepting positions forces rejection. -/
theorem not_accepts_of_disagreement (tr : FoldTrace domain d)
    {u : Fin (2 ^ n) → F} (hagree : ∀ i ∈ tr.accepting, u i = tr.initial i)
    {t : ℕ} {xs : Fin t → Fin (2 ^ n)}
    (h : ∃ j, u (xs j) ≠ tr.initial (xs j)) : ¬ tr.Accepts xs := by
  rintro ⟨_, hxs⟩
  obtain ⟨j, hj⟩ := h
  exact hj (hagree _ (hxs j))

/-- If a safe trace has positive degree bound and accepts `t > 0` queries with probability
at least `(1 - δ)^t`, where `δ ≤ θ` and `δ ≤ 1 - d / 2^n`, its initial word is `δ`-close
to its code. A unique codeword agrees on all accepting positions, is recovered by interpolation
on any `d` of those positions, and any query at a disagreement with it forces rejection. -/
theorem exists_codeword_of_query_probability (tr : FoldTrace domain d)
    (θ δ : ℝ) (hd : 0 < d) {t : ℕ} (ht : 0 < t) (hsafe : tr.Safe θ)
    (hδθ : δ ≤ θ) (hrate : δ ≤ 1 - (d : ℝ) / 2 ^ n)
    (hprob : ENNReal.ofReal (1 - δ) ^ t ≤ Pr{
      let xs ← $ᵗ (Fin t → Fin (2 ^ n))}[tr.Accepts xs]) :
    Code.relDistFromCode tr.initial
        (code (domain : Fin (2 ^ n) ↪ F) d : Set (Fin (2 ^ n) → F)) ≤
        ENNReal.ofReal δ ∧
      ∃ u, (u ∈ code domain d ∧ ∀ i ∈ tr.accepting, u i = tr.initial i) ∧
        (∀ v, (v ∈ code domain d ∧ ∀ i ∈ tr.accepting, v i = tr.initial i) → v = u) ∧
        (Code.relHammingDist tr.initial u : ℝ) ≤ δ ∧
        (∀ S : Finset (Fin (2 ^ n)), S ⊆ tr.accepting → S.card = d →
          let p := Lagrange.interpolate S domain tr.initial
          p.degree < d ∧ evalOnPoints domain p = u) ∧
        (∀ {m : ℕ} (xs : Fin m → Fin (2 ^ n)),
          (∃ j, u (xs j) ≠ tr.initial (xs j)) → ¬ tr.Accepts xs) := by
  have hn : (0 : ℝ) < 2 ^ n := by positivity
  have hδ : δ < 1 := by
    have : (0 : ℝ) < (d : ℝ) / 2 ^ n := div_pos (by exact_mod_cast hd) hn
    linarith
  have hfinal : tr.FinalInCode := by
    by_contra h
    have hzero : Pr{let xs ← $ᵗ (Fin t → Fin (2 ^ n))}[tr.Accepts xs] = 0 := by
      rw [prEvent_congr _ _ (fun _ ↦ False)
        (fun xs ↦ by simp only [Accepts, h, false_and])]
      exact prEvent_const_of_not _ not_false
    have hpos : 0 < ENNReal.ofReal (1 - δ) ^ t :=
      pos_iff_ne_zero.mpr (pow_ne_zero _ (ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))))
    rw [hzero] at hprob
    exact (not_le_of_gt hpos) hprob
  obtain ⟨u, hu, huniq⟩ := tr.exists_unique_codeword_agree_of_query_probability
    θ δ ht hsafe hfinal hδθ hrate hprob
  have hcard := tr.accepting_card_ge_of_query_probability δ ht hfinal hprob
  have hlarge : (2 ^ n : ℝ) * (1 - θ) ≤ tr.accepting.card :=
    (mul_le_mul_of_nonneg_left (sub_le_sub_left hδθ 1) hn.le).trans hcard
  have hagree : tr.accepting.card ≤ Code.agree u tr.initial := by
    apply Finset.card_le_card
    exact fun i hi ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu.2 i hi⟩
  have hdist : (Code.relHammingDist tr.initial u : ℝ) ≤ δ := by
    have h := Code.relHammingDist_le_one_sub_div_of_le_agree hagree
    simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] at h
    have hden := (le_div_iff₀ hn).mpr (by simpa [mul_comm] using hcard)
    linarith
  have hcode := Code.relDistFromCode_le_relDist_to_mem tr.initial u hu.1
  have hdist' : (Code.relHammingDist tr.initial u : ENNReal) ≤ ENNReal.ofReal δ := by
    rw [ENNReal.coe_NNRat_coe_NNReal, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hdist
  refine ⟨hcode.trans hdist', u, hu, huniq, hdist, ?_, ?_⟩
  · intro S hS hSCard
    obtain ⟨hp, hagree⟩ := tr.interpolate_accepting_agrees θ hsafe hfinal hlarge S hS hSCard
    exact ⟨hp, huniq _ ⟨evalOnPoints_mem_code_of_degree_lt hp, hagree⟩⟩
  · exact fun xs h ↦ tr.not_accepts_of_disagreement hu.2 h

end FoldTrace

end Fri
