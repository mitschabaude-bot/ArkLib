/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.ProofSystem.Fri.Interaction.Completeness
public import ArkLib.Interaction.Oracle.Security.KnowledgeComposition

/-!
# FRI's fold rounds: round-by-round knowledge

The knowledge state at a layer of log height `n` (`levelState`), after `j` folds, is about the
current word `f` and the set `C` of top positions at which every fold so far is consistent. Its
witness is a set `S` of top positions and a word `u`: `u` is a codeword of the layer's code that
agrees with `f` on the points `S` reduces to, `S ⊆ C` has at least `(1 - δ + j · loss) 2 ^ top`
points, and every input injected from this layer on is `δ`-close to its code. At the first layer,
`C` is everything and `f` is the tallest input, so the state says that the inputs are close to
their codes.

A fold round (`foldRound`) is the verifier's challenge `β` and the prover's next word. After `β`
the state (`foldedState`) is the same statement about the fold of `f` at `β`, one fold later; the
next word is then consistent with that fold on the new consistent set (`foldConsistent`), so the
oracle message maps witnesses back unchanged. The challenge maps a witness `(S, u)` back by
lossy correlated agreement (`foldBack`): `u` agrees with the folded word on the points `S`
reduces to, at least `1 - δ` of the folded domain, so unless `β` is a lossy MCA failure of the
fold (`FoldFails`), `f` agrees with a codeword above all of them but at most `loss · 2 ^ (n - k)`,
and so on all of `S` but at most `loss · 2 ^ top` positions (`exists_lift`). A challenge is bad
only if it is a failure (`badChallenge_foldRound`), with probability at most the fold's lossy MCA
error (`roundError`) whatever the earlier messages (`foldRoundCertificate`).

This is the argument of `FoldTrace.exists_codeword_agree_on_lossy`
(`ArkLib/ProofSystem/Fri/QuerySoundness.lean`), with the injected inputs, cut into rounds.
-/

@[expose] public section

open Interaction Interaction.Oracle Interaction.Oracle.Security OracleComp OracleSpec Domain
open ProximityGap ReedSolomon LinearCode CoreDefinitions
open scoped ProbabilityTheory

namespace Fri.Interaction

/-! ### Reducing top positions -/

section Proj

/-- At most `2 ^ (top - m)` top positions reduce to one point of the domain of `2 ^ m` points. -/
theorem card_filter_proj_eq_le {top m : ℕ} (hm : m ≤ top) (S : Finset (Fin (2 ^ top)))
    (y : Fin (2 ^ m)) : (S.filter fun x => proj m x = y).card ≤ 2 ^ (top - m) := by
  have hpow : 2 ^ top = 2 ^ m * 2 ^ (top - m) := by rw [← pow_add, Nat.add_sub_of_le hm]
  calc (S.filter fun x => proj m x = y).card
      ≤ (Finset.univ : Finset (Fin (2 ^ (top - m)))).card := by
        refine Finset.card_le_card_of_injOn
          (fun x => ⟨x / 2 ^ m, by
            rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos m), mul_comm, ← hpow]
            exact x.isLt⟩) (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) ?_
        intro x hx x' hx' h
        have hx := (Finset.mem_filter.mp hx).2
        have hx' := (Finset.mem_filter.mp hx').2
        have hmod : x.val % 2 ^ m = x'.val % 2 ^ m := by
          have := congrArg Fin.val (hx.trans hx'.symm)
          simpa [proj] using this
        have hdiv : x.val / 2 ^ m = x'.val / 2 ^ m := congrArg Fin.val h
        apply Fin.ext
        rw [← Nat.div_add_mod x.val (2 ^ m), ← Nat.div_add_mod x'.val (2 ^ m), hmod, hdiv]
    _ = 2 ^ (top - m) := by simp

/-- Reducing a set of top positions to the domain of `2 ^ m` points divides its size by at most
`2 ^ (top - m)`. -/
theorem card_le_mul_card_image_proj {top m : ℕ} (hm : m ≤ top) (S : Finset (Fin (2 ^ top))) :
    S.card ≤ 2 ^ (top - m) * (S.image (proj m)).card :=
  Finset.card_le_mul_card_image S _ fun y _ => card_filter_proj_eq_le hm S y

/-- The top positions of `S` reducing into `W` number at most `2 ^ (top - m) · |W|`. -/
theorem card_filter_proj_mem_le {top m : ℕ} (hm : m ≤ top) (S : Finset (Fin (2 ^ top)))
    (W : Finset (Fin (2 ^ m))) :
    (S.filter fun x => proj m x ∈ W).card ≤ 2 ^ (top - m) * W.card := by
  refine (card_le_mul_card_image_proj hm _).trans (Nat.mul_le_mul_left _ ?_)
  refine Finset.card_le_card fun y hy => ?_
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  exact (Finset.mem_filter.mp hx).2

/-- A fold by `2 ^ k` maps the reduction to the domain of `2 ^ n` points to the reduction to the
folded domain. -/
theorem sqFoldMapGen_proj {top n k : ℕ} (x : Fin (2 ^ top)) :
    CosetFftDomainClass.sqFoldMapGen (i := k) (proj n x) = proj (n - k) x := by
  apply Fin.ext
  simp only [CosetFftDomainClass.sqFoldMapGen, proj]
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (Nat.sub_le n k))

/-- The `2 ^ k`th power of a reduced top position is its reduction to the folded domain. -/
theorem pow_proj {K : Type} [Field K] {top n : ℕ} (ω : SmoothCosetFftDomain n K) (k : ℕ)
    (x : Fin (2 ^ top)) : ω (proj n x) ^ 2 ^ k = ω.subdomain k (proj (n - k) x) := by
  rw [← CosetFftDomainClass.pow_eq_subdomain_sqFoldMapGen (ω := ω) (i := k), sqFoldMapGen_proj]

end Proj

variable {K : Type} [Field K] [DecidableEq K]
variable (top d : ℕ) (inputs : (m : ℕ) → Fin (2 ^ m) → K) (δ loss : ℝ)

/-- The agreement density required after `j` folds: `1 - δ + j · loss`. -/
def threshold (j : ℕ) : ℝ := 1 - δ + j * loss

/-- The knowledge state at a layer of log height `n` with current word `f`, after `j` folds, with
`C` the top positions at which every fold so far is consistent. -/
def levelState {n : ℕ} (ω : SmoothCosetFftDomain n K) (s : Schedule n) (j : ℕ) (f : Word K n)
    (C : Finset (Fin (2 ^ top))) : KnowledgeState where
  Witness := Finset (Fin (2 ^ top)) × Word K n
  holds w := w.2 ∈ code (ω : Fin (2 ^ n) ↪ K) (s.degree d) ∧ w.1 ⊆ C ∧
    (∀ x ∈ w.1, w.2 (proj n x) = f (proj n x)) ∧ threshold δ loss j * 2 ^ top ≤ w.1.card ∧
    s.InputsAgree inputs d (1 - δ) ω

/-- The knowledge state after a fold's challenge `β`: the level state of the folded word, one fold
later, before the next word is sent. -/
def foldedState {n k : ℕ} (hk : k ≤ n) (ω : SmoothCosetFftDomain n K) (inject : Bool)
    (rest : Schedule (n - k)) (j : ℕ) (f : Word K n) (C : Finset (Fin (2 ^ top))) (β : K) :
    KnowledgeState where
  Witness := Finset (Fin (2 ^ top)) × Word K (n - k)
  holds w := w.2 ∈ code (ω.subdomain k : Fin (2 ^ (n - k)) ↪ K) (rest.degree d) ∧ w.1 ⊆ C ∧
    (∀ x ∈ w.1, w.2 (proj (n - k) x) =
      foldNext hk ω f β (injected inputs (n - k) inject) (proj (n - k) x)) ∧
    threshold δ loss (j + 1) * 2 ^ top ≤ w.1.card ∧
    rest.InputsAgree inputs d (1 - δ) (ω.subdomain k)

/-- The top positions consistent so far at which the next word is the fold. -/
def foldConsistent {n k : ℕ} (hk : k ≤ n) (ω : SmoothCosetFftDomain n K) (f : Word K n) (β : K)
    (g next : Word K (n - k)) (C : Finset (Fin (2 ^ top))) : Finset (Fin (2 ^ top)) :=
  C.filter fun x => foldNext hk ω f β g (proj (n - k) x) = next (proj (n - k) x)

/-- A fold round: the verifier's challenge, then the prover's next word. -/
def foldRound (K : Type) (n k : ℕ) : Protocol :=
  .public .receiver K fun _ => .oracle (Word K (n - k)) .done

/-- A fold's lossy bad event at `β`: ArkLib's lossy folding failure, or the injected fold's. -/
def FoldFails {n : ℕ} (ω : SmoothCosetFftDomain n K) (f : Word K n) (k D : ℕ) (θ : ℝ) (β : K) :
    Bool → Prop
  | false => LossyFoldingAgreementFailure ω f k D θ loss β
  | true => LossyInjectFailure ω f k D (inputs (n - k)) θ loss β

/-- A witness of the folded state lifts to `v` on the layer before the fold: `v` agrees with the
current word on all of `S` but at most `loss · 2 ^ top` positions, and an injected input is close
to its code. -/
def Lifts {n k : ℕ} (ω : SmoothCosetFftDomain n K) (inject : Bool) (rest : Schedule (n - k))
    (f : Word K n) (w : Finset (Fin (2 ^ top)) × Word K (n - k))
    (v : Finset (Fin (2 ^ top)) × Word K n) : Prop :=
  v.1 ⊆ w.1 ∧ (w.1.card : ℝ) ≤ v.1.card + loss * 2 ^ top ∧
    v.2 ∈ code (ω : Fin (2 ^ n) ↪ K) (2 ^ k * rest.degree d) ∧
    (∀ x ∈ v.1, v.2 (proj n x) = f (proj n x)) ∧
    (inject = true → Agrees (ω.subdomain k) (rest.degree d) (1 - δ) (inputs (n - k)))

open Classical in
/-- The challenge's backward map: a lift of the witness if there is one. -/
noncomputable def foldBack {n k : ℕ} (ω : SmoothCosetFftDomain n K) (inject : Bool)
    (rest : Schedule (n - k)) (f : Word K n) (w : Finset (Fin (2 ^ top)) × Word K (n - k)) :
    Finset (Fin (2 ^ top)) × Word K n :=
  if h : ∃ v, Lifts top d inputs δ loss ω inject rest f w v then h.choose else (w.1, 0)

variable {top d inputs δ loss}

theorem threshold_succ (j : ℕ) : threshold δ loss (j + 1) = threshold δ loss j + loss := by
  simp only [threshold, Nat.cast_add, Nat.cast_one]
  ring

theorem le_threshold (hloss : 0 ≤ loss) (j : ℕ) : 1 - δ ≤ threshold δ loss j := by
  unfold threshold
  have : (0 : ℝ) ≤ j * loss := mul_nonneg (Nat.cast_nonneg j) hloss
  linarith

/-- **Lossy agreement through a fold.** Unless the challenge is a lossy MCA failure of the fold, a
witness after the challenge lifts to the layer before it. -/
theorem exists_lift {n k : ℕ} (hn : n ≤ top) (hk : k ≤ n) (ω : SmoothCosetFftDomain n K)
    (inject : Bool) (rest : Schedule (n - k)) (j : ℕ) (f : Word K n)
    (C : Finset (Fin (2 ^ top))) (β : K) (hloss : 0 ≤ loss)
    (hfail : ¬ FoldFails inputs loss ω f k (rest.degree d) δ β inject)
    (w : Finset (Fin (2 ^ top)) × Word K (n - k))
    (hw : (foldedState top d inputs δ loss hk ω inject rest j f C β).holds w) :
    ∃ v, Lifts top d inputs δ loss ω inject rest f w v := by
  classical
  obtain ⟨S, u⟩ := w
  obtain ⟨hu, -, hagree, hcard, -⟩ := hw
  dsimp only at hu hagree hcard
  set T := S.image (proj (n - k)) with hTdef
  have hnk : n - k ≤ top := (Nat.sub_le n k).trans hn
  have hpow : (2 : ℝ) ^ top = 2 ^ (top - (n - k)) * 2 ^ (n - k) := by
    rw [← pow_add, Nat.sub_add_cancel hnk]
  have hpos : (0 : ℝ) < 2 ^ (top - (n - k)) := by positivity
  have hST : (S.card : ℝ) ≤ 2 ^ (top - (n - k)) * T.card := by
    exact_mod_cast card_le_mul_card_image_proj hnk S
  have hT : threshold δ loss (j + 1) * 2 ^ (n - k) ≤ T.card := by
    refine le_of_mul_le_mul_left ?_ hpos
    calc 2 ^ (top - (n - k)) * (threshold δ loss (j + 1) * 2 ^ (n - k))
        = threshold δ loss (j + 1) * 2 ^ top := by rw [hpow]; ring
      _ ≤ S.card := hcard
      _ ≤ _ := hST
  have hj := le_threshold (δ := δ) hloss j
  rw [threshold_succ] at hT
  have hN : (0 : ℝ) ≤ 2 ^ (n - k) := by positivity
  have hTθ : (Fintype.card (Fin (2 ^ (n - k))) : ℝ) * (1 - δ) ≤ T.card := by
    rw [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
    nlinarith
  have hfold : ∀ y ∈ T, u y = ProximityGap.foldWord ω f k β y +
      β ^ 2 ^ k * injected inputs (n - k) inject y := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [hagree x hx, foldNext_apply]
  -- The positions of `S` above the subset `T'` the lift reaches, and their count.
  have hlift : ∀ T' ⊆ T, (T'.card : ℝ) ≥ T.card - loss * Fintype.card (Fin (2 ^ (n - k))) →
      (S.card : ℝ) ≤ (S.filter fun x => proj (n - k) x ∈ T').card + loss * 2 ^ top := by
    intro T' hT' hT'card
    rw [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] at hT'card
    have hsplit := Finset.card_filter_add_card_filter_not (s := S)
      (fun x => proj (n - k) x ∈ T')
    have hrest : (S.filter fun x => ¬ proj (n - k) x ∈ T').card ≤
        2 ^ (top - (n - k)) * (T \ T').card := by
      refine le_trans (Finset.card_le_card ?_) (card_filter_proj_mem_le hnk S (T \ T'))
      intro x hx
      obtain ⟨hxS, hxT⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hxS, Finset.mem_sdiff.mpr
        ⟨Finset.mem_image_of_mem _ hxS, hxT⟩⟩
    have hsdiff : ((T \ T').card : ℝ) = T.card - T'.card := by
      rw [Finset.card_sdiff_of_subset hT']
      exact Nat.cast_sub (Finset.card_le_card hT')
    have hrest' : ((S.filter fun x => ¬ proj (n - k) x ∈ T').card : ℝ) ≤
        2 ^ (top - (n - k)) * (T.card - T'.card) := by
      rw [← hsdiff]
      exact_mod_cast hrest
    have hsplit' : (S.card : ℝ) = (S.filter fun x => proj (n - k) x ∈ T').card +
        (S.filter fun x => ¬ proj (n - k) x ∈ T').card := by
      exact_mod_cast hsplit.symm
    rw [hpow]
    have : 2 ^ (top - (n - k)) * ((T.card : ℝ) - T'.card) ≤
        2 ^ (top - (n - k)) * (loss * 2 ^ (n - k)) :=
      mul_le_mul_of_nonneg_left (by linarith) hpos.le
    nlinarith
  have hagreeT' : ∀ (T' : Finset (Fin (2 ^ (n - k)))) (v : Word K n),
      (∀ i x, x ∈ T' → ω i ^ (2 ^ k) = ω.subdomain k x → v i = f i) →
      ∀ x ∈ S.filter fun x => proj (n - k) x ∈ T', v (proj n x) = f (proj n x) :=
    fun T' v hv x hx => hv _ _ (Finset.mem_filter.mp hx).2 (pow_proj ω k x)
  cases inject with
  | false =>
    simp only [FoldFails, LossyFoldingAgreementFailure, not_exists, not_and, not_forall,
      not_not] at hfail
    obtain ⟨T', hT', hT'card, v, hv, hvf⟩ := hfail T hTθ
      ((mem_projectedCodeSubmod_iff _ _ _).mpr ⟨u, hu, funext fun y => by
        simp [projectedWord, hfold y.1 y.2, injected]⟩)
    exact ⟨(S.filter fun x => proj (n - k) x ∈ T', v), Finset.filter_subset _ _,
      hlift T' hT' hT'card, hv, hagreeT' T' v hvf, fun h => absurd h Bool.false_ne_true⟩
  | true =>
    simp only [FoldFails, LossyInjectFailure, not_exists, not_and, not_forall, not_not] at hfail
    obtain ⟨T', hT', hT'card, ⟨v, hv, hvf⟩, hg⟩ := hfail T hTθ
      ((mem_projectedCodeSubmod_iff _ _ _).mpr ⟨u, hu, funext fun y => by
        simp [projectedWord, hfold y.1 y.2, injected]⟩)
    refine ⟨(S.filter fun x => proj (n - k) x ∈ T', v), Finset.filter_subset _ _,
      hlift T' hT' hT'card, hv, hagreeT' T' v hvf, fun _ => ?_⟩
    obtain ⟨c, hc, hcg⟩ := (mem_projectedCodeSubmod_iff _ _ _).mp hg
    refine ⟨T', ?_, c, hc, fun y hy => (congrFun hcg ⟨y, hy⟩).symm⟩
    rw [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] at hT'card
    nlinarith

/-- A lift of a witness of the folded state is a witness of the state before the fold. -/
theorem levelState_holds_of_lifts {n k : ℕ} (hk : k ≤ n) (ω : SmoothCosetFftDomain n K)
    (inject : Bool) (rest : Schedule (n - k)) (j : ℕ) (f : Word K n)
    (C : Finset (Fin (2 ^ top))) (β : K) (w : Finset (Fin (2 ^ top)) × Word K (n - k))
    (hw : (foldedState top d inputs δ loss hk ω inject rest j f C β).holds w)
    (v : Finset (Fin (2 ^ top)) × Word K n) (hv : Lifts top d inputs δ loss ω inject rest f w v) :
    (levelState top d inputs δ loss ω (.fold k hk inject rest) j f C).holds v := by
  obtain ⟨-, hSC, -, hcard, hrest⟩ := hw
  obtain ⟨hvS, hvcard, hvcode, hvagree, hinj⟩ := hv
  refine ⟨hvcode, hvS.trans hSC, hvagree, ?_, ?_⟩
  · rw [threshold_succ] at hcard
    linarith
  · cases inject with
    | false => exact hrest
    | true => exact ⟨hinj rfl, hrest⟩

variable (top d inputs δ loss)

/-- The fold round's witness maps: back through the challenge by `foldBack`, and unchanged
through the next word, after which the state is the next layer's. -/
noncomputable def foldRoundExtractor {n k : ℕ} (hk : k ≤ n) (ω : SmoothCosetFftDomain n K)
    (inject : Bool) (rest : Schedule (n - k)) (j : ℕ) (f : Word K n)
    (C : Finset (Fin (2 ^ top))) :
    RoundExtractor (foldRound K n k).tree
      (levelState top d inputs δ loss ω (.fold k hk inject rest) j f C) :=
  fun β => ⟨foldedState top d inputs δ loss hk ω inject rest j f C β,
    foldBack top d inputs δ loss ω inject rest f,
    fun next => ⟨levelState top d inputs δ loss (ω.subdomain k) rest (j + 1) next
      (foldConsistent top hk ω f β (injected inputs (n - k) inject) next C), id, PUnit.unit⟩⟩

variable {top d inputs δ loss}

/-- After the round, the state is the next layer's, with the next word and the consistent set
it leaves. -/
theorem terminalState_foldRoundExtractor {n k : ℕ} (hk : k ≤ n) (ω : SmoothCosetFftDomain n K)
    (inject : Bool) (rest : Schedule (n - k)) (j : ℕ) (f : Word K n)
    (C : Finset (Fin (2 ^ top))) (path : (foldRound K n k).tree.ExecutionPath) :
    (foldRoundExtractor top d inputs δ loss hk ω inject rest j f C).terminalState path =
      levelState top d inputs δ loss (ω.subdomain k) rest (j + 1) path.2.1
        (foldConsistent top hk ω f path.1 (injected inputs (n - k) inject) path.2.1 C) :=
  rfl

/-- The next word cannot create knowledge: it is consistent with the fold on the new
consistent set. -/
theorem foldRoundExtractor_isProverPreserving {n k : ℕ} (hk : k ≤ n)
    (ω : SmoothCosetFftDomain n K) (inject : Bool) (rest : Schedule (n - k)) (j : ℕ)
    (f : Word K n) (C : Finset (Fin (2 ^ top))) :
    (foldRoundExtractor top d inputs δ loss hk ω inject rest j f C).IsProverPreserving
      (foldRound K n k).roles := by
  refine And.intro (fun _ h => nomatch h) fun β =>
    And.intro (fun next w hw => ?_) fun _ => trivial
  obtain ⟨hu, hSC, hagree, hcard, hrest⟩ := hw
  exact ⟨hu, hSC.trans (Finset.filter_subset _ _),
    fun x hx => (hagree x hx).trans ((Finset.mem_filter.mp (hSC hx)).2).symm, hcard, hrest⟩

/-- A bad challenge of the fold round is a lossy MCA failure of the fold. -/
theorem badChallenge_foldRound {n k : ℕ} (hn : n ≤ top) (hk : k ≤ n)
    (ω : SmoothCosetFftDomain n K) (inject : Bool) (rest : Schedule (n - k)) (j : ℕ)
    (f : Word K n) (C : Finset (Fin (2 ^ top))) (hloss : 0 ≤ loss) (β : K)
    (hbad : (foldRoundExtractor top d inputs δ loss hk ω inject rest j f C).badChallenge β) :
    FoldFails inputs loss ω f k (rest.degree d) δ β inject := by
  classical
  obtain ⟨w, hnot, hw⟩ := hbad
  by_contra hfail
  have hex := exists_lift hn hk ω inject rest j f C β hloss hfail w hw
  apply hnot
  change (levelState top d inputs δ loss ω (.fold k hk inject rest) j f C).holds
    (foldBack top d inputs δ loss ω inject rest f w)
  rw [show foldBack top d inputs δ loss ω inject rest f w = hex.choose from dite_eq_left hex]
  exact levelState_holds_of_lifts hk ω inject rest j f C β w hw _ hex.choose_spec

/-- A fold fails with probability at most its lossy MCA error, whatever the current word. -/
theorem prob_foldFails_le [Fintype K] [SampleableType K] {n : ℕ} (ω : SmoothCosetFftDomain n K)
    (f : Word K n) (k D : ℕ) (hD : 0 < D) (θ : ℝ) :
    ∀ inject, Pr{let β ←$ᵗ K}[FoldFails inputs loss ω f k D θ β inject] ≤
      Schedule.roundError ω k D θ loss inject
  | false => lossyFoldingAgreementFailure_prob_le_powers ω f hD θ loss
  | true => lossyInjectFailure_prob_le ω f (inputs (n - k)) hD θ loss

variable (top d inputs δ loss)

/-- **The fold round's knowledge certificate.** The challenge is uniform, and it is bad with
probability at most the fold's lossy MCA error (`Schedule.roundError`), whatever the earlier
messages. -/
noncomputable def foldRoundCertificate [Fintype K] [SampleableType K] (hd : 0 < d)
    (hloss : 0 ≤ loss) {n k : ℕ} (hn : n ≤ top) (hk : k ≤ n) (ω : SmoothCosetFftDomain n K)
    (inject : Bool) (rest : Schedule (n - k)) (j : ℕ) (f : Word K n)
    (C : Finset (Fin (2 ^ top))) :
    KnowledgeCertificate (foldRound K n k).tree (foldRound K n k).roles
      (levelState top d inputs δ loss ω (.fold k hk inject rest) j f C) where
  extractor := foldRoundExtractor top d inputs δ loss hk ω inject rest j f C
  challenges := ⟨($ᵗ K, Schedule.roundError ω k (rest.degree d) δ loss inject),
    fun _ _ => PUnit.unit⟩
  prover_preserving := foldRoundExtractor_isProverPreserving hk ω inject rest j f C
  local_bound := by
    refine ⟨?_, fun _ _ => trivial⟩
    rw [_root_.RoundByRound.GameFamily.isBounded_iff]
    intro _ _
    exact (prEvent_mono _ _ _ fun β hbad =>
      badChallenge_foldRound hn hk ω inject rest j f C hloss β hbad).trans
      (prob_foldFails_le ω f k _ (Schedule.degree_pos hd rest) δ inject)

end Fri.Interaction
