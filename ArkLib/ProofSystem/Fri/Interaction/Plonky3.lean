/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.ProofSystem.Fri.Interaction.Schedule

/-!
# Plonky3's folding schedule

`Schedule.plonky3` builds FRI's schedule as Plonky3's `fold_schedule` does for inputs of log
heights `m₁ > m₂ > …` below the tallest: from height `n`, fold by
`min (n - mᵢ) (n - logFinal) maxLogArity` towards the next input's height `mᵢ` and the final
height, and inject the input when its height is reached.

For heights strictly decreasing, all below `n` and at least `logFinal` (`Fits`), the folds reach
the final height exactly (`degree_plonky3`: the code before them has degree bound
`2 ^ (n - logFinal) d`), each fold halves the domain at least once (`arityPos_plonky3`), and every
input is injected: inputs agreeing in the schedule means each input agrees with its code, on a
domain the folds reach from the first (`agrees_of_inputsAgree`). Conversely, inputs that are
codewords on every domain the folds may reach are in their codes in the schedule
(`inputsInCode_plonky3`).
-/

@[expose] public section

namespace Fri.Interaction

open Domain

namespace Schedule

/-- The log arity of the fold from height `n`: towards the next input's height and the final
height, at most `maxLogArity`. -/
def logArity (maxLogArity logFinal n : ℕ) (heights : List ℕ) : ℕ :=
  min (min (n - heights.headD logFinal) (n - logFinal)) maxLogArity

theorem logArity_le (maxLogArity logFinal n : ℕ) (heights : List ℕ) :
    logArity maxLogArity logFinal n heights ≤ n - logFinal :=
  (min_le_left _ _).trans (min_le_right _ _)

/-- The fold towards the next input does not pass it. -/
theorem logArity_le_cons (maxLogArity logFinal n m : ℕ) (rest : List ℕ) :
    logArity maxLogArity logFinal n (m :: rest) ≤ n - m :=
  (min_le_left _ _).trans (min_le_left _ _)

/-- Plonky3's folding schedule from height `n` down to `logFinal`, injecting the input of each
height of `heights` (tallest first), with `fuel` folds at most. -/
def plonky3 (maxLogArity logFinal : ℕ) : (fuel n : ℕ) → List ℕ → Schedule n
  | 0, _, _ => .final
  | fuel + 1, n, heights =>
    if n ≤ logFinal then .final else
      let la := logArity maxLogArity logFinal n heights
      have hla : la ≤ n := (logArity_le _ _ _ _).trans (Nat.sub_le _ _)
      match heights with
      | [] => .fold la hla false (plonky3 maxLogArity logFinal fuel (n - la) [])
      | m :: rest =>
        if m = n - la then
          .fold la hla true (plonky3 maxLogArity logFinal fuel (n - la) rest)
        else .fold la hla false (plonky3 maxLogArity logFinal fuel (n - la) (m :: rest))

/-- Heights fit below height `n`: strictly decreasing, all below `n` and at least `logFinal`. -/
def Fits (logFinal n : ℕ) (heights : List ℕ) : Prop :=
  heights.Pairwise (· > ·) ∧ ∀ m ∈ heights, logFinal ≤ m ∧ m < n

theorem fits_nil (logFinal n : ℕ) : Fits logFinal n [] :=
  ⟨List.Pairwise.nil, fun _ h ↦ absurd h List.not_mem_nil⟩

/-- The fold from a height above the final one, with fitting heights, is by at least one bit. -/
theorem one_le_logArity {maxLogArity logFinal n : ℕ} (ha : 0 < maxLogArity) (hn : logFinal < n)
    {heights : List ℕ} (hfit : Fits logFinal n heights) :
    1 ≤ logArity maxLogArity logFinal n heights := by
  unfold logArity
  have hhead : heights.headD logFinal < n := by
    cases heights with
    | nil => exact hn
    | cons m _ => exact (hfit.2 m List.mem_cons_self).2
  omega

/-- After a fold that does not reach the next height, the heights still fit. -/
theorem fits_cons_of_ne {logFinal n la m : ℕ} {rest : List ℕ} (hfit : Fits logFinal n (m :: rest))
    (hla : la ≤ n - m) (hm : ¬ m = n - la) : Fits logFinal (n - la) (m :: rest) := by
  refine ⟨hfit.1, fun m' hm' ↦ ⟨(hfit.2 m' hm').1, ?_⟩⟩
  have hm0 := hfit.2 m List.mem_cons_self
  rcases List.mem_cons.mp hm' with rfl | hm'
  · omega
  · have := List.rel_of_pairwise_cons hfit.1 hm'
    omega

/-- After the fold that reaches the next height, the rest fit. -/
theorem fits_of_eq {logFinal n la m : ℕ} {rest : List ℕ} (hfit : Fits logFinal n (m :: rest))
    (hm : m = n - la) : Fits logFinal (n - la) rest := by
  refine ⟨(List.pairwise_cons.mp hfit.1).2, fun m' hm' ↦
    ⟨(hfit.2 m' (List.mem_cons_of_mem _ hm')).1, ?_⟩⟩
  have := List.rel_of_pairwise_cons hfit.1 hm'
  omega

/-- The folds reach the final height exactly: the code before them has degree bound
`2 ^ (n - logFinal) d`. -/
theorem degree_plonky3 {maxLogArity logFinal : ℕ} (ha : 0 < maxLogArity) (d : ℕ) :
    ∀ (fuel n : ℕ) (heights : List ℕ), logFinal ≤ n → n - logFinal ≤ fuel →
      Fits logFinal n heights →
      (plonky3 maxLogArity logFinal fuel n heights).degree d = 2 ^ (n - logFinal) * d
  | 0, n, _, hn, hfuel, _ => by
    rw [plonky3, degree, show n - logFinal = 0 by omega, pow_zero, one_mul]
  | fuel + 1, n, heights, hn, hfuel, hfit => by
    by_cases hfin : n ≤ logFinal
    · rw [plonky3, ite_eq_left hfin, degree, show n - logFinal = 0 by omega, pow_zero, one_mul]
    have h1 := one_le_logArity ha (by omega) hfit
    have h2 := logArity_le maxLogArity logFinal n heights
    have hpow (la r : ℕ) (hla : 1 ≤ la) (hle : la ≤ n - logFinal)
        (hr : r = 2 ^ (n - la - logFinal) * d) : 2 ^ la * r = 2 ^ (n - logFinal) * d := by
      rw [hr, ← mul_assoc, ← pow_add]
      congr 2
      omega
    rw [plonky3, ite_eq_right hfin]
    match heights, hfit, h1, h2 with
    | [], _, h1, h2 =>
      exact hpow _ _ h1 h2 (degree_plonky3 ha d fuel _ [] (by omega) (by omega) (fits_nil _ _))
    | m :: rest, hfit, h1, h2 =>
      have h3 := logArity_le_cons maxLogArity logFinal n m rest
      by_cases hm : m = n - logArity maxLogArity logFinal n (m :: rest)
      · simp only [ite_eq_left hm, degree]
        exact hpow _ _ h1 h2 (degree_plonky3 ha d fuel _ rest (by omega) (by omega)
          (fits_of_eq hfit hm))
      · simp only [ite_eq_right hm, degree]
        exact hpow _ _ h1 h2 (degree_plonky3 ha d fuel _ _ (by omega) (by omega)
          (fits_cons_of_ne hfit h3 hm))

/-- Every fold of the schedule halves the domain at least once, for fitting heights. -/
theorem arityPos_plonky3 {maxLogArity logFinal : ℕ} (ha : 0 < maxLogArity) :
    ∀ (fuel n : ℕ) (heights : List ℕ), Fits logFinal n heights →
      (plonky3 maxLogArity logFinal fuel n heights).ArityPos
  | 0, _, _, _ => trivial
  | fuel + 1, n, heights, hfit => by
    by_cases hfin : n ≤ logFinal
    · rw [plonky3, ite_eq_left hfin]
      trivial
    have h1 := one_le_logArity ha (by omega) hfit
    rw [plonky3, ite_eq_right hfin]
    match heights, hfit, h1 with
    | [], _, h1 => exact ⟨h1, arityPos_plonky3 ha fuel _ [] (fits_nil _ _)⟩
    | m :: rest, hfit, h1 =>
      have h3 := logArity_le_cons maxLogArity logFinal n m rest
      by_cases hm : m = n - logArity maxLogArity logFinal n (m :: rest)
      · simp only [ite_eq_left hm]
        exact ⟨h1, arityPos_plonky3 ha fuel _ rest (fits_of_eq hfit hm)⟩
      · simp only [ite_eq_right hm]
        exact ⟨h1, arityPos_plonky3 ha fuel _ _ (fits_cons_of_ne hfit h3 hm)⟩

variable {K : Type} [Field K]

/-- Agreement of a word on a domain of an equal height. -/
theorem exists_agrees_cast (P : ∀ {m : ℕ}, SmoothCosetFftDomain m K → Prop)
    (inputs : (m : ℕ) → Fin (2 ^ m) → K) {m m' : ℕ} (h : m = m')
    (D : SmoothCosetFftDomain m' K) (hD : P D) (deg : ℕ) (ρ : ℝ)
    (hg : Agrees D deg ρ (inputs m')) :
    ∃ D' : SmoothCosetFftDomain m K, P D' ∧ Agrees D' deg ρ (inputs m) := by
  subst h
  exact ⟨D, hD, hg⟩

/-- Every input is injected: if the schedule's inputs agree with their codes, each input agrees
with its code, on a domain the folds reach from the first, which keeps any property `P` that
subdomains keep. -/
theorem agrees_of_inputsAgree {maxLogArity logFinal : ℕ} (ha : 0 < maxLogArity)
    (inputs : (m : ℕ) → Fin (2 ^ m) → K) (d : ℕ) (ρ : ℝ)
    (P : ∀ {m : ℕ}, SmoothCosetFftDomain m K → Prop)
    (hP : ∀ {m : ℕ} (D : SmoothCosetFftDomain m K) (k : ℕ), P D → P (D.subdomain k)) :
    ∀ (fuel n : ℕ) (ω : SmoothCosetFftDomain n K) (heights : List ℕ),
      logFinal ≤ n → n - logFinal ≤ fuel → Fits logFinal n heights → P ω →
      (plonky3 maxLogArity logFinal fuel n heights).InputsAgree inputs d ρ ω →
      ∀ m ∈ heights, ∃ D : SmoothCosetFftDomain m K, P D ∧
        Agrees D (2 ^ (m - logFinal) * d) ρ (inputs m)
  | 0, n, _, heights, hn, hfuel, hfit, _, _, m, hm => by
    have := hfit.2 m hm
    omega
  | fuel + 1, n, ω, heights, hn, hfuel, hfit, hω, hin, m', hm' => by
    have hx := hfit.2 m' hm'
    have hfin : ¬ n ≤ logFinal := by omega
    have h1 := one_le_logArity ha (by omega) hfit
    have h2 := logArity_le maxLogArity logFinal n heights
    rw [plonky3, ite_eq_right hfin] at hin
    match heights, hfit, h1, h2, hin, hm' with
    | m :: rest, hfit, h1, h2, hin, hm' =>
      have h3 := logArity_le_cons maxLogArity logFinal n m rest
      by_cases hm : m = n - logArity maxLogArity logFinal n (m :: rest)
      · simp only [ite_eq_left hm, InputsAgree] at hin
        rcases List.mem_cons.mp hm' with rfl | hm'
        · refine exists_agrees_cast P inputs hm _ (hP ω _ hω) _ ρ ?_
          have hdeg := degree_plonky3 ha d fuel _ rest (by omega) (by omega)
            (fits_of_eq hfit hm)
          rw [hdeg, show n - logArity maxLogArity logFinal n (m' :: rest) - logFinal =
            m' - logFinal by omega] at hin
          exact hin.1
        · exact agrees_of_inputsAgree ha inputs d ρ P hP fuel _ _ rest (by omega) (by omega)
            (fits_of_eq hfit hm) (hP ω _ hω) hin.2 m' hm'
      · simp only [ite_eq_right hm, InputsAgree] at hin
        exact agrees_of_inputsAgree ha inputs d ρ P hP fuel _ _ _ (by omega) (by omega)
          (fits_cons_of_ne hfit h3 hm) (hP ω _ hω) hin m' hm'

/-- Every input is injected where it is in its code: if each input is a codeword of its code on
every domain of its height with a property `P` that subdomains keep, and `ω` has it, the
schedule's inputs are in their codes. -/
theorem inputsInCode_plonky3 {maxLogArity logFinal : ℕ} (ha : 0 < maxLogArity)
    (inputs : (m : ℕ) → Fin (2 ^ m) → K) (d : ℕ)
    (P : ∀ {m : ℕ}, SmoothCosetFftDomain m K → Prop)
    (hP : ∀ {m : ℕ} (D : SmoothCosetFftDomain m K) (k : ℕ), P D → P (D.subdomain k)) :
    ∀ (fuel n : ℕ) (ω : SmoothCosetFftDomain n K) (heights : List ℕ),
      logFinal ≤ n → n - logFinal ≤ fuel → Fits logFinal n heights → P ω →
      (∀ m ∈ heights, ∀ D : SmoothCosetFftDomain m K, P D →
        inputs m ∈ ReedSolomon.code (D : Fin (2 ^ m) ↪ K) (2 ^ (m - logFinal) * d)) →
      (plonky3 maxLogArity logFinal fuel n heights).InputsInCode inputs d ω
  | 0, _, _, _, _, _, _, _, _ => trivial
  | fuel + 1, n, ω, heights, hn, hfuel, hfit, hω, hin => by
    by_cases hfin : n ≤ logFinal
    · rw [plonky3, ite_eq_left hfin]
      trivial
    have h1 := one_le_logArity ha (by omega) hfit
    have h2 := logArity_le maxLogArity logFinal n heights
    rw [plonky3, ite_eq_right hfin]
    match heights, hfit, h1, h2, hin with
    | [], _, _, h2, _ =>
      exact inputsInCode_plonky3 ha inputs d P hP fuel _ _ [] (by omega) (by omega)
        (fits_nil _ _) (hP ω _ hω) fun _ hm ↦ absurd hm List.not_mem_nil
    | m :: rest, hfit, h1, h2, hin =>
      have h3 := logArity_le_cons maxLogArity logFinal n m rest
      by_cases hm : m = n - logArity maxLogArity logFinal n (m :: rest)
      · simp only [ite_eq_left hm, InputsInCode]
        have hdeg := degree_plonky3 ha d fuel _ rest (by omega) (by omega) (fits_of_eq hfit hm)
        refine ⟨?_, inputsInCode_plonky3 ha inputs d P hP fuel _ _ rest (by omega) (by omega)
          (fits_of_eq hfit hm) (hP ω _ hω) fun m' hm' ↦ hin m' (List.mem_cons_of_mem _ hm')⟩
        have key : ∀ m' : ℕ, m = m' → ∀ D : SmoothCosetFftDomain m' K, P D →
            inputs m' ∈ ReedSolomon.code (D : Fin (2 ^ m') ↪ K) (2 ^ (m' - logFinal) * d) := by
          intro m' h
          subst h
          exact hin m List.mem_cons_self
        rw [hdeg]
        exact key _ hm _ (hP ω _ hω)
      · simp only [ite_eq_right hm, InputsInCode]
        exact inputsInCode_plonky3 ha inputs d P hP fuel _ _ _ (by omega) (by omega)
          (fits_cons_of_ne hfit h3 hm) (hP ω _ hω) hin

end Schedule

end Fri.Interaction
