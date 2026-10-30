/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.ProofSystem.Fri.Interaction.Inject

/-!
# FRI folding schedules

A `Schedule n` lists FRI's folds from a domain of `2 ^ n` points: each fold is by `2 ^ k` and may
inject the input word of the folded domain's height, as Plonky3 does for inputs of several
heights. The schedule fixes the shape of the interaction, the degree bound of each layer
(`degree`: a fold by `2 ^ k` divides it by `2 ^ k`), and the soundness error: each fold's lossy
MCA error (`roundError`, summed in `foldError`) and the query term, minimized over the proximity
loss (`error`).

The inputs are words `inputs m` on the domains of `2 ^ m` points, indexed by their log height.
`InputsAgree` states that every injected input is close to its code on the domain where the folds
reach it.
-/

@[expose] public section

namespace Fri.Interaction

open Domain ReedSolomon CoreDefinitions
open scoped NNReal

/-- FRI's folds from a domain of `2 ^ n` points: each folds by `2 ^ k` and injects the input of
the folded domain's height if `inject` is set. -/
inductive Schedule : ℕ → Type
  | final {n : ℕ} : Schedule n
  | fold {n : ℕ} (k : ℕ) (hk : k ≤ n) (inject : Bool) (rest : Schedule (n - k)) : Schedule n

namespace Schedule

/-- The number of folds. -/
def numFolds : {n : ℕ} → Schedule n → ℕ
  | _, .final => 0
  | _, .fold _ _ _ rest => rest.numFolds + 1

/-- The degree bound of the code before the folds, for a final degree bound `d`. -/
def degree (d : ℕ) : {n : ℕ} → Schedule n → ℕ
  | _, .final => d
  | _, .fold k _ _ rest => 2 ^ k * rest.degree d

theorem degree_pos {d : ℕ} (hd : 0 < d) : ∀ {n : ℕ} (s : Schedule n), 0 < s.degree d
  | _, .final => hd
  | _, .fold _ _ _ rest => Nat.mul_pos (Nat.two_pow_pos _) (degree_pos hd rest)

variable {K : Type} [Field K]

/-- Every injected input agrees with a codeword of its code on a set of at least `ρ` of the
domain where the folds reach it. -/
def InputsAgree (inputs : (m : ℕ) → Fin (2 ^ m) → K) (d : ℕ) (ρ : ℝ) :
    {n : ℕ} → SmoothCosetFftDomain n K → Schedule n → Prop
  | _, _, .final => True
  | _, ω, .fold k _ false rest => rest.InputsAgree inputs d ρ (ω.subdomain k)
  | n, ω, .fold k _ true rest =>
      Agrees (ω.subdomain k) (rest.degree d) ρ (inputs (n - k)) ∧
        rest.InputsAgree inputs d ρ (ω.subdomain k)

/-- Agreement at a density gives agreement at every smaller density. -/
theorem InputsAgree.mono {inputs : (m : ℕ) → Fin (2 ^ m) → K} {d : ℕ} {ρ ρ' : ℝ}
    (h : ρ' ≤ ρ) : ∀ {n : ℕ} {ω : SmoothCosetFftDomain n K} {s : Schedule n},
      s.InputsAgree inputs d ρ ω → s.InputsAgree inputs d ρ' ω
  | _, _, .final, _ => trivial
  | _, _, .fold _ _ false rest, hs => InputsAgree.mono h (s := rest) hs
  | _, _, .fold _ _ true rest, hs => ⟨hs.1.mono h, InputsAgree.mono h (s := rest) hs.2⟩

variable [Fintype K] [DecidableEq K] [SampleableType K]

/-- The error of a fold by `2 ^ k` onto the code `code (ω.subdomain k) d'`: the lossy MCA error of
the powers of the challenge over the fold's `2 ^ k` coefficient words, and the injected input if
any. -/
noncomputable def roundError {n : ℕ} (ω : SmoothCosetFftDomain n K) (k d' : ℕ) (θ loss : ℝ) :
    Bool → ENNReal
  | false => lossyMcaError (univariatePowersGenerator K (2 ^ k - 1))
      (code (ω.subdomain k : Fin (2 ^ (n - k)) ↪ K) d') θ loss
  | true => lossyMcaError (univariatePowersGenerator K (2 ^ k))
      (code (ω.subdomain k : Fin (2 ^ (n - k)) ↪ K) d') θ loss

/-- The folds' errors at proximity `θ` and loss `loss`. -/
noncomputable def foldError (d : ℕ) (θ loss : ℝ) :
    {n : ℕ} → SmoothCosetFftDomain n K → Schedule n → ENNReal
  | _, _, .final => 0
  | _, ω, .fold k _ inject rest =>
      roundError ω k (rest.degree d) θ loss inject + rest.foldError d θ loss (ω.subdomain k)

end Schedule

/-- FRI's soundness error at proximity `δ` with `t` queries, at the best proximity loss: the folds'
lossy MCA errors and `(1 - δ + m · loss) ^ t` for the queries, `m` folds. -/
noncomputable def error {K : Type} [Field K] [Fintype K] [DecidableEq K] [SampleableType K]
    {n : ℕ} (ω : SmoothCosetFftDomain n K) (s : Schedule n) (d t : ℕ) (δ : ℝ) : ENNReal :=
  ⨅ loss : ℝ≥0, s.foldError d δ loss ω + ENNReal.ofReal (1 - δ + s.numFolds * loss) ^ t

end Fri.Interaction
