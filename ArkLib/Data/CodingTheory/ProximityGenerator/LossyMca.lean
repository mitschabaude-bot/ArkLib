/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.Data.CodingTheory.ProximityGenerator.Basic

/-!
# Mutual correlated agreement with loss

`IsMCA` asks that every large agreement set `T` of a generated word extend to the generating
words on that same `T`. Lossy MCA (`IsLossyMCA`) allows the extension to drop up to `loss · n`
points of `T`: outside the error event, for every agreement set `T` of the generated word with
`|T| ≥ (1 - δ) n`, all generating words agree with codewords on a common subset `T' ⊆ T` with
`|T \ T'| ≤ loss · n`. At `loss = 0` this is `IsMCA` (`isLossyMCA_zero_iff`).

The loss is what lets the error be independent of the block length `n` in the unique-decoding
regime: correlated agreement there holds with `O(1)` exceptional seeds up to a proximity loss
([BCHKS25, Theorem 1.3]), while lossless MCA needs `Ω(n)`.

## References

* [Ben-Sasson, E., Carmon, D., Haböck, U., Kopparty, S., Saraf, S., *On Proximity Gaps for
  Reed–Solomon Codes*][BCHKS25]
-/

@[expose] public section

namespace CoreDefinitions

open NNReal ENNReal unitInterval LinearCode
open scoped ProbabilityTheory

variable {ι : Type} [Fintype ι]
         {F : Type} [Field F]
         {ℓ : Type} [Fintype ℓ]

/-- The lossy MCA bad event at seed `x`: the generated word agrees with the code on a set `T`
of at least `(1 - δ) n` points, but on no subset of `T` missing at most `loss · n` points do all
the generating words agree with the code. -/
def IsLossyMCA {S : Type} [Nonempty S] [Fintype S] {A : Type} [AddCommMonoid A] [Module F A]
    (G : Generator S ℓ F) (MC : ModuleCode ι F A)
    (x : S) (U : ℓ → (ι → A)) (δ loss : ℝ) : Prop :=
  let v : ι → A := fun k => ∑ j, G x j • U j k
  ∃ T : Finset ι, (T.card : ℝ) ≥ (Fintype.card ι) * (1 - δ) ∧
    projectedWord v T ∈ projectedCodeSubmod MC T ∧
    ∀ T' ⊆ T, (T'.card : ℝ) ≥ T.card - loss * Fintype.card ι →
      ∃ j : ℓ, projectedWord (U j) T' ∉ projectedCodeSubmod MC T'

/-- The lossy MCA error: the largest probability of the lossy MCA bad event over the generating
words. -/
noncomputable def lossyMcaError {S : Type} [Nonempty S] [Fintype S] [SampleableType S]
    {A : Type} [AddCommMonoid A] [Module F A]
    (G : Generator S ℓ F) (MC : ModuleCode ι F A) (δ loss : ℝ) : ENNReal :=
  ⨆ U : ℓ → (ι → A), Pr{let x ←$ᵗ S}[IsLossyMCA G MC x U δ loss]

end CoreDefinitions
