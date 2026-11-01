/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.ProofSystem.Fri.Interaction.RoundKnowledge

/-!
# FRI's final polynomial and query phase: round-by-round knowledge

After the folds, the prover sends the final polynomial `c`; the top positions consistent so far
at which the verifier's word at the last layer agrees with `c` form the final consistent set
(`finalConsistent`). The
knowledge state after `c` (`finalState`) asks for a subset of it of at least
`(1 - δ + m · loss) 2 ^ top` positions, `m` folds. The final message maps such a set `S` back to
the witness `(S, c)` at the last layer, `c` being a codeword of the final code
(`evalCoeffs_mem_code`), so it cannot create knowledge (`finalMessageCertificate`).

The query phase samples `t` top positions. Its terminal state (`acceptedState`) holds for the
final consistent set when every query lands in it, which is when the verifier accepts. A query
challenge is bad only if every position lands in a final consistent set of density below
`1 - δ + m · loss`, which has probability at most `(1 - δ + m · loss) ^ t`
(`queryCertificate`). With the final message before it, this is `finalCertificate`.
-/

@[expose] public section

open Interaction Interaction.Oracle Interaction.Oracle.Security OracleComp OracleSpec Domain
open ReedSolomon
open scoped ProbabilityTheory

namespace Fri.Interaction

variable {K : Type} [Field K]

/-- The evaluations of `d` coefficients form a codeword of the code of degree `d`. -/
theorem evalCoeffs_mem_code {n d : ℕ} (ω : SmoothCosetFftDomain n K) (c : Fin d → K) :
    (fun y => evalCoeffs c (ω y)) ∈ code (ω : Fin (2 ^ n) ↪ K) d :=
  mem_code_of_polynomial_of_degree_lt_of_eval _ (Polynomial.degree_sum_fin_lt c) fun y => by
    simp [evalCoeffs, Polynomial.eval_finsetSum]

variable (top t : ℕ) (δ loss : ℝ)

/-- The final message: the final polynomial's `d` coefficients. -/
def finalMessage (K : Type) (d : ℕ) : Protocol :=
  .public .sender (Fin d → K) fun _ => .done

/-- The top positions consistent so far at which the verifier's word `f` at the last layer agrees
with the final polynomial `c`. -/
def finalConsistent [DecidableEq K] {n d : ℕ} (ω : SmoothCosetFftDomain n K) (f : Word K n)
    (c : Fin d → K) (C : Finset (Fin (2 ^ top))) : Finset (Fin (2 ^ top)) :=
  C.filter fun x => f (proj n x) = evalCoeffs c (ω (proj n x))

/-- The knowledge state after the final polynomial, `j` folds done: a subset of the final
consistent set `C` of at least `1 - δ + j · loss` of the top domain. -/
def finalState (j : ℕ) (C : Finset (Fin (2 ^ top))) : KnowledgeState where
  Witness := Finset (Fin (2 ^ top))
  holds S := S ⊆ C ∧ threshold δ loss j * 2 ^ top ≤ S.card

/-- The terminal state after the queries `xs`: the final consistent set, holding every query. -/
def acceptedState (C : Finset (Fin (2 ^ top))) (xs : Fin t → Fin (2 ^ top)) :
    KnowledgeState where
  Witness := Finset (Fin (2 ^ top))
  holds S := S = C ∧ ∀ i, xs i ∈ S

/-- The query phase's witness maps: the terminal witness is mapped back unchanged. -/
def queryExtractor (j : ℕ) (C : Finset (Fin (2 ^ top))) :
    RoundExtractor (queryPhase top t).tree (finalState top δ loss j C) :=
  fun xs => ⟨acceptedState top t C xs, id, PUnit.unit⟩

variable {top t δ loss}

/-- A bad query challenge lands every position in a final consistent set of density below the
threshold. -/
theorem badChallenge_query (j : ℕ) (C : Finset (Fin (2 ^ top))) (xs : Fin t → Fin (2 ^ top))
    (hbad : (queryExtractor top t δ loss j C).badChallenge xs) :
    (∀ i, xs i ∈ C) ∧ (C.card : ℝ) < threshold δ loss j * 2 ^ top := by
  obtain ⟨S, hnot, hS, hxs⟩ := hbad
  change Finset (Fin (2 ^ top)) at S
  change S = C at hS
  subst hS
  exact ⟨hxs, lt_of_not_ge fun h => hnot ⟨subset_rfl, h⟩⟩

/-- **The query bound.** Every query position lands in a set of density below `ρ` with
probability at most `ρ ^ t`. -/
theorem prob_badChallenge_query_le (j : ℕ) (C : Finset (Fin (2 ^ top))) :
    Pr{let xs ←$ᵗ (Fin t → Fin (2 ^ top))}[(queryExtractor top t δ loss j C).badChallenge xs] ≤
      ENNReal.ofReal (threshold δ loss j) ^ t := by
  classical
  by_cases hC : (C.card : ℝ) < threshold δ loss j * 2 ^ top
  · refine (prEvent_mono _ _ _ fun xs hbad => (badChallenge_query j C xs hbad).1).trans ?_
    rw [Probability.prob_uniform_pi_mem_finset_eq]
    refine pow_le_pow_left' ?_ t
    have hpos : (0 : ℝ) < 2 ^ top := by positivity
    rw [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, ← ENNReal.ofReal_natCast,
      show (2 : ENNReal) ^ top = ENNReal.ofReal (2 ^ top) by
        rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat],
      ← ENNReal.ofReal_div_of_pos hpos]
    exact ENNReal.ofReal_le_ofReal ((div_le_iff₀ hpos).mpr hC.le)
  · refine (prEvent_mono _ _ _ fun xs hbad => hC (badChallenge_query j C xs hbad).2).trans ?_
    simp

variable (top t δ loss)

/-- **The query phase's knowledge certificate.** The query positions are uniform, and they are
bad with probability at most `(1 - δ + j · loss) ^ t`. -/
noncomputable def queryCertificate (j : ℕ) (C : Finset (Fin (2 ^ top))) :
    KnowledgeCertificate (queryPhase top t).tree (queryPhase top t).roles
      (finalState top δ loss j C) where
  extractor := queryExtractor top t δ loss j C
  challenges := ⟨($ᵗ (Fin t → Fin (2 ^ top)), ENNReal.ofReal (threshold δ loss j) ^ t),
    fun _ => PUnit.unit⟩
  prover_preserving := And.intro (fun _ h => nomatch h) fun _ => trivial
  local_bound := by
    refine ⟨?_, fun _ => trivial⟩
    rw [_root_.RoundByRound.GameFamily.isBounded_iff]
    exact fun _ _ => prob_badChallenge_query_le j C

variable [DecidableEq K] (d : ℕ) (inputs : (m : ℕ) → Fin (2 ^ m) → K)

/-- The final message's witness maps: a final set `S` maps back to `S` and the final
polynomial's evaluations. -/
def finalMessageExtractor {n : ℕ} (ω : SmoothCosetFftDomain n K) (j : ℕ) (f : Word K n)
    (C : Finset (Fin (2 ^ top))) :
    RoundExtractor (finalMessage K d).tree (levelState top d inputs δ loss ω .final j f C) :=
  fun c => ⟨finalState top δ loss j (finalConsistent top ω f c C),
    fun S => (S, fun y => evalCoeffs c (ω y)), PUnit.unit⟩

/-- **The final message's knowledge certificate.** It has no challenge; the final polynomial
cannot create knowledge. -/
noncomputable def finalMessageCertificate {n : ℕ} (ω : SmoothCosetFftDomain n K) (j : ℕ)
    (f : Word K n) (C : Finset (Fin (2 ^ top))) :
    KnowledgeCertificate (finalMessage K d).tree (finalMessage K d).roles
      (levelState top d inputs δ loss ω .final j f C) where
  extractor := finalMessageExtractor top δ loss d inputs ω j f C
  challenges := ⟨PUnit.unit, fun _ => PUnit.unit⟩
  prover_preserving := by
    refine And.intro (fun c _ S hS => ?_) fun _ => trivial
    obtain ⟨hSC, hcard⟩ := hS
    exact ⟨evalCoeffs_mem_code ω c, hSC.trans (Finset.filter_subset _ _),
      fun x hx => ((Finset.mem_filter.mp (hSC hx)).2).symm, hcard, trivial⟩
  local_bound := fun _ => trivial

/-- **The last round's knowledge certificate**: the final message, then the query phase. Its
only error is the query phase's, `(1 - δ + j · loss) ^ t`. -/
noncomputable def finalCertificate {n : ℕ} (ω : SmoothCosetFftDomain n K) (j : ℕ)
    (f : Word K n) (C : Finset (Fin (2 ^ top))) :
    KnowledgeCertificate (protocol K top d t (.final (n := n))).tree
      (protocol K top d t (.final (n := n))).roles
      (levelState top d inputs δ loss ω .final j f C) :=
  (finalMessageCertificate top δ loss d inputs ω j f C).append (fun _ => (queryPhase top t).tree)
    (fun _ => (queryPhase top t).roles)
    fun path => queryCertificate top t δ loss j (finalConsistent top ω f path.1 C)

end Fri.Interaction
