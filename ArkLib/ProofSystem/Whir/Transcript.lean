/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.ProofSystem.Whir.Extractor

/-!
# WHIR transcript and terminal-state identities

Sequential extractor folds coincide with the transcript parser's full challenge vector.
Closing knowledge includes the residual weight in its final scalar equation.
-/

@[expose] public section

open Interaction Interaction.Oracle Interaction.Oracle.Security

namespace Whir

/-- Closing terminal knowledge is exactly its checks and the weighted final scalar equation. -/
theorem closing_terminal_iff {E : Type} [CommRing E] [DecidableEq E]
    (count : ℕ) (candidate : Table E count) (claim : Claim E count) (active : Bool)
    (path : (scalarRounds E count .done).tree.ExecutionPath) :
    (∃ witness, ((closingExtractor count candidate claim active).terminalState path).holds witness)
      ↔
      active = true ∧ (readRounds .done count claim.value path).2.2.1 = true ∧
        mle claim.weight (readRounds .done count claim.value path).2.1 *
          mle candidate (readRounds .done count claim.value path).2.1 =
            (readRounds .done count claim.value path).1 := by
  induction count generalizing active with
  | zero =>
      change (∃ _ : PUnit, active = true ∧ ∀ c ∈ [claim], c.Holds candidate) ↔ _
      simp only [readRounds, List.mem_singleton, forall_eq, exists_const, Claim.Holds,
        mle, eqWeight, Fin.prod_univ_zero, one_mul, Fintype.sum_unique, true_and]
  | succ count ih =>
      let q : Quadratic E := path.1
      let r : E := path.2.1
      change (∃ witness, ((closingExtractor count (foldMessageOne (vars := 0) candidate r)
        ⟨foldMessageOne (vars := 0) claim.weight r, evalQuadratic claim.value q r⟩
        (active && (Sumcheck.compressedOps 1).accept claim.value q)).terminalState
          path.2.2).holds witness) ↔ _
      rw [ih]
      simp only [readRounds, Sumcheck.compressedOps, Bool.and_true, Bool.true_and]
      rw [mle_foldMessageOne, mle_foldMessageOne]

/-- The last-level suffix reaches the closing extractor on its fixed final plaintext. -/
theorem lastExtractor_terminalState {K E : Type} [Semiring K] [CommRing E]
    [DecidableEq E] [Fintype E] {tail : ℕ} (lanes queries : ℕ) (enc : Encoding K tail)
    (ι : K →+* E) (sec : LevelSecurity) (word : Word E 0 (2 ^ (tail + enc.rate)))
    (claim : Claim E (0 + tail)) (active : Bool)
    (path : (transition E (.last lanes tail enc queries)).tree.ExecutionPath) :
    (lastExtractor lanes queries enc ι sec word claim active).terminalState path =
      (closingExtractor tail path.1
        (batch (⟨castTable (Nat.zero_add tail) claim.weight, claim.value⟩ ::
          List.ofFn (fun q : Fin queries =>
            ⟨fun u => ι (enc.weight (path.2.1 q) u), word (path.2.1 q) Fin.elim0⟩))
          path.2.2.1) active).terminalState path.2.2.2 := by
  rfl

/-- The boundary suffix reaches the supplied next-level extractor with all boundary claims. -/
theorem boundaryExtractor_terminalState {K E : Type} [Semiring K] [CommRing E]
    [DecidableEq E] [Fintype E] {tail : ℕ} (lanes queries : ℕ) (enc : Encoding K tail)
    (ι : K →+* E) (sec : LevelSecurity) (rest : Schedule K tail)
    (nextSec : SecurityParameters rest)
    (suffix : (word : oracleMessage E rest) → (claims : List (Claim E tail)) →
      (active : Bool) → RoundExtractor (opening E rest).tree
        (levelState ι rest nextSec word claims active))
    (word : Word E 0 (2 ^ (tail + enc.rate))) (claim : Claim E (0 + tail)) (active : Bool)
    (path : (transition E (.more lanes enc queries rest)).tree.ExecutionPath) :
    (boundaryExtractor lanes queries enc ι sec rest nextSec suffix word claim active).terminalState
      path =
      (suffix path.1
        (nextClaims enc ι ⟨castTable (Nat.zero_add tail) claim.weight, claim.value⟩
          path.2.1 path.2.2.1 path.2.2.2.1 (fun x => word x Fin.elim0)) active).terminalState
          path.2.2.2.2 := by
  rfl

/-- Terminal state after a fold block is the supplied suffix on its fully folded word and claim. -/
theorem foldExtractor_terminalState {K E : Type} [Semiring K] [CommRing E] [DecidableEq E]
    [Fintype E] {vars : ℕ} (enc : Encoding K vars) (ι : K →+* E) (γ : ℝ)
    {rest : Protocol}
    (finish : (word : Word E 0 (2 ^ (vars + enc.rate))) →
      (claim : Claim E (0 + vars)) → (active : Bool) →
      RoundExtractor rest.tree (candidateState enc ι γ word [claim] active))
    (lanes : ℕ) (word : Word E lanes (2 ^ (vars + enc.rate)))
    (claim : Claim E (lanes + vars)) (active : Bool)
    (path : (scalarRounds E lanes rest).tree.ExecutionPath) :
    (foldExtractor enc ι γ finish lanes word claim active).terminalState path =
      (finish
        (fun x _ => foldWord word (readRounds rest lanes claim.value path).2.1 x)
        ⟨castTable (Nat.zero_add vars).symm
          (restrict claim.weight (readRounds rest lanes claim.value path).2.1),
          (readRounds rest lanes claim.value path).1⟩
        (active && (readRounds rest lanes claim.value path).2.2.1)).terminalState
          (readRounds rest lanes claim.value path).2.2.2 := by
  induction lanes generalizing active with
  | zero =>
      change (finish word claim active).terminalState path =
        (finish (fun x (_ : Cube 0) => foldWord word Fin.elim0 x)
          ⟨castTable (Nat.zero_add vars).symm (restrict claim.weight Fin.elim0), claim.value⟩
          (active && true)).terminalState path
      rw [foldWord_zero, restrict_zero, castTable_inverse, Bool.and_true]
      have hword : (fun x (_ : Cube 0) => word x Fin.elim0) = word := by
        funext x u
        congr 1
        exact Subsingleton.elim _ _
      rw [hword]
  | succ lanes ih =>
      let q : Quadratic E := path.1
      let r : E := path.2.1
      change (foldExtractor enc ι γ finish lanes (foldRowsOne word r)
        ⟨foldMessageOne claim.weight r, evalQuadratic claim.value q r⟩
        (active && (Sumcheck.compressedOps 1).accept claim.value q)).terminalState
          path.2.2 = _
      rw [ih]
      simp only [readRounds]
      rw [foldWord_cons word r _, restrict_foldMessageOne claim.weight r _, Bool.and_assoc]

end Whir
