/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.ProofSystem.Whir.Transcript

/-!
# Acceptance supplies WHIR terminal knowledge

The extractor's accumulated checks and weighted final scalar relation coincide with the concrete
transcript predicate, independently of the initial witness-selection map.
-/

@[expose] public section

open Interaction Interaction.Oracle Interaction.Oracle.Security

namespace Whir

/-- Terminal knowledge of a level is exactly its initial activity and transcript acceptance. -/
theorem level_terminal_iff {K E : Type} [Semiring K] [CommRing E]
    [DecidableEq E] [Fintype E] (ι : K →+* E) {n : ℕ} (s : Schedule K n)
    (sec : SecurityParameters s) (word : oracleMessage E s) (claims : List (Claim E n))
    (active : Bool) (path : (opening E s).tree.ExecutionPath) :
    (∃ witness, ((levelExtractor ι s sec word claims active).terminalState path).holds witness) ↔
      active = true ∧ accepts ι s word claims path = true := by
  induction s generalizing active with
  | last lanes tail enc queries =>
      unfold accepts
      change LevelSecurity at sec
      change Word E lanes (2 ^ (tail + enc.rate)) at word
      change ((_ : E) × (scalarRounds E lanes
        (transition E (.last lanes tail enc queries))).tree.ExecutionPath) at path
      change (∃ witness, ((foldExtractor enc ι (radius enc sec)
        (lastExtractor lanes queries enc ι sec) lanes word (batch claims path.1)
          active).terminalState path.2).holds witness) ↔ _
      rw [foldExtractor_terminalState]
      rw [lastExtractor_terminalState]
      let round : E × (Fin lanes → E) × Bool ×
          ((_ : Table E tail) × (_ : Fin queries → enc.Columns) ×
            (_ : E) × (scalarRounds E tail .done).tree.ExecutionPath) :=
        readRounds (transition E (.last lanes tail enc queries)) lanes
          (batch claims path.1).value path.2
      let residual : Claim E tail :=
        ⟨restrict (batch claims path.1).weight round.2.1, round.1⟩
      let sampled : List (Claim E tail) := List.ofFn (fun q : Fin queries =>
        ⟨fun u => ι (enc.weight (round.2.2.2.2.1 q) u),
          foldWord word round.2.1 (round.2.2.2.2.1 q)⟩)
      let lifted : Claim E tail :=
        ⟨castTable (Nat.zero_add tail)
          (castTable (Nat.zero_add tail).symm residual.weight), residual.value⟩
      let finalBatch := batch (residual :: sampled) round.2.2.2.2.2.1
      let closing := readRounds .done tail finalBatch.value round.2.2.2.2.2.2
      change (∃ witness, ((closingExtractor tail round.2.2.2.1
        (batch (lifted :: sampled) round.2.2.2.2.2.1)
        (active && round.2.2.1)).terminalState round.2.2.2.2.2.2).holds witness) ↔
          active = true ∧ (round.2.2.1 && closing.2.2.1 &&
            decide (mle finalBatch.weight closing.2.1 *
              mle round.2.2.2.1 closing.2.1 = closing.1)) = true
      have transported : lifted = residual := by
        dsimp only [lifted]
        rw [castTable_inverse (Nat.zero_add tail).symm]
      rw [transported, closing_terminal_iff]
      simp only [Bool.and_eq_true_iff, decide_eq_true_eq]
      tauto
  | more lanes enc queries rest ih =>
      unfold accepts
      change LevelSecurity × SecurityParameters rest at sec
      change Word E lanes (2 ^ (_ + enc.rate)) at word
      change ((_ : E) × (scalarRounds E lanes
        (transition E (.more lanes enc queries rest))).tree.ExecutionPath) at path
      change (∃ witness, ((foldExtractor enc ι (radius enc sec.1)
        (boundaryExtractor lanes queries enc ι sec.1 rest sec.2 (levelExtractor ι rest sec.2))
        lanes word (batch claims path.1) active).terminalState path.2).holds witness) ↔ _
      rw [foldExtractor_terminalState]
      rw [boundaryExtractor_terminalState]
      let round : E × (Fin lanes → E) × Bool ×
          ((_ : oracleMessage E rest) × (_ : Fin _ → E) × (_ : E) ×
            (_ : Fin queries → enc.Columns) × (opening E rest).tree.ExecutionPath) :=
        readRounds (transition E (.more lanes enc queries rest)) lanes
          (batch claims path.1).value path.2
      let residual := (⟨restrict (batch claims path.1).weight round.2.1, round.1⟩ : Claim E _)
      let lifted : Claim E _ :=
        ⟨castTable (Nat.zero_add _) (castTable (Nat.zero_add _).symm residual.weight),
          residual.value⟩
      change (∃ witness, ((levelExtractor ι rest sec.2 round.2.2.2.1
        (nextClaims enc ι lifted round.2.2.2.2.1 round.2.2.2.2.2.1 round.2.2.2.2.2.2.1
          (foldWord word round.2.1)) (active && round.2.2.1)).terminalState
            round.2.2.2.2.2.2.2).holds witness) ↔
        active = true ∧ (round.2.2.1 && accepts ι rest round.2.2.2.1
          (nextClaims enc ι residual round.2.2.2.2.1 round.2.2.2.2.2.1 round.2.2.2.2.2.2.1
            (foldWord word round.2.1)) round.2.2.2.2.2.2.2) = true
      have transported : lifted = residual := by
        dsimp only [lifted]
        rw [castTable_inverse (Nat.zero_add _).symm]
      rw [transported, ih]
      simp only [Bool.and_eq_true_iff]
      tauto

/-- Replacing the initial backward map does not change the terminal state. -/
theorem openingExtractor_terminalState {K E : Type} [Semiring K] [CommRing E]
    [DecidableEq K] [DecidableEq E] [Fintype E] (ι : K →+* E) {n : ℕ}
    (s : Schedule K n) (sec : SecurityParameters s) (word : oracleMessage K s)
    (claims : List (Claim E n)) (decoder : InitialDecoder s)
    (path : (opening E s).tree.ExecutionPath) :
    (openingExtractor ι s sec word claims decoder).terminalState path =
      (levelExtractor ι s sec (fun x u => ι (word x u)) claims true).terminalState path := by
  cases s <;> rfl

end Whir
