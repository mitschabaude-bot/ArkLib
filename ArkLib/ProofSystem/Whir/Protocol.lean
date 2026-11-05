/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.ProofSystem.Whir.Basic
public import ArkLib.Interaction.Oracle.PublicCoin

/-!
# The Annex B WHIR oracle protocol

The initial oracle is base-field-valued and has no OOD challenge. Each later commitment is
followed by an OOD point, its answer, and queries to the preceding oracle. The final table is
sent before its queries, final batching challenge, and closing sumcheck. `accepts` is the
concrete transcript predicate; it reads oracle words only at the sampled columns.

The mathematical wire uses all three quadratic coefficients. The compressed two-coefficient
wire, field codecs, Merkle authentication, and a `Verifier.Strategy` refinement are separate
obligations. Failed checks are accumulated in the acceptance predicate without changing the
public-coin tree or sampling conditional challenges.
-/

@[expose] public section

open Interaction Interaction.Oracle

namespace Whir

/-- A nonempty sequence of encoded levels followed by a plaintext table. -/
inductive Schedule (K : Type) : ℕ → Type
  /-- The last encoded level folds to `tail` plaintext variables. -/
  | last (lanes tail : ℕ) (encoding : Encoding K tail) (queries : ℕ) :
      Schedule K (lanes + tail)
  /-- An encoded level folds to the variables of the following encoded level. -/
  | more {tail : ℕ} (lanes : ℕ) (encoding : Encoding K tail) (queries : ℕ)
      (rest : Schedule K tail) : Schedule K (lanes + tail)

/-- Sumcheck's prover messages alternate with fresh public challenges. -/
def scalarRounds (E : Type) : ℕ → Protocol → Protocol
  | 0, rest => rest
  | count + 1, rest => .public .sender (Quadratic E) fun _ =>
      .public .receiver E fun _ => scalarRounds E count rest

/-- The row count exponent of the head encoded level. -/
def Schedule.lanes {K : Type} {n : ℕ} : Schedule K n → ℕ
  | .last lanes _ _ _ => lanes
  | .more lanes _ _ _ => lanes

/-- The number of columns of the head encoded level. -/
def Schedule.columns {K : Type} {n : ℕ} : Schedule K n → ℕ
  | .last _ tail enc _ => 2 ^ (tail + enc.rate)
  | @Schedule.more _ tail _ enc _ _ => 2 ^ (tail + enc.rate)

/-- The column oracle message for the head of a schedule. -/
abbrev oracleMessage (E : Type) {K : Type} {n : ℕ} (s : Schedule K n) :=
  Word E s.lanes s.columns

/-- The opening phase of the public-coin oracle protocol. -/
def opening (E : Type) {K : Type} : {n : ℕ} → Schedule K n → Protocol
  | _, .last lanes tail enc queries => .public .receiver E fun _ =>
      scalarRounds E lanes
        (.public .sender (Table E tail) fun _ =>
          .public .receiver (Fin queries → enc.Columns) fun _ =>
            .public .receiver E fun _ => scalarRounds E tail .done)
  | _, @Schedule.more _ tail lanes enc queries rest => .public .receiver E fun _ =>
      scalarRounds E lanes
        (.oracle (oracleMessage E rest)
          (.public .receiver (Fin tail → E) fun _ =>
            .public .sender E fun _ =>
              .public .receiver (Fin queries → enc.Columns) fun _ => opening E rest))

/-- The suffix after the fold challenges of one encoded level. -/
def transition (E : Type) {K : Type} : {n : ℕ} → Schedule K n → Protocol
  | _, .last _ tail enc queries =>
      .public .sender (Table E tail) fun _ =>
        .public .receiver (Fin queries → enc.Columns) fun _ =>
          .public .receiver E fun _ => scalarRounds E tail .done
  | _, @Schedule.more _ tail _ enc queries rest =>
      .oracle (oracleMessage E rest)
        (.public .receiver (Fin tail → E) fun _ =>
          .public .sender E fun _ =>
            .public .receiver (Fin queries → enc.Columns) fun _ => opening E rest)

/-- The base-field commitment followed by its challenge-field opening phase. -/
def protocol (K E : Type) {n : ℕ} (s : Schedule K n) : Protocol :=
  .oracle (oracleMessage K s) (opening E s)

/-- Every verifier move in a scalar-round block is a fresh uniform public challenge. -/
def scalarRoundsPublicCoin {E : Type} [DecidableEq E] [SampleableType E]
    (count : ℕ) {rest : Protocol} (coin : PublicCoin rest) :
    PublicCoin (scalarRounds E count rest) :=
  match count with
  | 0 => coin
  | count + 1 => .sender fun _ => .challenge (scalarRoundsPublicCoin count coin)

/-- The opening's public-coin presentation follows the encoded-level schedule. -/
def openingPublicCoin {K E : Type} [DecidableEq E] [SampleableType E] :
    {n : ℕ} → (s : Schedule K n) → PublicCoin (opening E s)
  | _, .last lanes tail _ _ => .challenge (scalarRoundsPublicCoin lanes
      (.sender fun _ => .challenge (.challenge (scalarRoundsPublicCoin tail .done))))
  | _, .more lanes _ _ rest => .challenge (scalarRoundsPublicCoin lanes
      (.oracle (.challenge (.sender fun _ => .challenge (openingPublicCoin rest)))))

/-- Uniform public coins for the initial oracle and opening, with no initial OOD. -/
def publicCoin {K E : Type} [DecidableEq K] [DecidableEq E] [SampleableType E]
    {n : ℕ} (s : Schedule K n) : PublicCoin (protocol K E s) :=
  .oracle (openingPublicCoin s)

/-- Parse a block of sumcheck rounds and keep its checks, challenges, and concrete suffix. -/
def readRounds {E : Type} [CommRing E] [DecidableEq E] (rest : Protocol) :
    (count : ℕ) → E → (scalarRounds E count rest).tree.ExecutionPath →
      E × (Fin count → E) × Bool × rest.tree.ExecutionPath
  | 0, current, path => (current, Fin.elim0, true, path)
  | count + 1, current, path =>
      let q := path.1
      let r := path.2.1
      let next := readRounds rest count (evalQuadratic q r) path.2.2
      (next.1, Fin.cons r next.2.1,
        decide (evalQuadratic q 0 + evalQuadratic q 1 = current) && next.2.2.1,
        next.2.2.2)

/-- Add the residual, OOD, and sampled consistency claims in the Annex B order. -/
def nextClaims {K E : Type} [Semiring K] [CommRing E] {tail queries : ℕ}
    (enc : Encoding K tail) (ι : K →+* E) (residual : Claim E tail)
    (z : Fin tail → E) (answer : E) (xs : Fin queries → enc.Columns)
    (folded : enc.Columns → E) : List (Claim E tail) :=
  residual :: ⟨eqWeight z, answer⟩ ::
    List.ofFn (fun q => ⟨fun u => ι (enc.weight (xs q) u), folded (xs q)⟩)

/-- The verifier's transcript predicate, including the final plaintext evaluation check. -/
def accepts {K E : Type} [Semiring K] [CommRing E] [DecidableEq E] (ι : K →+* E) :
    {n : ℕ} → (s : Schedule K n) → oracleMessage E s → List (Claim E n) →
      (opening E s).tree.ExecutionPath → Bool
  | _, .last lanes tail enc queries, word, claims, path =>
      let batched := batch claims path.1
      let round := readRounds (transition E (.last lanes tail enc queries))
        lanes batched.value path.2
      let residual : Claim E tail := ⟨restrict batched.weight round.2.1, round.1⟩
      let finalTable := round.2.2.2.1
      let xs := round.2.2.2.2.1
      let finalClaims := residual :: List.ofFn (fun q : Fin queries =>
        (⟨fun u => ι (enc.weight (xs q) u), foldWord word round.2.1 (xs q)⟩ : Claim E tail))
      let finalBatch := batch finalClaims round.2.2.2.2.2.1
      let closing := readRounds .done tail finalBatch.value round.2.2.2.2.2.2
      round.2.2.1 && closing.2.2.1 && decide (mle finalTable closing.2.1 = closing.1)
  | _, .more lanes enc queries rest, word, claims, path =>
      let batched := batch claims path.1
      let round := readRounds (transition E (.more lanes enc queries rest))
        lanes batched.value path.2
      let residual := ⟨restrict batched.weight round.2.1, round.1⟩
      let after := round.2.2.2
      let claims' := nextClaims enc ι residual after.2.1 after.2.2.1 after.2.2.2.1
        (foldWord word round.2.1)
      round.2.2.1 && accepts ι rest after.1 claims' after.2.2.2.2

end Whir
