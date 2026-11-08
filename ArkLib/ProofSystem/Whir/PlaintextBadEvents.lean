/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.ProofSystem.Whir.LocalSecurity

/-! # Algebraic bad events for the public plaintext suffix -/

@[expose] public section

open Interaction Interaction.Oracle.Security OracleComp OracleSpec

namespace Whir

/-- A false fixed-plaintext claim list becomes true after power batching. -/
def BadFinalBatch {E : Type} [CommRing E] {n : ℕ}
    (candidate : Table E n) (claims : List (Claim E n)) (r : E) : Prop :=
  (∃ c ∈ claims, ¬ c.Holds candidate) ∧ (batch claims r).Holds candidate

/-- The public-plaintext batching event has a direct executable checker. -/
def checkBadFinalBatch {E : Type} [CommRing E] [DecidableEq E] {n : ℕ}
    (candidate : Table E n) (claims : List (Claim E n)) (r : E) : Bool :=
  claims.any (fun c => !decide (c.Holds candidate)) && decide ((batch claims r).Holds candidate)

/-- The final batching checker decides the false-claim root event. -/
theorem checkBadFinalBatch_iff {E : Type} [CommRing E] [DecidableEq E] {n : ℕ}
    (candidate : Table E n) (claims : List (Claim E n)) (r : E) :
    checkBadFinalBatch candidate claims r = true ↔ BadFinalBatch candidate claims r := by
  simp only [checkBadFinalBatch, Bool.and_eq_true, List.any_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_eq, BadFinalBatch]

/-- Final batching escape lies in the fixed-plaintext root event. -/
theorem finalBatch_escape_subset_bad {E : Type} [CommRing E] [DecidableEq E] {n : ℕ}
    (candidate : Table E n) (claims : List (Claim E n)) (active : Bool) (r : E)
    (escape : (finalBatchExtractor candidate claims active).badChallenge r) :
    BadFinalBatch candidate claims r := by
  obtain ⟨_, bad, good⟩ := escape
  refine ⟨?_, good.2 _ (List.mem_singleton_self _)⟩
  by_contra h
  apply bad
  exact ⟨good.1, by simpa only [not_exists, not_and, not_not] using h⟩

/-- Final batching keeps the original fixed-candidate bound without a Johnson list factor. -/
theorem prob_badFinalBatch_le {E : Type} [Field E] [Fintype E] [SampleableType E] {n : ℕ}
    (candidate : Table E n) (claims : List (Claim E n)) :
    Pr{let r ←$ᵗ E}[BadFinalBatch candidate claims r] ≤
      ((claims.length - 1 : ℕ) : ENNReal) / Fintype.card E := by
  classical
  by_cases lost : ∃ c ∈ claims, ¬ c.Holds candidate
  · exact (prEvent_mono ($ᵗ E) _ _ (fun _ h => h.2)).trans
      (prob_final_batch_escape_le claims candidate lost)
  · exact (prEvent_eq_zero_of_forall_not ($ᵗ E) _ (fun _ h => lost h.1)).le.trans zero_le

/-- A false fixed-plaintext claim becomes true after a quadratic closing fold. -/
def BadClosing {E : Type} [CommRing E] {n : ℕ}
    (candidate : Table E (n + 1)) (claim : Claim E (n + 1)) (q : Quadratic E) (r : E) : Prop :=
  ¬ claim.Holds candidate ∧
    (⟨foldMessageOne (vars := 0) claim.weight r, evalQuadratic claim.value q r⟩ :
      Claim E n).Holds (foldMessageOne (vars := 0) candidate r)

/-- The closing checker evaluates only fixed public data and the scalar challenge. -/
def checkBadClosing {E : Type} [CommRing E] [DecidableEq E] {n : ℕ}
    (candidate : Table E (n + 1)) (claim : Claim E (n + 1)) (q : Quadratic E) (r : E) : Bool :=
  decide (¬ claim.Holds candidate ∧
    (⟨foldMessageOne (vars := 0) claim.weight r, evalQuadratic claim.value q r⟩ :
      Claim E n).Holds (foldMessageOne (vars := 0) candidate r))

/-- The closing checker decides the quadratic root event. -/
theorem checkBadClosing_iff {E : Type} [CommRing E] [DecidableEq E] {n : ℕ}
    (candidate : Table E (n + 1)) (claim : Claim E (n + 1)) (q : Quadratic E) (r : E) :
    checkBadClosing candidate claim q r = true ↔ BadClosing candidate claim q r := by
  simp only [checkBadClosing, decide_eq_true_eq, BadClosing]

/-- A closing challenge escape is a false plaintext claim becoming true. -/
theorem closing_escape_subset_bad {E : Type} [CommRing E] [DecidableEq E] {n : ℕ}
    (candidate : Table E (n + 1)) (claim : Claim E (n + 1)) (q : Quadratic E)
    (active : Bool) (r : E)
    (escape : ((closingExtractor (n + 1) candidate claim active q).2.2).badChallenge r) :
    BadClosing candidate claim q r := by
  obtain ⟨_, bad, good⟩ := escape
  refine ⟨?_, good.2 _ (List.mem_singleton_self _)⟩
  intro hc
  exact bad ⟨good.1, by simpa only [List.mem_singleton, forall_eq] using hc⟩

/-- Closing retains its original degree-two root bound. -/
theorem prob_badClosing_le {E : Type} [Field E] [Fintype E] [SampleableType E] {n : ℕ}
    (candidate : Table E (n + 1)) (claim : Claim E (n + 1)) (q : Quadratic E) :
    Pr{let r ←$ᵗ E}[BadClosing candidate claim q r] ≤ (2 : ENNReal) / Fintype.card E := by
  classical
  by_cases lost : ¬ claim.Holds candidate
  · exact (prEvent_mono ($ᵗ E) _ _ (fun _ h => h.2)).trans
      (prob_closing_escape_le candidate claim q lost)
  · exact (prEvent_eq_zero_of_forall_not ($ᵗ E) _ (fun _ h => lost h.1)).le.trans zero_le

/-- Public plaintext and query equations preceding the final algebraic challenges. -/
structure PlaintextPublic (E : Type) (n columns queries : ℕ) where
  /-- The plaintext fixed before the queries. -/
  candidate : Table E n
  /-- The residual claims fixed before the queries. -/
  residual : List (Claim E n)
  /-- Public query weights in the original column order. -/
  weights : Fin queries → Table E n
  /-- The earlier query challenge. -/
  positions : Fin queries → Fin columns

/-- A plaintext suffix retains the masked oracle from which its query equations are read. -/
structure PlaintextPrefix (E : Type) (n columns queries : ℕ) where
  /-- Public messages and earlier challenges in the strict prefix. -/
  publicData : PlaintextPublic E n columns queries
  /-- The authenticated partial oracle used by the sampled equations. -/
  word : MaskedWord E 0 columns

/-- The plaintext prefix's public fields agree and its known columns extend. -/
def PlaintextPrefix.MaskLE {E : Type} {n columns queries : ℕ}
    (small large : PlaintextPrefix E n columns queries) : Prop :=
  small.publicData = large.publicData ∧ Whir.MaskLE small.word large.word

/-- Query equations are active exactly when every sampled column is known. -/
def PlaintextPrefix.known {E : Type} {n columns queries : ℕ}
    (pre : PlaintextPrefix E n columns queries) : Bool :=
  queriesKnown pre.word pre.publicData.positions

/-- Residual claims and the equations read from the known sampled columns. -/
def PlaintextPrefix.claims {E : Type} [Zero E] {n columns queries : ℕ}
    (pre : PlaintextPrefix E n columns queries) : List (Claim E n) :=
  pre.publicData.residual ++ List.ofFn (fun q =>
    ⟨pre.publicData.weights q, zeroFill pre.word (pre.publicData.positions q) Fin.elim0⟩)

/-- Extending a live masked prefix preserves its activity and every sampled equation. -/
theorem PlaintextPrefix.extend_known {E : Type} [Zero E] {n columns queries : ℕ}
    {small large : PlaintextPrefix E n columns queries} (h : small.MaskLE large)
    (known : small.known = true) :
    large.known = true ∧ small.claims = large.claims := by
  rcases small with ⟨publicData, small⟩
  rcases large with ⟨publicData', large⟩
  obtain ⟨rfl, masks⟩ := h
  have hk := (queriesKnown_iff small publicData.positions).mp known
  have eq (q : Fin queries) : small (publicData.positions q) = large (publicData.positions q) := by
    obtain ⟨column, hc⟩ := Option.isSome_iff_exists.mp (hk q)
    exact hc.trans (masks _ _ hc).symm
  refine ⟨(queriesKnown_iff large publicData.positions).mpr ?_, ?_⟩
  · intro q
    rw [← eq q]
    exact hk q
  · simp only [claims]
    congr 1
    apply congrArg List.ofFn
    funext q
    simp only [zeroFill, eq q]

/-- Final batching's bad relation includes the masked prefix's known-query guard. -/
def PrefixBadFinalBatch {E : Type} [CommRing E] {n columns queries : ℕ}
    (pre : PlaintextPrefix E n columns queries) (r : E) : Prop :=
  pre.known = true ∧ BadFinalBatch pre.publicData.candidate pre.claims r

/-- The final batching checker rejects hidden sampled columns before checking the root event. -/
def checkPrefixBadFinalBatch {E : Type} [CommRing E] [DecidableEq E] {n columns queries : ℕ}
    (pre : PlaintextPrefix E n columns queries) (r : E) : Bool :=
  pre.known && checkBadFinalBatch pre.publicData.candidate pre.claims r

/-- The guarded executable checker decides final batching badness on the masked prefix. -/
theorem checkPrefixBadFinalBatch_iff {E : Type} [CommRing E] [DecidableEq E]
    {n columns queries : ℕ} (pre : PlaintextPrefix E n columns queries) (r : E) :
    checkPrefixBadFinalBatch pre r = true ↔ PrefixBadFinalBatch pre r := by
  simp only [checkPrefixBadFinalBatch, Bool.and_eq_true, checkBadFinalBatch_iff,
    PrefixBadFinalBatch]

/-- Final batching is monotone over masked prefixes, including the query activity guard. -/
theorem BadFinalBatch.mask_mono {E : Type} [CommRing E] {n columns queries : ℕ}
    {small large : PlaintextPrefix E n columns queries} (h : small.MaskLE large) {r : E}
    (bad : PrefixBadFinalBatch small r) : PrefixBadFinalBatch large r := by
  obtain ⟨known, claims⟩ := PlaintextPrefix.extend_known h bad.1
  refine ⟨known, ?_⟩
  simpa only [h.1, claims] using bad.2

/-- Closing's data is computed from the guarded prefix and its public scalar history. -/
def PrefixBadClosing {E : Type} [CommRing E] {n m columns queries : ℕ}
    (closing : Table E n → List (Claim E n) → Table E (m + 1) × Claim E (m + 1))
    (pre : PlaintextPrefix E n columns queries) (q : Quadratic E) (r : E) : Prop :=
  pre.known = true ∧
    BadClosing (closing pre.publicData.candidate pre.claims).1
      (closing pre.publicData.candidate pre.claims).2 q r

/-- Closing's checker retains the original mask guard through the public scalar history. -/
def checkPrefixBadClosing {E : Type} [CommRing E] [DecidableEq E]
    {n m columns queries : ℕ}
    (closing : Table E n → List (Claim E n) → Table E (m + 1) × Claim E (m + 1))
    (pre : PlaintextPrefix E n columns queries) (q : Quadratic E) (r : E) : Bool :=
  pre.known && checkBadClosing (closing pre.publicData.candidate pre.claims).1
    (closing pre.publicData.candidate pre.claims).2 q r

/-- The guarded closing checker decides the masked-prefix root event. -/
theorem checkPrefixBadClosing_iff {E : Type} [CommRing E] [DecidableEq E]
    {n m columns queries : ℕ}
    (closing : Table E n → List (Claim E n) → Table E (m + 1) × Claim E (m + 1))
    (pre : PlaintextPrefix E n columns queries) (q : Quadratic E) (r : E) :
    checkPrefixBadClosing closing pre q r = true ↔ PrefixBadClosing closing pre q r := by
  simp only [checkPrefixBadClosing, Bool.and_eq_true, checkBadClosing_iff, PrefixBadClosing]

/-- Closing is monotone over live masked prefixes and their derived plaintext claims. -/
theorem BadClosing.mask_mono {E : Type} [CommRing E] {n m columns queries : ℕ}
    (closing : Table E n → List (Claim E n) → Table E (m + 1) × Claim E (m + 1))
    {small large : PlaintextPrefix E n columns queries} (h : small.MaskLE large)
    {q : Quadratic E} {r : E} (bad : PrefixBadClosing closing small q r) :
    PrefixBadClosing closing large q r := by
  obtain ⟨known, claims⟩ := PlaintextPrefix.extend_known h bad.1
  refine ⟨known, ?_⟩
  simpa only [h.1, claims] using bad.2

end Whir
