/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.ProofSystem.Whir.Protocol
public import ArkLib.Interaction.Oracle.Security.Knowledge
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Probability
public import ArkLib.Data.CodingTheory.ProximityGenerator.Interleaving

/-!
# Annex B local errors and the corresponding fresh-challenge schedule

The Johnson list bound uses the dimension rate. The MCA numerator uses the reduced rate
`(dimension - 1) / blockLength` and its adjusted slack at the same radius. These are distinct
parameters. `challenges` describes the samplers and errors, without asserting a knowledge bound.
-/

@[expose] public section

open Interaction Interaction.Oracle Interaction.Oracle.Security OracleComp OracleSpec

namespace Whir

/-- The Johnson slack at one encoded level. -/
structure LevelSecurity where
  /-- Slack relative to the square root of the dimension rate. -/
  slack : ℝ

/-- The dimension rate of the code. -/
noncomputable def dimensionRate {K : Type} {vars : ℕ} (enc : Encoding K vars) : ℝ :=
  (2 ^ vars : ℝ) / 2 ^ (vars + enc.rate)

/-- The analysis radius, using the dimension rate as in Annex B's RBR theorem. -/
noncomputable def radius {K : Type} {vars : ℕ} (enc : Encoding K vars)
    (sec : LevelSecurity) : ℝ :=
  1 - Real.sqrt (dimensionRate enc) - sec.slack

/-- The real Johnson list bound; rounding it up would weaken Annex B's constants. -/
noncomputable def listBound {K : Type} {vars : ℕ} (enc : Encoding K vars)
    (sec : LevelSecurity) : ℝ :=
  1 / (2 * sec.slack * Real.sqrt (dimensionRate enc))

/-- The Johnson regime and the binary encoder's parameter range. -/
def LevelSecurity.Valid {K : Type} {vars : ℕ} (sec : LevelSecurity)
    (enc : Encoding K vars) : Prop :=
  0 < vars ∧ 0 < enc.rate ∧ vars + enc.rate ≤ 64 ∧
    0 < sec.slack ∧ sec.slack < 1 - Real.sqrt (dimensionRate enc)

/-- The slightly reduced rate used by the MCA theorem, which is positive only for `vars > 0`. -/
noncomputable def reducedRate {K : Type} {vars : ℕ} (enc : Encoding K vars) : ℝ :=
  ((2 ^ vars - 1 : ℕ) : ℝ) / 2 ^ (vars + enc.rate)

/-- Annex B's MCA numerator, at the same radius as its dimension-rate Johnson list. -/
noncomputable def mcaNumerator {K : Type} {vars : ℕ} (enc : Encoding K vars)
    (sec : LevelSecurity) : ℝ :=
  let ρ := reducedRate enc
  let η := 1 - Real.sqrt ρ - radius enc sec
  let θ : ℝ := max ⌈Real.sqrt ρ / η⌉₊ 3
  ((2 * (θ + 1 / 2) ^ 5 + 3 * (θ + 1 / 2) * radius enc sec * ρ) /
    (3 * (Real.sqrt ρ) ^ 3)) * 2 ^ (vars + enc.rate) +
    (θ + 1 / 2) / Real.sqrt ρ

/-- The positive-reduced-rate MCA error; `LevelSecurity.Valid` excludes dimension one. -/
noncomputable def mcaError {K E : Type} [Fintype E] {vars : ℕ}
    (enc : Encoding K vars) (sec : LevelSecurity) : ENNReal :=
  ENNReal.ofReal (mcaNumerator enc sec / Fintype.card E)

/-- Batching loss `(J - 1) L / |E|` at an encoded level. -/
noncomputable def batchError {K E : Type} [Fintype E] {vars : ℕ}
    (enc : Encoding K vars) (sec : LevelSecurity) (claims : ℕ) : ENNReal :=
  ENNReal.ofReal ((claims - 1 : ℕ) * listBound enc sec / Fintype.card E)

/-- Each fold challenge pays the list root bound and the row-independent MCA bound. -/
noncomputable def foldError {K E : Type} [Fintype E] {vars : ℕ}
    (enc : Encoding K vars) (sec : LevelSecurity) : ENNReal :=
  ENNReal.ofReal (2 * listBound enc sec / Fintype.card E) + mcaError (E := E) enc sec

/-- OOD separation at the entering level, with the real bound `L(L - 1)/2`. -/
noncomputable def oodError {K E : Type} [Fintype E] {vars : ℕ}
    (enc : Encoding K vars) (sec : LevelSecurity) (nvars : ℕ) : ENNReal :=
  let L := listBound enc sec
  ENNReal.ofReal ((L * (L - 1) / 2) * nvars / Fintype.card E)

/-- Independent column queries pay `(1 - gamma)^t`, without an extra list factor. -/
noncomputable def queryError {K : Type} {vars : ℕ}
    (enc : Encoding K vars) (sec : LevelSecurity) (queries : ℕ) : ENNReal :=
  ENNReal.ofReal ((1 - radius enc sec) ^ queries)

/-- Security parameters mirror the nonempty sequence of encoded levels. -/
def SecurityParameters {K : Type} : {n : ℕ} → Schedule K n → Type
  | _, .last _ _ _ _ => LevelSecurity
  | _, .more _ _ _ rest => LevelSecurity × SecurityParameters rest

/-- Every level has a positive fold and satisfies both scalar-extension encoding contracts. -/
def Schedule.Valid {K E : Type} [Field K] [Field E] (ι : K →+* E) :
    {n : ℕ} → (s : Schedule K n) → SecurityParameters s → Prop
  | _, .last lanes _ enc _, sec => 0 < lanes ∧ sec.Valid enc ∧
      EncodingContract enc (RingHom.id K) ∧ EncodingContract enc ι
  | _, .more lanes enc _ rest, sec => 0 < lanes ∧ sec.1.Valid enc ∧
      EncodingContract enc (RingHom.id K) ∧ EncodingContract enc ι ∧ rest.Valid ι sec.2

/-- Local error metadata for a scalar-round block and its fixed suffix. -/
noncomputable def scalarChallenges {E : Type} [SampleableType E] (error : ENNReal)
    {rest : Protocol} (suffix : RoundExtractor.ChallengeSchedule rest.tree rest.roles) :
    (count : ℕ) → RoundExtractor.ChallengeSchedule (scalarRounds E count rest).tree
      (scalarRounds E count rest).roles
  | 0 => suffix
  | count + 1 => ⟨PUnit.unit, fun _ =>
      ⟨⟨$ᵗ E, error⟩, fun _ => scalarChallenges error suffix count⟩⟩

/-- Head-level OOD error of a schedule, charged only when entering that level. -/
noncomputable def enteringOodError {K E : Type} [Fintype E] :
    {n : ℕ} → (s : Schedule K n) → SecurityParameters s → ENNReal
  | _, .last lanes tail enc _, sec => oodError (E := E) enc sec (lanes + tail)
  | _, @Schedule.more _ tail lanes enc _ _, sec =>
      oodError (E := E) enc sec.1 (lanes + tail)

/-- Every verifier prefix has the Annex B sampler and local error, including closing rounds. -/
noncomputable def challenges {K E : Type} [Fintype E] [SampleableType E] :
    {n : ℕ} → (s : Schedule K n) → SecurityParameters s → ℕ →
      RoundExtractor.ChallengeSchedule (opening E s).tree (opening E s).roles
  | _, .last lanes tail enc queries, sec, J =>
      ⟨⟨$ᵗ E, batchError (E := E) enc sec J⟩, fun _ =>
        scalarChallenges (foldError (E := E) enc sec)
          (rest := transition E (.last lanes tail enc queries))
          ⟨PUnit.unit, fun _ =>
            ⟨⟨$ᵗ (Fin queries → enc.Columns), queryError enc sec queries⟩, fun _ =>
              ⟨⟨$ᵗ E, (queries : ENNReal) / Fintype.card E⟩, fun _ =>
                scalarChallenges ((2 : ENNReal) / Fintype.card E)
                  (rest := .done) PUnit.unit tail⟩⟩⟩ lanes⟩
  | _, @Schedule.more _ tail lanes enc queries rest, sec, J =>
      ⟨⟨$ᵗ E, batchError (E := E) enc sec.1 J⟩, fun _ =>
        scalarChallenges (foldError (E := E) enc sec.1)
          (rest := transition E (.more lanes enc queries rest))
          (fun _ => ⟨⟨$ᵗ (Fin tail → E), enteringOodError (E := E) rest sec.2⟩, fun _ =>
            ⟨PUnit.unit, fun _ =>
              ⟨⟨$ᵗ (Fin queries → enc.Columns), queryError enc sec.1 queries⟩, fun _ =>
                challenges rest sec.2 (queries + 2)⟩⟩⟩) lanes⟩

end Whir
