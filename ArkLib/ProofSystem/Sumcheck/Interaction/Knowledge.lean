/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.Interaction.Oracle.Security.Knowledge
public import ArkLib.ProofSystem.Sumcheck.Interaction.ProtocolSoundness
public import ArkLib.ProofSystem.Sumcheck.Message.Compressed

/-!
# Sumcheck knowledge with a retained witness

The summand is a bounded multivariate polynomial determined by a witness. Every backward
map retains that witness. At a round boundary, knowledge means that the witness is admissible,
all preceding checks passed, and its summand satisfies the current reduced sum claim.
The final relation is the admissible witness's evaluation claim; public abort has no valid witness.

Local bounds require that admissible witnesses determine one fixed polynomial before challenges
are sampled. This is a semantic binding premise, not a verifier query or a supplied valid witness.
It permits the existential witness inside `RoundExtractor.badChallenge` to be bounded using
`MultivariateRound.uniform_successor_soundness` for that fixed polynomial. Without binding,
different witnesses can supply different collision roots, so the fixed-polynomial soundness
bound does not bound their union.

The oracle interface accepts the running claim as part of an evaluation query. This supports
the neutral `MessageOps` contract, including compressed messages whose decoding uses that claim.
The tree has the native Sumcheck public abort branches and exports a final claim without
evaluating the witness's summand.
-/

@[expose] public section

open Interaction Interaction.Oracle Interaction.Oracle.TypeTree
  Interaction.Oracle.Security OracleComp OracleSpec

namespace Sumcheck.Interaction.Knowledge

open SingleRound MultivariateRound

variable {F : Type} {n deg : ℕ} {W M : Type}

section Algebra

variable [CommSemiring F]

/-- Evaluation access to a message decoded using the verifier's running claim. -/
@[reducible]
def messageInterface (ops : MessageOps F M) : OracleInterface M where
  Query := F × F
  toOC.spec := (F × F) →ₒ F
  toOC.impl query := do return ops.evaluate query.1 (← read) query.2

/-- Claim-aware messages alternate with optional public challenges; `none` aborts. -/
def protocol (ops : MessageOps F M) : ℕ → Protocol
  | 0 => .done
  | count + 1 => .oracleWith M (messageInterface ops)
      (.public .receiver (Option F) fun
        | none => .done
        | some _ => protocol ops count)

/-- Claim-aware evaluation preserves the native Sumcheck message and public-branch tree. -/
theorem protocol_tree_eq_native (ops : MessageOps F M) (count : ℕ) :
    (protocol ops count).tree =
      (Native.Core.protocol F M (fun q => ops.evaluate 0 q) count).tree := by
  sorry

/-- Native Sumcheck and claim-aware messages have the same tree and public ownership. -/
theorem protocol_tree_roles_eq_native (ops : MessageOps F M) (count : ℕ) :
    (⟨(protocol ops count).tree, (protocol ops count).roles⟩ :
      (tree : Oracle.TypeTree) × tree.RoleDecoration) =
    ⟨(Native.Core.protocol F M (fun q => ops.evaluate 0 q) count).tree,
      (Native.Core.protocol F M (fun q => ops.evaluate 0 q) count).roles⟩ := by
  sorry

/-- A retained witness satisfies the current reduced sum claim after all preceding checks. -/
def claimState {m : ℕ} (D : Fin m ↪ F) (valid : W → Prop)
    (summand : W → Spec.OracleStatement F n deg ()) (i : Fin (n + 1))
    (stmt : Spec.StatementRound F n i) (active : Bool) : KnowledgeState where
  Witness := W
  holds w := active = true ∧ valid w ∧ closedRelation F n deg D i
    ⟨stmt, (polynomialFamily F n deg).behaviorOfRealizations (fun _ => summand w)⟩

/-- Admissible witnesses must share a polynomial fixed before the fresh verifier challenge. -/
def BindsSummand (valid : W → Prop) (summand : W → Spec.OracleStatement F n deg ())
    (p : Spec.OracleStatement F n deg ()) : Prop :=
  ∀ w, valid w → summand w = p

/-- A rejected prefix retains candidate witnesses but satisfies no knowledge predicate. -/
def rejectedState (W : Type) : KnowledgeState where
  Witness := W
  holds _ := False

/-- Total identity maps retain the witness through every message, challenge, and abort branch. -/
def roundExtractor (ops : MessageOps F M) {m : ℕ} (D : Fin m ↪ F)
    (valid : W → Prop) (summand : W → Spec.OracleStatement F n deg ()) :
    (count start : ℕ) → (finish : start + count = n) →
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) → (active : Bool) →
    RoundExtractor (protocol ops count).tree
      (claimState D valid summand ⟨start, by omega⟩ stmt active)
  | 0, _, _, _, _ => PUnit.unit
  | count + 1, start, finish, stmt, active => fun q =>
      ⟨claimState D valid summand ⟨start, by omega⟩ stmt active, id, fun
        | none => ⟨rejectedState W, id, PUnit.unit⟩
        | some r =>
            ⟨claimState D valid summand ⟨start + 1, by omega⟩
              ⟨ops.evaluate stmt.target q r, Fin.snoc stmt.challenges r⟩
              (active && ops.accept stmt.target q), id,
              roundExtractor ops D valid summand count (start + 1) (by omega)
                ⟨ops.evaluate stmt.target q r, Fin.snoc stmt.challenges r⟩
                (active && ops.accept stmt.target q)⟩⟩

/-- The carrier at every concrete authored prefix is the retained witness carrier. -/
def prefixWitnessEquiv (ops : MessageOps F M) {m : ℕ} (D : Fin m ↪ F)
    (valid : W → Prop) (summand : W → Spec.OracleStatement F n deg ())
    (count start : ℕ) (finish : start + count = n)
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) (active : Bool)
    (pfx : ExecutionPrefix (protocol ops count).tree) :
    ((roundExtractor ops D valid summand count start finish stmt active).knowledgeState pfx).Witness
      ≃ W := by
  sorry

/-- Backward extraction through any actual prefix returns the supplied witness unchanged. -/
theorem extractPrefixWitness_eq (ops : MessageOps F M) {m : ℕ} (D : Fin m ↪ F)
    (valid : W → Prop) (summand : W → Spec.OracleStatement F n deg ())
    (count start : ℕ) (finish : start + count = n)
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) (active : Bool)
    (pfx : ExecutionPrefix (protocol ops count).tree)
    (w : ((roundExtractor ops D valid summand count start finish stmt active).knowledgeState
      pfx).Witness) :
    (roundExtractor ops D valid summand count start finish stmt active).extractPrefixWitness pfx w =
      prefixWitnessEquiv ops D valid summand count start finish stmt active pfx w := by
  sorry

/-- Oracle messages preserve the current knowledge predicate under their identity maps. -/
theorem roundExtractor_proverPreserving (ops : MessageOps F M) {m : ℕ} (D : Fin m ↪ F)
    (valid : W → Prop) (summand : W → Spec.OracleStatement F n deg ())
    (count start : ℕ) (finish : start + count = n)
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) (active : Bool) :
    (roundExtractor ops D valid summand count start finish stmt active).IsProverPreserving
      (protocol ops count).roles := by
  sorry

/-- Parse the output evaluation claim from actual messages, rejecting failed checks and aborts. -/
def outputClaim (ops : MessageOps F M) :
    (count start : ℕ) → (finish : start + count = n) →
    Spec.StatementRound F n ⟨start, by omega⟩ → Bool →
    (protocol ops count).tree.ExecutionPath → Option (Native.FinalStatement F n)
  | 0, start, finish, stmt, active, _ =>
      if active then
        some ⟨stmt.target, stmt.challenges ∘ Fin.cast (by change n = start; omega)⟩
      else none
  | count + 1, start, finish, stmt, active, path =>
      match path with
      | ⟨_, none, _⟩ => none
      | ⟨q, some r, rest⟩ => outputClaim ops count (start + 1) (by omega)
          ⟨ops.evaluate stmt.target q r, Fin.snoc stmt.challenges r⟩
          (active && ops.accept stmt.target q) rest

/-- Output claims are optional full-point evaluation statements. -/
def evaluationFamily (F : Type) (n : ℕ) : ClaimFamily Unit :=
  ⟨fun _ => Option (Native.FinalStatement F n)⟩

/-- An admissible retained witness discharges the exported evaluation claim; rejection is false. -/
def evaluationProblem (valid : W → Prop)
    (summand : W → Spec.OracleStatement F n deg ()) : Problem (evaluationFamily F n) where
  Witness _ _ := W
  admissible _ _ := True
  rel _ claim w := match claim with
    | none => False
    | some stmt => valid w ∧ (summand w).val.eval stmt.challenges = stmt.target
  rel_admissible := by sorry

/-- The extractor's endpoint relation is exactly the optional output evaluation claim. -/
def terminalRelation (ops : MessageOps F M) {m : ℕ} (D : Fin m ↪ F)
    (valid : W → Prop) (summand : W → Spec.OracleStatement F n deg ())
    (count start : ℕ) (finish : start + count = n)
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) (active : Bool) :
    TerminalRelation (roundExtractor ops D valid summand count start finish stmt active)
      (evaluationProblem valid summand) (fun _ => ())
      (outputClaim ops count start finish stmt active) := by
  sorry

end Algebra

section MessageModel

variable [CommRing F]

/-- Binding puts the existential bad-witness event inside one fixed-polynomial escape event. -/
theorem badChallenge_implies_successor (ops : MessageOps F M) {m : ℕ} (D : Fin m ↪ F)
    (model : MessageModel (Finset.univ.map D) ops deg)
    (valid : W → Prop) (summand : W → Spec.OracleStatement F n deg ())
    (p : Spec.OracleStatement F n deg ()) (binding : BindsSummand valid summand p)
    (count start : ℕ) (finish : start + (count + 1) = n)
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) (active : Bool) (q : M)
    (choice : Option F)
    (bad : RoundExtractor.badChallenge
      ((roundExtractor ops D valid summand (count + 1) start finish stmt active q).2.2) choice) :
    ¬ closedRelation F n deg D ⟨start, by omega⟩
      ⟨stmt, (polynomialFamily F n deg).behaviorOfRealizations (fun _ => p)⟩ ∧
    ops.accept stmt.target q = true ∧
    ∃ r, choice = some r ∧ closedRelation F n deg D ⟨start + 1, by omega⟩
      ⟨⟨(model.interpret stmt.target q).val.eval r, Fin.snoc stmt.challenges r⟩,
        (polynomialFamily F n deg).behaviorOfRealizations (fun _ => p)⟩ := by
  sorry

end MessageModel

section Probability

variable [Field F] [Fintype F] [SampleableType F]

/-- The actual public choice is a fresh uniform challenge on acceptance, and abort otherwise. -/
noncomputable def nextChallenge (ops : MessageOps F M) (current : F) (q : M) :
    ProbComp (Option F) :=
  if ops.accept current q then some <$> ($ᵗ F) else pure none

/-- Every authored verifier prefix uses the neutral message check and error `deg / card F`. -/
noncomputable def challenges (ops : MessageOps F M) (deg : ℕ) :
    (count : ℕ) → F → RoundExtractor.ChallengeSchedule (protocol ops count).tree
      (protocol ops count).roles
  | 0, _ => PUnit.unit
  | count + 1, current => fun q =>
      ⟨⟨nextChallenge ops current q, (deg : ENNReal) / Fintype.card F⟩, fun
        | none => PUnit.unit
        | some r => challenges ops deg count (ops.evaluate current q r)⟩

/-- The existing fixed-polynomial successor bound gives the local bad-challenge probability. -/
theorem local_badChallenge_le (ops : MessageOps F M) {m : ℕ} (D : Fin m ↪ F)
    (model : MessageModel (Finset.univ.map D) ops deg)
    (valid : W → Prop) (summand : W → Spec.OracleStatement F n deg ())
    (p : Spec.OracleStatement F n deg ()) (binding : BindsSummand valid summand p)
    (count start : ℕ) (finish : start + (count + 1) = n)
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) (active : Bool) (q : M) :
    Pr{let choice ← nextChallenge ops stmt.target q}[
      RoundExtractor.badChallenge
        ((roundExtractor ops D valid summand (count + 1) start finish stmt active q).2.2)
        choice] ≤ (deg : ENNReal) / Fintype.card F := by
  sorry

/-- Every authored prefix, including unreachable prefixes, satisfies the same local error bound. -/
theorem roundExtractor_locallyBounded (ops : MessageOps F M) {m : ℕ} (D : Fin m ↪ F)
    (model : MessageModel (Finset.univ.map D) ops deg)
    (valid : W → Prop) (summand : W → Spec.OracleStatement F n deg ())
    (p : Spec.OracleStatement F n deg ()) (binding : BindsSummand valid summand p)
    (count start : ℕ) (finish : start + count = n)
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) (active : Bool) :
    (roundExtractor ops D valid summand count start finish stmt active).IsLocallyBounded
      (protocol ops count).roles (challenges ops deg count stmt.target) := by
  sorry

/-- The witness-retaining Sumcheck certificate, conditional on semantic binding of the summand. -/
noncomputable def certificate (ops : MessageOps F M) {m : ℕ} (D : Fin m ↪ F)
    (model : MessageModel (Finset.univ.map D) ops deg)
    (valid : W → Prop) (summand : W → Spec.OracleStatement F n deg ())
    (p : Spec.OracleStatement F n deg ()) (binding : BindsSummand valid summand p)
    (count start : ℕ) (finish : start + count = n)
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) (active : Bool) :
    KnowledgeCertificate (protocol ops count).tree (protocol ops count).roles
      (claimState D valid summand ⟨start, by omega⟩ stmt active) where
  extractor := roundExtractor ops D valid summand count start finish stmt active
  challenges := challenges ops deg count stmt.target
  prover_preserving := by sorry
  local_bound := by sorry

/-- The summand polynomial itself is retained as the witness for a fixed input polynomial. -/
noncomputable def polynomialCertificate (ops : MessageOps F M) {m : ℕ} (D : Fin m ↪ F)
    (model : MessageModel (Finset.univ.map D) ops deg)
    (p : Spec.OracleStatement F n deg ())
    (count start : ℕ) (finish : start + count = n)
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) (active : Bool) :
    KnowledgeCertificate (protocol ops count).tree (protocol ops count).roles
      (claimState D (fun w => w = p) id ⟨start, by omega⟩ stmt active) :=
  certificate ops D model (fun w => w = p) id p (by sorry)
    count start finish stmt active

/-- The retained-witness certificate on the existing mathematical Sumcheck protocol. -/
noncomputable def nativeCertificate [DecidableEq F] {m : ℕ} (D : Fin m ↪ F)
    (valid : W → Prop) (summand : W → Spec.OracleStatement F n deg ())
    (p : Spec.OracleStatement F n deg ()) (binding : BindsSummand valid summand p)
    (count start : ℕ) (finish : start + count = n)
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) (active : Bool) :
    KnowledgeCertificate (Native.protocol F deg count).tree (Native.protocol F deg count).roles
      (claimState D valid summand ⟨start, by omega⟩ stmt active) :=
  let ops := plainOps (Finset.univ.map D) (fun q : Message F deg => q.val.eval)
  let state := claimState D valid summand ⟨start, by omega⟩ stmt active
  (congrArg (fun data : (tree : Oracle.TypeTree) × tree.RoleDecoration =>
    KnowledgeCertificate data.1 data.2 state) (protocol_tree_roles_eq_native ops count)) ▸
    certificate ops D (identityModel (Finset.univ.map D)) valid summand p binding
      count start finish stmt active

end Probability

end Sumcheck.Interaction.Knowledge
