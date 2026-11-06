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
  induction count with
  | zero => rfl
  | succ count ih =>
    apply congrArg (Oracle.TypeTree.oracle M)
    funext _
    apply congrArg (Oracle.TypeTree.public (Option F))
    funext choice
    cases choice with
    | none => rfl
    | some r => exact ih

/-- Native Sumcheck and claim-aware messages have the same tree and public ownership. -/
theorem protocol_tree_roles_eq_native (ops : MessageOps F M) (count : ℕ) :
    (⟨(protocol ops count).tree, (protocol ops count).roles⟩ :
      (tree : Oracle.TypeTree) × tree.RoleDecoration) =
    ⟨(Native.Core.protocol F M (fun q => ops.evaluate 0 q) count).tree,
      (Native.Core.protocol F M (fun q => ops.evaluate 0 q) count).roles⟩ := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have branches :
        (fun choice : Option F =>
          let rest := match choice with
            | none => Protocol.done
            | some _ => protocol ops count
          (⟨rest.tree, rest.roles⟩ : (tree : Oracle.TypeTree) × tree.RoleDecoration)) =
        (fun choice : Option F =>
          let rest := match choice with
            | none => Protocol.done
            | some _ => Native.Core.protocol F M (fun q => ops.evaluate 0 q) count
          (⟨rest.tree, rest.roles⟩ : (tree : Oracle.TypeTree) × tree.RoleDecoration)) := by
      funext choice
      cases choice with
      | none => rfl
      | some r => exact ih
    let step (rest : Option F → (tree : Oracle.TypeTree) × tree.RoleDecoration) :
        (tree : Oracle.TypeTree) × tree.RoleDecoration :=
      ⟨.oracle M (fun _ => .public (Option F) fun choice => (rest choice).1),
        ⟨PUnit.unit, fun _ => ⟨.receiver, fun choice => (rest choice).2⟩⟩⟩
    exact congrArg step branches

/-- A retained witness satisfies the current reduced sum claim after all preceding checks. -/
def claimState {m : ℕ} (D : Fin m ↪ F) (valid : W → Prop)
    (summand : W → Spec.OracleStatement F n deg ()) (i : Fin (n + 1))
    (stmt : Spec.StatementRound F n i) (active : Bool) : KnowledgeState where
  Witness := W
  holds w := active = true ∧ valid w ∧ closedRelation F n deg D i
    ⟨stmt, (polynomialFamily F n deg).behaviorOfRealizations (fun _ => summand w)⟩

/-- The summand is fixed by data committed before Sumcheck; `valid` means prefix consistency.
Without binding, `gₐ(X) = X + a` over `F₂`, with zero claim/message, gives error `1 > 1/2`. -/
def BindsSummand (valid : W → Prop) (summand : W → Spec.OracleStatement F n deg ())
    (p : Spec.OracleStatement F n deg ()) : Prop :=
  ∀ w, valid w → summand w = p

/-- A rejected prefix retains candidate witnesses but satisfies no knowledge predicate. -/
def rejectedState (W : Type) : KnowledgeState where
  Witness := W
  holds _ := False

/-- Proof-only retained knowledge at each Sumcheck statement and activity bit. -/
abbrev ClaimPredicate (F : Type) (n : ℕ) (W : Type) :=
  (i : Fin (n + 1)) → Spec.StatementRound F n i → Bool → W → Prop

/-- A retained carrier whose predicate is supplied independently of executable maps. -/
def retainedState (claim : ClaimPredicate F n W) (i : Fin (n + 1))
    (stmt : Spec.StatementRound F n i) (active : Bool) : KnowledgeState where
  Witness := W
  holds := claim i stmt active

/-- The mathematical summand is confined to the erased knowledge predicate. -/
def claimPredicate {m : ℕ} (D : Fin m ↪ F) (valid : W → Prop)
    (summand : W → Spec.OracleStatement F n deg ()) : ClaimPredicate F n W :=
  fun i stmt active w => (claimState D valid summand i stmt active).holds w

/-- Total identity maps retain the witness through every message, challenge, and abort branch. -/
def roundExtractor (ops : MessageOps F M) (claim : ClaimPredicate F n W) :
    (count start : ℕ) → (finish : start + count = n) →
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) → (active : Bool) →
    RoundExtractor (protocol ops count).tree
      (retainedState claim ⟨start, by omega⟩ stmt active)
  | 0, _, _, _, _ => PUnit.unit
  | count + 1, start, finish, stmt, active => fun q =>
      ⟨retainedState claim ⟨start, by omega⟩ stmt active, id, fun
        | none => ⟨rejectedState W, id, PUnit.unit⟩
        | some r =>
            ⟨retainedState claim ⟨start + 1, by omega⟩
              ⟨ops.evaluate stmt.target q r, Fin.snoc stmt.challenges r⟩
              (active && ops.accept stmt.target q), id,
              roundExtractor ops claim count (start + 1) (by omega)
                ⟨ops.evaluate stmt.target q r, Fin.snoc stmt.challenges r⟩
                (active && ops.accept stmt.target q)⟩⟩

/-- Every backward map of an extractor is bijective, at every concrete branch. -/
def mapsBijective : {tree : Oracle.TypeTree} → {state : KnowledgeState} →
    RoundExtractor tree state → Prop
  | .done, _, _ => True
  | .public _ _, _, extractor => ∀ move,
      Function.Bijective (extractor move).2.1 ∧ mapsBijective (extractor move).2.2
  | .oracle _ _, _, extractor => ∀ message,
      Function.Bijective (extractor message).2.1 ∧ mapsBijective (extractor message).2.2

/-- Bijective backward maps give a bijection along each concrete prefix spine. -/
theorem extractPrefix_bijective {tree residual : Oracle.TypeTree} {state : KnowledgeState}
    (extractor : RoundExtractor tree state) (bijective : mapsBijective extractor)
    (spine : PFunctor.FreeM.Cursor.Spine tree residual) (messages : PrefixMessages.Along spine) :
    Function.Bijective (extractor.extractPrefix spine messages) := by
  induction spine generalizing state with
  | root => exact Function.bijective_id
  | @down position next residual answer tail ih =>
    cases position with
    | «public» =>
      exact (bijective answer).1.comp
        (ih (extractor answer).2.2 (bijective answer).2 messages)
    | «oracle» =>
      exact (bijective messages.1).1.comp
        (ih (extractor messages.1).2.2 (bijective messages.1).2 messages.2)

omit [CommSemiring F] in
/-- Sumcheck's identity maps are bijective on every branch, including public abort. -/
theorem roundExtractor_mapsBijective (ops : MessageOps F M) (claim : ClaimPredicate F n W)
    (count start : ℕ) (finish : start + count = n)
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) (active : Bool) :
    mapsBijective (roundExtractor ops claim count start finish stmt active) := by
  induction count generalizing start active with
  | zero => trivial
  | succ count ih =>
    intro q
    refine ⟨Function.bijective_id, ?_⟩
    intro choice
    cases choice with
    | none => exact ⟨Function.bijective_id, trivial⟩
    | some r => exact ⟨Function.bijective_id, ih (start + 1) (by omega) _ _⟩

/-- Sumcheck's identity maps supply their own explicit inverses, including on abort. -/
def roundExtractor_mapEquivalences (ops : MessageOps F M) (claim : ClaimPredicate F n W) :
    (count start : ℕ) → (finish : start + count = n) →
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) → (active : Bool) →
    RoundExtractor.MapEquivalences (roundExtractor ops claim count start finish stmt
      active)
  | 0, _, _, _, _ => PUnit.unit
  | count + 1, start, _, stmt, active => fun q =>
      ⟨⟨Equiv.refl W, rfl⟩, fun
        | none => ⟨⟨Equiv.refl W, rfl⟩, PUnit.unit⟩
        | some r => ⟨⟨Equiv.refl W, rfl⟩,
            roundExtractor_mapEquivalences ops claim count (start + 1) (by omega)
              ⟨ops.evaluate stmt.target q r, Fin.snoc stmt.challenges r⟩
              (active && ops.accept stmt.target q)⟩⟩

/-- The carrier at every concrete authored prefix is the retained witness carrier. -/
def prefixWitnessEquiv (ops : MessageOps F M) (claim : ClaimPredicate F n W)
    (count start : ℕ) (finish : start + count = n)
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) (active : Bool)
    (pfx : ExecutionPrefix (protocol ops count).tree) :
    ((roundExtractor ops claim count start finish stmt active).knowledgeState pfx).Witness
      ≃ W :=
  RoundExtractor.extractPrefixEquiv _
    (roundExtractor_mapEquivalences ops claim count start finish stmt active)
    pfx.cursor.spine pfx.messages

omit [CommSemiring F] in
/-- Backward extraction through any actual prefix is the explicit carrier equivalence. -/
theorem extractPrefixWitness_eq (ops : MessageOps F M) (claim : ClaimPredicate F n W)
    (count start : ℕ) (finish : start + count = n)
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) (active : Bool)
    (pfx : ExecutionPrefix (protocol ops count).tree)
    (w : ((roundExtractor ops claim count start finish stmt active).knowledgeState
      pfx).Witness) :
    (roundExtractor ops claim count start finish stmt active).extractPrefixWitness pfx w =
      prefixWitnessEquiv ops claim count start finish stmt active pfx w :=
  (RoundExtractor.extractPrefixEquiv_apply _ _ _ _ _).symm

omit [CommSemiring F] in
/-- Oracle messages preserve the current knowledge predicate under their identity maps. -/
theorem roundExtractor_proverPreserving (ops : MessageOps F M) (claim : ClaimPredicate F n W)
    (count start : ℕ) (finish : start + count = n)
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) (active : Bool) :
    (roundExtractor ops claim count start finish stmt active).IsProverPreserving
      (protocol ops count).roles := by
  induction count generalizing start active with
  | zero => trivial
  | succ count ih =>
    constructor
    · intro q w good
      exact good
    · intro q
      constructor
      · intro choice impossible
        cases impossible
      · intro choice
        cases choice with
        | none => trivial
        | some r => exact ih (start + 1) (by omega) _ _

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
  rel_admissible := by intros; trivial

/-- The extractor's endpoint relation is exactly the optional output evaluation claim. -/
def terminalRelation (ops : MessageOps F M) {m : ℕ} (D : Fin m ↪ F)
    (valid : W → Prop) (summand : W → Spec.OracleStatement F n deg ())
    (count start : ℕ) (finish : start + count = n)
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) (active : Bool) :
    TerminalRelation (roundExtractor ops (claimPredicate D valid summand) count start finish stmt
      active)
      (evaluationProblem valid summand) (fun _ => ())
      (outputClaim ops count start finish stmt active) := by
  induction count generalizing start active with
  | zero =>
    have hn : n = start := by omega
    subst n
    refine ⟨fun _ => Equiv.refl W, ?_⟩
    intro path w
    cases active with
    | false =>
      change (false = true ∧ _) ↔ False
      simp only [Bool.false_eq_true, false_and]
    | true =>
      change (true = true ∧ valid w ∧ _) ↔
        (valid w ∧ (summand w).val.eval stmt.challenges = stmt.target)
      simp only [true_and]
      apply and_congr_right
      intro _
      exact closedRelation_last_iff F start deg D
        ⟨stmt, (polynomialFamily F start deg).behaviorOfRealizations (fun _ => summand w)⟩
  | succ count ih =>
    refine ⟨?_, ?_⟩
    · rintro ⟨q, choice, rest⟩
      cases choice with
      | none => exact Equiv.refl W
      | some r => exact (ih (start + 1) (by omega) _ _).witnessEquiv rest
    · rintro ⟨q, choice, rest⟩ w
      cases choice with
      | none => exact Iff.rfl
      | some r => exact (ih (start + 1) (by omega) _ _).knowledge_iff rest w

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
      ((roundExtractor ops (claimPredicate D valid summand) (count + 1) start finish stmt active
        q).2.2) choice) :
    ¬ closedRelation F n deg D ⟨start, by omega⟩
      ⟨stmt, (polynomialFamily F n deg).behaviorOfRealizations (fun _ => p)⟩ ∧
    ops.accept stmt.target q = true ∧
    ∃ r, choice = some r ∧ closedRelation F n deg D ⟨start + 1, by omega⟩
      ⟨⟨(model.interpret stmt.target q).val.eval r, Fin.snoc stmt.challenges r⟩,
        (polynomialFamily F n deg).behaviorOfRealizations (fun _ => p)⟩ := by
  cases choice with
  | none =>
    obtain ⟨w, _, good⟩ := bad
    exact good.elim
  | some r =>
    obtain ⟨w, notGood, good⟩ := bad
    change (active && ops.accept stmt.target q) = true ∧ valid w ∧ _ at good
    obtain ⟨activeGood, acceptGood⟩ := Bool.and_eq_true_iff.mp good.1
    have bound := binding w good.2.1
    refine ⟨?_, acceptGood, r, rfl, ?_⟩
    · intro related
      apply notGood
      change active = true ∧ valid w ∧ closedRelation F n deg D ⟨start, by omega⟩
        ⟨stmt, (polynomialFamily F n deg).behaviorOfRealizations (fun _ => summand w)⟩
      exact ⟨activeGood, good.2.1, by simpa only [bound] using related⟩
    · simpa only [bound, model.evaluate_eq] using good.2.2

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
        ((roundExtractor ops (claimPredicate D valid summand) (count + 1) start finish stmt
          active q).2.2)
        choice] ≤ (deg : ENNReal) / Fintype.card F := by
  classical
  let extractor :=
    (roundExtractor ops (claimPredicate D valid summand) (count + 1) start finish stmt active q).2.2
  change Pr{let choice ← nextChallenge ops stmt.target q}[
    RoundExtractor.badChallenge extractor choice] ≤ _
  have inclusion := badChallenge_implies_successor ops D model valid summand p binding
    count start finish stmt active q
  by_cases hcheck : ops.accept stmt.target q = true
  · simp only [nextChallenge, hcheck, ↓reduceIte, prEvent_map]
    by_cases hfalse : ¬ closedRelation F n deg D ⟨start, by omega⟩
        ⟨stmt, (polynomialFamily F n deg).behaviorOfRealizations (fun _ => p)⟩
    · have bound := uniform_successor_soundness n deg F D ⟨start, by omega⟩ stmt p
        (model.interpret stmt.target q) hfalse (by
          rw [Finset.sum_map_toList]
          exact (model.accept_iff _ _).mp hcheck)
      refine (prEvent_mono ($ᵗ F) _ _ ?_).trans bound
      intro r bad
      obtain ⟨_, _, r', same, good⟩ := inclusion (some r) bad
      cases Option.some.inj same
      exact good
    · have empty : ∀ r, ¬ RoundExtractor.badChallenge extractor (some r) := by
        intro r bad
        exact hfalse (inclusion (some r) bad).1
      refine (prEvent_mono ($ᵗ F) _ (fun _ => False) (fun r bad => empty r bad)).trans ?_
      simp only [prEvent_false, zero_le]
  · have empty : ¬ RoundExtractor.badChallenge extractor none := by
      intro bad
      exact hcheck (inclusion none bad).2.1
    simp [nextChallenge, hcheck, empty]

/-- Every authored prefix, including unreachable prefixes, satisfies the same local error bound. -/
theorem roundExtractor_locallyBounded (ops : MessageOps F M) {m : ℕ} (D : Fin m ↪ F)
    (model : MessageModel (Finset.univ.map D) ops deg)
    (valid : W → Prop) (summand : W → Spec.OracleStatement F n deg ())
    (p : Spec.OracleStatement F n deg ()) (binding : BindsSummand valid summand p)
    (count start : ℕ) (finish : start + count = n)
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) (active : Bool) :
    (roundExtractor ops (claimPredicate D valid summand) count start finish stmt
      active).IsLocallyBounded
      (protocol ops count).roles (challenges ops deg count stmt.target) := by
  induction count generalizing start active with
  | zero => trivial
  | succ count ih =>
    intro q
    refine ⟨?_, ?_⟩
    · rw [_root_.RoundByRound.GameFamily.isBounded_iff]
      intro _ _
      exact local_badChallenge_le ops D model valid summand p binding
        count start finish stmt active q
    · intro choice
      cases choice with
      | none => trivial
      | some r => exact ih (start + 1) (by omega) _ _

/-- The witness-retaining Sumcheck certificate, conditional on semantic binding of the summand. -/
noncomputable def certificate (ops : MessageOps F M) {m : ℕ} (D : Fin m ↪ F)
    (model : MessageModel (Finset.univ.map D) ops deg)
    (valid : W → Prop) (summand : W → Spec.OracleStatement F n deg ())
    (p : Spec.OracleStatement F n deg ()) (binding : BindsSummand valid summand p)
    (count start : ℕ) (finish : start + count = n)
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) (active : Bool) :
    KnowledgeCertificate (protocol ops count).tree (protocol ops count).roles
      (claimState D valid summand ⟨start, by omega⟩ stmt active) where
  extractor := roundExtractor ops (claimPredicate D valid summand) count start finish stmt active
  challenges := challenges ops deg count stmt.target
  prover_preserving := roundExtractor_proverPreserving ops (claimPredicate D valid summand)
    count start finish stmt active
  local_bound := roundExtractor_locallyBounded ops D model valid summand p binding
    count start finish stmt active

/-- The summand polynomial itself is retained as the witness for a fixed input polynomial. -/
noncomputable def polynomialCertificate (ops : MessageOps F M) {m : ℕ} (D : Fin m ↪ F)
    (model : MessageModel (Finset.univ.map D) ops deg)
    (p : Spec.OracleStatement F n deg ())
    (count start : ℕ) (finish : start + count = n)
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) (active : Bool) :
    KnowledgeCertificate (protocol ops count).tree (protocol ops count).roles
      (claimState D (fun w => w = p) id ⟨start, by omega⟩ stmt active) :=
  certificate ops D model (fun w => w = p) id p (fun _ h => h)
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
