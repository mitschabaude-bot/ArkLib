/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude
-/
module

public import ArkLib.Interaction.Oracle.Security.StateRestoration
public import ArkLib.Interaction.Oracle.Security.KnowledgeAppend
public import VCVio.OracleComp.QueryTracking.CostModel

/-!
# Local errors in state restoration

Each challenge node of a public-coin protocol has its own knowledge error (`Errors`), indexed by
the node: the prover's moves and oracle payloads before it, with the earlier challenges erased.
The errors may depend on the input. `errorSchedule` is the challenge schedule that samples each
challenge uniformly with its node's error. Completion of input `z` pays the errors along its path,
at most the largest path sum `pathError`; an adaptive adversary with at most `Q` queries pays `Q`
times the largest node error over all inputs. Hence the cached restoration experiment has
extraction error at most `Q * maxError errors + sumError errors`
(`restored_extraction_bound`).

A knowledge certificate whose schedule samples every challenge uniformly
(`UniformChallenges`) gives node errors by taking, at each node, the largest error over the
erased earlier challenges (`supErrors`), and its local bound holds for their schedule
(`isLocallyBounded_errorSchedule`). Uniform challenges compose along `PublicCoin.append`
(`uniformChallenges_append`).
-/

@[expose] public section

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec
open Interaction.Oracle.TypeTree

namespace Interaction.Oracle.Security.StateRestoration

universe w

/-- Local knowledge errors at the challenge nodes of a public-coin protocol. -/
abbrev Errors {protocol : Protocol} (coin : PublicCoin protocol) :=
  Prefix PUnit coin → ENNReal

/-- Every challenge is sampled uniformly, with its node's local error. -/
def errorSchedule : {protocol : Protocol} → (coin : PublicCoin protocol) → Errors coin →
    RoundExtractor.ChallengeSchedule protocol.tree protocol.roles
  | _, .done, _ => PUnit.unit
  | _, @PublicCoin.sender _ _ _ next, errors =>
      ⟨PUnit.unit, fun move => errorSchedule (next move) fun q => errors ⟨move, q⟩⟩
  | _, @PublicCoin.oracle _ _ _ _ next, errors =>
      fun message => errorSchedule next fun q => errors ⟨message, q⟩
  | _, @PublicCoin.challenge Challenge _ _ next, errors =>
      ⟨⟨$ᵗ Challenge, errors (.inl PUnit.unit)⟩,
        fun _ => errorSchedule next fun q => errors (.inr ⟨PUnit.unit, q⟩)⟩

/-- The largest sum of node errors along a complete path. -/
noncomputable def pathError : {protocol : Protocol} → (coin : PublicCoin protocol) →
    Errors coin → ENNReal
  | _, .done, _ => 0
  | _, @PublicCoin.sender _ _ _ next, errors => ⨆ move, pathError (next move) fun q => errors
      ⟨move, q⟩
  | _, @PublicCoin.oracle _ _ _ _ next, errors => ⨆ message, pathError next fun q => errors
      ⟨message, q⟩
  | _, @PublicCoin.challenge _ _ _ next, errors =>
      errors (.inl PUnit.unit) + pathError next fun q => errors (.inr ⟨PUnit.unit, q⟩)

/-- The charge of a salted prefix is the error of its node. -/
noncomputable abbrev prefixError {Salt : Type} {protocol : Protocol} {coin : PublicCoin protocol}
    (errors : Errors coin) (pre : Prefix Salt coin) : ENNReal :=
  errors pre.node

section

variable {Input : Type} {protocol : Input → Protocol}

/-- The charge of a restoration key is the error of its input's node. -/
noncomputable abbrev keyError {Salt : Type} {coin : (z : Input) → PublicCoin (protocol z)}
    (errors : (z : Input) → Errors (coin z)) (key : Key Input Salt coin) : ENNReal :=
  prefixError (errors key.1) key.2

/-- The largest node error over all inputs. -/
noncomputable def maxError {coin : (z : Input) → PublicCoin (protocol z)}
    (errors : (z : Input) → Errors (coin z)) : ENNReal :=
  ⨆ z, ⨆ node, errors z node

/-- The largest path sum of errors over all inputs. -/
noncomputable def sumError {coin : (z : Input) → PublicCoin (protocol z)}
    (errors : (z : Input) → Errors (coin z)) : ENNReal :=
  ⨆ z, pathError (coin z) (errors z)

/-- The largest path sum is monotone in the node errors. -/
theorem pathError_mono : {protocol : Protocol} → (coin : PublicCoin protocol) →
    {errors errors' : Errors coin} → (∀ node, errors node ≤ errors' node) →
    pathError coin errors ≤ pathError coin errors'
  | _, .done, _, _, _ => le_rfl
  | _, @PublicCoin.sender _ _ _ next, _, _, h =>
      iSup_mono fun move => pathError_mono (next move) fun node => h ⟨move, node⟩
  | _, @PublicCoin.oracle _ _ _ _ next, _, _, h =>
      iSup_mono fun message => pathError_mono next fun node => h ⟨message, node⟩
  | _, @PublicCoin.challenge _ _ _ next, _, _, h =>
      add_le_add (h (.inl PUnit.unit)) (pathError_mono next fun node => h (.inr ⟨PUnit.unit, node⟩))

/-- The largest node error is monotone in the node errors. -/
theorem maxError_mono {coin : (z : Input) → PublicCoin (protocol z)}
    {errors errors' : (z : Input) → Errors (coin z)} (h : ∀ z node, errors z node ≤ errors' z node) :
    maxError errors ≤ maxError errors' :=
  iSup_mono fun z => iSup_mono fun node => h z node

/-- The largest path sum over all inputs is monotone in the node errors. -/
theorem sumError_mono {coin : (z : Input) → PublicCoin (protocol z)}
    {errors errors' : (z : Input) → Errors (coin z)} (h : ∀ z node, errors z node ≤ errors' z node) :
    sumError errors ≤ sumError errors' :=
  iSup_mono fun z => pathError_mono (coin z) (h z)

/-- Every key charge is bounded by the largest node error. -/
theorem keyError_le_maxError {Salt : Type} {coin : (z : Input) → PublicCoin (protocol z)}
    (errors : (z : Input) → Errors (coin z)) (key : Key Input Salt coin) :
    keyError errors key ≤ maxError errors :=
  (le_iSup (errors key.1) key.2.node).trans (le_iSup (fun z => ⨆ node, errors z node) key.1)

end

/-! ### Errors of alternating rounds -/

/-- A vector of local knowledge errors of alternating rounds, indexed in protocol order. -/
abbrev RoundErrors (rounds : List Round) := Fin rounds.length → ENNReal

/-- The node errors of alternating rounds: each challenge node has its round's error. -/
def roundErrors : (rounds : List Round) → RoundErrors rounds → Errors (Round.coin rounds)
  | [], _ => fun node => nomatch node
  | _ :: rounds, errors => fun node =>
      Sum.casesOn node.2 (fun _ => errors 0) fun later =>
        roundErrors rounds (fun j => errors j.succ) later.2

/-- Each challenge is sampled uniformly with its round's error. -/
abbrev roundErrorSchedule (rounds : List Round) (errors : RoundErrors rounds) :
    RoundExtractor.ChallengeSchedule (protocol rounds).tree (protocol rounds).roles :=
  errorSchedule (Round.coin rounds) (roundErrors rounds errors)

/-- Every node error of alternating rounds is at most the largest round error. -/
theorem roundErrors_le (rounds : List Round) (errors : RoundErrors rounds)
    (node : Prefix PUnit (Round.coin rounds)) :
    roundErrors rounds errors node ≤ Finset.univ.sup errors := by
  induction rounds with
  | nil => exact node.elim
  | cons round rounds ih =>
      rcases node with ⟨message, node⟩
      cases node with
      | inl _ => exact Finset.le_sup (f := errors) (Finset.mem_univ 0)
      | inr later =>
          refine (ih (fun j => errors j.succ) later.2).trans (Finset.sup_le fun j _ => ?_)
          exact Finset.le_sup (f := errors) (Finset.mem_univ j.succ)

/-- The largest path sum of errors of alternating rounds is at most the sum of the round
errors. -/
theorem pathError_roundErrors_le (rounds : List Round) (errors : RoundErrors rounds) :
    pathError (Round.coin rounds) (roundErrors rounds errors) ≤ ∑ j, errors j := by
  induction rounds with
  | nil => simp [pathError, Round.coin]
  | cons round rounds ih =>
      simp only [Round.coin, pathError]
      exact iSup_le fun _ => (add_le_add (le_refl (errors 0)) (ih (fun j => errors j.succ))).trans
        (Fin.sum_univ_succ (n := rounds.length) errors).ge

/-- With one error at every challenge, the largest path sum of alternating rounds is at most the
number of rounds times that error. -/
theorem pathError_const_le (rounds : List Round) (error : ENNReal) :
    pathError (Round.coin rounds) (fun _ => error) ≤ rounds.length * error := by
  induction rounds with
  | nil => simp [pathError, Round.coin]
  | cons round rounds ih =>
      simp only [Round.coin, pathError, List.length_cons, Nat.cast_add, Nat.cast_one]
      exact iSup_le fun _ => (add_le_add (le_refl error) ih).trans (le_of_eq (by ring))

/-- With the same alternating rounds and errors for every input, the largest node error is at
most the largest round error. -/
theorem maxError_roundErrors_le {Input : Type} (rounds : List Round)
    (errors : RoundErrors rounds) :
    maxError (coin := fun _ : Input => Round.coin rounds) (fun _ => roundErrors rounds errors) ≤
      Finset.univ.sup errors :=
  iSup_le fun _ => iSup_le fun node => roundErrors_le rounds errors node

/-- With the same alternating rounds and errors for every input, the largest path sum is at most
the sum of the round errors. -/
theorem sumError_roundErrors_le {Input : Type} (rounds : List Round)
    (errors : RoundErrors rounds) :
    sumError (coin := fun _ : Input => Round.coin rounds) (fun _ => roundErrors rounds errors) ≤
      ∑ j, errors j :=
  iSup_le fun _ => pathError_roundErrors_le rounds errors

/-- All authored-prefix local bounds apply to each prefix's reconstructed pre-challenge state. -/
theorem prefixExtractor_bound {Salt : Type} {protocol : Protocol} (coin : PublicCoin protocol)
    {state : KnowledgeState.{w}} (extractor : RoundExtractor protocol.tree state)
    (errors : Errors coin)
    (bounded : RoundExtractor.IsLocallyBounded extractor protocol.roles
      (errorSchedule coin errors))
    (pre : Prefix Salt coin) (table : PrefixTable Salt coin) :
    Pr{let response ← $ᵗ pre.Challenge}[
      RoundExtractor.badChallenge (prefixExtractor coin extractor pre table).2 response] ≤
      prefixError errors pre := by
  induction coin generalizing state with
  | done => exact pre.elim
  | sender next ih =>
      rcases pre with ⟨move, pre⟩
      exact ih move _ _ (bounded move) pre _
  | oracle next ih =>
      rcases pre with ⟨message, pre⟩
      exact ih _ _ (bounded message) pre _
  | challenge next ih =>
      cases pre with
      | inl _ =>
          exact (_root_.RoundByRound.GameFamily.isBounded_iff _ _).mp bounded.1
            PUnit.unit PUnit.unit
      | inr data =>
          rcases data with ⟨salt, pre⟩
          exact ih _ _ (bounded.2 (table (.inl salt))) pre _

/-- Resampling a key in any background table has bad-event probability at most its error. -/
theorem badKey_resample_bound {Input Salt : Type} {protocol : Input → Protocol}
    {coin : (z : Input) → PublicCoin (protocol z)} [DecidableEq Input] [DecidableEq Salt]
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol z).tree (state z))
    (Z : Set Input) (errors : (z : Input) → Errors (coin z))
    (bounded : ∀ z ∈ Z, RoundExtractor.IsLocallyBounded (extractor z) (protocol z).roles
      (errorSchedule (coin z) (errors z)))
    (key : Key Input Salt coin) (table : Table Input Salt coin) :
    Pr{let response ← $ᵗ key.Challenge}[
      badKey state extractor Z key (Function.update table key response)] ≤
      keyError errors key := by
  simp_rw [badKey_update_iff]
  by_cases hz : key.1 ∈ Z
  · simp only [hz, true_and]
    exact prefixExtractor_bound (coin key.1) (extractor key.1) (errors key.1) (bounded key.1 hz)
      key.2 (Table.fibre table key.1)
  · simp only [hz, false_and]
    simp

/-! ### Costs -/

/-- Simulation keeps every returned value within the original support. -/
theorem simulateQ_support_subset {ι κ : Type}
    {ambient : OracleSpec ι} {source : OracleSpec κ}
    (impl : QueryImpl source (OracleComp ambient)) {α : Type} (program : OracleComp source α) :
    support (simulateQ impl program) ⊆ support program := by
  induction program using OracleComp.inductionOn with
  | pure a =>
      intro value supported
      simp only [simulateQ_pure] at supported
      have same := OracleComp.eq_of_mem_support_pure a supported
      subst value
      simp
  | query_bind q k ih =>
      intro value supported
      simp only [simulateQ_bind, simulateQ_liftM_query] at supported
      obtain ⟨response, _, hs⟩ := OracleComp.mem_support_bind_peel _ _ supported
      exact MonadAttach.mem_support_bind.mpr ⟨response, by simp, ih response hs⟩

/-- A worst-case budget is also a budget for any larger bound. -/
theorem worstCaseCostBound_mono {ι A : Type} {spec : OracleSpec ι} {program : OracleComp spec A}
    {model : CostModel spec ENNReal} {budget larger : ENNReal}
    (bounded : WorstCaseCostBound program model budget) (le : budget ≤ larger) :
    WorstCaseCostBound program model larger := by
  rw [worstCaseCostBound_iff_support_bound] at bounded ⊢
  exact fun result supported => (bounded result supported).trans le

/-- Reindexing charges each query the weight of its image, on every complete execution path. -/
theorem costDist_reindexQuery {D D' A : Type} {R : D → Type} (f : D' → D)
    (weight : D → ENNReal) (program : OracleComp (OracleSpec.ofFn fun q => R (f q)) A) :
    costDist (simulateQ (reindexQuery f) program)
        (⟨weight⟩ : CostModel (OracleSpec.ofFn R) ENNReal) =
      simulateQ (reindexQuery f)
        (costDist program (⟨fun q => weight (f q)⟩ :
          CostModel (OracleSpec.ofFn fun q => R (f q)) ENNReal)) := by
  induction program using OracleComp.inductionOn with
  | pure value => simp [costDist, instrumentedRun]
  | query_bind key next ih =>
      simp only [costDist, instrumentedRun, QueryImpl.withAddCost, QueryImpl.ofLift_eq_id'] at ih
      simp [costDist, instrumentedRun, QueryImpl.withAddCost, reindexQuery, OracleSpec.query,
        WriterT.run_bind, simulateQ_bind, simulateQ_query, bind_assoc, ih]

/-- Reindexing preserves a worst-case budget under the pulled-back weights. -/
theorem worstCaseCostBound_reindexQuery {D D' A : Type} {R : D → Type} (f : D' → D)
    (weight : D → ENNReal) (program : OracleComp (OracleSpec.ofFn fun q => R (f q)) A)
    (budget : ENNReal)
    (bounded : WorstCaseCostBound program (⟨fun q => weight (f q)⟩ :
      CostModel (OracleSpec.ofFn fun q => R (f q)) ENNReal) budget) :
    WorstCaseCostBound (simulateQ (reindexQuery f) program)
      (⟨weight⟩ : CostModel (OracleSpec.ofFn R) ENNReal) budget := by
  rw [worstCaseCostBound_iff_support_bound] at bounded ⊢
  intro result supported
  rw [costDist_reindexQuery] at supported
  exact bounded result (simulateQ_support_subset _ _ supported)

/-- A `Q`-query adversary pays at most `Q` times the largest error on every branch. -/
theorem queryBound_cost {Input Salt A : Type} {protocol : Input → Protocol}
    {coin : (z : Input) → PublicCoin (protocol z)} (errors : (z : Input) → Errors (coin z))
    (program : OracleComp (oracleSpec Input Salt coin) A)
    (Q : Nat) (bounded : IsTotalQueryBound program Q) :
    WorstCaseCostBound program (⟨keyError errors⟩ :
      CostModel (oracleSpec Input Salt coin) ENNReal) (Q * maxError errors) := by
  induction program using OracleComp.inductionOn generalizing Q with
  | pure value => simp
  | query_bind key next ih =>
      rw [isTotalQueryBound_query_bind_iff] at bounded
      apply (worstCaseCostBound_query_bind_iff _ _ _ _).mpr
      intro response result supported
      have tail := ih response (Q - 1) (bounded.2 response) result supported
      calc
        keyError errors key + Multiplicative.toAdd result.2 ≤
            maxError errors + (Q - 1 : Nat) * maxError errors :=
          add_le_add (keyError_le_maxError errors key) tail
        _ = Q * maxError errors := by
          have hQ : Q = (Q - 1) + 1 := by omega
          conv_rhs => rw [hQ]
          rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]

/-- Prefix completion pays one node error per actual access, at most the largest path sum. -/
theorem completePrefix_cost {Salt : Type} {protocol : Protocol} (coin : PublicCoin protocol)
    (errors : Errors coin) (messages : Messages Salt coin) :
    WorstCaseCostBound (completePrefix coin messages)
      (⟨prefixError errors⟩ : CostModel (prefixSpec Salt coin) ENNReal)
      (pathError coin errors) := by
  induction coin with
  | done => simp [completePrefix]
  | sender next ih =>
      rcases messages with ⟨move, messages⟩
      simp only [completePrefix, pathError]
      refine worstCaseCostBound_mono (budget := pathError (next move) (fun q => errors ⟨move, q⟩) +
          0)
        ((worstCaseCostBound_reindexQuery (R := Prefix.Challenge (coin := .sender next))
          (Sigma.mk move) (prefixError errors) _ _ (ih move (fun q => errors ⟨move, q⟩)
              messages)).bind fun _ => (worstCaseCostBound_pure _ _ _).mpr le_rfl) ?_
      rw [add_zero]
      exact le_iSup (fun move => pathError (next move) fun q => errors ⟨move, q⟩) move
  | oracle next ih =>
      rcases messages with ⟨message, messages⟩
      simp only [completePrefix, pathError]
      refine worstCaseCostBound_mono (budget := pathError next (fun q => errors ⟨message, q⟩) + 0)
        ((worstCaseCostBound_reindexQuery (R := Prefix.Challenge (coin := .oracle next))
          (Prod.mk message) (prefixError errors) _ _ (ih (fun q => errors ⟨message, q⟩)
              messages)).bind fun _ => (worstCaseCostBound_pure _ _ _).mpr le_rfl) ?_
      rw [add_zero]
      exact le_iSup (fun message => pathError next fun q => errors ⟨message, q⟩) message
  | challenge next ih =>
      rcases messages with ⟨salt, messages⟩
      simp only [completePrefix, pathError]
      apply (worstCaseCostBound_query_bind_iff _ _ _ _).mpr
      intro challenge result supported
      have combined := (worstCaseCostBound_reindexQuery (R := Prefix.Challenge (coin := .challenge
          next))
        (fun q : Prefix Salt next => Sum.inr ⟨salt, q⟩) (prefixError errors) _ _
        (ih (fun q => errors (.inr ⟨PUnit.unit, q⟩)) messages)).bind
          (k := fun path => (pure ⟨challenge, path⟩ : OracleComp (prefixSpec Salt (.challenge next))
            (Protocol.public .receiver _ fun _ => _).tree.ExecutionPath))
            fun _ => (worstCaseCostBound_pure _ _ _).mpr le_rfl
      rw [add_zero] at combined
      rw [worstCaseCostBound_iff_support_bound] at combined
      exact add_le_add le_rfl (combined result supported)

/-- Completion of input `z` pays at most the largest path sum over all inputs. -/
theorem complete_cost {Input Salt : Type} {protocol : Input → Protocol}
    (coin : (z : Input) → PublicCoin (protocol z)) (errors : (z : Input) → Errors (coin z))
    (z : Input) (messages : Messages Salt (coin z)) :
    WorstCaseCostBound (complete coin z messages)
      (⟨keyError errors⟩ : CostModel (oracleSpec Input Salt coin) ENNReal)
      (sumError errors) :=
  worstCaseCostBound_mono (worstCaseCostBound_reindexQuery (R := Key.Challenge) (Sigma.mk z)
    (keyError errors) _ _ (completePrefix_cost (coin z) (errors z) messages))
      (le_iSup (fun z => pathError (coin z) (errors z)) z)

/-- Adversary and completion budgets add in the same actual restoration oracle program. -/
theorem restoredExecution_cost {Input Salt W : Type} {protocol : Input → Protocol}
    (coin : (z : Input) → PublicCoin (protocol z)) (errors : (z : Input) → Errors (coin z))
    (adversary : OracleComp (oracleSpec Input Salt coin) (Selection Input Salt W coin))
    (Q : Nat) (bounded : IsTotalQueryBound adversary Q) :
    WorstCaseCostBound (restoredExecution coin adversary)
      (⟨keyError errors⟩ : CostModel (oracleSpec Input Salt coin) ENNReal)
      (Q * maxError errors + sumError errors) := by
  apply (queryBound_cost errors adversary Q bounded).bind
  rintro ⟨z, messages, witness⟩
  have completed := (complete_cost coin errors z messages).bind
    (fun path => show WorstCaseCostBound (pure (⟨z, path, witness⟩ : Outcome Input W protocol))
      (⟨keyError errors⟩ : CostModel (oracleSpec Input Salt coin) ENNReal) 0 from by simp)
  simpa only [add_zero] using completed

/-- Per-node knowledge errors imply the `Q * max + sum` extraction bound in the actual cached
restoration experiment: the completed path has a valid terminal witness whose backward extraction
fails with probability at most `Q * maxError errors + sumError errors`. Inputs may be adaptive and
keys may be queried out of order or repeatedly. The sum budget is proved for completion, rather
than assumed independent of earlier accesses. -/
theorem restored_extraction_bound {Input Salt W : Type} {protocol : Input → Protocol}
    {coin : (z : Input) → PublicCoin (protocol z)} [DecidableEq Input] [DecidableEq Salt]
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol z).tree (state z))
    (Z : Set Input) (errors : (z : Input) → Errors (coin z))
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol z).roles)
    (bounded : ∀ z ∈ Z, RoundExtractor.IsLocallyBounded (extractor z) (protocol z).roles
      (errorSchedule (coin z) (errors z)))
    (adversary : OracleComp (oracleSpec Input Salt coin) (Selection Input Salt W coin))
    (Q : ℕ) (queryBound : IsTotalQueryBound adversary Q) :
    Pr{let result ← (simulateQ randomOracle (restoredExecution coin adversary)).run' ∅}[
      result.1 ∈ Z ∧ ∃ witness, ((extractor result.1).terminalState result.2.1).holds witness ∧
        ¬ (state result.1).holds ((extractor result.1).extractWitness result.2.1 witness)] ≤
      Q * maxError errors + sumError errors := by
  apply prEvent_randomOracle_le_of_bad_queries_weighted _ (keyError errors) _
    (restoredExecution_cost coin errors adversary Q queryBound) _
    (badKey state extractor Z)
  · exact badKey_resample_bound state extractor Z errors bounded
  · exact restored_bad_trace state extractor Z preserving adversary

/-! ### Errors of a knowledge certificate -/

/-- Every challenge of a schedule is sampled uniformly. -/
def UniformChallenges : {protocol : Protocol} → (coin : PublicCoin protocol) →
    RoundExtractor.ChallengeSchedule protocol.tree protocol.roles → Prop
  | _, .done, _ => True
  | _, @PublicCoin.sender _ _ _ next, schedule => ∀ move, UniformChallenges (next move) (schedule.2
      move)
  | _, @PublicCoin.oracle _ _ _ _ next, schedule => ∀ message, UniformChallenges next (schedule
      message)
  | _, @PublicCoin.challenge Challenge _ _ next, schedule =>
      schedule.1.1 = $ᵗ Challenge ∧ ∀ challenge, UniformChallenges next (schedule.2 challenge)

/-- Uniform challenges compose along `PublicCoin.append`: the schedule of
`KnowledgeCertificate.append` is uniform when both stages are, for a suffix selected by the
prover's public moves alone. -/
theorem uniformChallenges_append : {protocol : Protocol} → (coin : PublicCoin protocol) →
    {suffix : coin.ErasedBranch → Protocol} →
    (second : (branch : coin.ErasedBranch) → PublicCoin (suffix branch)) →
    (first : RoundExtractor.ChallengeSchedule protocol.tree protocol.roles) →
    (rest : (path : protocol.tree.ExecutionPath) → RoundExtractor.ChallengeSchedule
      (suffix (coin.eraseBranch path.toBranchPath)).tree
      (suffix (coin.eraseBranch path.toBranchPath)).roles) →
    UniformChallenges coin first →
    (∀ path, UniformChallenges (second (coin.eraseBranch path.toBranchPath)) (rest path)) →
    UniformChallenges (coin.append second)
      (RoundExtractor.appendSchedule (fun path => (suffix (coin.eraseBranch path)).tree)
        protocol.roles (fun path => (suffix (coin.eraseBranch path)).roles) first rest)
  | _, .done, _, _, _, _, _, hrest => hrest PUnit.unit
  | _, @PublicCoin.sender _ _ _ next, _, second, first, rest, hfirst, hrest => fun move =>
      uniformChallenges_append (next move) (fun branch => second ⟨move, branch⟩) (first.2 move)
        (fun path => rest ⟨move, path⟩) (hfirst move) fun path => hrest ⟨move, path⟩
  | _, @PublicCoin.oracle _ _ _ _ next, _, second, first, rest, hfirst, hrest => fun message =>
      uniformChallenges_append next second (first message)
        (fun path => rest ⟨message, path⟩) (hfirst message) fun path => hrest ⟨message, path⟩
  | _, @PublicCoin.challenge _ _ _ next, _, second, first, rest, hfirst, hrest =>
      ⟨hfirst.1, fun challenge => uniformChallenges_append next second (first.2 challenge)
        (fun path => rest ⟨challenge, path⟩) (hfirst.2 challenge)
        fun path => hrest ⟨challenge, path⟩⟩

/-- The error of a schedule at each node: its largest error over the erased earlier
challenges. -/
noncomputable def supErrors : {protocol : Protocol} → (coin : PublicCoin protocol) →
    RoundExtractor.ChallengeSchedule protocol.tree protocol.roles → Errors coin
  | _, .done, _, node => nomatch node
  | _, @PublicCoin.sender _ _ _ next, schedule, ⟨move, node⟩ => supErrors (next move) (schedule.2
      move) node
  | _, @PublicCoin.oracle _ _ _ _ next, schedule, ⟨message, node⟩ => supErrors next (schedule
      message) node
  | _, @PublicCoin.challenge _ _ _ _, schedule, .inl _ => schedule.1.2
  | _, @PublicCoin.challenge _ _ _ next, schedule, .inr ⟨_, node⟩ =>
      ⨆ challenge, supErrors next (schedule.2 challenge) node

/-- A local bound for a uniform schedule holds for any node errors above its own. -/
theorem isLocallyBounded_errorSchedule {protocol : Protocol} (coin : PublicCoin protocol)
    {state : KnowledgeState.{w}} (extractor : RoundExtractor protocol.tree state)
    (schedule : RoundExtractor.ChallengeSchedule protocol.tree protocol.roles)
    (uniform : UniformChallenges coin schedule)
    (bounded : extractor.IsLocallyBounded protocol.roles schedule)
    (errors : Errors coin) (le : ∀ node, supErrors coin schedule node ≤ errors node) :
    extractor.IsLocallyBounded protocol.roles (errorSchedule coin errors) := by
  induction coin generalizing state with
  | done => trivial
  | sender next ih =>
      exact fun move => ih move _ _ (uniform move) (bounded move) _ fun node => le ⟨move, node⟩
  | oracle next ih =>
      exact fun message => ih _ _ (uniform message) (bounded message) _
        fun node => le ⟨message, node⟩
  | challenge next ih =>
      refine ⟨?_, fun challenge => ih _ _ (uniform.2 challenge) (bounded.2 challenge) _
        fun node => (le_iSup (fun challenge => supErrors next (schedule.2 challenge) node)
          challenge).trans (le (.inr ⟨PUnit.unit, node⟩))⟩
      have here := bounded.1
      rw [_root_.RoundByRound.GameFamily.isBounded_iff] at here ⊢
      intro round context
      have h := here round context
      rw [uniform.1] at h
      exact h.trans (le (.inl PUnit.unit))

end Interaction.Oracle.Security.StateRestoration
