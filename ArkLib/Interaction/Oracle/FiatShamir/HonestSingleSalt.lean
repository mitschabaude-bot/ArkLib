/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude
-/
module

public import ArkLib.Interaction.Oracle.FiatShamir.SingleSaltSecurity

/-!
# Honest private-coin provers for a single global Fiat–Shamir salt

An honest prover is a native strategy for the public protocol of its statement, with access only
to private uniform sampling. Its continuation may depend on each preceding public challenge. The
compiler below samples a single global salt before running that strategy, and hashes the key of
`(statement, salt)` and the full message prefix of a challenge only after its guard passes.
-/

@[expose] public section

open Interaction.Oracle OracleComp OracleSpec

namespace Interaction.Oracle.FiatShamir

open Security.StateRestoration

/-- A native honest public-message prover, with only private sampling as an ambient effect. -/
abbrev HonestProver {protocol : Protocol} (coin : PublicCoin protocol) :=
  Prover.Strategy unifSpec (publicProtocol coin).tree (publicProtocol coin).roles (fun _ => Unit)

/-- The prover's moves and messages along a path, with the unit salt at each challenge. -/
def pathMessages : {protocol : Protocol} → (coin : PublicCoin protocol) →
    protocol.tree.ExecutionPath → Messages PUnit coin
  | _, .done, _ => PUnit.unit
  | _, @PublicCoin.sender _ _ _ next, path => ⟨path.1, pathMessages (next path.1) path.2⟩
  | _, @PublicCoin.oracle _ _ _ _ next, path => ⟨path.1, pathMessages next path.2⟩
  | _, @PublicCoin.challenge _ _ _ _ _ next, path => ⟨PUnit.unit, pathMessages next path.2⟩

/-- The interactive uniform-challenge run of an adaptive honest strategy. A failed prefix guard
stops before sampling the current challenge. The result is the complete accepted path. -/
def honestInteractiveRun : {protocol : Protocol} → (coin : PublicCoin protocol) →
    GuardSchedule PUnit coin → HonestProver coin → ProbComp (Option protocol.tree.ExecutionPath)
  | _, .done, _, _ => pure (some PUnit.unit)
  | _, @PublicCoin.sender _ _ _ next, guards, prover => do
      let chosen ← prover
      let suffix ← honestInteractiveRun (next chosen.1) (guards chosen.1) chosen.2
      return suffix.map fun path => ⟨chosen.1, path⟩
  | _, @PublicCoin.oracle _ _ _ _ next, guards, prover => do
      let chosen ← prover
      let suffix ← honestInteractiveRun next (guards chosen.1) chosen.2
      return suffix.map fun path => ⟨chosen.1, path⟩
  | _, @PublicCoin.challenge Challenge _ _ _ _ next, guards, prover => do
      if !guards.1 PUnit.unit then
        return none
      let challenge ← $ᵗ Challenge
      let continuation ← prover challenge
      let suffix ← honestInteractiveRun next (guards.2 PUnit.unit challenge) continuation
      return suffix.map fun path => ⟨challenge, path⟩

/-- Adapt an unguarded private-coin strategy to the actual guarded public tree. A rejected
challenge has no prover continuation; a passed challenge keeps the private response action. -/
def guardedHonestProver : {protocol : Protocol} → (coin : PublicCoin protocol) →
    (guards : GuardSchedule PUnit coin) → HonestProver coin →
    Prover.Strategy unifSpec (guardedPublicProtocol coin guards).tree
      (guardedPublicProtocol coin guards).roles (fun _ => Unit)
  | _, .done, _, _ => ()
  | _, @PublicCoin.sender _ _ _ next, guards, prover =>
      do
        let chosen ← prover
        pure ⟨chosen.1, guardedHonestProver (next chosen.1) (guards chosen.1) chosen.2⟩
  | _, @PublicCoin.oracle _ _ _ _ next, guards, prover =>
      do
        let chosen ← prover
        pure ⟨chosen.1, guardedHonestProver next (guards chosen.1) chosen.2⟩
  | _, @PublicCoin.challenge Challenge _ _ _ _ next, guards, prover =>
      let after : (pass : Bool) → Prover.Strategy unifSpec
          (guardedChallenge Challenge (fun challenge =>
            guardedPublicProtocol next (guards.2 PUnit.unit challenge)) pass).tree
          (guardedChallenge Challenge (fun challenge =>
            guardedPublicProtocol next (guards.2 PUnit.unit challenge)) pass).roles
          (fun _ => Unit)
        | false => ()
        | true => fun challenge =>
            guardedHonestProver next (guards.2 PUnit.unit challenge) <$> prover challenge
      after (guards.1 PUnit.unit)

/-- The native interactive verifier samples each reached public challenge uniformly. -/
def honestUniformVerifier : {protocol : Protocol} → (coin : PublicCoin protocol) →
    (guards : GuardSchedule PUnit coin) →
    Verifier.Strategy unifSpec (guardedPublicProtocol coin guards).tree
      (guardedPublicProtocol coin guards).roles
      (guardedPublicProtocol coin guards).oracles 0 (fun _ => Unit)
  | _, .done, _ => pure ()
  | _, @PublicCoin.sender _ _ _ next, guards => fun move =>
      pure (honestUniformVerifier (next move) (guards move))
  | _, @PublicCoin.oracle _ _ _ _ next, guards => fun message =>
      pure (honestUniformVerifier next (guards message))
  | _, @PublicCoin.challenge Challenge _ _ _ _ next, guards =>
      let after : (pass : Bool) → Verifier.Strategy unifSpec
          (guardedChallenge Challenge (fun challenge =>
            guardedPublicProtocol next (guards.2 PUnit.unit challenge)) pass).tree
          (guardedChallenge Challenge (fun challenge =>
            guardedPublicProtocol next (guards.2 PUnit.unit challenge)) pass).roles
          (guardedChallenge Challenge (fun challenge =>
            guardedPublicProtocol next (guards.2 PUnit.unit challenge)) pass).oracles 0
          (fun _ => Unit)
        | false => pure ()
        | true => do
            let challenge ← liftComp ($ᵗ Challenge) (unifSpec + ofPFunctor 0)
            pure ⟨challenge, honestUniformVerifier next (guards.2 PUnit.unit challenge)⟩
      after (guards.1 PUnit.unit)

/-- The existing native paired strategy executor for the guarded interactive protocol. -/
def honestNativeInteractiveRun {protocol : Protocol} (coin : PublicCoin protocol)
    (guards : GuardSchedule PUnit coin) (prover : HonestProver coin) :
    ProbComp (Option protocol.tree.ExecutionPath) :=
  (fun result => acceptedPath coin guards result.1) <$>
    executeStrategies unifSpec (guardedPublicProtocol coin guards).tree
      (guardedPublicProtocol coin guards).roles
      (guardedPublicProtocol coin guards).oracles 0
      (fun q => nomatch q)
      (guardedHonestProver coin guards prover)
      (honestUniformVerifier coin guards)

private theorem honestUniformSample (Challenge : Type) [SampleableType Challenge] :
    simulateQ (Verifier.liftAccessImpl unifSpec 0 (fun q => nomatch q))
      (liftComp ($ᵗ Challenge) (unifSpec + ofPFunctor 0)) =
    ($ᵗ Challenge : ProbComp Challenge) := by
  rw [QueryImpl.simulateQ_liftComp_left_eq_of_apply
    (Verifier.liftAccessImpl unifSpec 0 (fun q => nomatch q))
    (QueryImpl.id' unifSpec) (by intro q; rfl) ($ᵗ Challenge)]
  exact simulateQ_id' _

set_option backward.isDefEq.respectTransparency false in
/-- The direct uniform-challenge interpreter is exactly the accepted-path projection of the
actual native guarded public strategy executor, for arbitrary adaptive private continuations. -/
theorem honestNativeInteractiveRun_eq {protocol : Protocol} (coin : PublicCoin protocol)
    (guards : GuardSchedule PUnit coin) (prover : HonestProver coin) :
    honestNativeInteractiveRun coin guards prover = honestInteractiveRun coin guards prover := by
  induction coin with
  | done =>
      unfold honestNativeInteractiveRun
      simp only [guardedPublicProtocol, Protocol.done_tree, Protocol.done_roles,
        Protocol.done_oracles]
      rw [executeStrategies_done]
      simp [honestInteractiveRun, guardedHonestProver, honestUniformVerifier, acceptedPath]
  | sender next ih =>
      unfold honestNativeInteractiveRun
      simp only [guardedPublicProtocol, Protocol.public_tree, Protocol.public_roles,
        Protocol.public_oracles]
      rw [executeStrategies_public_sender]
      simp only [guardedHonestProver, honestUniformVerifier, acceptedPath, honestInteractiveRun,
        simulateQ_pure, pure_bind, map_bind, bind_pure_comp, Functor.map_map, bind_map_left]
      apply bind_congr
      intro chosen
      rw [← ih]
      simp only [honestNativeInteractiveRun, Functor.map_map]
  | oracle next ih =>
      unfold honestNativeInteractiveRun
      simp only [guardedPublicProtocol, Protocol.public_tree, Protocol.public_roles,
        Protocol.public_oracles]
      rw [executeStrategies_public_sender]
      simp only [guardedHonestProver, honestUniformVerifier, acceptedPath, honestInteractiveRun,
        simulateQ_pure, pure_bind, map_bind, bind_pure_comp, Functor.map_map, bind_map_left]
      apply bind_congr
      intro chosen
      rw [← ih]
      simp only [honestNativeInteractiveRun, Functor.map_map]
  | @challenge Challenge _ _ _ rest next ih =>
      unfold honestNativeInteractiveRun
      simp only [guardedPublicProtocol, guardedHonestProver, honestUniformVerifier, acceptedPath,
        honestInteractiveRun]
      generalize guards.1 PUnit.unit = pass
      cases pass with
      | false => simp [guardedChallenge, decodeAfterGuard, executeStrategies_done]
      | true =>
          simp only [guardedChallenge, Protocol.public_tree, Protocol.public_roles,
            Protocol.public_oracles]
          rw [executeStrategies_public_receiver]
          simp only [simulateQ_bind, simulateQ_pure, Bool.not_true, Bool.false_eq_true,
            ite_false]
          rw [honestUniformSample Challenge]
          simp only [map_bind, bind_pure_comp, Functor.map_map, bind_map_left]
          apply bind_congr
          intro challenge
          apply bind_congr
          intro continuation
          rw [← ih]
          simp only [honestNativeInteractiveRun, Functor.map_map]
          rfl

/-- Compile the same adaptive strategy to the native lazy challenge oracle. The embedding
remembers the already-sent prefix when this definition recurses on a suffix. -/
def honestCompiledRun {Input : Type} {allProtocol : Input → Protocol}
    {allCoin : (z : Input) → PublicCoin (allProtocol z)} :
    {protocol : Protocol} → (coin : PublicCoin protocol) → GuardSchedule PUnit coin →
    HonestProver coin →
    (embed : Prefix PUnit coin → Key Input PUnit allCoin) →
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) →
    OracleComp (unifSpec + oracleSpec Input PUnit allCoin) (Option protocol.tree.ExecutionPath)
  | _, .done, _, _, _, _ => pure (some PUnit.unit)
  | _, @PublicCoin.sender _ _ _ next, guards, prover, embed, preserve => do
      let chosen ← liftM prover
      let suffix ← honestCompiledRun (next chosen.1) (guards chosen.1) chosen.2
        (fun key => embed ⟨chosen.1, key⟩) fun key => preserve ⟨chosen.1, key⟩
      return suffix.map fun path => ⟨chosen.1, path⟩
  | _, @PublicCoin.oracle _ _ _ _ next, guards, prover, embed, preserve => do
      let chosen ← liftM prover
      let suffix ← honestCompiledRun next (guards chosen.1) chosen.2
        (fun key => embed ⟨chosen.1, key⟩) fun key => preserve ⟨chosen.1, key⟩
      return suffix.map fun path => ⟨chosen.1, path⟩
  | _, @PublicCoin.challenge Challenge _ _ _ _ next, guards, prover, embed, preserve => do
      if !guards.1 PUnit.unit then
        return none
      let response ← liftM ((unifSpec + oracleSpec Input PUnit allCoin).query
        (.inr (embed (.inl PUnit.unit))))
      let challenge : Challenge := cast (preserve (.inl PUnit.unit)) response
      let continuation ← liftM (prover challenge)
      let suffix ← honestCompiledRun next (guards.2 PUnit.unit challenge) continuation
        (fun key => embed (.inr ⟨PUnit.unit, key⟩)) fun key => preserve (.inr ⟨PUnit.unit, key⟩)
      return suffix.map fun path => ⟨challenge, path⟩

/-- No key in the still-unplayed suffix has been queried. -/
def HonestCacheFresh {Input : Type} {allProtocol : Input → Protocol}
    {allCoin : (z : Input) → PublicCoin (allProtocol z)} {protocol : Protocol}
    {coin : PublicCoin protocol}
    (cache : (oracleSpec Input PUnit allCoin).QueryCache)
    (embed : Prefix PUnit coin → Key Input PUnit allCoin) : Prop :=
  ∀ key, cache (embed key) = none

/-- Uniform sampling commutes with the answer-type transport of this key embedding. This is
automatic for the concrete identity and prefix constructors used by the compiler. -/
def HonestSamplePreserving {Input : Type} {allProtocol : Input → Protocol}
    {allCoin : (z : Input) → PublicCoin (allProtocol z)} {protocol : Protocol}
    {coin : PublicCoin protocol}
    (embed : Prefix PUnit coin → Key Input PUnit allCoin)
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) : Prop :=
  ∀ key, (cast (preserve key)) <$> ($ᵗ (embed key).Challenge : ProbComp _) =
    ($ᵗ key.Challenge : ProbComp _)

/-- The prefixes of input `z`'s protocol embed injectively into the restoration keys. -/
theorem honestEmbed_injective {Input : Type} {protocol : Input → Protocol}
    (coin : (z : Input) → PublicCoin (protocol z)) (z : Input) :
    Function.Injective (fun pre : Prefix PUnit (coin z) => (⟨z, pre⟩ : Key Input PUnit coin)) :=
  fun _ _ h => eq_of_heq (Sigma.mk.inj h).2

theorem honestSamplePreserving_mk {Input : Type} {protocol : Input → Protocol}
    (coin : (z : Input) → PublicCoin (protocol z)) (z : Input) :
    HonestSamplePreserving (allCoin := coin) (fun pre => ⟨z, pre⟩) (fun _ => rfl) := by
  intro pre
  change (cast (rfl : pre.Challenge = pre.Challenge)) <$> ($ᵗ pre.Challenge) =
    ($ᵗ pre.Challenge : ProbComp _)
  have hcast : (cast (rfl : pre.Challenge = pre.Challenge)) =
      (id : pre.Challenge → pre.Challenge) := by
    funext x
    exact cast_eq _ x
  rw [hcast, id_map]

private theorem map_run_fst {S A B : Type} (f : A → B)
    (st : StateT S ProbComp A) (s : S) :
    (fun result => f result.1) <$> st.run s = f <$> st.run' s := by
  simp only [StateT.run'_eq, Functor.map_map]

private theorem bind_cast_sample {A B C : Type} (h : A = B)
    (sample : ProbComp A) (continuation : A → ProbComp C) :
    (sample >>= continuation) =
      ((cast h) <$> sample) >>= fun b => continuation (cast h.symm b) := by
  cases h
  have hcast : (cast (rfl : A = A)) = (id : A → A) := by
    funext x
    exact cast_eq _ x
  simp only [hcast, id_map, id_eq]

private theorem cast_symm_cast {A B : Type} (h : A = B) (b : B) :
    cast h (cast h.symm b) = b := by
  cases h
  calc
    cast (rfl : A = A) (cast (rfl : A = A) b) = cast (rfl : A = A) b := by
      exact congrArg (cast (rfl : A = A)) (cast_eq (rfl : A = A) b)
    _ = b := cast_eq _ b

private theorem cast_cast_symm {A B : Type} (h : A = B) (a : A) :
    cast h.symm (cast h a) = a := by
  cases h
  exact (cast_eq _ (cast (rfl : A = A) a)).trans (cast_eq _ a)

set_option backward.isDefEq.respectTransparency false in
/-- A cache that has no remaining suffix key makes each compiled hash answer an independent
uniform challenge. This equality includes all adaptive private continuation sampling. -/
theorem honestCompiledRun_eq_interactive {Input : Type} [DecidableEq Input]
    {allProtocol : Input → Protocol} {allCoin : (z : Input) → PublicCoin (allProtocol z)}
    {protocol : Protocol} (coin : PublicCoin protocol)
    (guards : GuardSchedule PUnit coin) (prover : HonestProver coin)
    (embed : Prefix PUnit coin → Key Input PUnit allCoin)
    (preserve : ∀ key, (embed key).Challenge = key.Challenge)
    (injective : Function.Injective embed)
    (sampleLaw : HonestSamplePreserving embed preserve)
    (cache : (oracleSpec Input PUnit allCoin).QueryCache)
    (fresh : HonestCacheFresh cache embed) :
    (simulateQ (oracleSpec Input PUnit allCoin).romImpl
      (honestCompiledRun coin guards prover embed preserve)).run' cache =
    honestInteractiveRun coin guards prover := by
  induction coin generalizing cache with
  | done => simp [honestCompiledRun, honestInteractiveRun]
  | @sender Moves _ rest next ih =>
      simp only [honestCompiledRun, honestInteractiveRun, simulateQ_bind]
      rw [roSim.run'_liftM_bind (hashSpec := oracleSpec Input PUnit allCoin)
        (ro := (oracleSpec Input PUnit allCoin).randomOracle) prover]
      apply bind_congr
      intro chosen
      have hinj : Function.Injective (fun key => embed ⟨chosen.1, key⟩) := fun x y hxy =>
        eq_of_heq (Sigma.mk.inj (injective hxy)).2
      rw [← ih chosen.1 (guards chosen.1) chosen.2 (fun key => embed ⟨chosen.1, key⟩)
        (fun key => preserve ⟨chosen.1, key⟩) hinj (fun key => sampleLaw ⟨chosen.1, key⟩) cache
        (fun key => fresh ⟨chosen.1, key⟩)]
      simp only [simulateQ_pure, StateT.run'_eq, bind_pure_comp, Functor.map_map,
        StateT.run_map]
  | oracle next ih =>
      simp only [honestCompiledRun, honestInteractiveRun, simulateQ_bind]
      rw [roSim.run'_liftM_bind (hashSpec := oracleSpec Input PUnit allCoin)
        (ro := (oracleSpec Input PUnit allCoin).randomOracle) prover]
      apply bind_congr
      intro chosen
      have hinj : Function.Injective (fun key => embed ⟨chosen.1, key⟩) := fun x y hxy =>
        (Prod.mk.inj (injective hxy)).2
      rw [← ih (guards chosen.1) chosen.2 (fun key => embed ⟨chosen.1, key⟩)
        (fun key => preserve ⟨chosen.1, key⟩) hinj (fun key => sampleLaw ⟨chosen.1, key⟩) cache
        (fun key => fresh ⟨chosen.1, key⟩)]
      simp only [simulateQ_pure, StateT.run'_eq, bind_pure_comp, Functor.map_map,
        StateT.run_map]
  | challenge next ih =>
      simp only [honestCompiledRun, honestInteractiveRun]
      cases hguard : guards.1 PUnit.unit with
      | false => simp
      | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ite_false]
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
            OracleQuery.input_query, id_map]
          simp only [simulateQ_pure, StateT.run'_bind', StateT.run'_pure']
          simp only [OracleSpec.romImpl_apply_inr, randomOracle.run_eq,
            fresh (.inl PUnit.unit)]
          simp only [bind_assoc, pure_bind]
          simp only [roSim.run_liftM, bind_map_left]
          simp only [bind_pure_comp]
          simp_rw [map_run_fst]
          rw [bind_cast_sample (preserve (.inl PUnit.unit))]
          rw [sampleLaw (.inl PUnit.unit)]
          simp only [cast_symm_cast]
          apply bind_congr
          intro challenge
          have harg : cast (preserve (.inl PUnit.unit))
              (cast (preserve (.inl PUnit.unit)).symm challenge) = challenge :=
            cast_symm_cast _ _
          erw [harg]
          apply bind_congr
          intro continuation
          have hinj : Function.Injective
              (fun key => embed (.inr ⟨PUnit.unit, key⟩)) := by
            intro x y hxy
            exact congrArg (fun data => data.2) (Sum.inr.inj (injective hxy))
          have hfresh : HonestCacheFresh
              (cache.cacheQuery (embed (.inl PUnit.unit))
                (cast (preserve (.inl PUnit.unit)).symm challenge))
              (fun key => embed (.inr ⟨PUnit.unit, key⟩)) := by
            intro key
            have hne : embed (.inr ⟨PUnit.unit, key⟩) ≠ embed (.inl PUnit.unit) := by
              intro h
              cases injective h
            rw [QueryCache.cacheQuery_of_ne _ _ hne]
            exact fresh _
          rw [ih (guards.2 PUnit.unit challenge) continuation
            (fun key => embed (.inr ⟨PUnit.unit, key⟩))
            (fun key => preserve (.inr ⟨PUnit.unit, key⟩)) hinj
            (fun key => sampleLaw (.inr ⟨PUnit.unit, key⟩)) _ hfresh]

/-- Draw a salt independently, then compile a private-coin strategy to a complete proof. The
selected proof is emitted only if every reached guard passed. -/
def honestSingleSaltAdversary {Statement GlobalSalt Witness : Type} {protocol : Statement → Protocol}
    [SampleableType GlobalSalt] (coin : (statement : Statement) → PublicCoin (protocol statement))
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (coin z.1))
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver (coin statement)) :
    SingleSaltAdversary Statement GlobalSalt Witness coin := do
  let salt ← liftM (($ᵗ GlobalSalt) : ProbComp GlobalSalt)
  let selected ← honestCompiledRun (coin statement) (guards (statement, salt)) (prover salt)
    (fun pre => ⟨(statement, salt), pre⟩) (fun _ => rfl)
  return selected.map fun path => ⟨statement, (salt, pathMessages (coin statement) path), witness⟩

/-- Uniform interactive challenges with the same independent salt and terminal check. This is
the observation compared with the accepted native-verifier output. -/
def honestInteractiveAccepted {Statement GlobalSalt Witness : Type} {protocol : Statement → Protocol}
    [SampleableType GlobalSalt] (coin : (statement : Statement) → PublicCoin (protocol statement))
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (coin z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol z.1).tree.ExecutionPath →
      Bool)
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver (coin statement)) :
    ProbComp
      (Option (Outcome (Statement × GlobalSalt) Witness (saltedProtocol GlobalSalt protocol))) := do
  let salt ← $ᵗ GlobalSalt
  let result ← honestInteractiveRun (coin statement) (guards (statement, salt))
    (prover salt)
  return (result.map fun path => ⟨(statement, salt), path, witness⟩).filter
    (fun selected => accepts selected.1 selected.2.1)

/-- The honest source endpoint uses the actual guarded public strategy executor and a pure
terminal acceptance predicate. The strategy is selected after the independent salt draw. -/
def honestNativeInteractiveAccepted {Statement GlobalSalt Witness : Type} {protocol : Statement → Protocol}
    [SampleableType GlobalSalt] (coin : (statement : Statement) → PublicCoin (protocol statement))
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (coin z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol z.1).tree.ExecutionPath →
      Bool)
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver (coin statement)) :
    ProbComp
      (Option (Outcome (Statement × GlobalSalt) Witness (saltedProtocol GlobalSalt protocol))) := do
  let salt ← $ᵗ GlobalSalt
  let path ← honestNativeInteractiveRun (coin statement) (guards (statement, salt))
    (prover salt)
  return (path.map fun transcript => ⟨(statement, salt), transcript, witness⟩).filter
    (fun selected => accepts selected.1 selected.2.1)

/-- The direct interactive interpreter and the actual guarded native source have exactly the
same accepted-output distribution for salt-aware adaptive private-coin provers. -/
theorem honestNativeInteractiveAccepted_eq
    {Statement GlobalSalt Witness : Type} {protocol : Statement → Protocol}
    [SampleableType GlobalSalt] (coin : (statement : Statement) → PublicCoin (protocol statement))
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (coin z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol z.1).tree.ExecutionPath →
      Bool)
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver (coin statement)) :
    honestNativeInteractiveAccepted coin guards accepts statement witness prover =
      honestInteractiveAccepted coin guards accepts statement witness prover := by
  unfold honestNativeInteractiveAccepted honestInteractiveAccepted
  simp only [honestNativeInteractiveRun_eq]

/-- The actual accepted native execution of the compiled honest prover. Verification reruns
the guarded public strategy against the same lazy challenge oracle. -/
def honestSingleSaltAccepted {Statement GlobalSalt Witness : Type} {protocol : Statement → Protocol}
    [SampleableType GlobalSalt] (coin : (statement : Statement) → PublicCoin (protocol statement))
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (coin z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol z.1).tree.ExecutionPath →
      Bool)
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver (coin statement)) :=
  singleSaltAcceptedExecution coin guards accepts
    (honestSingleSaltAdversary coin guards statement witness prover)


/-- With an initially empty oracle cache, the compiler's complete path has exactly the interactive uniform-challenge distribution. Ordered hash logs are projected
away; private sampling remains inside the same `ProbComp`. -/
theorem honestCompiledRun_empty_eq_interactive {Input : Type} [DecidableEq Input]
    {protocol : Input → Protocol} (coin : (z : Input) → PublicCoin (protocol z))
    (guards : (z : Input) → GuardSchedule PUnit (coin z))
    (z : Input) (prover : HonestProver (coin z)) :
    (fun result => result.1.1) <$>
      randomOracleLoggedRun (honestCompiledRun (allCoin := coin) (coin z) (guards z) prover
        (fun pre => ⟨z, pre⟩) (fun _ => rfl)) ∅ =
    honestInteractiveRun (coin z) (guards z) prover := by
  have hproj := randomOracleLoggedRun_project
    (honestCompiledRun (allCoin := coin) (coin z) (guards z) prover
      (fun pre => ⟨z, pre⟩) (fun _ => rfl))
    (∅ : (oracleSpec Input PUnit coin).QueryCache)
  have hresult := congrArg (fun computation => Prod.fst <$> computation) hproj
  simp only [Functor.map_map] at hresult
  have hfresh : HonestCacheFresh
      (∅ : (oracleSpec Input PUnit coin).QueryCache) (fun pre => ⟨z, pre⟩) := by
    intro key
    rfl
  simpa only [Function.comp_def] using hresult.trans
    (honestCompiledRun_eq_interactive (coin z) (guards z) prover (fun pre => ⟨z, pre⟩)
      (fun _ => rfl) (honestEmbed_injective coin z) (honestSamplePreserving_mk coin z) ∅
      hfresh)

/-- The salt is drawn before any prover action. The compiled proof producer therefore has
the same selected-proof distribution as the uniform interactive run, including aborts. -/
theorem honestSingleSaltAdversary_run'_eq_interactive
    {Statement GlobalSalt Witness : Type} {protocol : Statement → Protocol}
    [DecidableEq Statement] [DecidableEq GlobalSalt] [SampleableType GlobalSalt]
    (coin : (statement : Statement) → PublicCoin (protocol statement))
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (coin z.1))
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver (coin statement)) :
    (simulateQ (saltedSpec Statement GlobalSalt coin).romImpl
      (honestSingleSaltAdversary coin guards statement witness prover)).run' ∅ = (do
        let salt ← $ᵗ GlobalSalt
        let result ← honestInteractiveRun (coin statement) (guards (statement, salt))
          (prover salt)
        pure (result.map fun path =>
          ⟨statement, (salt, pathMessages (coin statement) path), witness⟩)) := by
  unfold honestSingleSaltAdversary
  simp only [simulateQ_bind, simulateQ_pure]
  rw [roSim.run'_liftM_bind
    (hashSpec := saltedSpec Statement GlobalSalt coin)
    (ro := (saltedSpec Statement GlobalSalt coin).randomOracle)
    (($ᵗ GlobalSalt) : ProbComp GlobalSalt)]
  apply bind_congr
  intro salt
  simp only [bind_pure_comp]
  rw [StateT.run'_map']
  have hfresh : HonestCacheFresh (∅ : (saltedSpec Statement GlobalSalt coin).QueryCache)
      (fun pre => ⟨(statement, salt), pre⟩) := by
    intro key
    rfl
  rw [honestCompiledRun_eq_interactive (allCoin := saltedCoin GlobalSalt coin)
    (coin statement) (guards (statement, salt))
    (prover salt) (fun pre => ⟨(statement, salt), pre⟩) (fun _ => rfl)
    (honestEmbed_injective (saltedCoin GlobalSalt coin) (statement, salt))
    (honestSamplePreserving_mk (saltedCoin GlobalSalt coin) (statement, salt)) ∅ hfresh]

/-- The actual logged lazy-oracle run of the honest proof producer has the same visible
selected-proof distribution as the salted interactive source. -/
theorem honestSingleSaltAdversary_logged_eq_interactive
    {Statement GlobalSalt Witness : Type} {protocol : Statement → Protocol}
    [DecidableEq Statement] [DecidableEq GlobalSalt] [SampleableType GlobalSalt]
    (coin : (statement : Statement) → PublicCoin (protocol statement))
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (coin z.1))
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver (coin statement)) :
    (fun result => result.1.1) <$> randomOracleLoggedRun
      (honestSingleSaltAdversary coin guards statement witness prover) ∅ = (do
        let salt ← $ᵗ GlobalSalt
        let result ← honestInteractiveRun (coin statement) (guards (statement, salt))
          (prover salt)
        pure (result.map fun path =>
          ⟨statement, (salt, pathMessages (coin statement) path), witness⟩)) := by
  have hproj := randomOracleLoggedRun_project
    (honestSingleSaltAdversary coin guards statement witness prover)
    (∅ : (saltedSpec Statement GlobalSalt coin).QueryCache)
  have hresult := congrArg (fun computation => Prod.fst <$> computation) hproj
  simp only [Functor.map_map] at hresult
  simpa only [Function.comp_def] using hresult.trans
    (honestSingleSaltAdversary_run'_eq_interactive coin guards statement witness prover)

/-- Every lazy random-oracle run extends its initial cache, even when private uniform draws
are interleaved and the program returns a failed result. -/
theorem honestRom_cache_le {Input : Type} [DecidableEq Input]
    {protocol : Input → Protocol} {coin : (z : Input) → PublicCoin (protocol z)} {α : Type}
    (program : OracleComp (unifSpec + oracleSpec Input PUnit coin) α)
    (initial : (oracleSpec Input PUnit coin).QueryCache)
    (result : α × (oracleSpec Input PUnit coin).QueryCache)
    (supported : result ∈ support
      ((simulateQ (oracleSpec Input PUnit coin).romImpl program).run initial)) :
    initial ≤ result.2 := by
  have hprivate : QueryImpl.PreservesInv (unifFwdImpl (oracleSpec Input PUnit coin))
      (initial ≤ ·) := by
    intro n cache hle value hvalue
    rw [show (unifFwdImpl (oracleSpec Input PUnit coin) n).run cache =
      (fun answer => (answer, cache)) <$> (unifSpec.query n : ProbComp (Fin (n + 1)))
      from roSim.run_apply_inl (ro := (oracleSpec Input PUnit coin).randomOracle) n cache] at hvalue
    rw [support_map] at hvalue
    obtain ⟨_, _, rfl⟩ := hvalue
    exact hle
  have hhash : QueryImpl.PreservesInv (oracleSpec Input PUnit coin).randomOracle (initial ≤ ·) :=
    QueryImpl.PreservesInv.withCaching_le uniformSampleImpl initial
  have himpl : QueryImpl.PreservesInv (oracleSpec Input PUnit coin).romImpl (initial ≤ ·) :=
    hprivate.add hhash
  exact OracleComp.simulateQ_run_preservesInv (oracleSpec Input PUnit coin).romImpl (initial ≤ ·) himpl
    program initial le_rfl result supported

/-- A successful compiler output records challenges that the final cache can replay, with every
guard on that path satisfied. -/
def HonestCachedPath {Input : Type} {allProtocol : Input → Protocol}
    {allCoin : (z : Input) → PublicCoin (allProtocol z)} :
    {protocol : Protocol} → (coin : PublicCoin protocol) → GuardSchedule PUnit coin →
    (embed : Prefix PUnit coin → Key Input PUnit allCoin) →
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) →
    protocol.tree.ExecutionPath → (oracleSpec Input PUnit allCoin).QueryCache → Prop
  | _, .done, _, _, _, _, _ => True
  | _, @PublicCoin.sender _ _ _ next, guards, embed, preserve, path, cache =>
      HonestCachedPath (next path.1) (guards path.1) (fun key => embed ⟨path.1, key⟩)
        (fun key => preserve ⟨path.1, key⟩) path.2 cache
  | _, @PublicCoin.oracle _ _ _ _ next, guards, embed, preserve, path, cache =>
      HonestCachedPath next (guards path.1) (fun key => embed ⟨path.1, key⟩)
        (fun key => preserve ⟨path.1, key⟩) path.2 cache
  | _, @PublicCoin.challenge _ _ _ _ _ next, guards, embed, preserve, path, cache =>
      guards.1 PUnit.unit = true ∧
        cache (embed (.inl PUnit.unit)) = some (cast (preserve (.inl PUnit.unit)).symm path.1) ∧
        HonestCachedPath next (guards.2 PUnit.unit path.1)
          (fun key => embed (.inr ⟨PUnit.unit, key⟩))
          (fun key => preserve (.inr ⟨PUnit.unit, key⟩)) path.2 cache

/-- A cached path remains cached when the oracle cache is extended. -/
theorem honestCachedPath_mono {Input : Type} {allProtocol : Input → Protocol}
    {allCoin : (z : Input) → PublicCoin (allProtocol z)} {protocol : Protocol}
    (coin : PublicCoin protocol) (guards : GuardSchedule PUnit coin)
    (embed : Prefix PUnit coin → Key Input PUnit allCoin)
    (preserve : ∀ key, (embed key).Challenge = key.Challenge)
    (path : protocol.tree.ExecutionPath)
    (cache₁ cache₂ : (oracleSpec Input PUnit allCoin).QueryCache) (hle : cache₁ ≤ cache₂)
    (cached : HonestCachedPath coin guards embed preserve path cache₁) :
    HonestCachedPath coin guards embed preserve path cache₂ := by
  induction coin with
  | done => trivial
  | sender next ih => exact ih path.1 _ _ _ path.2 cached
  | oracle next ih => exact ih _ _ _ path.2 cached
  | challenge next ih =>
      exact ⟨cached.1, hle cached.2.1, ih _ _ _ path.2 cached.2.2⟩

/-- Replaying a cached accepted path performs no fresh challenge sampling and returns the
same complete path. This is the operational fact used for actual native verification. -/
theorem honestCachedPath_replay {Input : Type} [DecidableEq Input]
    {allProtocol : Input → Protocol} {allCoin : (z : Input) → PublicCoin (allProtocol z)}
    {protocol : Protocol} (coin : PublicCoin protocol) (guards : GuardSchedule PUnit coin)
    (embed : Prefix PUnit coin → Key Input PUnit allCoin)
    (preserve : ∀ key, (embed key).Challenge = key.Challenge)
    (path : protocol.tree.ExecutionPath)
    (cache : (oracleSpec Input PUnit allCoin).QueryCache)
    (cached : HonestCachedPath coin guards embed preserve path cache) :
    (simulateQ (oracleSpec Input PUnit allCoin).randomOracle
      (mappedStoppedComplete coin guards (pathMessages coin path) embed preserve)).run cache =
      pure (some path, cache) := by
  induction coin with
  | done => simp [mappedStoppedComplete, simulateQ_pure]; rfl
  | sender next ih =>
      simp only [pathMessages, mappedStoppedComplete, simulateQ_bind, simulateQ_pure,
        StateT.run_bind]
      rw [ih path.1 _ _ _ path.2 cached]
      simp only [pure_bind, StateT.run_pure]
      rfl
  | oracle next ih =>
      simp only [pathMessages, mappedStoppedComplete, simulateQ_bind, simulateQ_pure,
        StateT.run_bind]
      rw [ih _ _ _ path.2 cached]
      simp only [pure_bind, StateT.run_pure]
      rfl
  | challenge next ih =>
      obtain ⟨hguard, hkey, htail⟩ := cached
      simp only [pathMessages, mappedStoppedComplete, hguard, Bool.not_true,
        Bool.false_eq_true, ite_false, simulateQ_bind, simulateQ_query,
        OracleQuery.cont_query, OracleQuery.input_query, id_map]
      rw [StateT.run_bind, randomOracle.run_eq, hkey]
      simp only [pure_bind]
      have hroundtrip : cast (preserve (.inl PUnit.unit))
          (cast (preserve (.inl PUnit.unit)).symm path.1) = path.1 := cast_symm_cast _ _
      simp only [hroundtrip, simulateQ_pure, StateT.run_bind]
      rw [ih _ _ _ path.2 htail]
      rfl

set_option backward.isDefEq.respectTransparency false in
/-- Whenever the compiled prover returns a complete path, its final cache contains every
challenge on that path; failed branches impose no path condition. -/
theorem honestCompiledRun_cached {Input : Type} [DecidableEq Input]
    {allProtocol : Input → Protocol} {allCoin : (z : Input) → PublicCoin (allProtocol z)}
    {protocol : Protocol} (coin : PublicCoin protocol) (guards : GuardSchedule PUnit coin)
    (prover : HonestProver coin)
    (embed : Prefix PUnit coin → Key Input PUnit allCoin)
    (preserve : ∀ key, (embed key).Challenge = key.Challenge)
    (cache : (oracleSpec Input PUnit allCoin).QueryCache)
    (result : Option protocol.tree.ExecutionPath × (oracleSpec Input PUnit allCoin).QueryCache)
    (supported : result ∈ support ((simulateQ (oracleSpec Input PUnit allCoin).romImpl
      (honestCompiledRun coin guards prover embed preserve)).run cache))
    (path : protocol.tree.ExecutionPath) (hresult : result.1 = some path) :
    HonestCachedPath coin guards embed preserve path result.2 := by
  induction coin generalizing cache with
  | done =>
      simp only [honestCompiledRun, simulateQ_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact True.intro
  | sender next ih =>
      simp only [honestCompiledRun, simulateQ_bind, StateT.run_bind] at supported
      rw [mem_support_bind_iff] at supported
      obtain ⟨⟨chosen, afterPrivate⟩, hprivate, hrest⟩ := supported
      rw [OracleSpec.simulateQ_romImpl_liftM_run, support_map] at hprivate
      obtain ⟨selected, _, hp⟩ := hprivate
      cases hp
      rw [mem_support_bind_iff] at hrest
      obtain ⟨⟨suffix, finalCache⟩, hsuffix, hfinal⟩ := hrest
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hfinal
      subst hfinal
      cases suffix with
      | none => simp at hresult
      | some tail =>
          cases hresult
          exact ih _ _ _ _ _ _ _ hsuffix tail rfl
  | oracle next ih =>
      simp only [honestCompiledRun, simulateQ_bind, StateT.run_bind] at supported
      rw [mem_support_bind_iff] at supported
      obtain ⟨⟨chosen, afterPrivate⟩, hprivate, hrest⟩ := supported
      rw [OracleSpec.simulateQ_romImpl_liftM_run, support_map] at hprivate
      obtain ⟨selected, _, hp⟩ := hprivate
      cases hp
      rw [mem_support_bind_iff] at hrest
      obtain ⟨⟨suffix, finalCache⟩, hsuffix, hfinal⟩ := hrest
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hfinal
      subst hfinal
      cases suffix with
      | none => simp at hresult
      | some tail =>
          cases hresult
          exact ih _ _ _ _ _ _ hsuffix tail rfl
  | challenge next ih =>
      cases hguard : guards.1 PUnit.unit with
      | false =>
          simp only [honestCompiledRun, hguard, Bool.not_false, ↓reduceIte, simulateQ_pure,
            StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          subst supported
          cases hresult
      | true =>
          simp only [honestCompiledRun, hguard, Bool.not_true, Bool.false_eq_true, ite_false,
            simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
            OracleQuery.input_query, id_map, StateT.run_bind] at supported
          rw [mem_support_bind_iff] at supported
          obtain ⟨⟨response, afterQuery⟩, hquery, hafterQuery⟩ := supported
          rw [mem_support_bind_iff] at hafterQuery
          obtain ⟨⟨continuation, afterContinuation⟩,
            hcontinuation, hafterContinuation⟩ := hafterQuery
          rw [OracleSpec.simulateQ_romImpl_liftM_run, support_map] at hcontinuation
          obtain ⟨sampledContinuation, _, hp⟩ := hcontinuation
          cases hp
          rw [mem_support_bind_iff] at hafterContinuation
          obtain ⟨⟨suffix, finalCache⟩, hsuffix, hfinal⟩ := hafterContinuation
          simp only [simulateQ_pure, StateT.run_pure,
            support_pure, Set.mem_singleton_iff] at hfinal
          have hcached : afterQuery (embed (.inl PUnit.unit)) = some response :=
            QueryImpl.withCaching_run_caches uniformSampleImpl
              (embed (.inl PUnit.unit)) cache (response, afterQuery) hquery
          have hle : afterQuery ≤ finalCache := honestRom_cache_le _ afterQuery
            (suffix, finalCache) hsuffix
          subst hfinal
          cases suffix with
          | none => simp at hresult
          | some tail =>
              cases hresult
              refine ⟨hguard, ?_, ih _ _ _ _ _ _ hsuffix tail rfl⟩
              simpa only [cast_cast_symm] using hle hcached

/-- The concrete guarded native verifier replays a path already present in the cache. Its
pure terminal acceptance test changes only the optional result, never the cache. -/
theorem honestSingleSaltVerify_replay
    {Statement GlobalSalt : Type}
    [DecidableEq Statement] [DecidableEq GlobalSalt]
    {protocol : Statement → Protocol}
    {coin : (statement : Statement) → PublicCoin (protocol statement)}
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (coin z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol z.1).tree.ExecutionPath →
      Bool)
    (z : Statement × GlobalSalt)
    (path : (protocol z.1).tree.ExecutionPath)
    (cache : (saltedSpec Statement GlobalSalt coin).QueryCache)
    (cached : HonestCachedPath (allCoin := saltedCoin GlobalSalt coin) (coin z.1)
      (guards z) (fun pre => ⟨z, pre⟩) (fun _ => rfl) path cache) :
    (simulateQ (saltedSpec Statement GlobalSalt coin).randomOracle
      (singleSaltVerify coin guards accepts z (pathMessages (coin z.1) path))).run cache =
    pure ((some path).filter (accepts z), cache) := by
  rw [singleSaltVerify, publicStoppedVerify_eq_with,
    publicStoppedVerifyWith_eq_mapped, simulateQ_map, StateT.run_map]
  rw [honestCachedPath_replay (coin z.1) (guards z) (fun pre => ⟨z, pre⟩) (fun _ => rfl)
    path cache cached]
  rfl

private theorem honestRom_restorationQueries {Input : Type} [DecidableEq Input]
    {protocol : Input → Protocol} {coin : (z : Input) → PublicCoin (protocol z)} :
    (oracleSpec Input PUnit coin).romImpl ∘ₛ
        restorationQueries Input PUnit coin =
      (oracleSpec Input PUnit coin).randomOracle := by
  funext key
  simp only [QueryImpl.apply_compose, restorationQueries, simulateQ_query,
    OracleQuery.cont_query, OracleQuery.input_query, id_map,
    OracleSpec.romImpl_apply_inr]

/-- The verifier replay law in the same interleaved `unifSpec + oracleSpec` runtime as the
compiled prover, including its exact final cache. -/
theorem honestSingleSaltVerify_replay_rom
    {Statement GlobalSalt : Type}
    [DecidableEq Statement] [DecidableEq GlobalSalt]
    {protocol : Statement → Protocol}
    {coin : (statement : Statement) → PublicCoin (protocol statement)}
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (coin z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol z.1).tree.ExecutionPath →
      Bool)
    (z : Statement × GlobalSalt)
    (path : (protocol z.1).tree.ExecutionPath)
    (cache : (saltedSpec Statement GlobalSalt coin).QueryCache)
    (cached : HonestCachedPath (allCoin := saltedCoin GlobalSalt coin) (coin z.1)
      (guards z) (fun pre => ⟨z, pre⟩) (fun _ => rfl) path cache) :
    (simulateQ (saltedSpec Statement GlobalSalt coin).romImpl
      (simulateQ (restorationQueries (Statement × GlobalSalt) PUnit
          (saltedCoin GlobalSalt coin))
        (singleSaltVerify coin guards accepts z (pathMessages (coin z.1) path)))).run cache =
    pure ((some path).filter (accepts z), cache) := by
  rw [← QueryImpl.simulateQ_compose,
    honestRom_restorationQueries]
  exact honestSingleSaltVerify_replay guards accepts z path cache cached

/-- Compile an honest strategy and run the actual guarded native verifier against the same
oracle cache. The compiler's path is retained only to state and prove cache consistency;
acceptance is determined by `singleSaltVerify`. -/
def honestCompiledVerify {Statement GlobalSalt Witness : Type} {protocol : Statement → Protocol}
    (coin : (statement : Statement) → PublicCoin (protocol statement))
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (coin z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol z.1).tree.ExecutionPath →
      Bool)
    (statement : Statement) (salt : GlobalSalt) (witness : Witness)
    (prover : HonestProver (coin statement)) :
    OracleComp (unifSpec + saltedSpec Statement GlobalSalt coin)
      (Option (Outcome (Statement × GlobalSalt) Witness (saltedProtocol GlobalSalt protocol))) := do
  let selected ← honestCompiledRun (coin statement) (guards (statement, salt)) prover
    (fun pre => ⟨(statement, salt), pre⟩) (fun _ => rfl)
  match selected with
  | none => pure none
  | some path =>
      let verified ← simulateQ (restorationQueries (Statement × GlobalSalt) PUnit
          (saltedCoin GlobalSalt coin))
        (singleSaltVerify coin guards accepts (statement, salt)
          (pathMessages (coin statement) path))
      pure (verified.map fun path => ⟨(statement, salt), path, witness⟩)

/-- Draw the independent global salt before running any private prover action, then compile
and verify in one shared lazy random-oracle execution. -/
def honestSingleSaltVerifiedProgram {Statement GlobalSalt Witness : Type} {protocol : Statement → Protocol}
    [SampleableType GlobalSalt]
    (coin : (statement : Statement) → PublicCoin (protocol statement))
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (coin z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol z.1).tree.ExecutionPath →
      Bool)
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver (coin statement)) :
    OracleComp (unifSpec + saltedSpec Statement GlobalSalt coin)
      (Option (Outcome (Statement × GlobalSalt) Witness (saltedProtocol GlobalSalt protocol))) := do
  let salt ← liftM (($ᵗ GlobalSalt) : ProbComp GlobalSalt)
  honestCompiledVerify coin guards accepts statement salt witness (prover salt)

/-- Filter a completed transcript by the pure terminal acceptance predicate. -/
def honestAcceptedResult {Statement GlobalSalt Witness : Type}
    {protocol : Statement → Protocol}
    (accepts : (z : Statement × GlobalSalt) → (protocol z.1).tree.ExecutionPath →
      Bool)
    (z : Statement × GlobalSalt) (witness : Witness)
    (selected : Option (protocol z.1).tree.ExecutionPath) :
    Option (Outcome (Statement × GlobalSalt) Witness (saltedProtocol GlobalSalt protocol)) :=
  (selected.map fun path => ⟨z, path, witness⟩).filter
    (fun accepted => accepts accepted.1 accepted.2.1)

/-- For a fixed salt, executing the compiler and concrete verifier has exactly the accepted
interactive output distribution. This program equality holds for arbitrary private samplers. -/
theorem honestCompiledVerify_eq_interactive
    {Statement GlobalSalt Witness : Type} {protocol : Statement → Protocol}
    [DecidableEq Statement] [DecidableEq GlobalSalt]
    (coin : (statement : Statement) → PublicCoin (protocol statement))
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (coin z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol z.1).tree.ExecutionPath →
      Bool)
    (statement : Statement) (salt : GlobalSalt) (witness : Witness)
    (prover : HonestProver (coin statement)) :
    (simulateQ (saltedSpec Statement GlobalSalt coin).romImpl
      (honestCompiledVerify coin guards accepts statement salt witness prover)).run' ∅ =
    (honestAcceptedResult accepts (statement, salt) witness) <$>
      honestInteractiveRun (coin statement) (guards (statement, salt)) prover := by
  unfold honestCompiledVerify
  simp only [simulateQ_bind, StateT.run'_bind']
  have hfresh : HonestCacheFresh (∅ : (saltedSpec Statement GlobalSalt coin).QueryCache)
      (fun pre => ⟨(statement, salt), pre⟩) := by
    intro key
    rfl
  rw [← honestCompiledRun_eq_interactive (allCoin := saltedCoin GlobalSalt coin)
    (coin statement) (guards (statement, salt)) prover
    (fun pre => ⟨(statement, salt), pre⟩) (fun _ => rfl)
    (honestEmbed_injective (saltedCoin GlobalSalt coin) (statement, salt))
    (honestSamplePreserving_mk (saltedCoin GlobalSalt coin) (statement, salt)) ∅ hfresh]
  simp only [StateT.run'_eq, map_eq_pure_bind, bind_assoc, pure_bind]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro ⟨selected, afterCompiled⟩ supported
  cases selected with
  | none =>
      simp [honestAcceptedResult]
  | some path =>
      have hcached := honestCompiledRun_cached (allCoin := saltedCoin GlobalSalt coin)
        (coin statement) (guards (statement, salt)) prover
        (fun pre => ⟨(statement, salt), pre⟩) (fun _ => rfl) ∅
        (some path, afterCompiled) supported path rfl
      simp only [honestAcceptedResult]
      simp only [bind_pure_comp, simulateQ_map, StateT.run_map]
      rw [honestSingleSaltVerify_replay_rom guards accepts
        (statement, salt) path afterCompiled hcached]
      cases hacc : accepts (statement, salt) path <;>
        simp [Option.filter, hacc]

/-- The actual guarded native single-salt verifier has the same accepted-output program as
the uniform interactive protocol, for every adaptive private-coin honest strategy. -/
theorem honestSingleSaltVerifiedProgram_eq_interactive
    {Statement GlobalSalt Witness : Type} {protocol : Statement → Protocol}
    [DecidableEq Statement] [DecidableEq GlobalSalt] [SampleableType GlobalSalt]
    (coin : (statement : Statement) → PublicCoin (protocol statement))
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (coin z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol z.1).tree.ExecutionPath →
      Bool)
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver (coin statement)) :
    (simulateQ (saltedSpec Statement GlobalSalt coin).romImpl
      (honestSingleSaltVerifiedProgram coin guards accepts
        statement witness prover)).run' ∅ =
    honestInteractiveAccepted coin guards accepts statement witness prover := by
  unfold honestSingleSaltVerifiedProgram honestInteractiveAccepted
  simp only [simulateQ_bind]
  rw [roSim.run'_liftM_bind
    (hashSpec := saltedSpec Statement GlobalSalt coin)
    (ro := (saltedSpec Statement GlobalSalt coin).randomOracle)
    (($ᵗ GlobalSalt) : ProbComp GlobalSalt)]
  apply bind_congr
  intro salt
  rw [honestCompiledVerify_eq_interactive coin guards accepts
    statement salt witness (prover salt)]
  simp only [honestAcceptedResult, map_eq_pure_bind]

private theorem erase_withQueryLog_bind {ι : Type} {spec : OracleSpec ι}
    {α β : Type} (program : OracleComp spec α)
    (continuation : α → OracleComp spec β) :
    (program.withQueryLog >>= fun phase => continuation phase.1) =
      program >>= continuation := by
  change ((simulateQ spec.loggingOracle program).run >>= fun result =>
    continuation result.1) = program >>= continuation
  exact loggingOracle.run_simulateQ_bind_fst program continuation

/-- Erasing only the adversary-phase query log from the existing accepted execution recovers
the direct honest compiler followed by the actual native verifier. -/
theorem honestSingleSaltAccepted_erase_log
    {Statement GlobalSalt Witness : Type} {protocol : Statement → Protocol}
    [SampleableType GlobalSalt]
    (coin : (statement : Statement) → PublicCoin (protocol statement))
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (coin z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol z.1).tree.ExecutionPath →
      Bool)
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver (coin statement)) :
    Prod.fst <$> honestSingleSaltAccepted coin guards accepts
      statement witness prover =
    honestSingleSaltVerifiedProgram coin guards accepts statement witness prover := by
  unfold honestSingleSaltAccepted
  rw [singleSaltAcceptedExecution_eq_verify]
  simp only [map_eq_pure_bind, bind_assoc]
  let finish : Option (SaltedSelection Statement GlobalSalt Witness coin) →
      OracleComp (unifSpec + saltedSpec Statement GlobalSalt coin)
        (Option (Outcome (Statement × GlobalSalt) Witness (saltedProtocol GlobalSalt protocol))) :=
      fun selected =>
    match selected with
    | none => pure none
    | some ⟨s, (salt, messages), w⟩ => do
        let path ← simulateQ (restorationQueries (Statement × GlobalSalt) PUnit
          (saltedCoin GlobalSalt coin))
          (singleSaltVerify coin guards accepts (s, salt) messages)
        pure (path.map fun p => ⟨(s, salt), p, w⟩)
  calc
    _ = ((honestSingleSaltAdversary coin guards statement witness prover).withQueryLog
      >>= fun phase => finish phase.1) := by
        apply bind_congr
        intro phase
        rcases phase with ⟨selected, log⟩
        cases selected with
        | none => rfl
        | some selected =>
            rcases selected with ⟨s, ⟨salt, messages⟩, w⟩
            simp only [finish, bind_pure_comp, Functor.map_map]
    _ = honestSingleSaltAdversary coin guards statement witness prover >>= finish :=
      erase_withQueryLog_bind _ _
    _ = honestSingleSaltVerifiedProgram coin guards accepts statement witness prover := by
      unfold honestSingleSaltAdversary honestSingleSaltVerifiedProgram honestCompiledVerify
      simp only [bind_assoc]
      congr 1
      funext salt
      simp only [pure_bind]
      congr 1
      funext selected
      cases selected with
      | none => rfl
      | some path => rfl

/-- The accepted output of the actual single-salt execution has exactly the honest
interactive distribution, after the adversary-phase log is forgotten. -/
theorem honestSingleSaltAccepted_run'_eq_interactive
    {Statement GlobalSalt Witness : Type} {protocol : Statement → Protocol}
    [DecidableEq Statement] [DecidableEq GlobalSalt] [SampleableType GlobalSalt]
    (coin : (statement : Statement) → PublicCoin (protocol statement))
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (coin z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol z.1).tree.ExecutionPath →
      Bool)
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver (coin statement)) :
    Prod.fst <$> (simulateQ (saltedSpec Statement GlobalSalt coin).romImpl
      (honestSingleSaltAccepted coin guards accepts statement witness prover)).run' ∅ =
    honestInteractiveAccepted coin guards accepts statement witness prover := by
  have h := congrArg (fun program =>
    (simulateQ (saltedSpec Statement GlobalSalt coin).romImpl program).run' ∅)
    (honestSingleSaltAccepted_erase_log coin guards accepts statement witness prover)
  simp only [simulateQ_map, StateT.run'_map'] at h
  exact h.trans (honestSingleSaltVerifiedProgram_eq_interactive coin guards accepts
    statement witness prover)

/-- Projecting the actual ordered-log experiment to its accepted result yields precisely the
uniform interactive accepted-output program. This includes guard failures and subprobability. -/
theorem honestSingleSaltAccepted_logged_eq_interactive
    {Statement GlobalSalt Witness : Type} {protocol : Statement → Protocol}
    [DecidableEq Statement] [DecidableEq GlobalSalt] [SampleableType GlobalSalt]
    (coin : (statement : Statement) → PublicCoin (protocol statement))
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (coin z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol z.1).tree.ExecutionPath →
      Bool)
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver (coin statement)) :
    (fun result => result.1.1.1) <$>
      randomOracleLoggedRun
        (honestSingleSaltAccepted coin guards accepts statement witness prover) ∅ =
    honestInteractiveAccepted coin guards accepts statement witness prover := by
  have hproj := randomOracleLoggedRun_project
    (honestSingleSaltAccepted coin guards accepts statement witness prover)
    (∅ : (saltedSpec Statement GlobalSalt coin).QueryCache)
  have hresult := congrArg (fun computation =>
    (fun result => result.1.1) <$> computation) hproj
  simp only [Functor.map_map] at hresult
  have hrun := honestSingleSaltAccepted_run'_eq_interactive coin guards accepts
    statement witness prover
  rw [StateT.run'_eq] at hrun
  simp only [Functor.map_map] at hrun
  simpa only [Functor.map_map, Function.comp_def] using hresult.trans hrun

/-- Every accepted-output event, including successful completion, has the same probability
in the actual native single-salt execution and the interactive uniform-challenge source. -/
theorem honestSingleSaltAccepted_event_eq_interactive
    {Statement GlobalSalt Witness : Type} {protocol : Statement → Protocol}
    [DecidableEq Statement] [DecidableEq GlobalSalt] [SampleableType GlobalSalt]
    (coin : (statement : Statement) → PublicCoin (protocol statement))
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (coin z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol z.1).tree.ExecutionPath →
      Bool)
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver (coin statement))
    (event : Option (Outcome (Statement × GlobalSalt) Witness (saltedProtocol GlobalSalt protocol)) →
      Prop) :
    Pr{let result ← randomOracleLoggedRun
        (honestSingleSaltAccepted coin guards accepts statement witness prover) ∅}[
      event result.1.1.1] =
    Pr{let result ← honestInteractiveAccepted coin guards accepts statement witness prover}[
      event result] := by
  rw [← prEvent_map]
  exact congrArg (fun program => Pr{let result ← program}[event result])
    (honestSingleSaltAccepted_logged_eq_interactive coin guards accepts
      statement witness prover)

/-- Honest completeness transfers exactly: a source success probability, possibly below one
or from a subprobabilistic private strategy, is the native single-salt success probability. -/
theorem honestSingleSaltAccepted_completeness
    {Statement GlobalSalt Witness : Type} {protocol : Statement → Protocol}
    [DecidableEq Statement] [DecidableEq GlobalSalt] [SampleableType GlobalSalt]
    (coin : (statement : Statement) → PublicCoin (protocol statement))
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (coin z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol z.1).tree.ExecutionPath →
      Bool)
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver (coin statement)) :
    Pr{let result ← randomOracleLoggedRun
        (honestSingleSaltAccepted coin guards accepts statement witness prover) ∅}[
      result.1.1.1.isSome = true] =
    Pr{let result ← honestInteractiveAccepted coin guards accepts statement witness prover}[
      result.isSome = true] := by
  exact honestSingleSaltAccepted_event_eq_interactive coin guards accepts
    statement witness prover (fun selected => selected.isSome = true)

/-- The actual logged single-salt target has the same accepted-output program as the actual
guarded native interactive source, including failed guards and subprobability. -/
theorem honestSingleSaltAccepted_logged_eq_native
    {Statement GlobalSalt Witness : Type} {protocol : Statement → Protocol}
    [DecidableEq Statement] [DecidableEq GlobalSalt] [SampleableType GlobalSalt]
    (coin : (statement : Statement) → PublicCoin (protocol statement))
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (coin z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol z.1).tree.ExecutionPath →
      Bool)
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver (coin statement)) :
    (fun result => result.1.1.1) <$>
      randomOracleLoggedRun
        (honestSingleSaltAccepted coin guards accepts statement witness prover) ∅ =
    honestNativeInteractiveAccepted coin guards accepts statement witness prover :=
  (honestSingleSaltAccepted_logged_eq_interactive coin guards accepts
    statement witness prover).trans
      (honestNativeInteractiveAccepted_eq coin guards accepts statement witness prover).symm

/-- Every accepted-result event transfers from the actual guarded native interactive source
to the actual logged single-salt target. -/
theorem honestSingleSaltAccepted_native_event
    {Statement GlobalSalt Witness : Type} {protocol : Statement → Protocol}
    [DecidableEq Statement] [DecidableEq GlobalSalt] [SampleableType GlobalSalt]
    (coin : (statement : Statement) → PublicCoin (protocol statement))
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (coin z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol z.1).tree.ExecutionPath →
      Bool)
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver (coin statement))
    (event : Option (Outcome (Statement × GlobalSalt) Witness (saltedProtocol GlobalSalt protocol)) →
      Prop) :
    Pr{let result ← randomOracleLoggedRun
        (honestSingleSaltAccepted coin guards accepts statement witness prover) ∅}[
      event result.1.1.1] =
    Pr{let result ← honestNativeInteractiveAccepted coin guards accepts
        statement witness prover}[event result] := by
  rw [← prEvent_map]
  exact congrArg (fun program => Pr{let result ← program}[event result])
    (honestSingleSaltAccepted_logged_eq_native coin guards accepts
      statement witness prover)

/-- Honest completeness of the actual native guarded protocol transfers exactly to the
single-salt Fiat–Shamir execution. No losslessness or unit success probability is assumed. -/
theorem honestSingleSaltAccepted_native_completeness
    {Statement GlobalSalt Witness : Type} {protocol : Statement → Protocol}
    [DecidableEq Statement] [DecidableEq GlobalSalt] [SampleableType GlobalSalt]
    (coin : (statement : Statement) → PublicCoin (protocol statement))
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (coin z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol z.1).tree.ExecutionPath →
      Bool)
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver (coin statement)) :
    Pr{let result ← randomOracleLoggedRun
        (honestSingleSaltAccepted coin guards accepts statement witness prover) ∅}[
      result.1.1.1.isSome = true] =
    Pr{let result ← honestNativeInteractiveAccepted coin guards accepts
        statement witness prover}[result.isSome = true] := by
  exact honestSingleSaltAccepted_native_event coin guards accepts
    statement witness prover (fun selected => selected.isSome = true)

end Interaction.Oracle.FiatShamir
