/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.FiatShamir.SingleSaltSecurity

/-!
# Honest private-coin provers for a single global Fiat–Shamir salt

An honest prover is a native public-protocol strategy for the rounds of its statement, with
access only to private uniform sampling. Its continuation may depend on each preceding public
challenge. The compiler below samples a single global salt before running that strategy, and
hashes the key of `(statement, salt)` and the full message prefix only after the corresponding
public message passes its guard.
-/

@[expose] public section

open Interaction.Oracle OracleComp OracleSpec

namespace Interaction.Oracle.FiatShamir

open Security.StateRestoration

/-- A native honest public-message prover, with only private sampling as an ambient effect. -/
abbrev HonestProver (rounds : List Round) :=
  Prover.Strategy unifSpec (publicProtocol rounds).tree
    (publicProtocol rounds).roles (fun _ => Unit)

/-- The interactive uniform-challenge run of an adaptive honest strategy. A failed prefix guard
stops before sampling the current challenge. The result keeps the messages and the complete
accepted path, so it can be compared with the compiled run at the same observation type. -/
def honestInteractiveRun : (rounds : List Round) →
    GuardSchedule PUnit rounds → HonestProver rounds →
    ProbComp (Option (PublicMessages rounds × (protocol rounds).tree.ExecutionPath))
  | [], _, _ => pure (some (PUnit.unit, PUnit.unit))
  | round :: rounds, (guard, next), prover => do
      let chosen ← prover
      let message := chosen.1
      if !guard message PUnit.unit then
        return none
      let challenge ← $ᵗ round.Challenge
      let continuation ← chosen.2 challenge
      let suffix ← honestInteractiveRun rounds (next message PUnit.unit challenge) continuation
      return suffix.map fun (messages, path) =>
        (⟨message, messages⟩, ⟨message, challenge, path⟩)

/-- Adapt an unguarded private-coin strategy to the actual guarded public tree. A rejected
message has no prover continuation; a passed challenge preserves the private response action. -/
def guardedHonestProver : (rounds : List Round) →
    (guards : GuardSchedule PUnit rounds) → HonestProver rounds →
    Prover.Strategy unifSpec (guardedPublicProtocol rounds guards).tree
      (guardedPublicProtocol rounds guards).roles (fun _ => Unit)
  | [], _, _ => ()
  | round :: rounds, (guard, next), prover => do
      let chosen ← prover
      let message := chosen.1
      let after : (pass : Bool) → Prover.Strategy unifSpec
          (publicRest round rounds next message pass).tree
          (publicRest round rounds next message pass).roles (fun _ => Unit)
        | false => ()
        | true => fun challenge => do
            let continuation ← chosen.2 challenge
            pure (guardedHonestProver rounds (next message PUnit.unit challenge) continuation)
      pure ⟨message, after (guard message PUnit.unit)⟩

/-- The native interactive verifier samples each reached public challenge uniformly. -/
def honestUniformVerifier : (rounds : List Round) →
    (guards : GuardSchedule PUnit rounds) →
    Verifier.Strategy unifSpec (guardedPublicProtocol rounds guards).tree
      (guardedPublicProtocol rounds guards).roles
      (guardedPublicProtocol rounds guards).oracles 0 (fun _ => Unit)
  | [], _ => pure ()
  | round :: rounds, (guard, next) => fun message =>
      let after : (pass : Bool) → OracleComp (unifSpec + ofPFunctor 0)
        (Verifier.Strategy unifSpec
          (publicRest round rounds next message pass).tree
          (publicRest round rounds next message pass).roles
          (publicRest round rounds next message pass).oracles 0 (fun _ => Unit))
        | false => pure (pure ())
        | true => pure (do
            let challenge ← liftComp ($ᵗ round.Challenge) (unifSpec + ofPFunctor 0)
            pure ⟨challenge,
              honestUniformVerifier rounds (next message PUnit.unit challenge)⟩)
      after (guard message PUnit.unit)

/-- The existing native paired strategy executor for the guarded interactive protocol. -/
def honestNativeInteractiveRun (rounds : List Round)
    (guards : GuardSchedule PUnit rounds)
    (prover : HonestProver rounds) :
    ProbComp (Option (protocol rounds).tree.ExecutionPath) :=
  (fun result => acceptedPath rounds guards result.1) <$>
    executeStrategies unifSpec (guardedPublicProtocol rounds guards).tree
      (guardedPublicProtocol rounds guards).roles
      (guardedPublicProtocol rounds guards).oracles 0
      (fun q => nomatch q)
      (guardedHonestProver rounds guards prover)
      (honestUniformVerifier rounds guards)

private def honestRoundProver (round : Round) (rounds : List Round)
    (next : round.Message → PUnit → round.Challenge → GuardSchedule PUnit rounds)
    (message : round.Message)
    (continuation : round.Challenge → ProbComp (HonestProver rounds)) :
    (pass : Bool) → Prover.Strategy unifSpec
      (publicRest round rounds next message pass).tree
      (publicRest round rounds next message pass).roles (fun _ => Unit)
  | false => ()
  | true => fun challenge =>
      guardedHonestProver rounds (next message PUnit.unit challenge) <$>
        continuation challenge

private def honestRoundVerifier (round : Round) (rounds : List Round)
    (next : round.Message → PUnit → round.Challenge → GuardSchedule PUnit rounds)
    (message : round.Message) :
    (pass : Bool) → OracleComp (unifSpec + ofPFunctor 0)
      (Verifier.Strategy unifSpec
        (publicRest round rounds next message pass).tree
        (publicRest round rounds next message pass).roles
        (publicRest round rounds next message pass).oracles 0 (fun _ => Unit))
  | false => pure (pure ())
  | true => pure (do
      let challenge ← liftComp ($ᵗ round.Challenge) (unifSpec + ofPFunctor 0)
      pure ⟨challenge, honestUniformVerifier rounds
        (next message PUnit.unit challenge)⟩)

private def honestAfterSend (round : Round) (rounds : List Round)
    (next : round.Message → PUnit → round.Challenge → GuardSchedule PUnit rounds)
    (message : round.Message)
    (continuation : round.Challenge → ProbComp (HonestProver rounds))
    (pass : Bool) : ProbComp (Option (protocol (round :: rounds)).tree.ExecutionPath) :=
  (fun result => decodeAfterGuard round rounds next message
    (fun challenge suffix => acceptedPath rounds (next message PUnit.unit challenge) suffix)
    pass result.1) <$>
    (do
      let verifier ← simulateQ (Verifier.liftAccessImpl unifSpec 0 (fun q => nomatch q))
        (honestRoundVerifier round rounds next message pass)
      executeStrategies unifSpec (publicRest round rounds next message pass).tree
        (publicRest round rounds next message pass).roles
        (publicRest round rounds next message pass).oracles 0 (fun q => nomatch q)
        (honestRoundProver round rounds next message continuation pass) verifier)

private theorem honestUniformSample (round : Round) :
    simulateQ (Verifier.liftAccessImpl unifSpec 0 (fun q => nomatch q))
      (liftComp ($ᵗ round.Challenge) (unifSpec + ofPFunctor 0)) =
    ($ᵗ round.Challenge : ProbComp round.Challenge) := by
  rw [QueryImpl.simulateQ_liftComp_left_eq_of_apply
    (Verifier.liftAccessImpl unifSpec 0 (fun q => nomatch q))
    (QueryImpl.id' unifSpec) (by intro q; rfl) ($ᵗ round.Challenge)]
  exact simulateQ_id' _

set_option backward.isDefEq.respectTransparency false in
private theorem honestAfterSend_eq (round : Round) (rounds : List Round)
    (next : round.Message → PUnit → round.Challenge → GuardSchedule PUnit rounds)
    (message : round.Message)
    (continuation : round.Challenge → ProbComp (HonestProver rounds))
    (ih : ∀ (guards : GuardSchedule PUnit rounds) (prover : HonestProver rounds),
      honestNativeInteractiveRun rounds guards prover =
        (fun result => result.map Prod.snd) <$>
          honestInteractiveRun rounds guards prover)
    (pass : Bool) :
    honestAfterSend round rounds next message continuation pass =
      if pass then (do
        let challenge ← $ᵗ round.Challenge
        let prover ← continuation challenge
        let suffix ← honestInteractiveRun rounds
          (next message PUnit.unit challenge) prover
        pure (suffix.map fun item => ⟨message, challenge, item.2⟩))
      else pure none := by
  cases pass with
  | false =>
      simp [honestAfterSend, honestRoundVerifier, honestRoundProver,
        publicRest, decodeAfterGuard, executeStrategies_done]
  | true =>
      unfold honestAfterSend
      simp only [honestRoundVerifier, honestRoundProver, publicRest,
        Protocol.public_tree, Protocol.public_roles, Protocol.public_oracles]
      simp only [simulateQ_pure, pure_bind]
      rw [executeStrategies_public_receiver]
      simp only [ite_true, decodeAfterGuard, map_bind, bind_pure_comp]
      rw [simulateQ_map, honestUniformSample]
      simp only [map_eq_pure_bind, bind_assoc, pure_bind]
      apply bind_congr
      intro challenge
      apply bind_congr
      intro prover
      have htail := ih (next message PUnit.unit challenge) prover
      have mapped := congrArg
        (fun run : ProbComp (Option (protocol rounds).tree.ExecutionPath) =>
          Option.map (fun tail =>
            (⟨message, challenge, tail⟩ : (protocol (round :: rounds)).tree.ExecutionPath))
              <$> run) htail
      simpa only [honestNativeInteractiveRun, map_eq_pure_bind, bind_assoc,
        pure_bind, Functor.map_map, Option.map_map, Function.comp_def] using mapped

set_option backward.isDefEq.respectTransparency false in
/-- The direct uniform-challenge interpreter is exactly the accepted-path projection of the
actual native guarded public strategy executor, for arbitrary adaptive private continuations. -/
theorem honestNativeInteractiveRun_eq :
    (rounds : List Round) → (guards : GuardSchedule PUnit rounds) →
    (prover : HonestProver rounds) →
    honestNativeInteractiveRun rounds guards prover =
      (fun result => result.map Prod.snd) <$>
        honestInteractiveRun rounds guards prover
  | [], _, prover => by
      simp [honestNativeInteractiveRun, honestInteractiveRun,
        guardedPublicProtocol, guardedHonestProver,
        honestUniformVerifier, acceptedPath, executeStrategies_done]
  | round :: rounds, (guard, next), prover => by
      have hstep :
          honestNativeInteractiveRun (round :: rounds) (guard, next) prover =
            (do
              let chosen ← prover
              honestAfterSend round rounds next chosen.1 chosen.2
                (guard chosen.1 PUnit.unit)) := by
        unfold honestNativeInteractiveRun
        simp only [guardedPublicProtocol, Protocol.public_tree,
          Protocol.public_roles, Protocol.public_oracles]
        rw [executeStrategies_public_sender]
        simp only [guardedHonestProver, honestUniformVerifier, acceptedPath,
          map_bind, bind_pure_comp]
        simp only [map_eq_pure_bind, bind_assoc, pure_bind]
        apply bind_congr
        intro chosen
        simp only [honestAfterSend, publicRest, honestRoundProver,
          honestRoundVerifier, decodeAfterGuard, map_bind, bind_pure_comp]
        rfl
      rw [hstep]
      simp only [honestInteractiveRun, map_bind]
      apply bind_congr
      intro chosen
      rw [honestAfterSend_eq round rounds next chosen.1 chosen.2
        (fun guards continuation => honestNativeInteractiveRun_eq rounds guards continuation)]
      cases hguard : guard chosen.1 PUnit.unit with
      | false => simp
      | true =>
          simp only [↓reduceIte, TypeTree.runtimeLens_toFunA_public,
            Protocol.public_tree, PFunctor.FreeM.liftBind_eq,
            PFunctor.selfMonomial_B, PFunctor.FreeM.bind_eq_bind,
            Protocol.public_roles, TypeTree.runtimeLens_toFunA_oracle,
            TypeTree.runtimeLens_toFunB_oracle,
            TypeTree.runtimeLens_toFunB_public, bind_pure_comp,
            Bool.not_true, Bool.false_eq_true, map_bind,
            Functor.map_map, Option.map_map]
          apply bind_congr
          intro challenge
          apply bind_congr
          intro tailProver
          congr 1

/-- Compile the same adaptive strategy to the native lazy challenge oracle. The embedding
remembers the already-sent message prefix when this definition recurses on a suffix. -/
def honestCompiledRun {Input : Type} {allRounds : Input → List Round} :
    (rounds : List Round) → GuardSchedule PUnit rounds →
    HonestProver rounds →
    (embed : Prefix PUnit rounds → Key Input PUnit allRounds) →
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) →
    OracleComp (unifSpec + oracleSpec Input PUnit allRounds)
      (Option (PublicMessages rounds × (protocol rounds).tree.ExecutionPath))
  | [], _, _, _, _ => pure (some (PUnit.unit, PUnit.unit))
  | round :: rounds, (guard, next), prover, embed, preserve => do
      let chosen ← liftM prover
      let message := chosen.1
      if !guard message PUnit.unit then
        return none
      let response ← liftM ((unifSpec + oracleSpec Input PUnit allRounds).query
        (.inr (embed (Prefix.here message PUnit.unit))))
      let challenge : round.Challenge :=
        cast (preserve (Prefix.here message PUnit.unit)) response
      let continuation ← liftM (chosen.2 challenge)
      let suffix ← honestCompiledRun rounds (next message PUnit.unit challenge)
        continuation (fun key => embed (Prefix.later message PUnit.unit key))
        (fun key => preserve (Prefix.later message PUnit.unit key))
      return suffix.map fun (messages, path) =>
        (⟨message, messages⟩, ⟨message, challenge, path⟩)

/-- Draw a salt independently, then compile a private-coin strategy to a complete proof. The
selected proof is emitted only if every reached guard passed. -/
def honestSingleSaltAdversary {Statement GlobalSalt Witness : Type}
    [SampleableType GlobalSalt] (rounds : Statement → List Round)
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (rounds z.1))
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver (rounds statement)) :
    SingleSaltAdversary Statement GlobalSalt Witness rounds := do
  let salt ← liftM (($ᵗ GlobalSalt) : ProbComp GlobalSalt)
  let selected ← honestCompiledRun (rounds statement) (guards (statement, salt)) (prover salt)
    (fun pre => ⟨(statement, salt), pre⟩) (fun _ => rfl)
  return selected.map fun (messages, _) => ⟨statement, (salt, messages), witness⟩

/-- Uniform interactive challenges with the same independent salt and terminal check. This is
the observation compared with the accepted native-verifier output. -/
def honestInteractiveAccepted {Statement GlobalSalt Witness : Type}
    [SampleableType GlobalSalt] (rounds : Statement → List Round)
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (rounds z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol (rounds z.1)).tree.ExecutionPath →
      Bool)
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver (rounds statement)) :
    ProbComp
      (Option (Outcome (Statement × GlobalSalt) Witness (saltedRounds GlobalSalt rounds))) := do
  let salt ← $ᵗ GlobalSalt
  let result ← honestInteractiveRun (rounds statement) (guards (statement, salt))
    (prover salt)
  return (result.map fun (_, path) => ⟨(statement, salt), path, witness⟩).filter
    (fun selected => accepts selected.1 selected.2.1)

/-- The honest source endpoint uses the actual guarded public strategy executor and a pure
terminal acceptance predicate. The strategy is selected after the independent salt draw. -/
def honestNativeInteractiveAccepted {Statement GlobalSalt Witness : Type}
    [SampleableType GlobalSalt] (rounds : Statement → List Round)
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (rounds z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol (rounds z.1)).tree.ExecutionPath →
      Bool)
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver (rounds statement)) :
    ProbComp
      (Option (Outcome (Statement × GlobalSalt) Witness (saltedRounds GlobalSalt rounds))) := do
  let salt ← $ᵗ GlobalSalt
  let path ← honestNativeInteractiveRun (rounds statement) (guards (statement, salt))
    (prover salt)
  return (path.map fun transcript => ⟨(statement, salt), transcript, witness⟩).filter
    (fun selected => accepts selected.1 selected.2.1)

/-- The direct interactive interpreter and the actual guarded native source have exactly the
same accepted-output distribution for salt-aware adaptive private-coin provers. -/
theorem honestNativeInteractiveAccepted_eq
    {Statement GlobalSalt Witness : Type}
    [SampleableType GlobalSalt] (rounds : Statement → List Round)
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (rounds z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol (rounds z.1)).tree.ExecutionPath →
      Bool)
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver (rounds statement)) :
    honestNativeInteractiveAccepted rounds guards accepts statement witness prover =
      honestInteractiveAccepted rounds guards accepts statement witness prover := by
  unfold honestNativeInteractiveAccepted honestInteractiveAccepted
  apply bind_congr
  intro salt
  rw [honestNativeInteractiveRun_eq]
  simp only [bind_pure_comp, Functor.map_map]
  congr 1
  funext selected
  cases selected with
  | none => rfl
  | some selected =>
      rcases selected with ⟨messages, path⟩
      rfl

/-- The actual accepted native execution of the compiled honest prover. Verification reruns
the guarded public strategy against the same lazy challenge oracle. -/
def honestSingleSaltAccepted {Statement GlobalSalt Witness : Type}
    [SampleableType GlobalSalt] (rounds : Statement → List Round)
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (rounds z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol (rounds z.1)).tree.ExecutionPath →
      Bool)
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver (rounds statement)) :=
  singleSaltAcceptedExecution rounds guards accepts
    (honestSingleSaltAdversary rounds guards statement witness prover)

/-- No key in the still-unplayed suffix has been queried. -/
def HonestCacheFresh {Input : Type} {rounds : List Round} {allRounds : Input → List Round}
    (cache : (oracleSpec Input PUnit allRounds).QueryCache)
    (embed : Prefix PUnit rounds → Key Input PUnit allRounds) : Prop :=
  ∀ key, cache (embed key) = none

/-- The next key is absent from a cache fresh on the remaining suffix. -/
theorem honestCacheFresh_here {Input : Type} {round : Round} {rounds : List Round}
    {allRounds : Input → List Round}
    (cache : (oracleSpec Input PUnit allRounds).QueryCache)
    (embed : Prefix PUnit (round :: rounds) → Key Input PUnit allRounds)
    (fresh : HonestCacheFresh cache embed) (message : round.Message) :
    cache (embed (Prefix.here message PUnit.unit)) = none :=
  fresh _

/-- Adding the current answer leaves every strictly later key fresh. -/
theorem honestCacheFresh_later {Input : Type} [DecidableEq Input]
    {round : Round} {rounds : List Round} {allRounds : Input → List Round}
    (cache : (oracleSpec Input PUnit allRounds).QueryCache)
    (embed : Prefix PUnit (round :: rounds) → Key Input PUnit allRounds)
    (injective : Function.Injective embed) (fresh : HonestCacheFresh cache embed)
    (message : round.Message)
    (response : (embed (Prefix.here message PUnit.unit)).Challenge) :
    HonestCacheFresh (cache.cacheQuery (embed (Prefix.here message PUnit.unit)) response)
      (fun key => embed (Prefix.later message PUnit.unit key)) := by
  intro key
  have hne : embed (Prefix.later message PUnit.unit key) ≠
      embed (Prefix.here message PUnit.unit) := by
    intro h
    have h' := injective h
    cases h'
  rw [QueryCache.cacheQuery_of_ne _ _ hne]
  exact fresh _

/-- Uniform sampling commutes with the answer-type transport of this key embedding. This is
automatic for the concrete identity and prefix constructors used by the compiler. -/
def HonestSamplePreserving {Input : Type} {rounds : List Round} {allRounds : Input → List Round}
    (embed : Prefix PUnit rounds → Key Input PUnit allRounds)
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) : Prop :=
  ∀ key, (cast (preserve key)) <$> ($ᵗ (embed key).Challenge : ProbComp _) =
    ($ᵗ key.Challenge : ProbComp _)

/-- The prefixes of input `z`'s rounds embed injectively into the restoration keys. -/
theorem honestEmbed_injective {Input : Type} (rounds : Input → List Round) (z : Input) :
    Function.Injective (fun pre : Prefix PUnit (rounds z) => (⟨z, pre⟩ : Key Input PUnit rounds)) :=
  fun _ _ h => eq_of_heq (Sigma.mk.inj h).2

theorem honestSamplePreserving_mk {Input : Type} (rounds : Input → List Round) (z : Input) :
    HonestSamplePreserving (allRounds := rounds) (fun pre => ⟨z, pre⟩) (fun _ => rfl) := by
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
    {allRounds : Input → List Round} (rounds : List Round)
    (guards : GuardSchedule PUnit rounds)
    (prover : HonestProver rounds)
    (embed : Prefix PUnit rounds → Key Input PUnit allRounds)
    (preserve : ∀ key, (embed key).Challenge = key.Challenge)
    (injective : Function.Injective embed)
    (sampleLaw : HonestSamplePreserving embed preserve)
    (cache : (oracleSpec Input PUnit allRounds).QueryCache)
    (fresh : HonestCacheFresh cache embed) :
    (simulateQ (oracleSpec Input PUnit allRounds).romImpl
      (honestCompiledRun rounds guards prover embed preserve)).run' cache =
    honestInteractiveRun rounds guards prover := by
  induction rounds generalizing allRounds with
  | nil =>
      simp [honestCompiledRun, honestInteractiveRun]
  | cons round rounds ih =>
      rcases guards with ⟨guard, next⟩
      simp only [honestCompiledRun, honestInteractiveRun]
      simp only [simulateQ_bind]
      rw [roSim.run'_liftM_bind
        (hashSpec := oracleSpec Input PUnit allRounds)
        (ro := (oracleSpec Input PUnit allRounds).randomOracle) prover]
      apply bind_congr
      intro chosen
      cases hguard : guard chosen.1 PUnit.unit with
      | false => simp
      | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ite_false]
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
            OracleQuery.input_query, id_map]
          simp only [simulateQ_pure, StateT.run'_bind', StateT.run'_pure']
          simp only [OracleSpec.romImpl_apply_inr, randomOracle.run_eq,
            fresh (Prefix.here chosen.1 PUnit.unit)]
          simp only [bind_assoc, pure_bind]
          simp only [roSim.run_liftM, bind_map_left]
          simp only [bind_pure_comp]
          simp_rw [map_run_fst]
          rw [bind_cast_sample (preserve (Prefix.here chosen.1 PUnit.unit))]
          rw [sampleLaw (Prefix.here chosen.1 PUnit.unit)]
          simp only [cast_symm_cast]
          apply bind_congr
          intro challenge
          conv_lhs =>
            arg 1
            change chosen.2 (cast (preserve (Prefix.here chosen.1 PUnit.unit))
              (cast (preserve (Prefix.here chosen.1 PUnit.unit)).symm challenge))
          have harg := cast_symm_cast
            (preserve (Prefix.here chosen.1 PUnit.unit)) challenge
          rw [harg]
          apply bind_congr
          intro continuation
          have hinj : Function.Injective
              (fun key => embed (Prefix.later chosen.1 PUnit.unit key)) := by
            intro x y hxy
            exact congrArg (fun data => data.2.2) (Sum.inr.inj (injective hxy))
          have hsamp : HonestSamplePreserving
              (fun key => embed (Prefix.later chosen.1 PUnit.unit key))
              (fun key => preserve (Prefix.later chosen.1 PUnit.unit key)) := by
            intro key
            exact sampleLaw (Prefix.later chosen.1 PUnit.unit key)
          have hfresh := honestCacheFresh_later cache embed injective fresh
            chosen.1
            (cast (preserve (Prefix.here chosen.1 PUnit.unit)).symm challenge)
          rw [ih (next chosen.1 PUnit.unit challenge) continuation
            (fun key => embed (Prefix.later chosen.1 PUnit.unit key))
            (fun key => preserve (Prefix.later chosen.1 PUnit.unit key))
            hinj hsamp _ hfresh]

/-- With an initially empty oracle cache, the compiler's complete path and message sequence
have exactly the interactive uniform-challenge distribution. Ordered hash logs are projected
away; private sampling remains inside the same `ProbComp`. -/
theorem honestCompiledRun_empty_eq_interactive {Input : Type} [DecidableEq Input]
    (rounds : Input → List Round) (guards : (z : Input) → GuardSchedule PUnit (rounds z))
    (z : Input) (prover : HonestProver (rounds z)) :
    (fun result => result.1.1) <$>
      randomOracleLoggedRun (honestCompiledRun (allRounds := rounds) (rounds z) (guards z) prover
        (fun pre => ⟨z, pre⟩) (fun _ => rfl)) ∅ =
    honestInteractiveRun (rounds z) (guards z) prover := by
  have hproj := randomOracleLoggedRun_project
    (honestCompiledRun (allRounds := rounds) (rounds z) (guards z) prover
      (fun pre => ⟨z, pre⟩) (fun _ => rfl))
    (∅ : (oracleSpec Input PUnit rounds).QueryCache)
  have hresult := congrArg (fun computation => Prod.fst <$> computation) hproj
  simp only [Functor.map_map] at hresult
  have hfresh : HonestCacheFresh
      (∅ : (oracleSpec Input PUnit rounds).QueryCache) (fun pre => ⟨z, pre⟩) := by
    intro key
    rfl
  simpa only [Function.comp_def] using hresult.trans
    (honestCompiledRun_eq_interactive (rounds z) (guards z) prover (fun pre => ⟨z, pre⟩)
      (fun _ => rfl) (honestEmbed_injective rounds z) (honestSamplePreserving_mk rounds z) ∅
      hfresh)

/-- The salt is drawn before any prover action. The compiled proof producer therefore has
the same selected-proof distribution as the uniform interactive run, including aborts. -/
theorem honestSingleSaltAdversary_run'_eq_interactive
    {Statement GlobalSalt Witness : Type}
    [DecidableEq Statement] [DecidableEq GlobalSalt] [SampleableType GlobalSalt]
    (rounds : Statement → List Round)
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (rounds z.1))
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver (rounds statement)) :
    (simulateQ (saltedSpec Statement GlobalSalt rounds).romImpl
      (honestSingleSaltAdversary rounds guards statement witness prover)).run' ∅ = (do
        let salt ← $ᵗ GlobalSalt
        let result ← honestInteractiveRun (rounds statement) (guards (statement, salt))
          (prover salt)
        pure (result.map fun (messages, _) => ⟨statement, (salt, messages), witness⟩)) := by
  unfold honestSingleSaltAdversary
  simp only [simulateQ_bind, simulateQ_pure]
  rw [roSim.run'_liftM_bind
    (hashSpec := saltedSpec Statement GlobalSalt rounds)
    (ro := (saltedSpec Statement GlobalSalt rounds).randomOracle)
    (($ᵗ GlobalSalt) : ProbComp GlobalSalt)]
  apply bind_congr
  intro salt
  simp only [bind_pure_comp]
  rw [StateT.run'_map']
  have hfresh : HonestCacheFresh (∅ : (saltedSpec Statement GlobalSalt rounds).QueryCache)
      (fun pre => ⟨(statement, salt), pre⟩) := by
    intro key
    rfl
  rw [honestCompiledRun_eq_interactive (allRounds := saltedRounds GlobalSalt rounds)
    (rounds statement) (guards (statement, salt))
    (prover salt) (fun pre => ⟨(statement, salt), pre⟩) (fun _ => rfl)
    (honestEmbed_injective (saltedRounds GlobalSalt rounds) (statement, salt))
    (honestSamplePreserving_mk (saltedRounds GlobalSalt rounds) (statement, salt)) ∅ hfresh]

/-- The actual logged lazy-oracle run of the honest proof producer has the same visible
selected-proof distribution as the salted interactive source. -/
theorem honestSingleSaltAdversary_logged_eq_interactive
    {Statement GlobalSalt Witness : Type}
    [DecidableEq Statement] [DecidableEq GlobalSalt] [SampleableType GlobalSalt]
    (rounds : Statement → List Round)
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (rounds z.1))
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver (rounds statement)) :
    (fun result => result.1.1) <$> randomOracleLoggedRun
      (honestSingleSaltAdversary rounds guards statement witness prover) ∅ = (do
        let salt ← $ᵗ GlobalSalt
        let result ← honestInteractiveRun (rounds statement) (guards (statement, salt))
          (prover salt)
        pure (result.map fun (messages, _) => ⟨statement, (salt, messages), witness⟩)) := by
  have hproj := randomOracleLoggedRun_project
    (honestSingleSaltAdversary rounds guards statement witness prover)
    (∅ : (saltedSpec Statement GlobalSalt rounds).QueryCache)
  have hresult := congrArg (fun computation => Prod.fst <$> computation) hproj
  simp only [Functor.map_map] at hresult
  simpa only [Function.comp_def] using hresult.trans
    (honestSingleSaltAdversary_run'_eq_interactive rounds guards statement witness prover)

/-- Every lazy random-oracle run extends its initial cache, even when private uniform draws
are interleaved and the program returns a failed result. -/
theorem honestRom_cache_le {Input : Type} [DecidableEq Input]
    {rounds : Input → List Round} {α : Type}
    (program : OracleComp (unifSpec + oracleSpec Input PUnit rounds) α)
    (initial : (oracleSpec Input PUnit rounds).QueryCache)
    (result : α × (oracleSpec Input PUnit rounds).QueryCache)
    (supported : result ∈ support
      ((simulateQ (oracleSpec Input PUnit rounds).romImpl program).run initial)) :
    initial ≤ result.2 := by
  let spec := oracleSpec Input PUnit rounds
  have hprivate : QueryImpl.PreservesInv (unifFwdImpl spec)
      (initial ≤ ·) := by
    intro n cache hle value hvalue
    rw [show (unifFwdImpl spec n).run cache =
      (fun answer => (answer, cache)) <$> (unifSpec.query n : ProbComp (Fin (n + 1)))
      from roSim.run_apply_inl (ro := spec.randomOracle) n cache] at hvalue
    rw [support_map] at hvalue
    obtain ⟨_, _, rfl⟩ := hvalue
    exact hle
  have hhash : QueryImpl.PreservesInv spec.randomOracle (initial ≤ ·) :=
    QueryImpl.PreservesInv.withCaching_le uniformSampleImpl initial
  have himpl : QueryImpl.PreservesInv spec.romImpl (initial ≤ ·) :=
    hprivate.add hhash
  exact OracleComp.simulateQ_run_preservesInv spec.romImpl (initial ≤ ·) himpl
    program initial le_rfl result supported

/-- A successful compiler output records messages and challenges that the final cache can
replay, with every guard on that path satisfied. -/
def HonestCachedPath {Input : Type} {allRounds : Input → List Round} :
    (rounds : List Round) → GuardSchedule PUnit rounds →
    (embed : Prefix PUnit rounds → Key Input PUnit allRounds) →
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) →
    PublicMessages rounds → (protocol rounds).tree.ExecutionPath →
    (oracleSpec Input PUnit allRounds).QueryCache → Prop
  | [], _, _, _, _, _, _ => True
  | _ :: rounds, (guard, next), embed, preserve, messages, path, cache =>
      messages.1 = path.1 ∧ guard path.1 PUnit.unit = true ∧
        cache (embed (Prefix.here path.1 PUnit.unit)) =
          some (cast (preserve (Prefix.here path.1 PUnit.unit)).symm path.2.1) ∧
        HonestCachedPath rounds (next path.1 PUnit.unit path.2.1)
          (fun key => embed (Prefix.later path.1 PUnit.unit key))
          (fun key => preserve (Prefix.later path.1 PUnit.unit key))
          messages.2 path.2.2 cache

/-- A cached path remains cached when the oracle cache is extended. -/
theorem honestCachedPath_mono {Input : Type}
    {allRounds : Input → List Round} :
    (rounds : List Round) → (guards : GuardSchedule PUnit rounds) →
    (embed : Prefix PUnit rounds → Key Input PUnit allRounds) →
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) →
    (messages : PublicMessages rounds) → (path : (protocol rounds).tree.ExecutionPath) →
    (cache₁ cache₂ : (oracleSpec Input PUnit allRounds).QueryCache) →
    cache₁ ≤ cache₂ → HonestCachedPath rounds guards embed preserve messages path cache₁ →
      HonestCachedPath rounds guards embed preserve messages path cache₂
  | [], _, _, _, _, _, _, _, _, _ => True.intro
  | round :: rounds, (guard, next), embed, preserve,
      (message, messages), ⟨pathMessage, challenge, tail⟩, cache₁, cache₂,
      hle, ⟨hmessage, hguard, hcache, htail⟩ => by
        change message = pathMessage ∧ guard pathMessage PUnit.unit = true ∧
          cache₂ (embed (Prefix.here pathMessage PUnit.unit)) =
            some (cast (preserve (Prefix.here pathMessage PUnit.unit)).symm challenge) ∧
          HonestCachedPath rounds (next pathMessage PUnit.unit challenge)
            (fun key => embed (Prefix.later pathMessage PUnit.unit key))
            (fun key => preserve (Prefix.later pathMessage PUnit.unit key)) messages tail cache₂
        exact ⟨hmessage, hguard, hle hcache,
          honestCachedPath_mono rounds (next pathMessage PUnit.unit challenge)
            (fun key => embed (Prefix.later pathMessage PUnit.unit key))
            (fun key => preserve (Prefix.later pathMessage PUnit.unit key))
            messages tail cache₁ cache₂ hle htail⟩

/-- Replaying a cached accepted path performs no fresh challenge sampling and returns the
same complete path. This is the operational fact used for actual native verification. -/
theorem honestCachedPath_replay {Input : Type} [DecidableEq Input]
    {allRounds : Input → List Round} :
    (rounds : List Round) → (guards : GuardSchedule PUnit rounds) →
    (messages : PublicMessages rounds) →
    (embed : Prefix PUnit rounds → Key Input PUnit allRounds) →
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) →
    (path : (protocol rounds).tree.ExecutionPath) →
    (cache : (oracleSpec Input PUnit allRounds).QueryCache) →
    HonestCachedPath rounds guards embed preserve messages path cache →
    (simulateQ (oracleSpec Input PUnit allRounds).randomOracle
      (mappedStoppedComplete rounds guards messages embed preserve)).run cache =
      pure (some path, cache)
  | [], _, _, _, _, path, _, _ => by
      cases path
      simp [mappedStoppedComplete, simulateQ_pure]
  | round :: rounds, (guard, next), (message, messages), embed, preserve,
      ⟨pathMessage, challenge, tail⟩, cache,
      ⟨hmessage, hguard, hkey, htail⟩ => by
        change message = pathMessage at hmessage
        subst pathMessage
        simp only [mappedStoppedComplete, hguard, Bool.not_true,
          Bool.false_eq_true, ite_false, simulateQ_bind, simulateQ_query,
          OracleQuery.cont_query, OracleQuery.input_query, id_map]
        rw [StateT.run_bind, randomOracle.run_eq, hkey]
        simp only [pure_bind]
        have hroundtrip : ∀ (h : (embed (Prefix.here message PUnit.unit)).Challenge =
              round.Challenge),
            cast h (cast (preserve (Prefix.here message PUnit.unit)).symm challenge) =
              challenge := by
          intro h
          have heq : h = preserve (Prefix.here message PUnit.unit) :=
            Subsingleton.elim _ _
          rw [heq]
          exact cast_symm_cast _ _
        simp only [hroundtrip, simulateQ_pure, StateT.run_bind]
        have htail' : HonestCachedPath rounds (next message PUnit.unit challenge)
            (fun key => embed (Prefix.later message PUnit.unit key))
            (fun key => preserve (Prefix.later message PUnit.unit key))
            messages tail cache := htail
        rw [honestCachedPath_replay rounds (next message PUnit.unit challenge)
          messages (fun key => embed (Prefix.later message PUnit.unit key))
          (fun key => preserve (Prefix.later message PUnit.unit key)) tail cache htail']
        rfl

set_option backward.isDefEq.respectTransparency false in
/-- Whenever the compiled prover returns a complete path, its final cache contains every
challenge on that path; failed branches impose no path condition. -/
theorem honestCompiledRun_cached {Input : Type} [DecidableEq Input]
    {allRounds : Input → List Round} :
    (rounds : List Round) → (guards : GuardSchedule PUnit rounds) →
    (prover : HonestProver rounds) →
    (embed : Prefix PUnit rounds → Key Input PUnit allRounds) →
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) →
    (cache : (oracleSpec Input PUnit allRounds).QueryCache) →
    (result : Option (PublicMessages rounds × (protocol rounds).tree.ExecutionPath) ×
      (oracleSpec Input PUnit allRounds).QueryCache) →
    result ∈ support ((simulateQ (oracleSpec Input PUnit allRounds).romImpl
      (honestCompiledRun rounds guards prover embed preserve)).run cache) →
    ∀ messages path, result.1 = some (messages, path) →
      HonestCachedPath rounds guards embed preserve messages path result.2
  | [], _, _, _, _, _, result, supported, messages, path, hresult => by
      simp only [honestCompiledRun, simulateQ_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact True.intro
  | round :: rounds, (guard, next), prover, embed, preserve,
      cache, result, supported, messages, path, hresult => by
        simp only [honestCompiledRun, simulateQ_bind, StateT.run_bind] at supported
        rw [mem_support_bind_iff] at supported
        obtain ⟨⟨chosen, afterPrivate⟩, hprivate, hrest⟩ := supported
        rw [OracleSpec.simulateQ_romImpl_liftM_run] at hprivate
        rw [support_map] at hprivate
        obtain ⟨selected, _, hp⟩ := hprivate
        cases hp
        cases hguard : guard chosen.1 PUnit.unit with
        | false =>
            simp only [TypeTree.runtimeLens_toFunA_public, Protocol.public_tree,
              PFunctor.FreeM.liftBind_eq, PFunctor.selfMonomial_B,
              PFunctor.FreeM.bind_eq_bind, Protocol.public_roles, hguard,
              Bool.not_false, ↓reduceIte, simulateQ_pure, StateT.run_pure,
              MonadAttach.support_pure, Set.mem_singleton_iff] at hrest
            cases hrest
            cases hresult
        | true =>
            simp only [hguard, Bool.not_true, Bool.false_eq_true, ite_false,
              simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
              OracleQuery.input_query, id_map, StateT.run_bind] at hrest
            rw [mem_support_bind_iff] at hrest
            obtain ⟨⟨response, afterQuery⟩, hquery, hafterQuery⟩ := hrest
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
            have hcached : afterQuery
                (embed (Prefix.here chosen.1 PUnit.unit)) = some response := by
              exact QueryImpl.withCaching_run_caches uniformSampleImpl
                (embed (Prefix.here chosen.1 PUnit.unit)) cache
                (response, afterQuery) hquery
            have hle : afterQuery ≤ finalCache :=
              honestRom_cache_le
                (honestCompiledRun rounds
                  (next chosen.1 PUnit.unit
                    (cast (preserve (Prefix.here chosen.1 PUnit.unit)) response))
                  continuation (fun key => embed (Prefix.later chosen.1 PUnit.unit key))
                  (fun key => preserve (Prefix.later chosen.1 PUnit.unit key)))
                afterQuery (suffix, finalCache) hsuffix
            cases hfinal
            cases suffix with
            | none => simp at hresult
            | some suffixData =>
                rcases suffixData with ⟨suffixMessages, suffixPath⟩
                have hpair :
                    ((chosen.1, suffixMessages),
                      (⟨chosen.1,
                        cast (preserve (Prefix.here chosen.1 PUnit.unit)) response,
                        suffixPath⟩ : (protocol (round :: rounds)).tree.ExecutionPath)) =
                    (messages, path) := by
                  exact Option.some.inj hresult
                cases hpair
                have hcurrent : finalCache (embed (Prefix.here chosen.1 PUnit.unit)) =
                    some response := hle hcached
                refine ⟨rfl, hguard, ?_, ?_⟩
                · simpa only [cast_cast_symm] using hcurrent
                · exact honestCompiledRun_cached rounds
                    (next chosen.1 PUnit.unit
                      (cast (preserve (Prefix.here chosen.1 PUnit.unit)) response))
                    continuation (fun key => embed (Prefix.later chosen.1 PUnit.unit key))
                    (fun key => preserve (Prefix.later chosen.1 PUnit.unit key))
                    afterQuery (some (suffixMessages, suffixPath), finalCache)
                    hsuffix suffixMessages suffixPath rfl

/-- The concrete guarded native verifier replays a path already present in the cache. Its
pure terminal acceptance test changes only the optional result, never the cache. -/
theorem honestSingleSaltVerify_replay
    {Statement GlobalSalt : Type}
    [DecidableEq Statement] [DecidableEq GlobalSalt]
    {rounds : Statement → List Round}
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (rounds z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol (rounds z.1)).tree.ExecutionPath →
      Bool)
    (z : Statement × GlobalSalt)
    (messages : PublicMessages (rounds z.1))
    (path : (protocol (rounds z.1)).tree.ExecutionPath)
    (cache : (saltedSpec Statement GlobalSalt rounds).QueryCache)
    (cached : HonestCachedPath (allRounds := saltedRounds GlobalSalt rounds) (rounds z.1)
      (guards z) (fun pre => ⟨z, pre⟩) (fun _ => rfl) messages path cache) :
    (simulateQ (saltedSpec Statement GlobalSalt rounds).randomOracle
      (singleSaltVerify rounds guards accepts z messages)).run cache =
    pure ((some path).filter (accepts z), cache) := by
  rw [singleSaltVerify, publicStoppedVerify_eq_with,
    publicStoppedVerifyWith_eq_mapped, simulateQ_map, StateT.run_map]
  rw [honestCachedPath_replay (rounds z.1) (guards z) messages (fun pre => ⟨z, pre⟩) (fun _ => rfl)
    path cache cached]
  rfl

private theorem honestRom_restorationQueries {Input : Type} [DecidableEq Input]
    {rounds : Input → List Round} :
    (oracleSpec Input PUnit rounds).romImpl ∘ₛ
        restorationQueries Input PUnit rounds =
      (oracleSpec Input PUnit rounds).randomOracle := by
  funext key
  simp only [QueryImpl.apply_compose, restorationQueries, simulateQ_query,
    OracleQuery.cont_query, OracleQuery.input_query, id_map,
    OracleSpec.romImpl_apply_inr]

/-- The verifier replay law in the same interleaved `unifSpec + oracleSpec` runtime as the
compiled prover, including its exact final cache. -/
theorem honestSingleSaltVerify_replay_rom
    {Statement GlobalSalt : Type}
    [DecidableEq Statement] [DecidableEq GlobalSalt]
    {rounds : Statement → List Round}
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (rounds z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol (rounds z.1)).tree.ExecutionPath →
      Bool)
    (z : Statement × GlobalSalt)
    (messages : PublicMessages (rounds z.1))
    (path : (protocol (rounds z.1)).tree.ExecutionPath)
    (cache : (saltedSpec Statement GlobalSalt rounds).QueryCache)
    (cached : HonestCachedPath (allRounds := saltedRounds GlobalSalt rounds) (rounds z.1)
      (guards z) (fun pre => ⟨z, pre⟩) (fun _ => rfl) messages path cache) :
    (simulateQ (saltedSpec Statement GlobalSalt rounds).romImpl
      (simulateQ (restorationQueries (Statement × GlobalSalt) PUnit
          (saltedRounds GlobalSalt rounds))
        (singleSaltVerify rounds guards accepts z messages))).run cache =
    pure ((some path).filter (accepts z), cache) := by
  rw [← QueryImpl.simulateQ_compose,
    honestRom_restorationQueries]
  exact honestSingleSaltVerify_replay guards accepts z messages path cache cached

/-- Compile an honest strategy and run the actual guarded native verifier against the same
oracle cache. The compiler's path is retained only to state and prove cache consistency;
acceptance is determined by `singleSaltVerify`. -/
def honestCompiledVerify {Statement GlobalSalt Witness : Type}
    (rounds : Statement → List Round)
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (rounds z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol (rounds z.1)).tree.ExecutionPath →
      Bool)
    (statement : Statement) (salt : GlobalSalt) (witness : Witness)
    (prover : HonestProver (rounds statement)) :
    OracleComp (unifSpec + saltedSpec Statement GlobalSalt rounds)
      (Option (Outcome (Statement × GlobalSalt) Witness (saltedRounds GlobalSalt rounds))) := do
  let selected ← honestCompiledRun (rounds statement) (guards (statement, salt)) prover
    (fun pre => ⟨(statement, salt), pre⟩) (fun _ => rfl)
  match selected with
  | none => pure none
  | some (messages, _) =>
      let verified ← simulateQ (restorationQueries (Statement × GlobalSalt) PUnit
          (saltedRounds GlobalSalt rounds))
        (singleSaltVerify rounds guards accepts (statement, salt) messages)
      pure (verified.map fun path => ⟨(statement, salt), path, witness⟩)

/-- Draw the independent global salt before running any private prover action, then compile
and verify in one shared lazy random-oracle execution. -/
def honestSingleSaltVerifiedProgram {Statement GlobalSalt Witness : Type}
    [SampleableType GlobalSalt]
    (rounds : Statement → List Round)
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (rounds z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol (rounds z.1)).tree.ExecutionPath →
      Bool)
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver (rounds statement)) :
    OracleComp (unifSpec + saltedSpec Statement GlobalSalt rounds)
      (Option (Outcome (Statement × GlobalSalt) Witness (saltedRounds GlobalSalt rounds))) := do
  let salt ← liftM (($ᵗ GlobalSalt) : ProbComp GlobalSalt)
  honestCompiledVerify rounds guards accepts statement salt witness (prover salt)

/-- Filter a completed transcript by the pure terminal acceptance predicate. -/
def honestAcceptedResult {Statement GlobalSalt Witness : Type}
    {rounds : Statement → List Round}
    (accepts : (z : Statement × GlobalSalt) → (protocol (rounds z.1)).tree.ExecutionPath →
      Bool)
    (z : Statement × GlobalSalt) (witness : Witness)
    (selected : Option (PublicMessages (rounds z.1) × (protocol (rounds z.1)).tree.ExecutionPath)) :
    Option (Outcome (Statement × GlobalSalt) Witness (saltedRounds GlobalSalt rounds)) :=
  (selected.map fun (_, path) => ⟨z, path, witness⟩).filter
    (fun accepted => accepts accepted.1 accepted.2.1)

/-- For a fixed salt, executing the compiler and concrete verifier has exactly the accepted
interactive output distribution. This program equality holds for arbitrary private samplers. -/
theorem honestCompiledVerify_eq_interactive
    {Statement GlobalSalt Witness : Type}
    [DecidableEq Statement] [DecidableEq GlobalSalt]
    (rounds : Statement → List Round)
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (rounds z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol (rounds z.1)).tree.ExecutionPath →
      Bool)
    (statement : Statement) (salt : GlobalSalt) (witness : Witness)
    (prover : HonestProver (rounds statement)) :
    (simulateQ (saltedSpec Statement GlobalSalt rounds).romImpl
      (honestCompiledVerify rounds guards accepts statement salt witness prover)).run' ∅ =
    (honestAcceptedResult accepts (statement, salt) witness) <$>
      honestInteractiveRun (rounds statement) (guards (statement, salt)) prover := by
  unfold honestCompiledVerify
  simp only [simulateQ_bind, StateT.run'_bind']
  have hfresh : HonestCacheFresh (∅ : (saltedSpec Statement GlobalSalt rounds).QueryCache)
      (fun pre => ⟨(statement, salt), pre⟩) := by
    intro key
    rfl
  rw [← honestCompiledRun_eq_interactive (allRounds := saltedRounds GlobalSalt rounds)
    (rounds statement) (guards (statement, salt)) prover
    (fun pre => ⟨(statement, salt), pre⟩) (fun _ => rfl)
    (honestEmbed_injective (saltedRounds GlobalSalt rounds) (statement, salt))
    (honestSamplePreserving_mk (saltedRounds GlobalSalt rounds) (statement, salt)) ∅ hfresh]
  simp only [StateT.run'_eq, map_eq_pure_bind, bind_assoc, pure_bind]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro ⟨selected, afterCompiled⟩ supported
  cases selected with
  | none =>
      simp [honestAcceptedResult]
  | some selected =>
      rcases selected with ⟨messages, path⟩
      have hcached := honestCompiledRun_cached (allRounds := saltedRounds GlobalSalt rounds)
        (rounds statement) (guards (statement, salt)) prover
        (fun pre => ⟨(statement, salt), pre⟩) (fun _ => rfl) ∅
        (some (messages, path), afterCompiled) supported messages path rfl
      simp only [honestAcceptedResult]
      simp only [bind_pure_comp, simulateQ_map, StateT.run_map]
      rw [honestSingleSaltVerify_replay_rom guards accepts
        (statement, salt) messages path afterCompiled hcached]
      cases hacc : accepts (statement, salt) path <;>
        simp [Option.filter, hacc]

/-- The actual guarded native single-salt verifier has the same accepted-output program as
the uniform interactive protocol, for every adaptive private-coin honest strategy. -/
theorem honestSingleSaltVerifiedProgram_eq_interactive
    {Statement GlobalSalt Witness : Type}
    [DecidableEq Statement] [DecidableEq GlobalSalt] [SampleableType GlobalSalt]
    (rounds : Statement → List Round)
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (rounds z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol (rounds z.1)).tree.ExecutionPath →
      Bool)
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver (rounds statement)) :
    (simulateQ (saltedSpec Statement GlobalSalt rounds).romImpl
      (honestSingleSaltVerifiedProgram rounds guards accepts
        statement witness prover)).run' ∅ =
    honestInteractiveAccepted rounds guards accepts statement witness prover := by
  unfold honestSingleSaltVerifiedProgram honestInteractiveAccepted
  simp only [simulateQ_bind]
  rw [roSim.run'_liftM_bind
    (hashSpec := saltedSpec Statement GlobalSalt rounds)
    (ro := (saltedSpec Statement GlobalSalt rounds).randomOracle)
    (($ᵗ GlobalSalt) : ProbComp GlobalSalt)]
  apply bind_congr
  intro salt
  rw [honestCompiledVerify_eq_interactive rounds guards accepts
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
    {Statement GlobalSalt Witness : Type}
    [SampleableType GlobalSalt]
    (rounds : Statement → List Round)
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (rounds z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol (rounds z.1)).tree.ExecutionPath →
      Bool)
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver (rounds statement)) :
    Prod.fst <$> honestSingleSaltAccepted rounds guards accepts
      statement witness prover =
    honestSingleSaltVerifiedProgram rounds guards accepts statement witness prover := by
  unfold honestSingleSaltAccepted
  rw [singleSaltAcceptedExecution_eq_verify]
  simp only [map_eq_pure_bind, bind_assoc]
  let finish : Option (SaltedSelection Statement GlobalSalt Witness rounds) →
      OracleComp (unifSpec + saltedSpec Statement GlobalSalt rounds)
        (Option (Outcome (Statement × GlobalSalt) Witness (saltedRounds GlobalSalt rounds))) :=
      fun selected =>
    match selected with
    | none => pure none
    | some ⟨s, (salt, messages), w⟩ => do
        let path ← simulateQ (restorationQueries (Statement × GlobalSalt) PUnit
          (saltedRounds GlobalSalt rounds))
          (singleSaltVerify rounds guards accepts (s, salt) messages)
        pure (path.map fun p => ⟨(s, salt), p, w⟩)
  calc
    _ = ((honestSingleSaltAdversary rounds guards statement witness prover).withQueryLog
      >>= fun phase => finish phase.1) := by
        apply bind_congr
        intro phase
        rcases phase with ⟨selected, log⟩
        cases selected with
        | none => rfl
        | some selected =>
            rcases selected with ⟨s, ⟨salt, messages⟩, w⟩
            simp only [finish, bind_pure_comp, Functor.map_map]
    _ = honestSingleSaltAdversary rounds guards statement witness prover >>= finish :=
      erase_withQueryLog_bind _ _
    _ = honestSingleSaltVerifiedProgram rounds guards accepts statement witness prover := by
      unfold honestSingleSaltAdversary honestSingleSaltVerifiedProgram honestCompiledVerify
      simp only [bind_assoc]
      congr 1
      funext salt
      simp only [pure_bind]
      congr 1
      funext selected
      cases selected with
      | none => rfl
      | some selected =>
          rcases selected with ⟨messages, path⟩
          rfl

/-- The accepted output of the actual single-salt execution has exactly the honest
interactive distribution, after the adversary-phase log is forgotten. -/
theorem honestSingleSaltAccepted_run'_eq_interactive
    {Statement GlobalSalt Witness : Type}
    [DecidableEq Statement] [DecidableEq GlobalSalt] [SampleableType GlobalSalt]
    (rounds : Statement → List Round)
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (rounds z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol (rounds z.1)).tree.ExecutionPath →
      Bool)
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver (rounds statement)) :
    Prod.fst <$> (simulateQ (saltedSpec Statement GlobalSalt rounds).romImpl
      (honestSingleSaltAccepted rounds guards accepts statement witness prover)).run' ∅ =
    honestInteractiveAccepted rounds guards accepts statement witness prover := by
  have h := congrArg (fun program =>
    (simulateQ (saltedSpec Statement GlobalSalt rounds).romImpl program).run' ∅)
    (honestSingleSaltAccepted_erase_log rounds guards accepts statement witness prover)
  simp only [simulateQ_map, StateT.run'_map'] at h
  exact h.trans (honestSingleSaltVerifiedProgram_eq_interactive rounds guards accepts
    statement witness prover)

/-- Projecting the actual ordered-log experiment to its accepted result yields precisely the
uniform interactive accepted-output program. This includes guard failures and subprobability. -/
theorem honestSingleSaltAccepted_logged_eq_interactive
    {Statement GlobalSalt Witness : Type}
    [DecidableEq Statement] [DecidableEq GlobalSalt] [SampleableType GlobalSalt]
    (rounds : Statement → List Round)
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (rounds z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol (rounds z.1)).tree.ExecutionPath →
      Bool)
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver (rounds statement)) :
    (fun result => result.1.1.1) <$>
      randomOracleLoggedRun
        (honestSingleSaltAccepted rounds guards accepts statement witness prover) ∅ =
    honestInteractiveAccepted rounds guards accepts statement witness prover := by
  have hproj := randomOracleLoggedRun_project
    (honestSingleSaltAccepted rounds guards accepts statement witness prover)
    (∅ : (saltedSpec Statement GlobalSalt rounds).QueryCache)
  have hresult := congrArg (fun computation =>
    (fun result => result.1.1) <$> computation) hproj
  simp only [Functor.map_map] at hresult
  have hrun := honestSingleSaltAccepted_run'_eq_interactive rounds guards accepts
    statement witness prover
  rw [StateT.run'_eq] at hrun
  simp only [Functor.map_map] at hrun
  simpa only [Functor.map_map, Function.comp_def] using hresult.trans hrun

/-- Every accepted-output event, including successful completion, has the same probability
in the actual native single-salt execution and the interactive uniform-challenge source. -/
theorem honestSingleSaltAccepted_event_eq_interactive
    {Statement GlobalSalt Witness : Type}
    [DecidableEq Statement] [DecidableEq GlobalSalt] [SampleableType GlobalSalt]
    (rounds : Statement → List Round)
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (rounds z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol (rounds z.1)).tree.ExecutionPath →
      Bool)
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver (rounds statement))
    (event : Option (Outcome (Statement × GlobalSalt) Witness (saltedRounds GlobalSalt rounds)) →
      Prop) :
    Pr{let result ← randomOracleLoggedRun
        (honestSingleSaltAccepted rounds guards accepts statement witness prover) ∅}[
      event result.1.1.1] =
    Pr{let result ← honestInteractiveAccepted rounds guards accepts statement witness prover}[
      event result] := by
  rw [← prEvent_map]
  exact congrArg (fun program => Pr{let result ← program}[event result])
    (honestSingleSaltAccepted_logged_eq_interactive rounds guards accepts
      statement witness prover)

/-- Honest completeness transfers exactly: a source success probability, possibly below one
or from a subprobabilistic private strategy, is the native single-salt success probability. -/
theorem honestSingleSaltAccepted_completeness
    {Statement GlobalSalt Witness : Type}
    [DecidableEq Statement] [DecidableEq GlobalSalt] [SampleableType GlobalSalt]
    (rounds : Statement → List Round)
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (rounds z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol (rounds z.1)).tree.ExecutionPath →
      Bool)
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver (rounds statement)) :
    Pr{let result ← randomOracleLoggedRun
        (honestSingleSaltAccepted rounds guards accepts statement witness prover) ∅}[
      result.1.1.1.isSome = true] =
    Pr{let result ← honestInteractiveAccepted rounds guards accepts statement witness prover}[
      result.isSome = true] := by
  exact honestSingleSaltAccepted_event_eq_interactive rounds guards accepts
    statement witness prover (fun selected => selected.isSome = true)

/-- The actual logged single-salt target has the same accepted-output program as the actual
guarded native interactive source, including failed guards and subprobability. -/
theorem honestSingleSaltAccepted_logged_eq_native
    {Statement GlobalSalt Witness : Type}
    [DecidableEq Statement] [DecidableEq GlobalSalt] [SampleableType GlobalSalt]
    (rounds : Statement → List Round)
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (rounds z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol (rounds z.1)).tree.ExecutionPath →
      Bool)
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver (rounds statement)) :
    (fun result => result.1.1.1) <$>
      randomOracleLoggedRun
        (honestSingleSaltAccepted rounds guards accepts statement witness prover) ∅ =
    honestNativeInteractiveAccepted rounds guards accepts statement witness prover :=
  (honestSingleSaltAccepted_logged_eq_interactive rounds guards accepts
    statement witness prover).trans
      (honestNativeInteractiveAccepted_eq rounds guards accepts statement witness prover).symm

/-- Every accepted-result event transfers from the actual guarded native interactive source
to the actual logged single-salt target. -/
theorem honestSingleSaltAccepted_native_event
    {Statement GlobalSalt Witness : Type}
    [DecidableEq Statement] [DecidableEq GlobalSalt] [SampleableType GlobalSalt]
    (rounds : Statement → List Round)
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (rounds z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol (rounds z.1)).tree.ExecutionPath →
      Bool)
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver (rounds statement))
    (event : Option (Outcome (Statement × GlobalSalt) Witness (saltedRounds GlobalSalt rounds)) →
      Prop) :
    Pr{let result ← randomOracleLoggedRun
        (honestSingleSaltAccepted rounds guards accepts statement witness prover) ∅}[
      event result.1.1.1] =
    Pr{let result ← honestNativeInteractiveAccepted rounds guards accepts
        statement witness prover}[event result] := by
  rw [← prEvent_map]
  exact congrArg (fun program => Pr{let result ← program}[event result])
    (honestSingleSaltAccepted_logged_eq_native rounds guards accepts
      statement witness prover)

/-- Honest completeness of the actual native guarded protocol transfers exactly to the
single-salt Fiat–Shamir execution. No losslessness or unit success probability is assumed. -/
theorem honestSingleSaltAccepted_native_completeness
    {Statement GlobalSalt Witness : Type}
    [DecidableEq Statement] [DecidableEq GlobalSalt] [SampleableType GlobalSalt]
    (rounds : Statement → List Round)
    (guards : (z : Statement × GlobalSalt) → GuardSchedule PUnit (rounds z.1))
    (accepts : (z : Statement × GlobalSalt) → (protocol (rounds z.1)).tree.ExecutionPath →
      Bool)
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver (rounds statement)) :
    Pr{let result ← randomOracleLoggedRun
        (honestSingleSaltAccepted rounds guards accepts statement witness prover) ∅}[
      result.1.1.1.isSome = true] =
    Pr{let result ← honestNativeInteractiveAccepted rounds guards accepts
        statement witness prover}[result.isSome = true] := by
  exact honestSingleSaltAccepted_native_event rounds guards accepts
    statement witness prover (fun selected => selected.isSome = true)

end Interaction.Oracle.FiatShamir
