/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.Interaction.Oracle.Security.GroupedOracle
public import ArkLib.Interaction.Oracle.Security.DecodedChallenges

/-!
# Fiat–Shamir on a hash chain with challenges of several squeezes

A duplex challenger answers each chain query with a state and a buffer of outputs; a challenge
that needs more outputs than one buffer holds squeezes again, a chain query with the empty input
`e` at the state the previous squeeze answered. The `j`th squeeze after absorbing `x :: p` is the
chain's answer to the prefix `e ^ j ++ x :: p` (`squeezePrefix`).

A protocol's challenges are drawn from coins `Fin m → S × O` (`DecodedChallenges.lean`): at a node
squeezed `n ≤ m` times (`squeezes`), the answers of its `n` squeezes, and the default answer at the
other places (`pad`). The verifier squeezes exactly `n` times, so a node squeezed `0` times makes no
chain query, and the node's draw reads only the first `n` coins (`Decoder.Reads`).
`KnowledgeCertificate.chainSqueeze_knowledge_soundness` bounds the probability that the verifier
completes a path whose coins all pass, decoding to a path of the protocol with a valid terminal
witness whose backward extraction fails, by `chainError S q` plus the state-restoration bound
`maxError * q + sumError` of the certificates' node errors, each multiplied by its draw's ratio:
a challenge of several squeezes costs the adversary one query for the error of the whole draw,
as one of a single squeeze does.

## Proof

Off a state collision or prediction, the verifier's squeezes read the prefix-keyed random oracle
(`HashChain.lean`). The prefixes fall into groups of `m`, the prefixes `e ^ j ++ b` for `j < m` of
a base `b` whose leading empty inputs are a multiple of `m` (`squeezeEquiv`); the squeezes of a
key that squeezes are one group, since its absorbed input is not empty. Reading the prefix oracle
in these groups (`GroupedOracle.lean`), on the left side of an oracle on bases and keys
(`liftInl`), a key's `n` squeezes are the first `n` components of one answer at the key's base. The
verifier's path is then the path of the encoded random oracle on that oracle
(`EncodedSecurityEvent.lean`), keys that squeeze encoded by their bases and the others by
themselves (`squeezeCodec`), with each node's coins padded (`padPath`), less the queries of the
keys squeezed `0` times, whose answers it never reads (`evalDistEq_run'_simulateQ_of_discard`).
Padding changes no decoded path, so the encoded random oracle's bound applies.
-/

@[expose] public section

open OracleComp OracleSpec Interaction.Oracle Interaction.Oracle.Security.StateRestoration
open MeasureTheory
open scoped ENNReal

namespace Interaction.Oracle.Security.HashChain

/-! ### Groups of squeezes -/

section Groups

variable {I : Type} [DecidableEq I]

/-- The number of leading empty inputs `e` of a prefix. -/
def leadingCount (e : I) : List I → ℕ
  | [] => 0
  | x :: l => if x = e then leadingCount e l + 1 else 0

/-- The prefixes whose number of leading empty inputs is a multiple of `m`: each is the first
squeeze of a group of `m`. -/
abbrev SqueezeBase (e : I) (m : ℕ) : Type := {d : List I // leadingCount e d % m = 0}

/-- The prefix of the `j`th squeeze after absorbing `x :: p`: `j` empty inputs more. -/
def squeezePrefix (e x : I) (p : List I) (j : ℕ) : List I := List.replicate j e ++ x :: p

/-- Leading empty inputs before a list add to its own. -/
theorem leadingCount_replicate_append (e : I) (j : ℕ) (l : List I) :
    leadingCount e (List.replicate j e ++ l) = j + leadingCount e l := by
  induction j with
  | zero => simp only [List.replicate_zero, List.nil_append, Nat.zero_add]
  | succ j ih =>
    simp only [List.replicate_succ, List.cons_append, leadingCount, ↓reduceIte, ih]
    omega

/-- A prefix is its first `j` inputs, all empty, followed by the rest, for `j` up to its leading
empty inputs. -/
theorem replicate_append_drop (e : I) :
    ∀ (j : ℕ) (d : List I), j ≤ leadingCount e d → List.replicate j e ++ d.drop j = d
  | 0, _, _ => rfl
  | j + 1, [], h => by simp only [leadingCount, Nat.le_zero, Nat.add_one_ne_zero] at h
  | j + 1, x :: d, h => by
    by_cases hx : x = e
    · subst hx
      simp only [leadingCount, ↓reduceIte, Nat.add_le_add_iff_right] at h
      simp only [List.replicate_succ, List.cons_append, List.drop_succ_cons,
        replicate_append_drop x j d h]
    · simp only [leadingCount, hx, ↓reduceIte, Nat.le_zero, Nat.add_one_ne_zero] at h

/-- Every prefix is a squeeze of one group: `e ^ j ++ b` for a base `b` and `j < m`. -/
def squeezeEquiv (e : I) (m : ℕ) [NeZero m] : List I ≃ SqueezeBase e m × Fin m where
  toFun d := (⟨d.drop (leadingCount e d % m), by
      have h := leadingCount_replicate_append e (leadingCount e d % m)
        (d.drop (leadingCount e d % m))
      rw [replicate_append_drop e _ d (Nat.mod_le _ _)] at h
      have h' := Nat.mod_add_div (leadingCount e d) m
      rw [show leadingCount e (d.drop (leadingCount e d % m)) = m * (leadingCount e d / m) by
        omega]
      exact Nat.mul_mod_right _ _⟩,
    ⟨leadingCount e d % m, Nat.mod_lt _ (NeZero.pos m)⟩)
  invFun b := List.replicate b.2 e ++ b.1.1
  left_inv d := replicate_append_drop e _ d (Nat.mod_le _ _)
  right_inv b := by
    obtain ⟨⟨b, hb⟩, j⟩ := b
    have hk : leadingCount e (List.replicate j e ++ b) % m = j := by
      rw [leadingCount_replicate_append, Nat.add_mod, hb, Nat.add_zero, Nat.mod_mod,
        Nat.mod_eq_of_lt j.isLt]
    refine Prod.ext (Subtype.ext ?_) (Fin.ext hk)
    change (List.replicate j e ++ b).drop _ = b
    rw [hk, List.drop_left' List.length_replicate]

/-- The prefix of a squeeze of a group: `j` empty inputs before the group's base. -/
theorem squeezeEquiv_symm_apply (e : I) (m : ℕ) [NeZero m] (b : SqueezeBase e m) (j : Fin m) :
    (squeezeEquiv e m).symm (b, j) = List.replicate j e ++ b.1 := rfl

/-- The base of a prefix absorbing a nonempty input. -/
def squeezeBase (e : I) (m : ℕ) {x : I} (hx : x ≠ e) (p : List I) : SqueezeBase e m :=
  ⟨x :: p, by simp [leadingCount, hx]⟩

/-- The `j`th squeeze after a nonempty input is the `j`th prefix of its group. -/
theorem squeezeEquiv_squeezePrefix (e : I) (m : ℕ) [NeZero m] {x : I} (hx : x ≠ e)
    (p : List I) (j : Fin m) :
    squeezeEquiv e m (squeezePrefix e x p j) = (squeezeBase e m hx p, j) := by
  exact (squeezeEquiv e m).eq_symm_apply.mp rfl

end Groups

/-! ### Squeezes and coins -/

section Coins

variable {S O : Type} [Inhabited S] [Inhabited O] {m : ℕ}

/-- The answers of `n` squeezes, in order, the `j`th read by `answer j`. -/
def squeezeAnswers {M : Type → Type} [Monad M] (answer : ℕ → M (S × O)) : ℕ → M (List (S × O))
  | 0 => pure []
  | n + 1 => do
      let l ← squeezeAnswers answer n
      let a ← answer n
      pure (l ++ [a])

/-- The coins of answers: the `i`th answer at place `i`, the default answer at the others. -/
def coinsOf (l : List (S × O)) : Fin m → S × O := fun i => l.getD i default

/-- The coins at the first `n` places, the default answer at the others. -/
def pad (n : ℕ) (c : Fin m → S × O) : Fin m → S × O :=
  fun i => if (i : ℕ) < n then c i else default

omit [Inhabited S] [Inhabited O] in
/-- Answering each squeeze through an implementation answers the squeezes' programs in order. -/
theorem simulateQ_squeezeAnswers {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (impl : QueryImpl spec (OracleComp spec')) (answer : ℕ → OracleComp spec (S × O)) (n : ℕ) :
    simulateQ impl (squeezeAnswers answer n) =
      squeezeAnswers (fun j => simulateQ impl (answer j)) n := by
  induction n with
  | zero => simp only [squeezeAnswers, simulateQ_pure]
  | succ n ih => simp only [squeezeAnswers, simulateQ_bind, simulateQ_pure, ih]

omit [Inhabited S] [Inhabited O] in
/-- The answers of `n` squeezes read only the first `n` answer programs. -/
theorem squeezeAnswers_congr {M : Type → Type} [Monad M] {answer answer' : ℕ → M (S × O)}
    {n : ℕ} (h : ∀ j < n, answer j = answer' j) :
    squeezeAnswers answer n = squeezeAnswers answer' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [squeezeAnswers, ih fun j hj => h j (Nat.lt_succ_of_lt hj), h n (Nat.lt_succ_self n)]

omit [Inhabited S] [Inhabited O] in
/-- Squeezes whose programs draw no private coin draw none. -/
theorem isQueryBoundP_squeezeAnswers {ι : Type} {spec : OracleSpec ι}
    {answer : ℕ → OracleComp spec (S × O)} {p : ι → Prop} [DecidablePred p]
    (h : ∀ j, IsQueryBoundP (answer j) p 0) (n : ℕ) :
    IsQueryBoundP (squeezeAnswers answer n) p 0 := by
  induction n with
  | zero => trivial
  | succ n ih =>
    exact isQueryBoundP_bind (n := 0) (m := 0) ih fun _ _ =>
      isQueryBoundP_bind (n := 0) (m := 0) (h n) fun _ _ => trivial

omit [Inhabited S] [Inhabited O] in
/-- Replaying squeezes succeeds alike when each squeeze's replay does. -/
theorem replay_squeezeAnswers {ι₁ ι₂ : Type} {hs₁ : OracleSpec ι₁} {hs₂ : OracleSpec ι₂}
    (c₁ : hs₁.QueryCache) (c₂ : hs₂.QueryCache) {answer₁ : ℕ → OracleComp (unifSpec + hs₁) (S × O)}
    {answer₂ : ℕ → OracleComp (unifSpec + hs₂) (S × O)}
    (h : ∀ j v, replay c₁ (answer₁ j) = some v → replay c₂ (answer₂ j) = some v) (n : ℕ)
    (l : List (S × O)) (hl : replay c₁ (squeezeAnswers answer₁ n) = some l) :
    replay c₂ (squeezeAnswers answer₂ n) = some l := by
  induction n generalizing l with
  | zero => simpa only [squeezeAnswers, replay_pure] using hl
  | succ n ih =>
    simp only [squeezeAnswers, replay_bind, replay_pure] at hl ⊢
    obtain ⟨l', hl', hl⟩ := Option.bind_eq_some_iff.mp hl
    obtain ⟨a, ha, hl⟩ := Option.bind_eq_some_iff.mp hl
    simp only [ih l' hl', h n a ha, Option.bind_eq_bind, Option.bind_some]
    exact hl

/-- The coins of the first `n` components of `g`, read off in order, are `g` padded at `n`. -/
theorem coinsOf_map_range (g : Fin m → S × O) (n : ℕ) :
    coinsOf ((List.range n).map fun j => if h : j < m then g ⟨j, h⟩ else default) =
      pad n g := by
  funext i
  simp only [coinsOf, pad, List.getD_eq_getElem?_getD, List.getElem?_map]
  split_ifs with hi
  · simp only [List.getElem?_range hi, Option.map_some, Option.getD_some, i.isLt, dite_true]
  · rw [List.getElem?_eq_none (by simpa only [List.length_range, not_lt] using hi)]
    rfl

end Coins

/-! ### Squeezes of one random-oracle answer -/

section Runs

variable {S O : Type} {ι : Type} [DecidableEq ι] {hs : OracleSpec ι}
  [∀ t, SampleableType (hs.Range t)]

/-- Querying the random oracle twice at a point answers both queries alike. -/
theorem simulateQ_romImpl_query_bind_query {α : Type} (t : ι)
    (k : (unifSpec + hs).Range (.inr t) → (unifSpec + hs).Range (.inr t) →
      OracleComp (unifSpec + hs) α) :
    simulateQ hs.romImpl (liftM ((unifSpec + hs).query (.inr t)) >>= fun u =>
        liftM ((unifSpec + hs).query (.inr t)) >>= k u) =
      simulateQ hs.romImpl (liftM ((unifSpec + hs).query (.inr t)) >>= fun u => k u u) := by
  refine StateT.ext fun c => ?_
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  cases hc : c t with
  | some u => simp only [romImpl_run_of_some hc, pure_bind]
  | none =>
    simp only [romImpl_run_of_none hc, bind_map_left]
    refine bind_congr fun u => ?_
    rw [romImpl_run_of_some (QueryCache.cacheQuery_self c t u), pure_bind]

/-- Squeezes that each read a component of one random-oracle answer read that one answer. -/
theorem simulateQ_romImpl_squeezeAnswers (t : ι) (sel : ℕ → hs.Range t → S × O) :
    (n : ℕ) → 0 < n →
    simulateQ hs.romImpl (squeezeAnswers (fun j =>
        sel j <$> liftM ((unifSpec + hs).query (.inr t))) n) =
      simulateQ hs.romImpl ((fun g => (List.range n).map fun j => sel j g) <$>
        liftM ((unifSpec + hs).query (.inr t)))
  | 0, h => absurd h (Nat.lt_irrefl 0)
  | 1, _ => by
    simp only [squeezeAnswers, pure_bind, List.nil_append, List.range_one,
      List.map_singleton, map_eq_bind_pure_comp, Function.comp_def, bind_assoc]
  | n + 2, _ => by
    rw [squeezeAnswers, simulateQ_bind, simulateQ_romImpl_squeezeAnswers t sel (n + 1)
      (Nat.succ_pos n), ← simulateQ_bind]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    refine (simulateQ_romImpl_query_bind_query t fun u u' => pure _).trans ?_
    simp only [List.range_succ (n := n + 1), List.map_append, List.map_singleton]
    rfl

/-- **Discarded queries.** A program has the same output distribution on the random oracle when
some of its queries are answered after an extra random-oracle query whose answer is discarded. -/
theorem evalDistEq_run'_simulateQ_of_discard {κ : Type} {spec : OracleSpec κ}
    (impl₀ impl₁ : QueryImpl spec (OracleComp (unifSpec + hs)))
    (h : ∀ k, simulateQ hs.romImpl (impl₁ k) = simulateQ hs.romImpl (impl₀ k) ∨
      ∃ t, impl₁ k = liftM ((unifSpec + hs).query (.inr t)) >>= fun _ => impl₀ k)
    {α : Type} (P : OracleComp spec α) (c : hs.QueryCache) :
    (simulateQ hs.romImpl (simulateQ impl₁ P)).run' c =ᵈ
      (simulateQ hs.romImpl (simulateQ impl₀ P)).run' c := by
  induction P using OracleComp.inductionOn generalizing c with
  | pure a => exact EvalDistEq.rfl
  | query_bind k cont ih =>
    have e : ∀ impl : QueryImpl spec (OracleComp (unifSpec + hs)),
        simulateQ impl (liftM (spec.query k) >>= cont) =
          impl k >>= fun u => simulateQ impl (cont u) := fun impl => by
      simp only [simulateQ_bind, simulateQ_spec_query]
    rw [e, e]
    have step : (simulateQ hs.romImpl (impl₁ k >>= fun u => simulateQ impl₁ (cont u))).run' c =ᵈ
        (simulateQ hs.romImpl (impl₀ k >>= fun u => simulateQ impl₁ (cont u))).run' c := by
      rcases h k with hk | ⟨t, hk⟩
      · rw [simulateQ_bind, hk, ← simulateQ_bind]
      · rw [hk, bind_assoc]
        exact evalDistEq_iff_evalDist_eq.mpr
          (letI : MeasurableSpace α := ⊤; evalDist_run'_query_bind_discard t _ c)
    refine step.trans ?_
    simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
    exact EvalDistEq.bind_congr .rfl fun p => by simpa only [StateT.run'_eq] using ih p.1 p.2

end Runs

/-! ### Guards that always pass -/

/-- The guards that pass every challenge. -/
def GuardSchedule.pass {Salt : Type} : {protocol : Protocol} → (coin : PublicCoin protocol) →
    GuardSchedule Salt coin
  | _, .done => PUnit.unit
  | _, @PublicCoin.sender _ _ _ next => fun move => GuardSchedule.pass (next move)
  | _, @PublicCoin.oracle _ _ _ _ next => fun _ => GuardSchedule.pass next
  | _, @PublicCoin.challenge _ _ _ next => (fun _ => true, fun _ _ => GuardSchedule.pass next)

/-! ### Draws reading their squeezes -/

section Reads

open PublicCoin

variable {C₀ : Type} {m : ℕ}

/-- Each draw reads only the coins of its node's squeezes: the first `squeezes node` places. -/
def Decoder.Reads : {protocol : Protocol} → (coin : PublicCoin protocol) →
    Decoder (Fin m → C₀) coin → (Prefix PUnit coin → ℕ) → Prop
  | _, .done, _, _ => True
  | _, @PublicCoin.sender _ _ _ next, dec, squeezes =>
      ∀ move, Decoder.Reads (next move) (dec move) fun node => squeezes ⟨move, node⟩
  | _, @PublicCoin.oracle _ _ _ _ next, dec, squeezes =>
      ∀ message, Decoder.Reads next dec fun node => squeezes ⟨message, node⟩
  | _, @PublicCoin.challenge _ _ _ next, dec, squeezes =>
      (∀ c c' : Fin m → C₀, (∀ i : Fin m, (i : ℕ) < squeezes (.inl PUnit.unit) → c i = c' i) →
        dec.1.accept c = dec.1.accept c' ∧ dec.1.decode c = dec.1.decode c') ∧
      Decoder.Reads next dec.2 fun node => squeezes (.inr ⟨PUnit.unit, node⟩)

end Reads

/-! ### Padded paths -/

section Pad

open PublicCoin StateRestoration Security

variable {S O : Type} [Inhabited S] [Inhabited O] {m : ℕ}

/-- A path of the decoded presentation with each challenge's coins padded at its node's number of
squeezes. -/
def padPath : {protocol : Protocol} → (coin : PublicCoin protocol) →
    (dec : Decoder (Fin m → S × O) coin) → (Prefix PUnit coin → ℕ) →
    (decodedProtocol (Fin m → S × O) coin dec).tree.ExecutionPath →
    (decodedProtocol (Fin m → S × O) coin dec).tree.ExecutionPath
  | _, .done, _, _, path => path
  | _, @PublicCoin.sender _ _ _ next, dec, squeezes, path =>
      ⟨path.1, padPath (next path.1) (dec path.1) (fun node => squeezes ⟨path.1, node⟩) path.2⟩
  | _, @PublicCoin.oracle _ _ _ _ next, dec, squeezes, path =>
      ⟨path.1, padPath next dec (fun node => squeezes ⟨path.1, node⟩) path.2⟩
  | _, @PublicCoin.challenge _ _ _ next, dec, squeezes, path =>
      ⟨path.1, pad (squeezes (.inl PUnit.unit)) path.2.1,
        padPath next dec.2 (fun node => squeezes (.inr ⟨PUnit.unit, node⟩)) path.2.2⟩

/-- Padding a path changes no decoded path, when each draw reads only its node's squeezes. -/
theorem decodePath_padPath : {protocol : Protocol} → (coin : PublicCoin protocol) →
    (dec : Decoder (Fin m → S × O) coin) → (squeezes : Prefix PUnit coin → ℕ) →
    Decoder.Reads coin dec squeezes →
    (path : (decodedProtocol (Fin m → S × O) coin dec).tree.ExecutionPath) →
    decodePath coin dec (padPath coin dec squeezes path) = decodePath coin dec path
  | _, .done, _, _, _, _ => rfl
  | _, @PublicCoin.sender _ _ _ next, dec, squeezes, reads, path => by
      simp only [padPath, decodePath]
      rw [decodePath_padPath (next path.1) (dec path.1) _ (reads path.1) path.2]
  | _, @PublicCoin.oracle _ _ _ _ next, dec, squeezes, reads, path => by
      simp only [padPath, decodePath]
      rw [decodePath_padPath next dec _ (reads path.1) path.2]
  | _, @PublicCoin.challenge _ _ _ next, dec, squeezes, reads, path => by
      have h := reads.1 (pad (squeezes (.inl PUnit.unit)) path.2.1) path.2.1 fun i hi => by
        simp only [pad, hi, ↓reduceIte]
      simp only [padPath, decodePath, h.1, h.2, decodePath_padPath next dec.2 _ reads.2 path.2.2]

/-- Answering through a reindexing answers the reindexed queries. -/
theorem simulateQ_reindexQuery {D D' : Type} {R : D → Type} {ι : Type} {spec : OracleSpec ι}
    (f : D' → D) (impl : QueryImpl (OracleSpec.ofFn R) (OracleComp spec)) {α : Type}
    (P : OracleComp (OracleSpec.ofFn fun q => R (f q)) α) :
    simulateQ impl (simulateQ (reindexQuery f) P) = simulateQ (fun q => impl (f q)) P :=
  QueryImpl.simulateQ_simulateQ_eq_of_apply (fun q => simulateQ_spec_query impl (f q)) P

/-- Answering through a reindexing of a reindexing answers the twice reindexed queries. -/
theorem simulateQ_reindexQuery_comp {D D' D'' : Type} {R : D → Type} {ι : Type}
    {spec : OracleSpec ι} (f : D'' → D') (g : D' → D)
    (impl : QueryImpl (OracleSpec.ofFn R) (OracleComp spec)) {α : Type}
    (P : OracleComp (OracleSpec.ofFn fun q => R (g (f q))) α) :
    simulateQ impl (simulateQ (fun q => reindexQuery g (f q)) P) =
      simulateQ (fun q => impl (g (f q))) P :=
  QueryImpl.simulateQ_simulateQ_eq_of_apply (fun q => simulateQ_spec_query impl (g (f q))) P

variable [SampleableType S] [SampleableType O]

/-- Answer each prefix of the decoded presentation with `impl`'s coins padded at its node's
number of squeezes. -/
noncomputable def padQueries {ι : Type} {spec : OracleSpec ι} {protocol : Protocol}
    (coin : PublicCoin protocol) (dec : Decoder (Fin m → S × O) coin)
    (squeezes : Prefix PUnit coin → ℕ)
    (impl : QueryImpl (StateRestoration.prefixSpec PUnit (decoded (Fin m → S × O) coin dec))
      (OracleComp spec)) :
    QueryImpl (StateRestoration.prefixSpec PUnit (decoded (Fin m → S × O) coin dec))
      (OracleComp spec) :=
  fun pre => (Equiv.cast (challenge_decoded coin dec pre)).symm <$>
    pad (squeezes (Prefix.undecode coin dec pre)) <$>
      Equiv.cast (challenge_decoded coin dec pre) <$> impl pre

/-- **Padding commutes with completion.** Completing a transcript under passing guards with each
challenge's coins padded is completing it and padding the path. -/
theorem simulateQ_padQueries {ι : Type} {spec : OracleSpec ι} :
    {protocol : Protocol} → (coin : PublicCoin protocol) →
    (dec : Decoder (Fin m → S × O) coin) → (squeezes : Prefix PUnit coin → ℕ) →
    (impl : QueryImpl (StateRestoration.prefixSpec PUnit (decoded (Fin m → S × O) coin dec))
      (OracleComp spec)) →
    (messages : Messages PUnit (decoded (Fin m → S × O) coin dec)) →
    simulateQ (padQueries coin dec squeezes impl)
        (stoppedCompletePrefix (decoded (Fin m → S × O) coin dec) (GuardSchedule.pass _)
          messages) =
      Option.map (padPath coin dec squeezes) <$>
        simulateQ impl (stoppedCompletePrefix (decoded (Fin m → S × O) coin dec)
          (GuardSchedule.pass _) messages)
  | _, .done, _, _, _, _ => by
      simp only [stoppedCompletePrefix, simulateQ_pure, map_pure]
      rfl
  | _, @PublicCoin.sender _ _ _ next, dec, squeezes, impl, messages => by
      have ih := simulateQ_padQueries (next messages.1) (dec messages.1)
        (fun node => squeezes ⟨messages.1, node⟩) (fun pre => impl ⟨messages.1, pre⟩) messages.2
      simp only [stoppedCompletePrefix, simulateQ_bind, simulateQ_pure, simulateQ_reindexQuery,
        map_bind, map_pure]
      refine (congrArg (· >>= _) ih).trans ?_
      simp only [bind_map_left]
      exact bind_congr fun a => by cases a <;> rfl
  | _, @PublicCoin.oracle _ _ _ _ next, dec, squeezes, impl, messages => by
      have ih := simulateQ_padQueries next dec (fun node => squeezes ⟨messages.1, node⟩)
        (fun pre => impl ⟨messages.1, pre⟩) messages.2
      simp only [stoppedCompletePrefix, simulateQ_bind, simulateQ_pure, simulateQ_reindexQuery,
        map_bind, map_pure]
      refine (congrArg (· >>= _) ih).trans ?_
      simp only [bind_map_left]
      exact bind_congr fun a => by cases a <;> rfl
  | _, @PublicCoin.challenge _ _ _ next, dec, squeezes, impl, messages => by
      have ih := simulateQ_padQueries next dec.2 (fun node => squeezes (.inr ⟨PUnit.unit, node⟩))
        (fun pre => impl ⟨messages.1, .inr ⟨messages.2.1, pre⟩⟩) messages.2.2
      have hpass : GuardSchedule.pass (Salt := PUnit)
          (decoded (Fin m → S × O) (.challenge next) dec) messages.1 =
          (fun _ => true, fun _ _ => GuardSchedule.pass (decoded (Fin m → S × O) next dec.2)) :=
        rfl
      have ih' : simulateQ (fun q => padQueries (.challenge next) dec squeezes impl
          ⟨messages.1, .inr (messages.2.1, q)⟩) (stoppedCompletePrefix
            (decoded (Fin m → S × O) next dec.2) (GuardSchedule.pass _) messages.2.2) = _ := ih
      simp only [stoppedCompletePrefix, simulateQ_bind, simulateQ_pure, simulateQ_reindexQuery,
        map_bind, map_pure, hpass, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        simulateQ_reindexQuery_comp, bind_assoc, pure_bind]
      rw [ih']
      simp only [simulateQ_spec_query, padQueries, bind_map_left]
      exact bind_congr fun a => bind_congr fun b => by cases b <;> rfl

end Pad

/-! ### The game -/

section Game

open PublicCoin

variable {S I O : Type} [DecidableEq S] [DecidableEq I] [SampleableType S] [SampleableType O]
  [Inhabited S] [Inhabited O] {m : ℕ}
variable {Input W : Type} {protocol : Input → Protocol}
  {coin : (z : Input) → PublicCoin (protocol z)}

/-- The `j`th squeeze after absorbing `x :: p` through the chain from `s₀`. -/
def squeezeAt (s₀ : S) (e x : I) (p : List I) :
    ℕ → OracleComp (unifSpec + (chainSpec S I O + []ₒ)) (S × O)
  | 0 => absorb s₀ x p
  | j + 1 => absorb s₀ e (squeezePrefix e x p j)

/-- The number of squeezes at a key of the decoded presentation: its node's. -/
noncomputable def keySqueezes (dec : (z : Input) → Decoder (Fin m → S × O) (coin z))
    (squeezes : (z : Input) → Prefix PUnit (coin z) → ℕ)
    (key : Key Input PUnit fun z => decoded (Fin m → S × O) (coin z) (dec z)) : ℕ :=
  squeezes key.1 (Prefix.undecode (coin key.1) (dec key.1) key.2)

/-- The Fiat–Shamir verifier's coins at a key: absorb the key's encoding through the chain from
`s₀`, squeeze as often as the key's node, and pad. -/
noncomputable def squeezeCompletionQueries (s₀ : S) (e : I)
    (dec : (z : Input) → Decoder (Fin m → S × O) (coin z))
    (squeezes : (z : Input) → Prefix PUnit (coin z) → ℕ)
    (encode : (Key Input PUnit fun z => decoded (Fin m → S × O) (coin z) (dec z)) → I × List I) :
    QueryImpl (oracleSpec Input PUnit fun z => decoded (Fin m → S × O) (coin z) (dec z))
      (OracleComp (unifSpec + (chainSpec S I O + []ₒ))) :=
  fun key => ((Security.decodedCommon coin dec).challengeEquiv key).symm <$> coinsOf <$>
    squeezeAnswers (squeezeAt s₀ e (encode key).1 (encode key).2)
      (keySqueezes dec squeezes key)

/-- Complete a selected transcript of the decoded presentation, each challenge's coins squeezed
from the chain. -/
noncomputable def squeezeCompletionAfter (s₀ : S) (e : I)
    (dec : (z : Input) → Decoder (Fin m → S × O) (coin z))
    (squeezes : (z : Input) → Prefix PUnit (coin z) → ℕ)
    (encode : (Key Input PUnit fun z => decoded (Fin m → S × O) (coin z) (dec z)) → I × List I)
    (selected :
      Option (Selection Input PUnit W fun z => decoded (Fin m → S × O) (coin z) (dec z))) :
    OracleComp (unifSpec + (chainSpec S I O + []ₒ))
      (Option (Outcome Input W fun z => decodedProtocol (Fin m → S × O) (coin z) (dec z))) :=
  match selected with
  | none => pure none
  | some ⟨z, messages, witness⟩ =>
      (fun path => path.map (fun p => ⟨z, p, witness⟩)) <$>
        simulateQ (squeezeCompletionQueries s₀ e dec squeezes encode)
          (stoppedComplete (fun z => decoded (Fin m → S × O) (coin z) (dec z))
            (fun _ => GuardSchedule.pass _) z messages)

/-- The Fiat–Shamir game on a hash chain with challenges of several squeezes: the adversary
queries the chain and selects a transcript of the decoded presentation, and the verifier
completes it, squeezing each challenge's coins from the same chain. -/
noncomputable def squeezeExecution (s₀ : S) (e : I)
    (dec : (z : Input) → Decoder (Fin m → S × O) (coin z))
    (squeezes : (z : Input) → Prefix PUnit (coin z) → ℕ)
    (encode : (Key Input PUnit fun z => decoded (Fin m → S × O) (coin z) (dec z)) → I × List I)
    (adversary : OracleComp (unifSpec + (chainSpec S I O + []ₒ))
      (Option (Selection Input PUnit W fun z => decoded (Fin m → S × O) (coin z) (dec z)))) :
    OracleComp (unifSpec + (chainSpec S I O + []ₒ))
      (Option (Outcome Input W fun z => decodedProtocol (Fin m → S × O) (coin z) (dec z))) :=
  adversary >>= squeezeCompletionAfter s₀ e dec squeezes encode

end Game

/-! ### Groups read from one side of an oracle -/

section Lift

variable {B K R : Type} [DecidableEq B] [DecidableEq K] [SampleableType R]

/-- Answer the oracle on `B` from the left side of the oracle on `B ⊕ K`. -/
def liftInl : QueryImpl (unifSpec + (B →ₒ R)) (OracleComp (unifSpec + ((B ⊕ K) →ₒ R)))
  | .inl n => liftM ((unifSpec + ((B ⊕ K) →ₒ R)).query (.inl n))
  | .inr b => liftM ((unifSpec + ((B ⊕ K) →ₒ R)).query (.inr (.inl b)))

/-- The left side of a cache of the oracle on `B ⊕ K`. -/
def inlCache (c : ((B ⊕ K) →ₒ R).QueryCache) : (B →ₒ R).QueryCache :=
  QueryCache.ofFn fun b => c (.inl b)

omit [SampleableType R] in
theorem inlCache_cacheQuery (c : ((B ⊕ K) →ₒ R).QueryCache) (b : B) (u : R) :
    inlCache (c.cacheQuery (.inl b) u) = (inlCache c).cacheQuery b u := by
  refine QueryCache.ext fun b' => ?_
  by_cases h : b' = b
  · subst h
    simp only [inlCache, QueryCache.ofFn_apply, QueryCache.cacheQuery_self]
  · rw [QueryCache.cacheQuery_of_ne _ _ h]
    simp only [inlCache, QueryCache.ofFn_apply]
    exact QueryCache.cacheQuery_of_ne _ _ (by simpa only [ne_eq, Sum.inl.injEq] using h)

/-- The random oracle on `B ⊕ K`, read on its left side, is the random oracle on `B`. -/
theorem map_run_liftInl {α : Type} (P : OracleComp (unifSpec + (B →ₒ R)) α)
    (c : ((B ⊕ K) →ₒ R).QueryCache) :
    (fun z => (z.1, inlCache z.2)) <$>
        (simulateQ ((B ⊕ K) →ₒ R).romImpl (simulateQ liftInl P)).run c =
      (simulateQ (B →ₒ R).romImpl P).run (inlCache c) := by
  induction P using OracleComp.inductionOn generalizing c with
  | pure a => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rcases t with n | b
    · simp only [liftInl, simulateQ_spec_query, romImpl_run_unif, bind_map_left, ih]
    · simp only [liftInl, simulateQ_spec_query]
      cases hc : c (.inl b) with
      | some u =>
        rw [romImpl_run_of_some hc, romImpl_run_of_some (show inlCache c b = some u from hc),
          pure_bind, pure_bind, ih]
      | none =>
        rw [romImpl_run_of_none hc, romImpl_run_of_none (show inlCache c b = none from hc)]
        simp only [bind_map_left, ih, inlCache_cacheQuery]

/-- An event of a program's output on the oracle on `B` has the same probability on the left side
of the oracle on `B ⊕ K`. -/
theorem prEvent_run'_liftInl {α : Type} (P : OracleComp (unifSpec + (B →ₒ R)) α)
    (E : α → Prop) :
    Pr{let a ← (simulateQ (B →ₒ R).romImpl P).run' ∅}[E a] =
      Pr{let a ← (simulateQ ((B ⊕ K) →ₒ R).romImpl (simulateQ liftInl P)).run' ∅}[E a] := by
  have h := map_run_liftInl (K := K) P ∅
  have h0 : inlCache (∅ : ((B ⊕ K) →ₒ R).QueryCache) = ∅ := QueryCache.ext fun _ => rfl
  rw [h0] at h
  simp only [StateT.run'_eq, ← h, Functor.map_map]

omit [DecidableEq B] [DecidableEq K] [SampleableType R] in
/-- Reading the left side makes one query per query. -/
theorem isQueryBoundP_liftInl {α : Type} {P : OracleComp (unifSpec + (B →ₒ R)) α} {q : ℕ}
    (hP : IsQueryBoundP P (fun t => isUnif t = false) q) :
    IsQueryBoundP (simulateQ (liftInl (K := K)) P) (fun t => isUnif t = false) q := by
  refine hP.simulateQ_of_step (fun t ht => ?_) (fun t ht => ?_)
  · rcases t with n | b
    · cases ht
    · exact (isQueryBoundP_query_iff _ _ _).mpr fun _ => Nat.one_pos
  · rcases t with n | b
    · exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [isUnif])
    · exact absurd rfl ht

end Lift

/-! ### The verifier on the prefix oracle and on the grouped oracle -/

section Reduction

open PublicCoin Security

variable {S I O : Type} [DecidableEq S] [DecidableEq I] [SampleableType S] [SampleableType O]
  [Inhabited S] [Inhabited O] {m : ℕ}
variable {Input W : Type} {protocol : Input → Protocol}
  {coin : (z : Input) → PublicCoin (protocol z)}

omit [DecidableEq S] [DecidableEq I] in
/-- The verifier's coins at a key read off the prefix oracle: its answers at the prefixes of the
key's squeezes. -/
noncomputable def prefixSqueezeQueries (e : I)
    (dec : (z : Input) → Decoder (Fin m → S × O) (coin z))
    (squeezes : (z : Input) → Prefix PUnit (coin z) → ℕ)
    (encode : (Key Input PUnit fun z => decoded (Fin m → S × O) (coin z) (dec z)) → I × List I) :
    QueryImpl (oracleSpec Input PUnit fun z => decoded (Fin m → S × O) (coin z) (dec z))
      (OracleComp (unifSpec + (List I →ₒ (S × O)))) :=
  fun key => ((decodedCommon coin dec).challengeEquiv key).symm <$> coinsOf <$>
    squeezeAnswers (fun j => liftM ((unifSpec + (List I →ₒ (S × O))).query
      (.inr (squeezePrefix e (encode key).1 (encode key).2 j)))) (keySqueezes dec squeezes key)

omit [DecidableEq S] [DecidableEq I] in
/-- Complete a selected transcript of the decoded presentation, each challenge's coins read off
the prefix oracle. -/
noncomputable def prefixSqueezeCompletionAfter (e : I)
    (dec : (z : Input) → Decoder (Fin m → S × O) (coin z))
    (squeezes : (z : Input) → Prefix PUnit (coin z) → ℕ)
    (encode : (Key Input PUnit fun z => decoded (Fin m → S × O) (coin z) (dec z)) → I × List I)
    (selected :
      Option (Selection Input PUnit W fun z => decoded (Fin m → S × O) (coin z) (dec z))) :
    OracleComp (unifSpec + (List I →ₒ (S × O)))
      (Option (Outcome Input W fun z => decodedProtocol (Fin m → S × O) (coin z) (dec z))) :=
  match selected with
  | none => pure none
  | some ⟨z, messages, witness⟩ =>
      (fun path => path.map (fun p => ⟨z, p, witness⟩)) <$>
        simulateQ (prefixSqueezeQueries e dec squeezes encode)
          (stoppedComplete (fun z => decoded (Fin m → S × O) (coin z) (dec z))
            (fun _ => GuardSchedule.pass _) z messages)

omit [DecidableEq S] [Inhabited S] [Inhabited O] in
/-- The grouped oracle's point of a key: the base of its squeezes' group if it squeezes, the key
itself if not. -/
noncomputable def squeezePoint (e : I) (m : ℕ)
    (dec : (z : Input) → Decoder (Fin m → S × O) (coin z))
    (squeezes : (z : Input) → Prefix PUnit (coin z) → ℕ)
    (encode : (Key Input PUnit fun z => decoded (Fin m → S × O) (coin z) (dec z)) → I × List I)
    (nonempty : ∀ key, keySqueezes dec squeezes key ≠ 0 → (encode key).1 ≠ e)
    (key : Key Input PUnit fun z => decoded (Fin m → S × O) (coin z) (dec z)) :
    SqueezeBase e m ⊕ Key Input PUnit fun z => decoded (Fin m → S × O) (coin z) (dec z) :=
  if h : keySqueezes dec squeezes key = 0 then .inr key
  else .inl (squeezeBase e m (nonempty key h) (encode key).2)

omit [DecidableEq S] [Inhabited S] [Inhabited O] in
/-- Distinct keys have distinct points when the encodings of the keys that squeeze are
distinct. -/
theorem squeezePoint_injective (e : I) (m : ℕ)
    (dec : (z : Input) → Decoder (Fin m → S × O) (coin z))
    (squeezes : (z : Input) → Prefix PUnit (coin z) → ℕ)
    (encode : (Key Input PUnit fun z => decoded (Fin m → S × O) (coin z) (dec z)) → I × List I)
    (injective : ∀ key key', keySqueezes dec squeezes key ≠ 0 →
      keySqueezes dec squeezes key' ≠ 0 → encode key = encode key' → key = key')
    (nonempty : ∀ key, keySqueezes dec squeezes key ≠ 0 → (encode key).1 ≠ e) :
    Function.Injective (squeezePoint e m dec squeezes encode nonempty) := by
  intro key key' h
  by_cases h₁ : keySqueezes dec squeezes key = 0 <;>
    by_cases h₂ : keySqueezes dec squeezes key' = 0 <;>
    simp only [squeezePoint, h₁, h₂, ↓reduceDIte, reduceCtorEq, Sum.inr.injEq, Sum.inl.injEq,
      squeezeBase, Subtype.mk.injEq, List.cons.injEq] at h
  · exact h
  · exact injective key key' h₁ h₂ (Prod.ext h.1 h.2)

omit [DecidableEq S] [Inhabited S] [Inhabited O] in
/-- The strict codec of keys into the grouped oracle's points. -/
noncomputable def squeezeCodec (e : I) (m : ℕ)
    (dec : (z : Input) → Decoder (Fin m → S × O) (coin z))
    (squeezes : (z : Input) → Prefix PUnit (coin z) → ℕ)
    (encode : (Key Input PUnit fun z => decoded (Fin m → S × O) (coin z) (dec z)) → I × List I)
    (injective : ∀ key key', keySqueezes dec squeezes key ≠ 0 →
      keySqueezes dec squeezes key' ≠ 0 → encode key = encode key' → key = key')
    (nonempty : ∀ key, keySqueezes dec squeezes key ≠ 0 → (encode key).1 ≠ e) :
    StrictCodec (Key Input PUnit fun z => decoded (Fin m → S × O) (coin z) (dec z))
      (SqueezeBase e m ⊕ Key Input PUnit fun z => decoded (Fin m → S × O) (coin z) (dec z)) where
  encode := squeezePoint e m dec squeezes encode nonempty
  decode d := open Classical in
    if h : ∃ key, squeezePoint e m dec squeezes encode nonempty key = d then some h.choose
    else none
  decode_encode key := by
    have h : ∃ key', squeezePoint e m dec squeezes encode nonempty key' =
        squeezePoint e m dec squeezes encode nonempty key := ⟨key, rfl⟩
    simp only [h, ↓reduceDIte]
    exact congrArg some
      (squeezePoint_injective e m dec squeezes encode injective nonempty h.choose_spec)
  encode_decode d key h := by
    split_ifs at h with hd
    cases h
    exact hd.choose_spec

omit [DecidableEq S] [DecidableEq I] in
/-- Answer each key of the decoded presentation with `impl`'s coins padded at its number of
squeezes. -/
noncomputable def padKeyQueries {ι : Type} {spec : OracleSpec ι}
    (dec : (z : Input) → Decoder (Fin m → S × O) (coin z))
    (squeezes : (z : Input) → Prefix PUnit (coin z) → ℕ)
    (impl : QueryImpl (oracleSpec Input PUnit fun z => decoded (Fin m → S × O) (coin z) (dec z))
      (OracleComp spec)) :
    QueryImpl (oracleSpec Input PUnit fun z => decoded (Fin m → S × O) (coin z) (dec z))
      (OracleComp spec) :=
  fun key => ((decodedCommon coin dec).challengeEquiv key).symm <$>
    pad (keySqueezes dec squeezes key) <$> (decodedCommon coin dec).challengeEquiv key <$> impl key

omit [DecidableEq S] [DecidableEq I] in
/-- Completing a selected transcript with each key's coins padded is completing it and padding
the path. -/
theorem simulateQ_padKeyQueries {ι : Type} {spec : OracleSpec ι}
    (dec : (z : Input) → Decoder (Fin m → S × O) (coin z))
    (squeezes : (z : Input) → Prefix PUnit (coin z) → ℕ)
    (impl : QueryImpl (oracleSpec Input PUnit fun z => decoded (Fin m → S × O) (coin z) (dec z))
      (OracleComp spec)) (z : Input)
    (messages : Messages PUnit (decoded (Fin m → S × O) (coin z) (dec z))) :
    simulateQ (padKeyQueries dec squeezes impl)
        (stoppedComplete (fun z => decoded (Fin m → S × O) (coin z) (dec z))
          (fun _ => GuardSchedule.pass _) z messages) =
      Option.map (padPath (coin z) (dec z) (squeezes z)) <$>
        simulateQ impl (stoppedComplete (fun z => decoded (Fin m → S × O) (coin z) (dec z))
          (fun _ => GuardSchedule.pass _) z messages) := by
  simp only [stoppedComplete, inputQuery, simulateQ_reindexQuery]
  exact simulateQ_padQueries (coin z) (dec z) (squeezes z) (fun pre => impl ⟨z, pre⟩) messages

omit [DecidableEq S] in
/-- **A key's squeezes on the grouped oracle.** Read through `ungroup`, the squeezes of a key that
squeezes are components of the grouped oracle's answer at its base, and run as that answer read
once and padded; a key squeezed `0` times makes no query, and its padded answer is the same after
a discarded query at the key. -/
theorem squeezeQueries_grouped [NeZero m] [DecidableEq Input] (e : I)
    (dec : (z : Input) → Decoder (Fin m → S × O) (coin z))
    (squeezes : (z : Input) → Prefix PUnit (coin z) → ℕ)
    (hsqueezes : ∀ z node, squeezes z node ≤ m)
    (encode : (Key Input PUnit fun z => decoded (Fin m → S × O) (coin z) (dec z)) → I × List I)
    (injective : ∀ key key', keySqueezes dec squeezes key ≠ 0 →
      keySqueezes dec squeezes key' ≠ 0 → encode key = encode key' → key = key')
    (nonempty : ∀ key, keySqueezes dec squeezes key ≠ 0 → (encode key).1 ≠ e)
    (key : Key Input PUnit fun z => decoded (Fin m → S × O) (coin z) (dec z)) :
    simulateQ ((SqueezeBase e m ⊕ Key Input PUnit fun z => decoded (Fin m → S × O) (coin z)
          (dec z)) →ₒ (Fin m → S × O)).romImpl
        (padKeyQueries dec squeezes (encodedCompletionQueries (decodedCommon coin dec)
          (squeezeCodec e m dec squeezes encode injective nonempty)) key) =
      simulateQ ((SqueezeBase e m ⊕ Key Input PUnit fun z => decoded (Fin m → S × O) (coin z)
          (dec z)) →ₒ (Fin m → S × O)).romImpl
        (simulateQ liftInl (simulateQ (ungroup (squeezeEquiv e m))
          (prefixSqueezeQueries e dec squeezes encode key))) ∨
    ∃ t, padKeyQueries dec squeezes (encodedCompletionQueries (decodedCommon coin dec)
          (squeezeCodec e m dec squeezes encode injective nonempty)) key =
        liftM ((unifSpec + ((SqueezeBase e m ⊕ Key Input PUnit fun z =>
          decoded (Fin m → S × O) (coin z) (dec z)) →ₒ (Fin m → S × O))).query (.inr t)) >>=
          fun _ => simulateQ liftInl (simulateQ (ungroup (squeezeEquiv e m))
            (prefixSqueezeQueries e dec squeezes encode key)) := by
  by_cases h0 : keySqueezes dec squeezes key = 0
  · refine .inr ⟨.inr key, ?_⟩
    have hp : squeezePoint e m dec squeezes encode nonempty key = .inr key :=
      dite_eq_left_of_eq_true (eq_true h0)
    simp only [prefixSqueezeQueries, h0, squeezeAnswers, map_pure, simulateQ_pure]
    simp only [padKeyQueries, encodedCompletionQueries, h0]
    rw [show (squeezeCodec e m dec squeezes encode injective nonempty).encode key = .inr key
      from hp]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
      Equiv.apply_symm_apply]
    refine bind_congr fun x => congrArg pure (congrArg _ (funext fun i => ?_))
    simp only [pad, Nat.not_lt_zero, ↓reduceIte]
    rfl
  · refine .inl ?_
    have hx := nonempty key h0
    have hp : squeezePoint e m dec squeezes encode nonempty key =
        .inl (squeezeBase e m hx (encode key).2) := dite_eq_right_of_eq_false (eq_false h0)
    have hn : keySqueezes dec squeezes key ≤ m := hsqueezes _ _
    have hq : ∀ j < keySqueezes dec squeezes key,
        simulateQ (liftInl (K := Key Input PUnit fun z => decoded (Fin m → S × O) (coin z) (dec z)))
          (ungroup (R := S × O) (squeezeEquiv e m)
          (.inr (squeezePrefix e (encode key).1 (encode key).2 j))) =
        (fun g => if h : j < m then g ⟨j, h⟩ else default) <$>
          liftM ((unifSpec + ((SqueezeBase e m ⊕ Key Input PUnit fun z =>
            decoded (Fin m → S × O) (coin z) (dec z)) →ₒ (Fin m → S × O))).query
              (.inr (.inl (squeezeBase e m hx (encode key).2)))) := by
      intro j hj
      have hjm : j < m := lt_of_lt_of_le hj hn
      have he := squeezeEquiv_squeezePrefix e m hx (encode key).2 ⟨j, hjm⟩
      simp only at he
      simp only [ungroup, simulateQ_map, simulateQ_spec_query, liftInl, hjm, dite_true]
      rw [he]
      rfl
    simp only [prefixSqueezeQueries, simulateQ_map, simulateQ_squeezeAnswers,
      simulateQ_spec_query]
    rw [squeezeAnswers_congr hq, simulateQ_romImpl_squeezeAnswers _ _ _ (Nat.pos_of_ne_zero h0)]
    simp only [padKeyQueries, encodedCompletionQueries]
    rw [show (squeezeCodec e m dec squeezes encode injective nonempty).encode key =
      .inl (squeezeBase e m hx (encode key).2) from hp]
    simp only [simulateQ_map, Functor.map_map, Equiv.apply_symm_apply, coinsOf_map_range]

omit [DecidableEq S] in
/-- **The verifier on the grouped oracle.** Read through `ungroup` on the left side of the oracle on
bases and keys, the verifier's completion on the prefix oracle completes a selected transcript as
the encoded random oracle's verifier does, with each challenge's coins padded, up to the discarded
queries of the keys squeezed `0` times. An event that ignores padding has the same probability. -/
theorem prEvent_prefixSqueeze_eq_grouped [NeZero m] [DecidableEq Input] (e : I)
    (dec : (z : Input) → Decoder (Fin m → S × O) (coin z))
    (squeezes : (z : Input) → Prefix PUnit (coin z) → ℕ)
    (hsqueezes : ∀ z node, squeezes z node ≤ m)
    (encode : (Key Input PUnit fun z => decoded (Fin m → S × O) (coin z) (dec z)) → I × List I)
    (injective : ∀ key key', keySqueezes dec squeezes key ≠ 0 →
      keySqueezes dec squeezes key' ≠ 0 → encode key = encode key' → key = key')
    (nonempty : ∀ key, keySqueezes dec squeezes key ≠ 0 → (encode key).1 ≠ e)
    (external : OracleComp (unifSpec + (List I →ₒ (S × O)))
      (Option (Selection Input PUnit W fun z => decoded (Fin m → S × O) (coin z) (dec z))))
    (E : Option (Outcome Input W fun z => decodedProtocol (Fin m → S × O) (coin z) (dec z)) → Prop)
    (hE : ∀ r, E (r.map fun o => ⟨o.1, padPath (coin o.1) (dec o.1) (squeezes o.1) o.2.1, o.2.2⟩) ↔
      E r) :
    Pr{let r ← (simulateQ (List I →ₒ (S × O)).romImpl
        (external >>= prefixSqueezeCompletionAfter e dec squeezes encode)).run' ∅}[E r] =
      Pr{let r ← (simulateQ ((SqueezeBase e m ⊕ Key Input PUnit fun z =>
          decoded (Fin m → S × O) (coin z) (dec z)) →ₒ (Fin m → S × O)).romImpl
        (simulateQ liftInl (simulateQ (ungroup (squeezeEquiv e m)) external) >>=
          encodedExternalCompletionAfter (fun z => decoded (Fin m → S × O) (coin z) (dec z))
            (decodedCommon coin dec) (squeezeCodec e m dec squeezes encode injective nonempty)
            (fun _ => GuardSchedule.pass _))).run' ∅}[E r] := by
  rw [prEvent_run'_ungroup (squeezeEquiv e m),
    prEvent_run'_liftInl (K := Key Input PUnit fun z => decoded (Fin m → S × O) (coin z) (dec z))]
  let padOutcome : Option (Outcome Input W fun z => decodedProtocol (Fin m → S × O) (coin z)
      (dec z)) → Option (Outcome Input W fun z => decodedProtocol (Fin m → S × O) (coin z)
      (dec z)) := fun r => r.map fun o => ⟨o.1, padPath (coin o.1) (dec o.1) (squeezes o.1) o.2.1,
        o.2.2⟩
  let codec := squeezeCodec e m dec squeezes encode injective nonempty
  let G := (SqueezeBase e m ⊕ Key Input PUnit fun z =>
    decoded (Fin m → S × O) (coin z) (dec z)) →ₒ (Fin m → S × O)
  let impl₀ := liftInl (K := Key Input PUnit fun z => decoded (Fin m → S × O) (coin z) (dec z)) ∘ₛ
    (ungroup (R := S × O) (squeezeEquiv e m) ∘ₛ prefixSqueezeQueries e dec squeezes encode)
  let impl₁ := padKeyQueries dec squeezes
    (encodedCompletionQueries (decodedCommon coin dec) codec)
  have hsel : ∀ selected c,
      (simulateQ G.romImpl (simulateQ liftInl (simulateQ (ungroup (squeezeEquiv e m))
        (prefixSqueezeCompletionAfter e dec squeezes encode selected)))).run' c =ᵈ
      (simulateQ G.romImpl (padOutcome <$> encodedExternalCompletionAfter
        (fun z => decoded (Fin m → S × O) (coin z) (dec z)) (decodedCommon coin dec) codec
        (fun _ => GuardSchedule.pass _) selected)).run' c := by
    rintro (_ | ⟨z, messages, witness⟩) c
    · simp only [prefixSqueezeCompletionAfter, encodedExternalCompletionAfter, simulateQ_pure,
        map_pure]
      exact EvalDistEq.rfl
    · have h₀ : simulateQ liftInl (simulateQ (ungroup (squeezeEquiv e m))
          (prefixSqueezeCompletionAfter e dec squeezes encode (some ⟨z, messages, witness⟩))) =
          simulateQ impl₀ ((fun path => path.map (fun p => ⟨z, p, witness⟩)) <$>
            stoppedComplete (fun z => decoded (Fin m → S × O) (coin z) (dec z))
              (fun _ => GuardSchedule.pass _) z messages) := by
        simp only [prefixSqueezeCompletionAfter, impl₀, QueryImpl.simulateQ_compose,
          simulateQ_map]
      have h₁ : padOutcome <$> encodedExternalCompletionAfter
          (fun z => decoded (Fin m → S × O) (coin z) (dec z)) (decodedCommon coin dec) codec
          (fun _ => GuardSchedule.pass _) (some ⟨z, messages, witness⟩) =
          simulateQ impl₁ ((fun path => path.map (fun p => ⟨z, p, witness⟩)) <$>
            stoppedComplete (fun z => decoded (Fin m → S × O) (coin z) (dec z))
              (fun _ => GuardSchedule.pass _) z messages) := by
        simp only [encodedExternalCompletionAfter, impl₁, simulateQ_map,
          simulateQ_padKeyQueries, Functor.map_map]
        refine congrArg (· <$> _) (funext fun path => ?_)
        cases path <;> rfl
      rw [h₀, h₁]
      exact (evalDistEq_run'_simulateQ_of_discard impl₀ impl₁ (fun key =>
        squeezeQueries_grouped e dec squeezes hsqueezes encode injective nonempty key) _ c).symm
  have hrun : (simulateQ G.romImpl (simulateQ liftInl (simulateQ (ungroup (squeezeEquiv e m))
      (external >>= prefixSqueezeCompletionAfter e dec squeezes encode)))).run' ∅ =ᵈ
      padOutcome <$> (simulateQ G.romImpl
        (simulateQ liftInl (simulateQ (ungroup (squeezeEquiv e m)) external) >>=
          encodedExternalCompletionAfter (fun z => decoded (Fin m → S × O) (coin z) (dec z))
            (decodedCommon coin dec) codec (fun _ => GuardSchedule.pass _))).run' ∅ := by
    simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
    exact EvalDistEq.bind_congr .rfl fun p => by
      simpa only [StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map] using
        hsel p.1 p.2
  refine (hrun.prEvent_eq E).trans ?_
  rw [prEvent_map]
  exact prEvent_congr _ _ _ hE

omit [DecidableEq S] [DecidableEq I] in
/-- The verifier's completion draws no private coin. -/
theorem isQueryBoundP_squeezeCompletionAfter (s₀ : S) (e : I)
    (dec : (z : Input) → Decoder (Fin m → S × O) (coin z))
    (squeezes : (z : Input) → Prefix PUnit (coin z) → ℕ)
    (encode : (Key Input PUnit fun z => decoded (Fin m → S × O) (coin z) (dec z)) → I × List I)
    (selected :
      Option (Selection Input PUnit W fun z => decoded (Fin m → S × O) (coin z) (dec z))) :
    IsQueryBoundP (squeezeCompletionAfter s₀ e dec squeezes encode selected)
      (fun t => isUnif t = true) 0 := by
  rcases selected with _ | ⟨z, messages, witness⟩
  · trivial
  · refine (isQueryBoundP_map_iff _ _ _).mpr (isQueryBoundP_simulateQ_zero _ fun key => ?_)
    refine (isQueryBoundP_map_iff _ _ _).mpr ((isQueryBoundP_map_iff _ _ _).mpr
      (isQueryBoundP_squeezeAnswers (fun j => ?_) _))
    cases j <;> exact isQueryBoundP_absorb s₀ _ _

omit [SampleableType S] [SampleableType O] [Inhabited S] [Inhabited O] in
/-- Off a collision, replaying a squeeze through `view` answers the prefix oracle's cached answer at
the squeeze's prefix. -/
theorem replay_squeezeAt (s₀ : S) (e x : I) (p : List I) {σ : IdealState S I O []ₒ} (hI : Inv σ)
    (hG : Good s₀ σ.1) (j : ℕ) (v : S × O)
    (h : replay (view s₀ σ) (squeezeAt s₀ e x p j) = some v) :
    replay (dropCache σ.2)
      (liftM ((unifSpec + (List I →ₒ (S × O))).query (.inr (squeezePrefix e x p j)))) =
      some v := by
  have hcache : σ.2 (.inl (squeezePrefix e x p j)) = some v := by
    cases j with
    | zero => exact replay_view_absorb s₀ hI hG x p v h
    | succ j => exact replay_view_absorb s₀ hI hG e _ v h
  simpa [replay, cacheAnswers] using hcache

/-- Off a collision, replaying the verifier's chain completion through `view` succeeds as replaying
its completion on the prefix oracle's cache. -/
theorem replay_squeezeCompletion (s₀ : S) (e : I)
    (dec : (z : Input) → Decoder (Fin m → S × O) (coin z))
    (squeezes : (z : Input) → Prefix PUnit (coin z) → ℕ)
    (encode : (Key Input PUnit fun z => decoded (Fin m → S × O) (coin z) (dec z)) → I × List I)
    {σ : IdealState S I O []ₒ} (hI : Inv σ) (hG : Good s₀ σ.1)
    (selected : Option (Selection Input PUnit W fun z => decoded (Fin m → S × O) (coin z) (dec z)))
    (r : Option (Outcome Input W fun z => decodedProtocol (Fin m → S × O) (coin z) (dec z)))
    (h : replay (view s₀ σ) (squeezeCompletionAfter s₀ e dec squeezes encode selected) = some r) :
    replay (dropCache σ.2) (prefixSqueezeCompletionAfter e dec squeezes encode selected) =
      some r := by
  rcases selected with _ | ⟨z, messages, witness⟩
  · simpa [squeezeCompletionAfter, prefixSqueezeCompletionAfter] using h
  · simp only [squeezeCompletionAfter, prefixSqueezeCompletionAfter, replay_map] at h ⊢
    obtain ⟨path, hpath, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [replay_simulateQ_of_forall (view s₀ σ) (dropCache σ.2) _ _ (fun key u hu => ?_) _ path
      hpath]
    · rfl
    simp only [squeezeCompletionQueries, prefixSqueezeQueries, replay_map] at hu ⊢
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hu
    obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp hc
    rw [replay_squeezeAnswers (view s₀ σ) (dropCache σ.2)
      (fun j v hv => replay_squeezeAt s₀ e _ _ hI hG j v hv) _ l hl]
    rfl

/-- The adversary extended by the verifier's completion of its selection, returning both. -/
noncomputable def squeezeAdversary (s₀ : S) (e : I)
    (dec : (z : Input) → Decoder (Fin m → S × O) (coin z))
    (squeezes : (z : Input) → Prefix PUnit (coin z) → ℕ)
    (encode : (Key Input PUnit fun z => decoded (Fin m → S × O) (coin z) (dec z)) → I × List I)
    (adversary : OracleComp (unifSpec + (chainSpec S I O + []ₒ))
      (Option (Selection Input PUnit W fun z => decoded (Fin m → S × O) (coin z) (dec z)))) :
    OracleComp (unifSpec + (chainSpec S I O + []ₒ))
      (Option (Selection Input PUnit W fun z => decoded (Fin m → S × O) (coin z) (dec z)) ×
        Option (Outcome Input W fun z => decodedProtocol (Fin m → S × O) (coin z) (dec z))) :=
  adversary >>= fun selected =>
    (selected, ·) <$> squeezeCompletionAfter s₀ e dec squeezes encode selected

omit [DecidableEq S] [DecidableEq I] in
/-- The game is the extended adversary's run, read off its completion. -/
theorem squeezeExecution_eq (s₀ : S) (e : I)
    (dec : (z : Input) → Decoder (Fin m → S × O) (coin z))
    (squeezes : (z : Input) → Prefix PUnit (coin z) → ℕ)
    (encode : (Key Input PUnit fun z => decoded (Fin m → S × O) (coin z) (dec z)) → I × List I)
    (adversary : OracleComp (unifSpec + (chainSpec S I O + []ₒ))
      (Option (Selection Input PUnit W fun z => decoded (Fin m → S × O) (coin z) (dec z)))) :
    squeezeExecution s₀ e dec squeezes encode adversary =
      Prod.snd <$> squeezeAdversary s₀ e dec squeezes encode adversary := by
  simp only [squeezeExecution, squeezeAdversary, map_bind, Functor.map_map]
  simp

/-- **Off a collision, the prefix oracle.** An event of the verifier's completed path on the hash
chain is at most the same event of its completion on the prefix oracle, after the simulated
extended adversary, plus `chainError S q`. -/
theorem prEvent_squeezeExecution_le (s₀ : S) (e : I)
    (dec : (z : Input) → Decoder (Fin m → S × O) (coin z))
    (squeezes : (z : Input) → Prefix PUnit (coin z) → ℕ)
    (encode : (Key Input PUnit fun z => decoded (Fin m → S × O) (coin z) (dec z)) → I × List I)
    (adversary : OracleComp (unifSpec + (chainSpec S I O + []ₒ))
      (Option (Selection Input PUnit W fun z => decoded (Fin m → S × O) (coin z) (dec z))))
    {q : ℕ} (hq : IsQueryBoundP (squeezeExecution s₀ e dec squeezes encode adversary)
      (fun t => isChain t = true) q)
    (E : Option (Outcome Input W fun z => decodedProtocol (Fin m → S × O) (coin z) (dec z)) →
      Prop) :
    Pr{let result ← (simulateQ (chainSpec S I O + []ₒ).romImpl
        (squeezeExecution s₀ e dec squeezes encode adversary)).run' ∅}[E result] ≤
      Pr{let r ← (simulateQ (List I →ₒ (S × O)).romImpl
        ((Prod.fst <$> simulateQ dropEmpty (simulate s₀
          (squeezeAdversary s₀ e dec squeezes encode adversary))) >>=
            prefixSqueezeCompletionAfter e dec squeezes encode)).run' ∅}[E r] +
        chainError S q := by
  classical
  let cc := squeezeCompletionAfter (W := W) s₀ e dec squeezes encode
  let enc := prefixSqueezeCompletionAfter (W := W) e dec squeezes encode
  let Aplus := squeezeAdversary s₀ e dec squeezes encode adversary
  have hG := squeezeExecution_eq s₀ e dec squeezes encode adversary
  have hqA : IsQueryBoundP Aplus (fun t => isChain t = true) q := by
    rw [hG] at hq
    exact (isQueryBoundP_map_iff _ _ _).mp hq
  -- The game's event is an event of the extended adversary's output and final chain cache.
  have h1 : Pr{let result ← (simulateQ (chainSpec S I O + []ₒ).romImpl
      (squeezeExecution s₀ e dec squeezes encode adversary)).run' ∅}[E result] ≤
      Pr{let z ← (simulateQ (chainSpec S I O + []ₒ).romImpl Aplus).run ∅}[
        replay z.2 (cc z.1.1) = some z.1.2 ∧ E z.1.2] := by
    have e1 : (simulateQ (chainSpec S I O + []ₒ).romImpl
        (squeezeExecution s₀ e dec squeezes encode adversary)).run' ∅ =
        (fun z => z.1.2) <$> (simulateQ (chainSpec S I O + []ₒ).romImpl Aplus).run ∅ := by
      rw [hG]
      change Prod.fst <$> (simulateQ (chainSpec S I O + []ₒ).romImpl (Prod.snd <$> Aplus)).run ∅ =
        _
      rw [simulateQ_map, StateT.run_map, Functor.map_map]
    rw [e1, prEvent_map]
    refine prEvent_mono_of_support _ _ _ fun z hz hE => ⟨?_, hE⟩
    simp only [Aplus, squeezeAdversary, simulateQ_bind, StateT.run_bind] at hz
    obtain ⟨w, -, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    rw [simulateQ_map, StateT.run_map, support_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact replay_of_mem_support_run _ (isQueryBoundP_squeezeCompletionAfter s₀ e dec squeezes
      encode w.1) w.2 y hy
  -- Off a collision, it is the replay of the prefix completion in the simulated run.
  have h2 :=
    (dominatedUntilBad (I := I) (O := O) (extra := []ₒ) s₀).prEvent_simulateQ_run_le_map_or_bad
    (preservesInv_inv s₀) (preservesInv_bad s₀) Aplus (SimState.init, ∅) inv_init
    (fun z => replay z.2 (cc z.1.1) = some z.1.2 ∧ E z.1.2)
  rw [view_init] at h2
  have h3 : Pr{let z ← (simulateQ (idealImpl s₀) Aplus).run (SimState.init, ∅)}[
      (replay (view s₀ z.2) (cc z.1.1) = some z.1.2 ∧ E z.1.2) ∨ ¬ Good s₀ z.2.1] ≤
      Pr{let z ← (simulateQ (idealImpl s₀) Aplus).run (SimState.init, ∅)}[
        replay (dropCache z.2.2) (enc z.1.1) = some z.1.2 ∧ E z.1.2] + chainError S q := by
    refine (prEvent_mono_of_support _ _ _ fun z hz h => ?_).trans
      ((prEvent_or_le _ _ _).trans (add_le_add le_rfl (prEvent_bad_le s₀ Aplus hqA)))
    by_cases hgood : Good s₀ z.2.1
    · rcases h with ⟨hr, hE⟩ | hbad
      · exact .inl ⟨replay_squeezeCompletion s₀ e dec squeezes encode
          (simulateQ_run_preservesInv _ _ (preservesInv_inv s₀) Aplus _ inv_init z hz) hgood
          _ _ hr, hE⟩
      · exact absurd hgood hbad
    · exact .inr hgood
  -- The simulated run is the prefix oracle's run of the simulated extended adversary.
  let X := simulateQ dropEmpty (simulate s₀ Aplus)
  have h4 : Pr{let z ← (simulateQ (idealImpl s₀) Aplus).run (SimState.init, ∅)}[
      replay (dropCache z.2.2) (enc z.1.1) = some z.1.2 ∧ E z.1.2] =
      Pr{let w ← (simulateQ (prefixSpec S I O).romImpl X).run ∅}[
        replay w.2 (enc w.1.1) = some w.1.2 ∧ E w.1.2] := by
    have e4 : (simulateQ (prefixSpec S I O).romImpl X).run ∅ =
        (fun z => (z.1, dropCache z.2.2)) <$>
          (simulateQ (idealImpl s₀) Aplus).run (SimState.init, ∅) := by
      have hsim := run_simulateQ_sim s₀ Aplus SimState.init ∅
      have hdrop := map_run_dropEmpty (simulate s₀ Aplus) ∅
      rw [dropCache_empty] at hdrop
      rw [← hdrop]
      change (fun z : (Option (Selection Input PUnit W fun z =>
            decoded (Fin m → S × O) (coin z) (dec z)) ×
          Option (Outcome Input W fun z => decodedProtocol (Fin m → S × O) (coin z) (dec z))) ×
          (prefixSpec S I O + []ₒ).QueryCache => (z.1, dropCache z.2)) <$>
        (simulateQ (prefixSpec S I O + []ₒ).romImpl
          (Prod.fst <$> (simulateQ (sim s₀) Aplus).run SimState.init)).run ∅ = _
      rw [simulateQ_map, StateT.run_map, hsim, Functor.map_map, Functor.map_map]
    rw [e4, prEvent_map]
  -- A successful replay of the prefix completion is its run.
  have h5 : Pr{let w ← (simulateQ (prefixSpec S I O).romImpl X).run ∅}[
      replay w.2 (enc w.1.1) = some w.1.2 ∧ E w.1.2] ≤
      Pr{let r ← (simulateQ (List I →ₒ (S × O)).romImpl
        ((Prod.fst <$> X) >>= enc)).run' ∅}[E r] := by
    rw [StateT.run'_eq, prEvent_map, simulateQ_bind, StateT.run_bind, simulateQ_map,
      StateT.run_map, bind_map_left]
    conv_lhs => rw [← bind_pure ((simulateQ (prefixSpec S I O).romImpl X).run ∅)]
    refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun w => ?_
    by_cases hR : replay w.2 (enc w.1.1) = some w.1.2 ∧ E w.1.2
    · rw [run_of_replay _ w.2 w.1.2 hR.1, prEvent_pure, prEvent_pure]
      simp [hR]
    · rw [prEvent_pure]
      simp [hR]
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ _ := h3
    _ = _ := by rw [h4]
    _ ≤ _ := add_le_add h5 le_rfl

end Reduction

/-! ### Knowledge soundness -/

section Soundness

open PublicCoin

variable {S I O : Type} [DecidableEq S] [DecidableEq I] [SampleableType S] [SampleableType O]
  [Inhabited S] [Inhabited O] {m : ℕ} [NeZero m]
variable {Input W : Type} {protocol : Input → Protocol}

/-- **Fiat–Shamir on a hash chain, with grinding and challenges of several squeezes.** The
verifier draws each challenge off the coins of its node's squeezes (`squeezes`, at most `m`), the
`j`th squeeze after absorbing a key's encoding `x :: p` the chain's answer at `e ^ j ++ x :: p`,
through the draws `dec`: after the prover's witness, absorbed into the key, it rejects the coins
that fail the draw's check (a grinding draw's proof of work) and decodes the challenge from the
others, each draw reading only its node's squeezes. The encodings of the keys that squeeze are
distinct and their absorbed inputs are not the empty input `e`; a key squeezed `0` times is not
absorbed. Each draw is bounded by the ratio at its node (`ratio`). If every input's certificate
samples its challenges uniformly and the adversary and the verifier together make at most `q`
chain queries, the verifier completes a path whose coins all pass, decoding to a path of
the protocol with a valid terminal witness whose backward extraction fails, with probability at
most `chainError S q` plus the state-restoration bound `maxError * q + sumError` of the
certificates' node errors, each multiplied by its node's ratio. -/
theorem KnowledgeCertificate.chainSqueeze_knowledge_soundness (s₀ : S) (e : I)
    (coin : (z : Input) → PublicCoin (protocol z))
    (dec : (z : Input) → Decoder (Fin m → S × O) (coin z))
    (ratio : (z : Input) → Errors (coin z)) (hdec : ∀ z, Decoder.Bounded (coin z) (dec z) (ratio z))
    (squeezes : (z : Input) → Prefix PUnit (coin z) → ℕ)
    (hsqueezes : ∀ z node, squeezes z node ≤ m)
    (reads : ∀ z, Decoder.Reads (coin z) (dec z) (squeezes z))
    (encode : (Key Input PUnit fun z => decoded (Fin m → S × O) (coin z) (dec z)) → I × List I)
    (injective : ∀ key key', keySqueezes dec squeezes key ≠ 0 →
      keySqueezes dec squeezes key' ≠ 0 → encode key = encode key' → key = key')
    (nonempty : ∀ key, keySqueezes dec squeezes key ≠ 0 → (encode key).1 ≠ e)
    (state : Input → KnowledgeState)
    (certificate : (z : Input) → KnowledgeCertificate (protocol z).tree (protocol z).roles
      (state z))
    (uniform : ∀ z, UniformChallenges (coin z) (certificate z).challenges)
    (adversary : OracleComp (unifSpec + (chainSpec S I O + []ₒ))
      (Option (Selection Input PUnit W fun z => decoded (Fin m → S × O) (coin z) (dec z))))
    {q : ℕ} (hq : IsQueryBoundP (squeezeExecution s₀ e dec squeezes encode adversary)
      (fun t => isChain t = true) q) :
    Pr{let result ← (simulateQ (chainSpec S I O + []ₒ).romImpl
        (squeezeExecution s₀ e dec squeezes encode adversary)).run' ∅}[
      ∃ z path seed, result = some ⟨z, path, seed⟩ ∧
        ∃ p, decodePath (coin z) (dec z) path = some p ∧
          ∃ witness, ((certificate z).extractor.terminalState p).holds witness ∧
            ¬ (state z).holds ((certificate z).extractor.extractWitness p witness)] ≤
      chainError S q + (maxError (fun z node => ratio z node *
          supErrors (coin z) (certificate z).challenges node) * q +
        sumError (fun z node => ratio z node *
          supErrors (coin z) (certificate z).challenges node)) := by
  classical
  let A := Prod.fst <$> simulateQ dropEmpty (simulate s₀
    (squeezeAdversary s₀ e dec squeezes encode adversary))
  let codec := squeezeCodec e m dec squeezes encode injective nonempty
  let external := simulateQ
    (liftInl (K := Key Input PUnit fun z => decoded (Fin m → S × O) (coin z) (dec z)))
    (simulateQ (ungroup (squeezeEquiv e m)) A)
  let errors : (z : Input) → Errors (decoded (Fin m → S × O) (coin z) (dec z)) := fun z node =>
    ratio z (Prefix.undecode (coin z) (dec z) node) *
      supErrors (coin z) (certificate z).challenges (Prefix.undecode (coin z) (dec z) node)
  have hA := prEvent_squeezeExecution_le s₀ e dec squeezes encode adversary hq fun result =>
    ∃ z path seed, result = some ⟨z, path, seed⟩ ∧
      ∃ p, decodePath (coin z) (dec z) path = some p ∧
        ∃ witness, ((certificate z).extractor.terminalState p).holds witness ∧
          ¬ (state z).holds ((certificate z).extractor.extractWitness p witness)
  have hB := prEvent_prefixSqueeze_eq_grouped e dec squeezes hsqueezes encode injective nonempty
    A (fun result => ∃ z path seed, result = some ⟨z, path, seed⟩ ∧
      ∃ p, decodePath (coin z) (dec z) path = some p ∧
        ∃ witness, ((certificate z).extractor.terminalState p).holds witness ∧
          ¬ (state z).holds ((certificate z).extractor.extractWitness p witness)) (by
    rintro (_ | ⟨z, path, seed⟩)
    · exact Iff.rfl
    · constructor
      · rintro ⟨z', path', seed', h, rest⟩
        cases h
        exact ⟨z, path, seed, rfl, by rwa [decodePath_padPath _ _ _ (reads z)] at rest⟩
      · rintro ⟨z', path', seed', h, rest⟩
        cases h
        exact ⟨z, _, seed, rfl, by rwa [decodePath_padPath _ _ _ (reads z)]⟩)
  have h6 := encodedExternalStopped_extraction_le_adversaryCount
    (protocol := fun z => decodedProtocol (Fin m → S × O) (coin z) (dec z))
    (fun z => decoded (Fin m → S × O) (coin z) (dec z)) (decodedCommon coin dec) codec
    (fun _ => GuardSchedule.pass _) errors external state
    (fun z => decodeExtractor (coin z) (dec z) (certificate z).extractor) Set.univ
    (fun z _ => isProverPreserving_decodeExtractor (coin z) (dec z) _
      (certificate z).prover_preserving)
    (fun z _ => isLocallyBounded_errorSchedule _ _ _
      (uniformChallenges_decodeSchedule (coin z) (dec z) (ratio z) (certificate z).challenges)
      (isLocallyBounded_decodeExtractor (coin z) (dec z) (ratio z) (hdec z) _ _ (uniform z)
        (certificate z).local_bound) _
      (supErrors_decodeSchedule_le (coin z) (dec z) (ratio z) (certificate z).challenges))
  have h5 : Pr{let r ← (simulateQ ((SqueezeBase e m ⊕ Key Input PUnit fun z =>
        decoded (Fin m → S × O) (coin z) (dec z)) →ₒ (Fin m → S × O)).romImpl
      (external >>= encodedExternalCompletionAfter
        (fun z => decoded (Fin m → S × O) (coin z) (dec z)) (decodedCommon coin dec) codec
        (fun _ => GuardSchedule.pass _))).run' ∅}[
      ∃ z path seed, r = some ⟨z, path, seed⟩ ∧
        ∃ p, decodePath (coin z) (dec z) path = some p ∧
          ∃ witness, ((certificate z).extractor.terminalState p).holds witness ∧
            ¬ (state z).holds ((certificate z).extractor.extractWitness p witness)] ≤
      Pr{let joint ← (randomOracleLoggedRun (encodedExternalStoppedExecution
        (fun z => decoded (Fin m → S × O) (coin z) (dec z)) (decodedCommon coin dec) codec
        (fun _ => GuardSchedule.pass _) external) ∅)}[
        stoppedExtractionFails state
          (fun z => decodeExtractor (coin z) (dec z) (certificate z).extractor) Set.univ
          joint.1.1] := by
    rw [StateT.run'_eq, prEvent_map, ← randomOracleLoggedRun_project, prEvent_map]
    refine prEvent_mono _ _ _ fun joint hjoint => ?_
    obtain ⟨z, path, seed, hz, bad⟩ := hjoint
    simp only at hz
    rw [hz]
    exact ⟨Set.mem_univ z, (badTerminal_decode (coin z) (dec z) (certificate z).extractor path
      (fun w => ¬ (state z).holds w)).mpr bad⟩
  have hqA : IsQueryBoundP (squeezeAdversary s₀ e dec squeezes encode adversary)
      (fun t => isChain t = true) q := by
    rw [squeezeExecution_eq] at hq
    exact (isQueryBoundP_map_iff _ _ _).mp hq
  have h7 : expectedFreshQueryCharge external (fun _ => 1) ≤ q :=
    expectedFreshQueryCharge_le external (isQueryBoundP_liftInl (isQueryBoundP_ungroup _
      ((isQueryBoundP_map_iff _ _ _).mpr (isQueryBoundP_dropEmpty_simulate s₀ hqA))))
  have hmax : maxError errors ≤ maxError (fun z node =>
      ratio z node * supErrors (coin z) (certificate z).challenges node) :=
    iSup_le fun z => iSup_le fun node =>
      le_iSup_of_le z (le_iSup (fun node => ratio z node *
        supErrors (coin z) (certificate z).challenges node) (Prefix.undecode (coin z) (dec z) node))
  have hsum : sumError errors ≤ sumError (fun z node =>
      ratio z node * supErrors (coin z) (certificate z).challenges node) :=
    iSup_mono fun z => pathError_undecode_le (coin z) (dec z) fun node =>
      ratio z node * supErrors (coin z) (certificate z).challenges node
  refine hA.trans ((add_le_add (hB.le.trans (h5.trans (h6.trans ?_))) le_rfl).trans_eq
    (add_comm _ _))
  exact add_le_add (mul_le_mul' hmax h7) hsum

end Soundness

/-! ### Chain queries of the verifier -/

/-- Every path of a public-coin protocol has at most `N` challenges. -/
def _root_.Interaction.Oracle.PublicCoin.ChallengesLE :
    {protocol : Protocol} → PublicCoin protocol → ℕ → Prop
  | _, .done, _ => True
  | _, @PublicCoin.sender _ _ _ next, N => ∀ move, PublicCoin.ChallengesLE (next move) N
  | _, @PublicCoin.oracle _ _ _ _ next, N => PublicCoin.ChallengesLE next N
  | _, @PublicCoin.challenge _ _ _ next, N => 0 < N ∧ PublicCoin.ChallengesLE next (N - 1)

section ChainQueries

open PublicCoin Security

variable {S I O : Type}

/-- Absorbing `x :: p` makes `p.length + 1` chain queries. -/
theorem isQueryBoundP_absorb_chain {ι : Type} {extra : OracleSpec ι} (s₀ : S) (x : I)
    (p : List I) :
    IsQueryBoundP (absorb (O := O) (extra := extra) s₀ x p) (fun t => isChain t = true)
      (p.length + 1) := by
  induction p generalizing x with
  | nil => exact (isQueryBoundP_query_iff _ _ _).mpr fun _ => Nat.one_pos
  | cons y p ih =>
    rw [absorb]
    exact isQueryBoundP_bind (ih y) fun v _ =>
      (isQueryBoundP_query_iff _ (Sum.inr (Sum.inl (v.1, x))) 1).mpr fun _ => Nat.one_pos

/-- The `j`th squeeze, for `j < m`, after absorbing `x :: p` with `p` of length at most `L`, makes
at most `L + m` chain queries. -/
theorem isQueryBoundP_squeezeAt_chain (s₀ : S) (e x : I) (p : List I) {m L j : ℕ} (hj : j < m)
    (hp : p.length ≤ L) :
    IsQueryBoundP (squeezeAt (O := O) s₀ e x p j) (fun t => isChain t = true) (L + m) := by
  cases j with
  | zero => exact (isQueryBoundP_absorb_chain s₀ x p).mono (by omega)
  | succ j =>
    refine (isQueryBoundP_absorb_chain s₀ e _).mono ?_
    simp only [squeezePrefix, List.length_append, List.length_replicate, List.length_cons]
    omega

/-- `n` squeezes of at most `k` queries each make at most `n * k` queries. -/
theorem isQueryBoundP_squeezeAnswers_le {ι : Type} {spec : OracleSpec ι}
    {answer : ℕ → OracleComp spec (S × O)} {p : ι → Prop} [DecidablePred p] {k : ℕ} (n : ℕ)
    (h : ∀ j < n, IsQueryBoundP (answer j) p k) :
    IsQueryBoundP (squeezeAnswers answer n) p (n * k) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    refine (isQueryBoundP_bind (m := k + 0) (ih fun j hj => h j (Nat.lt_succ_of_lt hj))
      fun _ _ => isQueryBoundP_bind (h n (Nat.lt_succ_self n)) fun _ _ => ?_).mono ?_
    · trivial
    · rw [Nat.succ_mul, Nat.add_zero]

variable [SampleableType S] [SampleableType O]

/-- Completing a transcript of the decoded presentation under passing guards queries at most
`N` prefixes, when every path of the protocol has at most `N` challenges. -/
theorem isTotalQueryBound_stoppedCompletePrefix {C : Type} [SampleableType C] :
    {protocol : Protocol} → (coin : PublicCoin protocol) → (dec : Decoder C coin) → (N : ℕ) →
    coin.ChallengesLE N → (messages : Messages PUnit (decoded C coin dec)) →
    IsTotalQueryBound (stoppedCompletePrefix (decoded C coin dec) (GuardSchedule.pass _)
      messages) N
  | _, .done, _, _, _, _ => trivial
  | _, @PublicCoin.sender _ _ _ next, dec, N, h, messages => by
      simp only [stoppedCompletePrefix]
      refine IsTotalQueryBound.mono (n₁ := N + 0) (isTotalQueryBound_bind
        (isTotalQueryBound_reindexQuery _ _ _ (isTotalQueryBound_stoppedCompletePrefix
          (next messages.1) (dec messages.1) N (h messages.1) messages.2)) fun _ => ?_) le_rfl
      trivial
  | _, @PublicCoin.oracle _ _ _ _ next, dec, N, h, messages => by
      simp only [stoppedCompletePrefix]
      refine IsTotalQueryBound.mono (n₁ := N + 0) (isTotalQueryBound_bind
        (isTotalQueryBound_reindexQuery _ _ _ (isTotalQueryBound_stoppedCompletePrefix
          next dec N h messages.2)) fun _ => ?_) le_rfl
      trivial
  | _, @PublicCoin.challenge _ _ _ next, dec, N, h, messages => by
      have hpass : GuardSchedule.pass (Salt := PUnit) (decoded C (.challenge next) dec)
          messages.1 =
          (fun _ => true, fun _ _ => GuardSchedule.pass (decoded C next dec.2)) := rfl
      simp only [stoppedCompletePrefix, hpass, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      refine IsTotalQueryBound.mono (n₁ := N + 0) (isTotalQueryBound_bind
        (isTotalQueryBound_reindexQuery _ _ _ ?_) fun _ => ?_) le_rfl
      · refine isTotalQueryBound_query_bind_iff.mpr ⟨h.1, fun _ => ?_⟩
        refine IsTotalQueryBound.mono (n₁ := (N - 1) + 0) (isTotalQueryBound_bind
          (isTotalQueryBound_reindexQuery _ _ _ (isTotalQueryBound_stoppedCompletePrefix
            next dec.2 (N - 1) h.2 messages.2.2)) fun _ => ?_) le_rfl
        trivial
      · trivial

variable [Inhabited S] [Inhabited O] {m : ℕ}
variable {Input W : Type} {protocol : Input → Protocol}
  {coin : (z : Input) → PublicCoin (protocol z)}

/-- **The verifier's chain queries.** If every path of each input's protocol has at most `N`
challenges, every node squeezes at most `m` times, every key's absorbed inputs after the first
number at most `L`, and the adversary makes at most `Q` chain queries, the game makes at most
`Q + N * (m * (L + m))`: the verifier queries at most `N` keys, and the `j`th squeeze of a key
absorbs `squeezePrefix e x p j`, at most `L + m` chain queries. -/
theorem isQueryBoundP_squeezeExecution (s₀ : S) (e : I)
    (dec : (z : Input) → Decoder (Fin m → S × O) (coin z))
    (squeezes : (z : Input) → Prefix PUnit (coin z) → ℕ)
    (encode : (Key Input PUnit fun z => decoded (Fin m → S × O) (coin z) (dec z)) → I × List I)
    (adversary : OracleComp (unifSpec + (chainSpec S I O + []ₒ))
      (Option (Selection Input PUnit W fun z => decoded (Fin m → S × O) (coin z) (dec z))))
    {N L Q : ℕ} (hN : ∀ z, (coin z).ChallengesLE N) (hsqueezes : ∀ z node, squeezes z node ≤ m)
    (hL : ∀ key, (encode key).2.length ≤ L)
    (hQ : IsQueryBoundP adversary (fun t => isChain t = true) Q) :
    IsQueryBoundP (squeezeExecution s₀ e dec squeezes encode adversary)
      (fun t => isChain t = true) (Q + N * (m * (L + m))) := by
  refine isQueryBoundP_bind hQ fun selected _ => ?_
  rcases selected with _ | ⟨z, messages, witness⟩
  · trivial
  refine (isQueryBoundP_map_iff _ _ _).mpr
    (IsQueryBoundP.simulateQ_of_step_le_total (isTotalQueryBound_reindexQuery _ _ _
      (isTotalQueryBound_stoppedCompletePrefix (coin z) (dec z) N (hN z) messages)) fun key => ?_)
  refine (isQueryBoundP_map_iff _ _ _).mpr ((isQueryBoundP_map_iff _ _ _).mpr
    ((isQueryBoundP_squeezeAnswers_le _ fun j hj => isQueryBoundP_squeezeAt_chain s₀ e _ _
      (lt_of_lt_of_le hj (hsqueezes _ _)) (hL key)).mono ?_))
  exact Nat.mul_le_mul_right _ (hsqueezes _ _)

end ChainQueries

end Interaction.Oracle.Security.HashChain
