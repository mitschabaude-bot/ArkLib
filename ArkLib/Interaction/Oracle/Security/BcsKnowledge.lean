/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.Interaction.Oracle.Security.BcsCertificate
public import ArkLib.Interaction.Oracle.Security.BcsFill
public import ArkLib.Interaction.Oracle.Security.BcsSimulation

/-!
# Knowledge soundness of the BCS transformation

The BCS transformation compiles a public-coin protocol with oracle messages into a
non-interactive argument: each oracle message is replaced by a commitment (a Merkle cap), and a
Fiat–Shamir verifier on a duplex chain absorbs the commitments together with the other moves and
squeezes the challenges. The message behind a commitment is only determined by the auxiliary hash
oracle's answers so far (straight-line extraction), so the chain inputs of a key of the compiled
protocol do not determine its messages, and no injective encoding of keys with messages into chain
inputs exists, which the hash-chain Fiat–Shamir theorem
(`KnowledgeCertificate.chainSqueeze_knowledge_soundness`) needs.

The compiler therefore runs that theorem on the *snapshot protocol* (`BcsProtocol.lean`): every
oracle message becomes a commitment move, and each chain block starts with a snapshot move, a
cache of the hash oracle's answers, read by the ideal chain as part of the block's input. Its keys
encode injectively into inputs over `F ⊕ Snap` (`idealEncode`), and a commitment opens to the
message `open T c` on the latest snapshot `T` (`openPath`), so the protocol's certificate pulls back
to the snapshot protocol (`snapCertificate`) with the same errors.

The real game (`realExecution`) runs the adversary against the chain over real inputs `List F` and
the hash oracle, and the duplex verifier completes its selection, absorbing the inputs with the
snapshots erased (`realEncode`). It is simulated exactly (`BcsSimulation.lean`) by a game against
the ideal chain over `List (F ⊕ Snap)`, each fresh chain query forwarded with the snapshot of the
hash answers at that moment. When the selection's snapshot moves are those of its blocks' chain
queries (`SnapsOK`), the ideal verifier's completion replays on the ideal cache to the real
outcome (`replay_idealCompletion`), so the real event is an event of the ideal game whose adversary
is the simulated real game (`idealAdversary`).

## Main statements

- `prEvent_realExecution_le`: an event of the real game is at most the same event of the simulated
  game, in which moreover the real completion replays on the log and the log matches the ideal
  cache.
- `replay_idealCompletion`: on such a run, the ideal completion of a selection with consistent
  snapshots replays to the real outcome.
- `KnowledgeCertificate.bcs_knowledge_soundness`: the real verifier completes a selection with
  consistent snapshots to a path whose opened path has a valid terminal witness whose backward
  extraction fails with probability at most the hash-chain Fiat–Shamir bound for `Q + 2 V` chain
  queries, `V = completionQueries N m` the completion's.
-/

@[expose] public section

open OracleComp OracleSpec
open scoped ENNReal

namespace Interaction.Oracle.Security.Bcs

open PublicCoin StateRestoration HashChain

/-! ### The snapshot protocol -/

section Snapshot

variable {F Snap C : Type} [DecidableEq Snap]

/-- The snapshot protocol has as many challenges on every path as the protocol. -/
theorem challengesLE_snapCoin : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    (dec : Decoder C coin) → (lay : Layout F Snap coin dec) → (start : Bool) → {N : ℕ} →
    coin.ChallengesLE N → (snapCoin coin dec lay start).ChallengesLE N
  | _, .done, _, _, _, _, _ => trivial
  | _, @PublicCoin.sender _ _ _ next, dec, lay, start, _, h => by
      have hf : (snapCoin (.sender next) dec lay false).ChallengesLE _ := fun move =>
        challengesLE_snapCoin (next move) (dec move) (lay.2 move) false (h move)
      cases start
      · exact hf
      · exact fun _ => hf
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay, start, _, h => by
      have hf : (snapCoin (.oracle next) dec lay false).ChallengesLE _ := fun _ =>
        challengesLE_snapCoin next dec lay.2 false h
      cases start
      · exact hf
      · exact fun _ => hf
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, start, _, h => by
      have hf : (snapCoin (.challenge next) dec lay false).ChallengesLE _ :=
        ⟨h.1, challengesLE_snapCoin next dec.2 lay.2.2 (lay.1 != 0) h.2⟩
      cases start
      · exact hf
      · exact fun _ => hf

end Snapshot

/-! ### Replaying the chain beside the hash oracle -/

section Lift

variable {S I O ι : Type} {hs : OracleSpec ι}

/-- The queries of a program on the chain alone, asked of the chain beside the hash oracle. -/
def liftHash : QueryImpl (unifSpec + (chainSpec S I O + []ₒ))
    (OracleComp (unifSpec + (chainSpec S I O + hs)))
  | .inl n => liftM ((unifSpec + (chainSpec S I O + hs)).query (.inl n))
  | .inr (.inl q) => liftM ((unifSpec + (chainSpec S I O + hs)).query (.inr (.inl q)))
  | .inr (.inr e) => PEmpty.elim e

/-- The chain answers of a cache of the chain beside the hash oracle. -/
def chainPart (c : (chainSpec S I O + hs).QueryCache) : (chainSpec S I O + []ₒ).QueryCache :=
  QueryCache.inl c.fst

/-- Replaying a query answers it from the cache. -/
theorem replay_query {κ : Type} {spec : OracleSpec κ} (c : spec.QueryCache) (t : κ) :
    replay c (liftM ((unifSpec + spec).query (.inr t))) = c t := by
  simp [replay, cacheAnswers]

/-- Replaying a program asked of the chain beside the hash oracle replays it on the chain
answers. -/
theorem replay_simulateQ_liftHash {α : Type} (c : (chainSpec S I O + hs).QueryCache)
    (P : OracleComp (unifSpec + (chainSpec S I O + []ₒ)) α) :
    replay c (simulateQ liftHash P) = replay (chainPart c) P := by
  induction P using OracleComp.inductionOn with
  | pure a => simp only [simulateQ_pure, replay_pure]
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, replay_bind, replay_query_bind]
    rcases t with n | q | e
    · simp [replay, liftHash, cacheAnswers]
    · simp only [liftHash, replay_query, ih]
      rfl
    · exact e.elim

end Lift

/-! ### Real chain queries read on the ideal chain -/

section Transfer

variable {S O F Snap : Type}

/-- The ideal cache `cI` answers the ideal query of every real chain query `(s, x)` cached by `cR`
alike, at `(s, enc T x)` with `T` its snapshot `snapAt (s, x)`, and `answerAt` reads `cR`. -/
def Follows (cR : (chainSpec S (List F) O + []ₒ).QueryCache)
    (cI : (chainSpec S (List (F ⊕ Snap)) O + []ₒ).QueryCache) (snapAt : S × List F → Snap)
    (answerAt : S × List F → S × O) : Prop :=
  ∀ s x a, cR (.inl (s, x)) = some a →
    answerAt (s, x) = a ∧ cI (.inl (s, enc (snapAt (s, x)) x)) = some a

variable {cR : (chainSpec S (List F) O + []ₒ).QueryCache}
  {cI : (chainSpec S (List (F ⊕ Snap)) O + []ₒ).QueryCache} {snapAt : S × List F → Snap}
  {answerAt : S × List F → S × O}

/-- **Absorbing real inputs on the ideal chain.** Absorbing real inputs `x :: p` from `s₀` on the
real cache is absorbing the ideal inputs they stand for on the ideal cache, to the answer
`answerAt` reads at the state reached. -/
theorem replay_absorb_ideal (s₀ : S) (H : Follows cR cI snapAt answerAt) :
    (p : List (List F)) → (x : List F) → (v : S × O) →
    replay cR (absorb s₀ x p) = some v →
    answerAt (chainState answerAt s₀ p.reverse, x) = v ∧
      replay cI (absorb s₀ (enc (snapAt (chainState answerAt s₀ p.reverse, x)) x)
        (idealBlocks snapAt answerAt s₀ p.reverse).reverse) = some v
  | [], x, v, h => by
    rw [absorb, replay_query] at h
    refine ⟨(H s₀ x v h).1, ?_⟩
    rw [List.reverse_nil, idealBlocks, List.reverse_nil, absorb, replay_query]
    exact (H s₀ x v h).2
  | y :: p, x, v, h => by
    rw [absorb, replay_bind] at h
    obtain ⟨v', hv', h⟩ := Option.bind_eq_some_iff.mp h
    rw [replay_query] at h
    obtain ⟨hy, hI⟩ := replay_absorb_ideal s₀ H p y v' hv'
    have hs : chainState answerAt s₀ (y :: p).reverse = v'.1 := by
      rw [List.reverse_cons, chainState_append, ← hy]
      rfl
    rw [hs, List.reverse_cons, idealBlocks_append]
    refine ⟨(H _ x v h).1, ?_⟩
    simp only [idealBlocks, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append]
    rw [absorb, replay_bind, hI]
    exact (replay_query _ _).trans (H _ x v h).2

/-- The ideal inputs of the `j`th squeeze after real inputs are the `j`th squeeze after their
ideal inputs. -/
theorem idealBlocks_squeezePrefix (s₀ : S) (x : List F) (p : List (List F)) (j : ℕ) :
    (idealBlocks snapAt answerAt s₀ (squeezePrefix [] x p j).reverse).reverse =
      squeezePrefix [] (idealOf snapAt answerAt s₀ (x, p)).1
        (idealOf snapAt answerAt s₀ (x, p)).2 j := by
  simp only [squeezePrefix, idealOf, List.reverse_append, List.reverse_cons,
    List.reverse_replicate, idealBlocks_append, idealBlocks_replicate_nil, idealBlocks,
    List.append_assoc, List.singleton_append]

/-- **Squeezing real inputs on the ideal chain.** The `j`th squeeze after real inputs on the real
cache is the `j`th squeeze after their ideal inputs on the ideal cache. -/
theorem replay_squeezeAt_ideal (s₀ : S) (H : Follows cR cI snapAt answerAt) (x : List F)
    (p : List (List F)) (j : ℕ) (v : S × O) (h : replay cR (squeezeAt s₀ [] x p j) = some v) :
    replay cI (squeezeAt s₀ [] (idealOf snapAt answerAt s₀ (x, p)).1
      (idealOf snapAt answerAt s₀ (x, p)).2 j) = some v := by
  cases j with
  | zero => exact (replay_absorb_ideal s₀ H p x v h).2
  | succ j =>
    have h' := (replay_absorb_ideal s₀ H _ [] v h).2
    rw [enc_nil, idealBlocks_squeezePrefix] at h'
    exact h'

end Transfer

/-! ### Replaying completions -/

section Completion

/-- **Replaying a completion.** Completing messages on coins `QA` replays from `c₁` to the same
result as on coins `QB` from `c₂`, when every coin the completion reads replays alike. -/
theorem replay_stoppedCompletePrefix {κ₁ κ₂ Salt : Type} {spec₁ : OracleSpec κ₁}
    {spec₂ : OracleSpec κ₂} (c₁ : spec₁.QueryCache) (c₂ : spec₂.QueryCache) :
    {protocol : Protocol} → (coin : PublicCoin protocol) → (guards : GuardSchedule Salt coin) →
    (messages : Messages Salt coin) →
    (QA : QueryImpl (StateRestoration.prefixSpec Salt coin) (OracleComp (unifSpec + spec₁))) →
    (QB : QueryImpl (StateRestoration.prefixSpec Salt coin) (OracleComp (unifSpec + spec₂))) →
    (∀ pre ∈ prefixKeys coin messages, ∀ u, replay c₁ (QA pre) = some u →
      replay c₂ (QB pre) = some u) →
    ∀ r, replay c₁ (simulateQ QA (stoppedCompletePrefix coin guards messages)) = some r →
      replay c₂ (simulateQ QB (stoppedCompletePrefix coin guards messages)) = some r
  | _, .done, _, _, _, _, _, r, h => by simpa [stoppedCompletePrefix] using h
  | _, @PublicCoin.sender _ _ _ next, guards, ⟨move, messages⟩, QA, QB, hQ, r, h => by
      simp only [stoppedCompletePrefix, simulateQ_bind, simulateQ_pure, simulateQ_reindexQuery,
        replay_bind, replay_pure] at h ⊢
      obtain ⟨a, ha, hr⟩ := Option.bind_eq_some_iff.mp h
      rw [replay_stoppedCompletePrefix c₁ c₂ (next move) (guards move) messages _ _
        (fun pre hpre => hQ _ (List.mem_map_of_mem hpre)) a ha]
      exact hr
  | _, @PublicCoin.oracle _ _ _ _ next, guards, ⟨message, messages⟩, QA, QB, hQ, r, h => by
      simp only [stoppedCompletePrefix, simulateQ_bind, simulateQ_pure, simulateQ_reindexQuery,
        replay_bind, replay_pure] at h ⊢
      obtain ⟨a, ha, hr⟩ := Option.bind_eq_some_iff.mp h
      rw [replay_stoppedCompletePrefix c₁ c₂ next (guards message) messages _ _
        (fun pre hpre => hQ _ (List.mem_map_of_mem hpre)) a ha]
      exact hr
  | _, @PublicCoin.challenge _ _ _ next, guards, ⟨salt, messages⟩, QA, QB, hQ, r, h => by
      cases hg : guards.1 salt
      · simpa [stoppedCompletePrefix, hg] using h
      · simp only [stoppedCompletePrefix, hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          simulateQ_bind, simulateQ_pure, simulateQ_spec_query, replay_bind, replay_pure] at h ⊢
        obtain ⟨ch, hch, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨a, ha, hr⟩ := Option.bind_eq_some_iff.mp h
        rw [hQ _ (List.mem_cons_self ..) ch hch]
        refine Option.bind_eq_some_iff.mpr ⟨ch, rfl, Option.bind_eq_some_iff.mpr ⟨a, ?_, hr⟩⟩
        rw [simulateQ_reindexQuery] at ha ⊢
        exact replay_stoppedCompletePrefix c₁ c₂ next (guards.2 salt ch) messages _ _
          (fun pre hpre => hQ _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hpre))) a ha

end Completion

/-! ### The real game -/

section Game

variable {S O : Type} [DecidableEq S] [SampleableType S] [SampleableType O] [Inhabited S]
  [Inhabited O] {m : ℕ} {F : Type} [DecidableEq F] {ι : Type} [DecidableEq ι]
  {hs : OracleSpec ι} [∀ t, SampleableType (hs.Range t)] [DecidableEq hs.QueryCache]
  {Input W : Type} {protocol : Input → Protocol.{0}}

/-- A selection of a transcript of the decoded snapshot protocols. -/
abbrev SnapSelection (W : Type) (coin : (z : Input) → PublicCoin (protocol z))
    (dec : (z : Input) → Decoder (Fin m → S × O) (coin z))
    (lay : (z : Input) → Layout F hs.QueryCache (coin z) (dec z)) : Type :=
  Option (Selection Input PUnit W fun z => decoded (Fin m → S × O)
    (snapCoin (coin z) (dec z) (lay z) true) (snapDecoder (coin z) (dec z) (lay z) true))

/-- An outcome of the decoded snapshot protocols. -/
abbrev SnapOutcome (W : Type) (coin : (z : Input) → PublicCoin (protocol z))
    (dec : (z : Input) → Decoder (Fin m → S × O) (coin z))
    (lay : (z : Input) → Layout F hs.QueryCache (coin z) (dec z)) : Type :=
  Option (Outcome Input W fun z => decodedProtocol (Fin m → S × O)
    (snapCoin (coin z) (dec z) (lay z) true) (snapDecoder (coin z) (dec z) (lay z) true))

/-- The duplex verifier's completion of a selection: each challenge's coins squeezed from the
chain after absorbing the key's real inputs. -/
noncomputable def realCompletion (s₀ : S) (coin : (z : Input) → PublicCoin (protocol z))
    (dec : (z : Input) → Decoder (Fin m → S × O) (coin z))
    (lay : (z : Input) → Layout F hs.QueryCache (coin z) (dec z)) (tail : Input → List F)
    (selected : SnapSelection W coin dec lay) :
    OracleComp (unifSpec + (chainSpec S (List F) O + []ₒ)) (SnapOutcome W coin dec lay) :=
  squeezeCompletionAfter s₀ [] (fun z => snapDecoder (coin z) (dec z) (lay z) true)
    (fun z => (snapObserver (coin z) (dec z) (lay z) true).squeezes _ _)
    (realEncode coin dec lay tail) selected

/-- The ideal verifier's completion of a selection: each challenge's coins squeezed from the
ideal chain after absorbing the key's ideal inputs. -/
noncomputable def idealCompletion (s₀ : S) (coin : (z : Input) → PublicCoin (protocol z))
    (dec : (z : Input) → Decoder (Fin m → S × O) (coin z))
    (lay : (z : Input) → Layout F hs.QueryCache (coin z) (dec z)) (tail : Input → List F)
    (selected : SnapSelection W coin dec lay) :
    OracleComp (unifSpec + (chainSpec S (List (F ⊕ hs.QueryCache)) O + []ₒ))
      (SnapOutcome W coin dec lay) :=
  squeezeCompletionAfter s₀ [] (fun z => snapDecoder (coin z) (dec z) (lay z) true)
    (fun z => (snapObserver (coin z) (dec z) (lay z) true).squeezes _ _)
    (idealEncode coin dec lay tail) selected

/-- **The real game.** The adversary, querying the chain and the hash oracle, selects a transcript
of the decoded snapshot protocols, and the duplex verifier completes it on the same chain; the
game returns the selection and the outcome. -/
noncomputable def realExecution (s₀ : S) (coin : (z : Input) → PublicCoin (protocol z))
    (dec : (z : Input) → Decoder (Fin m → S × O) (coin z))
    (lay : (z : Input) → Layout F hs.QueryCache (coin z) (dec z)) (tail : Input → List F)
    (adversary : OracleComp (unifSpec + (chainSpec S (List F) O + hs))
      (SnapSelection W coin dec lay)) :
    OracleComp (unifSpec + (chainSpec S (List F) O + hs))
      (SnapSelection W coin dec lay × SnapOutcome W coin dec lay) :=
  adversary >>= fun selected =>
    (selected, ·) <$> simulateQ liftHash (realCompletion s₀ coin dec lay tail selected)

/-- The adversary of the ideal game: the real game simulated against the ideal chain
(`bcsSim enc`), returning the selection. -/
noncomputable def idealAdversary (s₀ : S) (coin : (z : Input) → PublicCoin (protocol z))
    (dec : (z : Input) → Decoder (Fin m → S × O) (coin z))
    (lay : (z : Input) → Layout F hs.QueryCache (coin z) (dec z)) (tail : Input → List F)
    (adversary : OracleComp (unifSpec + (chainSpec S (List F) O + hs))
      (SnapSelection W coin dec lay)) :
    OracleComp (unifSpec + (chainSpec S (List (F ⊕ hs.QueryCache)) O + []ₒ))
      (SnapSelection W coin dec lay) :=
  (fun w => w.1.1) <$>
    (simulateQ (bcsSim enc) (realExecution s₀ coin dec lay tail adversary)).run []

/-- The answer a log records for a chain query, or the default answer. -/
def answerAt (log : QueryLog (chainSpec S (List F) O + hs)) (q : S × List F) : S × O :=
  ((cacheOf log) (.inl q)).getD (default : S × O)

/-- The chain queries of the duplex verifier's completion: at most `N` keys of at most `m`
squeezes, each absorbing at most `N * m + m` inputs. -/
def completionQueries (N m : ℕ) : ℕ := N * (m * (N * m + m))

/-- A cached key of a log is logged with its answer. -/
theorem mem_of_cacheOf_eq_some {κ : Type} [DecidableEq κ] {spec : OracleSpec κ} :
    (log : QueryLog spec) → {t : κ} → {u : spec.Range t} → cacheOf log t = some u →
    (⟨t, u⟩ : (t : κ) × spec.Range t) ∈ log
  | [], _, _, h => by simp at h
  | ⟨t', u'⟩ :: log, t, u, h => by
    by_cases ht : t = t'
    · subst ht
      rw [cacheOf_cons, QueryCache.cacheQuery_self, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self ..
    · rw [cacheOf_cons, QueryCache.cacheQuery_of_ne _ _ ht] at h
      exact List.mem_cons_of_mem _ (mem_of_cacheOf_eq_some log h)

omit [SampleableType S] [SampleableType O] [∀ t, SampleableType (hs.Range t)]
  [DecidableEq hs.QueryCache] in
/-- The chain answers of a log are followed by an ideal cache matching it. -/
theorem follows_of_matches {log : QueryLog (chainSpec S (List F) O + hs)}
    {cI : (chainSpec S (List (F ⊕ hs.QueryCache)) O + []ₒ).QueryCache}
    (hM : Matches enc log cI) :
    Follows (chainPart (cacheOf log)) cI (snapshotAt log) (answerAt log) := by
  intro s x a ha
  change cacheOf log (.inl (s, x)) = some a at ha
  exact ⟨by simp only [answerAt, ha, Option.getD_some], hM s x a (mem_of_cacheOf_eq_some log ha)⟩

omit [∀ t, SampleableType (hs.Range t)] in
/-- **The ideal completion replays the real one.** When the chain answers of a log are matched by
an ideal cache and a selection's snapshots are consistent with the log, the ideal verifier's
completion replays on the ideal cache to the duplex verifier's outcome on the log. -/
theorem replay_idealCompletion (s₀ : S) (coin : (z : Input) → PublicCoin (protocol z))
    (dec : (z : Input) → Decoder (Fin m → S × O) (coin z))
    (lay : (z : Input) → Layout F hs.QueryCache (coin z) (dec z)) (tail : Input → List F)
    {log : QueryLog (chainSpec S (List F) O + hs)}
    {cI : (chainSpec S (List (F ⊕ hs.QueryCache)) O + []ₒ).QueryCache}
    (hM : Matches enc log cI) (z : Input)
    (messages : Messages PUnit (decoded (Fin m → S × O) (snapCoin (coin z) (dec z) (lay z) true)
      (snapDecoder (coin z) (dec z) (lay z) true))) (w : W)
    (hok : SnapsOK coin dec lay tail (snapshotAt log) (answerAt log) s₀ z messages)
    (r : SnapOutcome W coin dec lay)
    (h : replay (chainPart (cacheOf log))
      (realCompletion s₀ coin dec lay tail (some ⟨z, messages, w⟩)) = some r) :
    replay cI (idealCompletion s₀ coin dec lay tail (some ⟨z, messages, w⟩)) = some r := by
  have H := follows_of_matches hM
  simp only [realCompletion, idealCompletion, squeezeCompletionAfter, stoppedComplete,
    simulateQ_reindexQuery, replay_map] at h ⊢
  obtain ⟨path, hpath, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [replay_stoppedCompletePrefix _ _ _ _ messages _ _ (fun pre hpre u hu => ?_) path hpath]
  · rfl
  simp only [squeezeCompletionQueries, replay_map] at hu ⊢
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hu
  obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp hc
  by_cases h0 : keySqueezes (fun z => snapDecoder (coin z) (dec z) (lay z) true)
      (fun z => (snapObserver (coin z) (dec z) (lay z) true).squeezes _ _) ⟨z, pre⟩ = 0
  · rw [h0] at hl ⊢
    simp only [squeezeAnswers, replay_pure, Option.some.injEq] at hl
    subst hl
    simp only [squeezeAnswers, replay_pure]
    rfl
  · rw [hok ⟨z, pre⟩ (List.mem_map_of_mem hpre) h0, replay_squeezeAnswers _ _
      (fun j v hv => replay_squeezeAt_ideal s₀ H _ _ j v hv) _ l hl]
    rfl

/-! ### Query bounds -/

omit [DecidableEq S] [DecidableEq F] [DecidableEq ι] [∀ t, SampleableType (hs.Range t)] in
/-- The duplex verifier's completion draws no private coin. -/
theorem isQueryBoundP_realCompletion_unif (s₀ : S)
    (coin : (z : Input) → PublicCoin (protocol z))
    (dec : (z : Input) → Decoder (Fin m → S × O) (coin z))
    (lay : (z : Input) → Layout F hs.QueryCache (coin z) (dec z)) (tail : Input → List F)
    (selected : SnapSelection W coin dec lay) :
    IsQueryBoundP (simulateQ (liftHash (hs := hs)) (realCompletion s₀ coin dec lay tail selected))
      (fun t => isUnif t = true) 0 := by
  refine (isQueryBoundP_squeezeCompletionAfter _ _ _ _ _ selected).simulateQ_of_step
    (fun t ht => ?_) (fun t ht => ?_)
  · rcases t with n | q | e
    · exact (isQueryBoundP_query_iff _ _ _).mpr fun _ => Nat.one_pos
    · cases ht
    · exact e.elim
  · rcases t with n | q | e
    · exact absurd rfl ht
    · exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [isUnif])
    · exact e.elim

omit [DecidableEq S] [SampleableType S] [SampleableType O] [Inhabited S] [Inhabited O]
  [DecidableEq F] [DecidableEq ι] [∀ t, SampleableType (hs.Range t)]
  [DecidableEq hs.QueryCache] in
/-- Asking the chain beside the hash oracle makes the same chain queries. -/
theorem isQueryBoundP_liftHash_chain {I α : Type}
    {P : OracleComp (unifSpec + (chainSpec S I O + []ₒ)) α} {n : ℕ}
    (hP : IsQueryBoundP P (fun t => isChain t = true) n) :
    IsQueryBoundP (simulateQ (liftHash (hs := hs)) P) (fun t => isChain t = true) n := by
  refine hP.simulateQ_of_step (fun t ht => ?_) (fun t ht => ?_)
  · rcases t with n | q | e
    · cases ht
    · exact (isQueryBoundP_query_iff _ _ _).mpr fun _ => Nat.one_pos
    · exact e.elim
  · rcases t with n | q | e
    · exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [isChain])
    · exact absurd rfl ht
    · exact e.elim

omit [DecidableEq S] [Inhabited S] [Inhabited O] [DecidableEq F] [DecidableEq ι]
  [∀ t, SampleableType (hs.Range t)] in
/-- A key's inputs before its first squeeze number at most `N m`. -/
theorem length_idealEncode_le (coin : (z : Input) → PublicCoin (protocol z))
    (dec : (z : Input) → Decoder (Fin m → S × O) (coin z))
    (lay : (z : Input) → Layout F hs.QueryCache (coin z) (dec z)) (tail : Input → List F)
    {N : ℕ} (hN : ∀ z, (coin z).ChallengesLE N) (hsqueezes : ∀ z node, (lay z).squeezes node ≤ m)
    (key : Key Input PUnit fun z => decoded (Fin m → S × O)
      (snapCoin (coin z) (dec z) (lay z) true) (snapDecoder (coin z) (dec z) (lay z) true)) :
    (idealEncode coin dec lay tail key).2.length ≤ N * m := by
  simpa only [idealEncode, List.length_nil, Nat.zero_add] using
    (snapObserver (coin key.1) (dec key.1) (lay key.1) true).length_encodeFrom_le _ _
      (challengesLE_snapCoin _ _ _ true (hN key.1))
      (squeezes_snapObserver_le _ _ _ true ∅ (hsqueezes key.1)) [] _ [] key.2

omit [DecidableEq S] [DecidableEq F] [DecidableEq ι] [∀ t, SampleableType (hs.Range t)] in
/-- The duplex verifier's completion makes at most `completionQueries N m` chain queries. -/
theorem isQueryBoundP_realCompletion (s₀ : S)
    (coin : (z : Input) → PublicCoin (protocol z))
    (dec : (z : Input) → Decoder (Fin m → S × O) (coin z))
    (lay : (z : Input) → Layout F hs.QueryCache (coin z) (dec z)) (tail : Input → List F)
    {N : ℕ} (hN : ∀ z, (coin z).ChallengesLE N) (hsqueezes : ∀ z node, (lay z).squeezes node ≤ m)
    (selected : SnapSelection W coin dec lay) :
    IsQueryBoundP (realCompletion s₀ coin dec lay tail selected) (fun t => isChain t = true)
      (completionQueries N m) := by
  have h := isQueryBoundP_squeezeExecution s₀ [] _ _ (realEncode coin dec lay tail)
    (pure selected) (fun z => challengesLE_snapCoin _ _ _ true (hN z))
    (fun z => squeezes_snapObserver_le _ _ _ true ∅ (hsqueezes z))
    (fun key => (List.length_map _).trans_le (length_idealEncode_le coin dec lay tail hN
      hsqueezes key)) (Q := 0) (by trivial)
  rw [squeezeExecution, pure_bind, Nat.zero_add] at h
  exact h

omit [DecidableEq S] [DecidableEq F] [DecidableEq ι] [∀ t, SampleableType (hs.Range t)] in
/-- The real game makes at most `Q + completionQueries N m` chain queries. -/
theorem isQueryBoundP_realExecution (s₀ : S) (coin : (z : Input) → PublicCoin (protocol z))
    (dec : (z : Input) → Decoder (Fin m → S × O) (coin z))
    (lay : (z : Input) → Layout F hs.QueryCache (coin z) (dec z)) (tail : Input → List F)
    (adversary : OracleComp (unifSpec + (chainSpec S (List F) O + hs))
      (SnapSelection W coin dec lay))
    {N Q : ℕ} (hN : ∀ z, (coin z).ChallengesLE N) (hsqueezes : ∀ z node, (lay z).squeezes node ≤ m)
    (hQ : IsQueryBoundP adversary (fun t => isChain t = true) Q) :
    IsQueryBoundP (realExecution s₀ coin dec lay tail adversary) (fun t => isChain t = true)
      (Q + completionQueries N m) :=
  isQueryBoundP_bind hQ fun selected _ => (isQueryBoundP_map_iff _ _ _).mpr
    (isQueryBoundP_liftHash_chain (isQueryBoundP_realCompletion s₀ coin dec lay tail hN
      hsqueezes selected))

omit [DecidableEq S] [SampleableType S] [SampleableType O] [Inhabited S] [Inhabited O]
  [DecidableEq F] [DecidableEq ι] [∀ t, SampleableType (hs.Range t)]
  [DecidableEq hs.QueryCache] in
/-- Private coins make no chain query. -/
theorem isQueryBoundP_liftM_probComp_chain {I α : Type} (oa : ProbComp α) :
    IsQueryBoundP (liftM oa : OracleComp (unifSpec + (chainSpec S I O + []ₒ)) α)
      (fun t => isChain t = true) 0 := by
  change IsQueryBoundP (liftComp oa _) _ 0
  rw [liftComp_def]
  refine isQueryBoundP_simulateQ_zero oa fun t => ?_
  change IsQueryBoundP (liftM ((unifSpec + (chainSpec S I O + []ₒ)).query (.inl t))) _ 0
  rw [isQueryBoundP_query_iff]
  simp [isChain]

/-- The ideal adversary makes at most `Q + completionQueries N m` chain queries. -/
theorem isQueryBoundP_idealAdversary (s₀ : S) (coin : (z : Input) → PublicCoin (protocol z))
    (dec : (z : Input) → Decoder (Fin m → S × O) (coin z))
    (lay : (z : Input) → Layout F hs.QueryCache (coin z) (dec z)) (tail : Input → List F)
    (adversary : OracleComp (unifSpec + (chainSpec S (List F) O + hs))
      (SnapSelection W coin dec lay))
    {N Q : ℕ} (hN : ∀ z, (coin z).ChallengesLE N) (hsqueezes : ∀ z node, (lay z).squeezes node ≤ m)
    (hQ : IsQueryBoundP adversary (fun t => isChain t = true) Q) :
    IsQueryBoundP (idealAdversary s₀ coin dec lay tail adversary) (fun t => isChain t = true)
      (Q + completionQueries N m) := by
  rw [idealAdversary, isQueryBoundP_map_iff]
  refine (isQueryBoundP_realExecution s₀ coin dec lay tail adversary hN hsqueezes
    hQ).simulateQ_run_of_step (fun t ht log => ?_) (fun t ht log => ?_) []
  · rcases t with n | q | t
    · cases ht
    · change IsQueryBoundP (simChain enc q log) _ 1
      unfold simChain
      split
      · trivial
      · rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
        exact fun _ => Nat.one_pos
    · cases ht
  · rcases t with n | q | t
    · simp [bcsSim, isChain]
    · exact absurd rfl ht
    · change IsQueryBoundP (simHash t log) _ 0
      unfold simHash
      split
      · trivial
      · rw [isQueryBoundP_map_iff]
        exact isQueryBoundP_liftM_probComp_chain _

/-! ### From the real game to the ideal game -/

/-- **The real game, simulated.** An event of the real game's output and log is at most the same
event of the real game simulated against the ideal chain, where moreover the duplex verifier's
completion replays on the log's chain answers to its outcome and the log matches the ideal
cache. -/
theorem prEvent_realExecution_le (s₀ : S) (coin : (z : Input) → PublicCoin (protocol z))
    (dec : (z : Input) → Decoder (Fin m → S × O) (coin z))
    (lay : (z : Input) → Layout F hs.QueryCache (coin z) (dec z)) (tail : Input → List F)
    (adversary : OracleComp (unifSpec + (chainSpec S (List F) O + hs))
      (SnapSelection W coin dec lay))
    (E : (SnapSelection W coin dec lay × SnapOutcome W coin dec lay) ×
      QueryLog (chainSpec S (List F) O + hs) → Prop) :
    Pr{let z ← (simulateQ realImpl (realExecution s₀ coin dec lay tail adversary)).run []}[
      E z] ≤
    Pr{let w ← (simulateQ (chainSpec S (List (F ⊕ hs.QueryCache)) O + []ₒ).romImpl
        ((simulateQ (bcsSim enc) (realExecution s₀ coin dec lay tail adversary)).run [])).run ∅}[
      (E w.1 ∧ replay (chainPart (cacheOf w.1.2))
        (realCompletion s₀ coin dec lay tail w.1.1.1) = some w.1.1.2) ∧
      Matches enc w.1.2 w.2] := by
  have henc : ∀ (T T' : hs.QueryCache) (x x' : List F), enc T x = enc T' x' → x = x' :=
    fun T T' x x' h => by simpa only [erase_enc] using congrArg erase h
  refine le_trans ?_ (prEvent_real_le_sim henc (realExecution s₀ coin dec lay tail adversary)
    fun z => E z ∧ replay (chainPart (cacheOf z.2)) (realCompletion s₀ coin dec lay tail z.1.1) =
      some z.1.2)
  refine prEvent_mono_of_support _ _ _ fun z hz hE => ⟨hE, ?_⟩
  simp only [realExecution, simulateQ_bind, StateT.run_bind] at hz
  obtain ⟨w, -, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
  rw [simulateQ_map, StateT.run_map, support_map] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  have hy' : (y.1, cacheOf y.2) ∈ support ((simulateQ (chainSpec S (List F) O + hs).romImpl
      (simulateQ liftHash (realCompletion s₀ coin dec lay tail w.1))).run (cacheOf w.2)) := by
    rw [← map_run_simulateQ_realImpl, support_map]
    exact ⟨y, hy, rfl⟩
  rw [← replay_simulateQ_liftHash]
  exact replay_of_mem_support_run _ (isQueryBoundP_realCompletion_unif s₀ coin dec lay tail w.1)
    _ _ hy'

end Game

/-! ### Knowledge soundness -/

section Soundness

variable {S O : Type} [DecidableEq S] [SampleableType S] [SampleableType O] [Inhabited S]
  [Inhabited O] {m : ℕ} [NeZero m] {F : Type} [DecidableEq F] {ι : Type} [DecidableEq ι]
  {hs : OracleSpec ι} [∀ t, SampleableType (hs.Range t)] [DecidableEq hs.QueryCache]
  {Input W : Type}

/-- **Knowledge soundness of the BCS transformation on a duplex chain.** A public-coin protocol
with oracle messages committed by the layout `lay` (prefix-free observations, at most `m`
squeezes per challenge, draws reading their squeezes and bounded by `ratio` against the
certificates' laws, at most `N` challenges on every path) is compiled with the statement's
elements `tail` (injective) observed at the first squeeze. An adversary on the chain and the hash
oracle making at most `Q` chain queries selects a transcript of the snapshot protocol, and the
duplex verifier completes it. The probability that the selection's snapshots are those of its
blocks' chain queries and the completed path, opened on the snapshots, has a valid terminal
witness whose backward extraction fails is at most `chainError S q` plus the state-restoration
bound `maxError * q + sumError` of the certificates' errors, each multiplied by its draw's ratio,
for `q = Q + 2 * completionQueries N m`: the ideal game's adversary makes the real completion's
chain queries, and the ideal completion makes them again. -/
theorem KnowledgeCertificate.bcs_knowledge_soundness (s₀ : S) {protocol : Protocol.{0}}
    (coin : PublicCoin protocol) (dec : Decoder (Fin m → S × O) coin)
    (lay : Layout F hs.QueryCache coin dec) (ratio : Input → Errors coin)
    (hsqueezes : ∀ node, lay.squeezes node ≤ m) (reads : Decoder.Reads coin dec lay.squeezes)
    (tail : Input → List F) (htail : Function.Injective tail)
    (hprefix : Layout.PrefixFree coin dec lay) (state : Input → KnowledgeState)
    (certificate : (z : Input) → KnowledgeCertificate protocol.tree protocol.roles (state z))
    (hdec : ∀ z, Decoder.Bounded coin dec (ratio z) (certificate z).challenges)
    (adversary : OracleComp (unifSpec + (chainSpec S (List F) O + hs))
      (SnapSelection W (fun _ : Input => coin) (fun _ => dec) fun _ => lay))
    {N Q : ℕ} (hN : coin.ChallengesLE N)
    (hQ : IsQueryBoundP adversary (fun t => isChain t = true) Q) :
    Pr{let z ← (simulateQ realImpl (realExecution s₀ (fun _ => coin) (fun _ => dec)
        (fun _ => lay) tail adversary)).run []}[
      ∃ zz messages w path, z.1.1 = some ⟨zz, messages, w⟩ ∧ z.1.2 = some ⟨zz, path, w⟩ ∧
        SnapsOK (fun _ => coin) (fun _ => dec) (fun _ => lay) tail (snapshotAt z.2)
          (answerAt z.2) s₀ zz messages ∧
        ∃ p, decodePath (snapCoin coin dec lay true) (snapDecoder coin dec lay true) path =
            some p ∧
          ∃ witness, ((certificate zz).extractor.terminalState
              (openPath coin dec lay true ∅ p)).holds witness ∧
            ¬ (state zz).holds ((certificate zz).extractor.extractWitness
              (openPath coin dec lay true ∅ p) witness)] ≤
      chainError S (Q + 2 * completionQueries N m) +
        (maxError (fun z node => ratio z node * supErrors coin (certificate z).challenges node) *
            ((Q + 2 * completionQueries N m : ℕ) : ℝ≥0∞) +
          sumError fun z node =>
            ratio z node * supErrors coin (certificate z).challenges node) := by
  classical
  have hinj : ∀ key key',
      keySqueezes (fun _ => snapDecoder coin dec lay true)
        (fun _ => (snapObserver coin dec lay true).squeezes _ _) key ≠ 0 →
      keySqueezes (fun _ => snapDecoder coin dec lay true)
        (fun _ => (snapObserver coin dec lay true).squeezes _ _) key' ≠ 0 →
      idealEncode (fun _ => coin) (fun _ => dec) (fun _ => lay) tail key =
        idealEncode (fun _ => coin) (fun _ => dec) (fun _ => lay) tail key' → key = key' :=
    fun key key' hk hk' h => (snapObserver coin dec lay true).encode_injective
      (prefixFree_snapObserver coin dec lay true hprefix) (fun z => (tail z).map .inl)
      ((List.map_injective_iff.mpr Sum.inl_injective).comp htail) key key' hk hk' h
  have hne : ∀ key,
      keySqueezes (fun _ => snapDecoder coin dec lay true)
        (fun _ => (snapObserver coin dec lay true).squeezes _ _) key ≠ 0 →
      (idealEncode (fun _ => coin) (fun _ => dec) (fun _ => lay) tail key).1 ≠ [] :=
    fun key hk => (snapObserver coin dec lay true).encode_fst_ne_nil
      (fills_snapObserver coin dec lay true False fun h => by cases h)
      (fun z => (tail z).map .inl) key hk
  have hq := isQueryBoundP_squeezeExecution s₀ [] _ _
    (idealEncode (fun _ => coin) (fun _ => dec) (fun _ => lay) tail)
    (idealAdversary s₀ (fun _ => coin) (fun _ => dec) (fun _ => lay) tail adversary)
    (fun _ => challengesLE_snapCoin _ _ _ true hN)
    (fun _ => squeezes_snapObserver_le _ _ _ true ∅ hsqueezes)
    (length_idealEncode_le _ _ _ tail (fun _ => hN) fun _ => hsqueezes)
    (isQueryBoundP_idealAdversary s₀ (fun _ => coin) (fun _ => dec) (fun _ => lay) tail
      adversary (fun _ => hN) (fun _ => hsqueezes) hQ)
  have hcs := KnowledgeCertificate.chainSqueeze_knowledge_soundness s₀ [] _ _
    (fun z => snapErrors coin dec lay true ∅ (ratio z)) _
    (fun _ => squeezes_snapObserver_le _ _ _ true ∅ hsqueezes)
    (fun _ => reads_snapObserver coin dec lay true ∅ reads) _ hinj hne state
    (fun z => snapCertificate coin dec lay true ∅ (certificate z))
    (fun z => bounded_snapDecoder coin dec lay true ∅ (ratio z) _ (hdec z)) _
    (hq.mono (show _ ≤ Q + 2 * completionQueries N m by rw [two_mul, ← add_assoc]; rfl))
  refine (prEvent_realExecution_le s₀ _ _ _ tail adversary _).trans (le_trans ?_ (hcs.trans ?_))
  · simp only [squeezeExecution, idealAdversary, simulateQ_bind, StateT.run'_eq,
      StateT.run_bind, bind_map_left, map_bind]
    refine (prEvent_le_prEvent_bind_of_support (m := ProbComp) _ (fun a => (fun x => x.1) <$>
      (simulateQ (chainSpec S (List (F ⊕ hs.QueryCache)) O + []ₒ).romImpl (idealCompletion s₀
        (fun _ => coin) (fun _ => dec) (fun _ => lay) tail a.1.1.1)).run a.2) _
      (fun result => ∃ z path seed, result = some ⟨z, path, seed⟩ ∧
        ∃ p, decodePath (snapCoin coin dec lay true) (snapDecoder coin dec lay true) path =
            some p ∧
          ∃ witness, ((snapCertificate coin dec lay true ∅ (certificate z)).extractor.terminalState
              p).holds witness ∧
            ¬ (state z).holds ((snapCertificate coin dec lay true ∅
              (certificate z)).extractor.extractWitness p witness))
      fun p _ hp => ?_).trans_eq ?_
    swap
    · rw [map_bind]
      rfl
    obtain ⟨⟨⟨zz, messages, w, path, hsel, hout, hok, pp, hdecode, witness, hterm, hbad⟩, hR⟩,
      hM⟩ := hp
    rw [hsel] at hR
    have hr := replay_idealCompletion s₀ (fun _ => coin) (fun _ => dec) (fun _ => lay) tail hM zz
      messages w hok _ hR
    rw [← hsel] at hr
    rw [run_of_replay _ _ _ hr, map_pure, prEvent_pure, ite_eq_left_iff]
    refine fun hq => absurd ?_ hq
    rw [hout]
    exact ⟨zz, path, w, rfl, pp, hdecode, (badTerminal_snapCertificate coin dec lay true ∅
      (certificate zz) pp).mpr ⟨witness, hterm, hbad⟩⟩
  · exact add_le_add le_rfl (add_le_add (mul_le_mul'
      (maxError_snapCertificate_le (fun _ => coin) (fun _ => dec) (fun _ => lay) ∅ ratio
        certificate) le_rfl)
      (sumError_snapCertificate_le (fun _ => coin) (fun _ => dec) (fun _ => lay) ∅ ratio
        certificate))

end Soundness

end Interaction.Oracle.Security.Bcs
