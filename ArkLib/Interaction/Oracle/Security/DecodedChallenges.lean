/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.Interaction.Oracle.Security.StateRestorationBudget
public import ArkLib.Interaction.Oracle.Security.EncodedChallenges
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Challenges decoded from common coins

A Fiat–Shamir verifier reads every challenge off one kind of random-oracle answer, the coins `C`
(for a hash chain, its state and output), through a map `C → Challenge` per challenge node
(`PublicCoin.Decoder`). The *decoded presentation* of a public-coin protocol (`decodedProtocol`,
`PublicCoin.decoded`) samples coins at every challenge node, with the same prover moves, oracle
messages and continuations; its executions decode to the protocol's (`decodePath`). Every
restoration key of the decoded presentation answers coins, so the encoded random-oracle and
hash-chain theorems (`CommonChallenge`) apply to it with the identity carrier (`decodedCommon`).

A knowledge certificate of the protocol pulls back along the decoders (`decodeCertificate`): the
same states, with the state after coins `c` the protocol's after the challenge `decode c`. A
challenge decoded from uniform coins is bad with probability at most `ratio` times its probability
under the uniform challenge when the decoder's pushforward is within `ratio` of uniform
(`Decoder.Bounded`); for a decoder that pushes uniform coins to uniform challenges the ratio is `1`.
The pulled-back certificate's node errors are then the protocol's times the ratios
(`supErrors_decodeCertificate_le`), and its terminal knowledge failures are the protocol's on the
decoded path (`badTerminal_decode`).
-/

@[expose] public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Interaction.Oracle

namespace PublicCoin

/-- Decoders of the coins `C` into the challenge alphabets: a map at every challenge node, which
may depend on the prover's public moves before it. -/
@[reducible] def Decoder (C : Type) {protocol : Protocol.{0}} (coin : PublicCoin protocol) :
    Type :=
  PublicCoin.rec (motive := fun _ _ => Type) PUnit
    (fun {Moves} _ _ _ decoders => (move : Moves) → decoders move)
    (fun {_} _ _ _ _ decoders => decoders)
    (@fun Challenge _ _ _ decoders => (C → Challenge) × decoders) coin

variable {C : Type}

/-- The decoded presentation: the protocol with coins of `C` at every challenge node. -/
@[reducible] def decodedProtocol (C : Type) : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    Decoder C coin → Protocol.{0}
  | _, .done, _ => .done
  | _, @sender Moves _ _ next, dec => .public .sender Moves fun move =>
      decodedProtocol C (next move) (dec move)
  | _, @oracle Messages _ interface _ next, dec =>
      .oracleWith Messages interface (decodedProtocol C next dec)
  | _, @challenge _ _ _ next, dec => .public .receiver C fun _ => decodedProtocol C next dec.2

/-- The decoded presentation is public-coin. -/
@[reducible] def decoded (C : Type) [SampleableType C] : {protocol : Protocol.{0}} →
    (coin : PublicCoin protocol) → (dec : Decoder C coin) →
    PublicCoin (decodedProtocol C coin dec)
  | _, .done, _ => .done
  | _, @sender _ _ _ next, dec => .sender fun move => decoded C (next move) (dec move)
  | _, @oracle _ _ _ _ next, dec => .oracle (decoded C next dec)
  | _, @challenge _ _ _ next, dec => .challenge (decoded C next dec.2)

/-- The protocol's execution an execution of the decoded presentation decodes to. -/
def decodePath : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    (dec : Decoder C coin) → (decodedProtocol C coin dec).tree.ExecutionPath →
    protocol.tree.ExecutionPath
  | _, .done, _, _ => PUnit.unit
  | _, @sender _ _ _ next, dec, path => ⟨path.1, decodePath (next path.1) (dec path.1) path.2⟩
  | _, @oracle _ _ _ _ next, dec, path => ⟨path.1, decodePath next dec path.2⟩
  | _, @challenge _ _ _ next, dec, path => ⟨dec.1 path.1, decodePath next dec.2 path.2⟩

end PublicCoin

namespace Security

open PublicCoin StateRestoration

variable {C : Type}

/-- The witness maps of the decoded presentation: after coins `c`, the protocol's after the
challenge they decode to. -/
def decodeExtractor : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    (dec : Decoder C coin) → {state : KnowledgeState} →
    RoundExtractor protocol.tree state →
    RoundExtractor (decodedProtocol C coin dec).tree state
  | _, .done, _, _, _ => PUnit.unit
  | _, @PublicCoin.sender _ _ _ next, dec, _, extractor => fun move =>
      ⟨(extractor move).1, (extractor move).2.1,
        decodeExtractor (next move) (dec move) (extractor move).2.2⟩
  | _, @PublicCoin.oracle _ _ _ _ next, dec, _, extractor => fun message =>
      ⟨(extractor message).1, (extractor message).2.1,
        decodeExtractor next dec (extractor message).2.2⟩
  | _, @PublicCoin.challenge _ _ _ next, dec, _, extractor => fun c =>
      ⟨(extractor (dec.1 c)).1, (extractor (dec.1 c)).2.1,
        decodeExtractor next dec.2 (extractor (dec.1 c)).2.2⟩

/-- Prover messages preserve the decoded states as they preserve the protocol's. -/
theorem isProverPreserving_decodeExtractor : {protocol : Protocol.{0}} →
    (coin : PublicCoin protocol) → (dec : Decoder C coin) → {state : KnowledgeState} →
    (extractor : RoundExtractor protocol.tree state) →
    extractor.IsProverPreserving protocol.roles →
    (decodeExtractor coin dec extractor).IsProverPreserving
      (decodedProtocol C coin dec).roles
  | _, .done, _, _, _, _ => trivial
  | _, @PublicCoin.sender _ _ _ next, dec, _, _, h =>
      ⟨fun move hs w hw => h.1 move hs w hw, fun move =>
        isProverPreserving_decodeExtractor (next move) (dec move) _ (h.2 move)⟩
  | _, @PublicCoin.oracle _ _ _ _ next, dec, _, _, h =>
      ⟨fun message w hw => h.1 message w hw, fun message =>
        isProverPreserving_decodeExtractor next dec _ (h.2 message)⟩
  | _, @PublicCoin.challenge _ _ _ next, dec, _, _, h =>
      ⟨fun _ hs => (nomatch hs), fun c =>
        isProverPreserving_decodeExtractor next dec.2 _ (h.2 (dec.1 c))⟩

/-- Every decoder's pushforward of uniform coins is within `ratio` of the uniform challenge: an
event of the decoded challenge has at most `ratio` times its uniform probability. -/
def Decoder.Bounded [SampleableType C] (ratio : ENNReal) : {protocol : Protocol.{0}} →
    (coin : PublicCoin protocol) → Decoder C coin → Prop
  | _, .done, _ => True
  | _, @PublicCoin.sender _ _ _ next, dec => ∀ move, Decoder.Bounded ratio (next move) (dec move)
  | _, @PublicCoin.oracle _ _ _ _ next, dec => Decoder.Bounded ratio next dec
  | _, @PublicCoin.challenge Challenge _ _ next, dec =>
      (∀ E : Challenge → Prop, Pr{let c ← ($ᵗ C : ProbComp C)}[E (dec.1 c)] ≤
        ratio * Pr{let x ← ($ᵗ Challenge : ProbComp Challenge)}[E x]) ∧
        Decoder.Bounded ratio next dec.2

/-- A decoder that pushes uniform coins to the uniform challenge is within ratio `1`. -/
theorem decoder_bounded_one [SampleableType C] {Challenge : Type} [SampleableType Challenge]
    (decode : C → Challenge)
    (uniform : ∀ E : Challenge → Prop, Pr{let c ← ($ᵗ C : ProbComp C)}[E (decode c)] =
      Pr{let x ← ($ᵗ Challenge : ProbComp Challenge)}[E x])
    (E : Challenge → Prop) :
    Pr{let c ← ($ᵗ C : ProbComp C)}[E (decode c)] ≤
      1 * Pr{let x ← ($ᵗ Challenge : ProbComp Challenge)}[E x] := by
  rw [one_mul]
  exact le_of_eq (uniform E)

/-- The challenge schedule of the decoded presentation: uniform coins, with `ratio` times the
protocol's error at the node. -/
noncomputable def decodeSchedule [SampleableType C] (ratio : ENNReal) : {protocol : Protocol.{0}} →
    (coin : PublicCoin protocol) → (dec : Decoder C coin) →
    RoundExtractor.ChallengeSchedule protocol.tree protocol.roles →
    RoundExtractor.ChallengeSchedule (decodedProtocol C coin dec).tree
      (decodedProtocol C coin dec).roles
  | _, .done, _, _ => PUnit.unit
  | _, @PublicCoin.sender _ _ _ next, dec, schedule =>
      ⟨PUnit.unit, fun move => decodeSchedule ratio (next move) (dec move) (schedule.2 move)⟩
  | _, @PublicCoin.oracle _ _ _ _ next, dec, schedule => fun message =>
      decodeSchedule ratio next dec (schedule message)
  | _, @PublicCoin.challenge _ _ _ next, dec, schedule =>
      ⟨($ᵗ C, ratio * schedule.1.2), fun c => decodeSchedule ratio next dec.2 (schedule.2 (dec.1 c))⟩

/-- The pulled-back witness maps are locally bounded by the decoders' ratio times the protocol's
errors, when the protocol's challenges are uniform. -/
theorem isLocallyBounded_decodeExtractor [SampleableType C] (ratio : ENNReal) : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) → (dec : Decoder C coin) →
    Decoder.Bounded ratio coin dec → {state : KnowledgeState} →
    (extractor : RoundExtractor protocol.tree state) →
    (schedule : RoundExtractor.ChallengeSchedule protocol.tree protocol.roles) →
    UniformChallenges coin schedule → extractor.IsLocallyBounded protocol.roles schedule →
    (decodeExtractor coin dec extractor).IsLocallyBounded (decodedProtocol C coin dec).roles
      (decodeSchedule ratio coin dec schedule)
  | _, .done, _, _, _, _, _, _, _ => trivial
  | _, @PublicCoin.sender _ _ _ next, dec, hdec, _, extractor, schedule, uniform, bounded =>
      fun move => isLocallyBounded_decodeExtractor ratio (next move) (dec move) (hdec move) _ _
        (uniform move) (bounded move)
  | _, @PublicCoin.oracle _ _ _ _ next, dec, hdec, _, extractor, schedule, uniform, bounded =>
      fun message => isLocallyBounded_decodeExtractor ratio next dec hdec _ _ (uniform message)
        (bounded message)
  | _, @PublicCoin.challenge Challenge _ _ next, dec, hdec, _, extractor, schedule, uniform,
      bounded => by
      refine ⟨?_, fun c => isLocallyBounded_decodeExtractor ratio next dec.2 hdec.2 _ _
        (uniform.2 (dec.1 c)) (bounded.2 (dec.1 c))⟩
      have here := bounded.1
      rw [_root_.RoundByRound.GameFamily.isBounded_iff] at here ⊢
      intro round context
      have h := here round context
      rw [uniform.1] at h
      change Pr{let x ← ($ᵗ Challenge : ProbComp Challenge)}[
        RoundExtractor.badChallenge extractor x] ≤ schedule.1.2 at h
      change Pr{let c ← ($ᵗ C : ProbComp C)}[RoundExtractor.badChallenge extractor (dec.1 c)] ≤
        ratio * schedule.1.2
      exact (hdec.1 _).trans (by gcongr)

/-- **A certificate pulled back along decoders.** A knowledge certificate whose challenges are
uniform is a certificate of the decoded presentation, with every node's error multiplied by the
decoders' ratio. -/
noncomputable def decodeCertificate [SampleableType C] (ratio : ENNReal) {protocol : Protocol.{0}}
    (coin : PublicCoin protocol) (dec : Decoder C coin) (hdec : Decoder.Bounded ratio coin dec)
    {state : KnowledgeState} (certificate : KnowledgeCertificate protocol.tree protocol.roles state)
    (uniform : UniformChallenges coin certificate.challenges) :
    KnowledgeCertificate (decodedProtocol C coin dec).tree (decodedProtocol C coin dec).roles
      state where
  extractor := decodeExtractor coin dec certificate.extractor
  challenges := decodeSchedule ratio coin dec certificate.challenges
  prover_preserving := isProverPreserving_decodeExtractor coin dec _ certificate.prover_preserving
  local_bound := isLocallyBounded_decodeExtractor ratio coin dec hdec certificate.extractor
    certificate.challenges uniform certificate.local_bound

/-! ### Keys, errors and terminal states of the decoded presentation -/

/-- Every key of the decoded presentation answers coins. -/
theorem challenge_decoded [SampleableType C] {Salt : Type} : {protocol : Protocol.{0}} →
    (coin : PublicCoin protocol) → (dec : Decoder C coin) →
    (pre : Prefix Salt (decoded C coin dec)) → pre.Challenge = C
  | _, .done, _, pre => nomatch pre
  | _, @PublicCoin.sender Moves _ _ next, dec, pre => by
      obtain ⟨move, pre⟩ := (pre : (move : Moves) × Prefix Salt (decoded C (next move) (dec move)))
      exact challenge_decoded (next move) (dec move) pre
  | _, @PublicCoin.oracle Messages _ _ _ next, dec, pre => by
      obtain ⟨_, pre⟩ := (pre : Messages × Prefix Salt (decoded C next dec))
      exact challenge_decoded next dec pre
  | _, @PublicCoin.challenge _ _ _ next, dec, pre => by
      obtain _ | ⟨_, pre⟩ := (pre : Salt ⊕ (Salt × Prefix Salt (decoded C next dec.2)))
      · rfl
      · exact challenge_decoded next dec.2 pre

/-- The decoded presentations of an input-indexed protocol answer every key with coins: the
common challenge carrier is the coins themselves. -/
def decodedCommon [SampleableType C] {Input Salt : Type} {protocol : Input → Protocol.{0}}
    (coin : (z : Input) → PublicCoin (protocol z)) (dec : (z : Input) → Decoder C (coin z)) :
    CommonChallenge Input Salt C (fun z => decoded C (coin z) (dec z)) where
  challengeEquiv key := Equiv.cast (challenge_decoded (coin key.1) (dec key.1) key.2)

/-- The prefix of the protocol a prefix of the decoded presentation stands for. -/
@[reducible] noncomputable def Prefix.undecode [SampleableType C] {Salt : Type} {protocol : Protocol.{0}}
    (coin : PublicCoin protocol) :
    (dec : Decoder C coin) → Prefix Salt (decoded C coin dec) → Prefix Salt coin :=
  PublicCoin.rec (motive := fun _ coin =>
      (dec : Decoder C coin) → Prefix Salt (decoded C coin dec) → Prefix Salt coin)
    (fun _ pre => nomatch pre)
    (fun _ undecode dec pre => ⟨pre.1, undecode pre.1 (dec pre.1) pre.2⟩)
    (fun _ undecode dec pre => ⟨pre.1, undecode dec pre.2⟩)
    (fun _ undecode dec pre => Sum.casesOn (motive := fun _ => Salt ⊕ (Salt × _)) pre
      (fun salt => .inl salt) fun pre => .inr ⟨pre.1, undecode dec.2 pre.2⟩) coin

/-- The decoded schedule samples uniform coins. -/
theorem uniformChallenges_decodeSchedule [SampleableType C] (ratio : ENNReal) :
    {protocol : Protocol.{0}} → (coin : PublicCoin protocol) → (dec : Decoder C coin) →
    (schedule : RoundExtractor.ChallengeSchedule protocol.tree protocol.roles) →
    UniformChallenges (decoded C coin dec) (decodeSchedule ratio coin dec schedule)
  | _, .done, _, _ => trivial
  | _, @PublicCoin.sender _ _ _ next, dec, schedule => fun move =>
      uniformChallenges_decodeSchedule ratio (next move) (dec move) (schedule.2 move)
  | _, @PublicCoin.oracle _ _ _ _ next, dec, schedule => fun message =>
      uniformChallenges_decodeSchedule ratio next dec (schedule message)
  | _, @PublicCoin.challenge _ _ _ next, dec, schedule => ⟨rfl, fun c =>
      uniformChallenges_decodeSchedule ratio next dec.2 (schedule.2 (dec.1 c))⟩

/-- A node error of the decoded schedule is at most the ratio times the protocol's error at the
node it stands for. -/
theorem supErrors_decodeSchedule_le [SampleableType C] (ratio : ENNReal) :
    {protocol : Protocol.{0}} → (coin : PublicCoin protocol) → (dec : Decoder C coin) →
    (schedule : RoundExtractor.ChallengeSchedule protocol.tree protocol.roles) →
    (node : Prefix PUnit (decoded C coin dec)) →
    supErrors (decoded C coin dec) (decodeSchedule ratio coin dec schedule) node ≤
      ratio * supErrors coin schedule (Prefix.undecode coin dec node)
  | _, .done, _, _, node => nomatch node
  | _, @PublicCoin.sender Moves _ _ next, dec, schedule, node => by
      obtain ⟨move, node⟩ :=
        (node : (move : Moves) × Prefix PUnit (decoded C (next move) (dec move)))
      exact supErrors_decodeSchedule_le ratio (next move) (dec move) (schedule.2 move) node
  | _, @PublicCoin.oracle Messages _ _ _ next, dec, schedule, node => by
      obtain ⟨message, node⟩ := (node : Messages × Prefix PUnit (decoded C next dec))
      exact supErrors_decodeSchedule_le ratio next dec (schedule message) node
  | _, @PublicCoin.challenge _ _ _ next, dec, schedule, node => by
      obtain _ | ⟨_, node⟩ := (node : PUnit ⊕ (PUnit × Prefix PUnit (decoded C next dec.2)))
      · exact le_rfl
      · exact iSup_le fun c => (supErrors_decodeSchedule_le ratio next dec.2
          (schedule.2 (dec.1 c)) node).trans (by
            gcongr
            exact le_iSup (fun x => supErrors next (schedule.2 x) _) (dec.1 c))

/-- The path sum of errors read through `undecode` and scaled by the ratio is the ratio times the
protocol's path sum. -/
theorem pathError_undecode [SampleableType C] (ratio : ENNReal) :
    {protocol : Protocol.{0}} → (coin : PublicCoin protocol) → (dec : Decoder C coin) →
    (errors : Errors coin) →
    pathError (decoded C coin dec) (fun node => ratio * errors (Prefix.undecode coin dec node)) =
      ratio * pathError coin errors
  | _, .done, _, _ => (mul_zero ratio).symm
  | _, @PublicCoin.sender _ _ _ next, dec, errors => by
      change (⨆ move, pathError (decoded C (next move) (dec move))
        (fun q => ratio * errors ⟨move, Prefix.undecode (next move) (dec move) q⟩)) =
        ratio * ⨆ move, pathError (next move) (fun q => errors ⟨move, q⟩)
      rw [ENNReal.mul_iSup]
      exact iSup_congr fun move =>
        pathError_undecode ratio (next move) (dec move) fun q => errors ⟨move, q⟩
  | _, @PublicCoin.oracle _ _ _ _ next, dec, errors => by
      change (⨆ message, pathError (decoded C next dec)
        (fun q => ratio * errors ⟨message, Prefix.undecode next dec q⟩)) =
        ratio * ⨆ message, pathError next (fun q => errors ⟨message, q⟩)
      rw [ENNReal.mul_iSup]
      exact iSup_congr fun message =>
        pathError_undecode ratio next dec fun q => errors ⟨message, q⟩
  | _, @PublicCoin.challenge _ _ _ next, dec, errors => by
      change ratio * errors (.inl PUnit.unit) + pathError (decoded C next dec.2)
        (fun q => ratio * errors (.inr ⟨PUnit.unit, Prefix.undecode next dec.2 q⟩)) =
        ratio * (errors (.inl PUnit.unit) + pathError next (fun q => errors (.inr ⟨PUnit.unit, q⟩)))
      rw [pathError_undecode ratio next dec.2 fun q => errors (.inr ⟨PUnit.unit, q⟩), mul_add]

/-- A terminal knowledge failure of the decoded presentation is one of the protocol on the decoded
path: a valid terminal witness whose backward extraction fails. -/
theorem badTerminal_decode : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    (dec : Decoder C coin) → {state : KnowledgeState} →
    (extractor : RoundExtractor protocol.tree state) →
    (path : (decodedProtocol C coin dec).tree.ExecutionPath) → (P : state.Witness → Prop) →
    (∃ w, ((decodeExtractor coin dec extractor).terminalState path).holds w ∧
      P ((decodeExtractor coin dec extractor).extractWitness path w)) ↔
    (∃ w, (extractor.terminalState (decodePath coin dec path)).holds w ∧
      P (extractor.extractWitness (decodePath coin dec path) w))
  | _, .done, _, _, _, _, _ => Iff.rfl
  | _, @PublicCoin.sender _ _ _ next, dec, _, extractor, path, P =>
      badTerminal_decode (next path.1) (dec path.1) (extractor path.1).2.2 path.2
        (P ∘ (extractor path.1).2.1)
  | _, @PublicCoin.oracle _ _ _ _ next, dec, _, extractor, path, P =>
      badTerminal_decode next dec (extractor path.1).2.2 path.2 (P ∘ (extractor path.1).2.1)
  | _, @PublicCoin.challenge _ _ _ next, dec, _, extractor, path, P =>
      badTerminal_decode next dec.2 (extractor (dec.1 path.1)).2.2 path.2
        (P ∘ (extractor (dec.1 path.1)).2.1)

end Security

end Interaction.Oracle
