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
# Challenges drawn from common coins, with grinding

A Fiat–Shamir verifier reads every challenge off one kind of random-oracle answer, the coins `C`
(for a hash chain, its state and output). At each challenge node it draws the challenge as a
`PublicCoin.Draw`: the prover first sends a witness, absorbed before the coins; the verifier
rejects coins that fail the draw's check, and decodes the challenge from the others. A grinding
draw (`Draw.grind`) checks a proof-of-work sample: it accepts the coins whose sample has `bits`
vanishing low bits. A plain draw (`Draw.plain`) has a trivial witness and accepts every coin.

The *decoded presentation* of a public-coin protocol (`decodedProtocol`, `PublicCoin.decoded`)
has, at every challenge node, the draw's witness move followed by the coins, with the same prover
moves, oracle messages and continuations. An execution whose coins all pass decodes to one of the
protocol (`decodePath`). Every restoration key of the decoded presentation answers coins, so the
encoded random-oracle and hash-chain theorems (`CommonChallenge`) apply to it with the identity
carrier (`decodedCommon`); the key of a draw's coins includes the prover's witness.

A knowledge certificate of the protocol pulls back along the draws (`decodeCertificate`): the
same states, with the state after accepted coins `c` the protocol's after the challenge decoded
from `c`, and after rejected coins a state no witness satisfies (`KnowledgeState.empty`). A draw
is bounded by a ratio `r` against a law of the challenge (`Draw.Bounded`) when accepted coins
decode into any event with at most `r` times the event's probability under the law; the decoder
is bounded against a certificate (`Decoder.Bounded`) when each draw is, against the law the
certificate's schedule samples at its node. The certificate's local bounds are then bounds on the
decoded coins: its challenges need not be uniform, so a certificate whose bound at a node holds
for the law the draw actually decodes to (the residues of uniform field elements for query
positions, say) pays no ratio for that law. The pulled-back certificate's error at a node is the
protocol's times the node's ratio (`supErrors_decodeSchedule_le`), and its terminal knowledge
failures are the protocol's on the decoded path (`badTerminal_decode`). A grinding draw's ratio is
the proof-of-work pass probability (`powFraction` for a uniform residue) times its decoder's
ratio, when the sample is independent of the decoded challenge (`Draw.Bounded.grind`).
-/

@[expose] public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

universe w

namespace Interaction.Oracle

namespace PublicCoin

/-- How a Fiat–Shamir verifier draws one challenge from coins `C`: the prover's witness, absorbed
before the coins, the coins the verifier accepts, and the challenge read off them. -/
structure Draw (C Challenge : Type) where
  /-- The prover's witness, absorbed before the coins are drawn. -/
  Witness : Type
  [decEq : DecidableEq Witness]
  /-- The coins the verifier accepts. -/
  accept : C → Bool
  /-- The challenge read off the coins. -/
  decode : C → Challenge

attribute [instance] Draw.decEq

variable {C Challenge : Type}

/-- A draw without grinding: no witness, every coin accepted. -/
def Draw.plain (decode : C → Challenge) : Draw C Challenge where
  Witness := PUnit
  accept _ := true
  decode := decode

/-- A grinding draw: after the prover's witness, the verifier accepts the coins whose
proof-of-work sample has its `bits` low bits zero. -/
def Draw.grind (Witness : Type) [DecidableEq Witness] (bits : ℕ) (sample : C → ℕ)
    (decode : C → Challenge) : Draw C Challenge where
  Witness := Witness
  accept c := sample c % 2 ^ bits == 0
  decode := decode

/-- Draws at every challenge node, which may depend on the prover's public moves before it. -/
@[reducible] def Decoder (C : Type) {protocol : Protocol.{0}} (coin : PublicCoin protocol) :
    Type 1 :=
  PublicCoin.rec (motive := fun _ _ => Type 1) PUnit
    (fun {Moves} _ _ _ decoders => (move : Moves) → decoders move)
    (fun {_} _ _ _ _ decoders => decoders)
    (@fun Challenge _ _ _ decoders => Draw C Challenge × decoders) coin

/-- The decoded presentation: the protocol with, at every challenge node, the draw's witness
move followed by coins of `C`. -/
@[reducible] def decodedProtocol (C : Type) : {protocol : Protocol.{0}} →
    (coin : PublicCoin protocol) →
    Decoder C coin → Protocol.{0}
  | _, .done, _ => .done
  | _, @sender Moves _ _ next, dec => .public .sender Moves fun move =>
      decodedProtocol C (next move) (dec move)
  | _, @oracle Messages _ interface _ next, dec =>
      .oracleWith Messages interface (decodedProtocol C next dec)
  | _, @challenge _ _ _ next, dec => .public .sender dec.1.Witness fun _ =>
      .public .receiver C fun _ => decodedProtocol C next dec.2

/-- The decoded presentation is public-coin. -/
@[reducible] def decoded (C : Type) [SampleableType C] : {protocol : Protocol.{0}} →
    (coin : PublicCoin protocol) → (dec : Decoder C coin) →
    PublicCoin (decodedProtocol C coin dec)
  | _, .done, _ => .done
  | _, @sender _ _ _ next, dec => .sender fun move => decoded C (next move) (dec move)
  | _, @oracle _ _ _ _ next, dec => .oracle (decoded C next dec)
  | _, @challenge _ _ _ next, dec => .sender fun _ => .challenge (decoded C next dec.2)

/-- The protocol's execution an execution of the decoded presentation decodes to, if the
verifier accepts all its coins. -/
def decodePath : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    (dec : Decoder C coin) → (decodedProtocol C coin dec).tree.ExecutionPath →
    Option protocol.tree.ExecutionPath
  | _, .done, _, _ => some PUnit.unit
  | _, @sender _ _ _ next, dec, path =>
      (decodePath (next path.1) (dec path.1) path.2).map fun rest => ⟨path.1, rest⟩
  | _, @oracle _ _ _ _ next, dec, path =>
      (decodePath next dec path.2).map fun rest => ⟨path.1, rest⟩
  | _, @challenge _ _ _ next, dec, path =>
      bif dec.1.accept path.2.1 then
        (decodePath next dec.2 path.2.2).map fun rest => ⟨dec.1.decode path.2.1, rest⟩
      else none

/-- A draw is bounded by `ratio` against the law `law` of the challenge when accepted coins decode
into any event with at most `ratio` times the event's probability under `law`. -/
def Draw.Bounded [SampleableType C] (draw : Draw C Challenge) (law : ProbComp Challenge)
    (ratio : ENNReal) : Prop :=
  ∀ E : Challenge → Prop, Pr{let c ← ($ᵗ C : ProbComp C)}[draw.accept c = true ∧
    E (draw.decode c)] ≤ ratio * Pr{let x ← law}[E x]

/-- A plain draw is bounded by its decoder's ratio. -/
theorem Draw.Bounded.plain [SampleableType C] {law : ProbComp Challenge}
    {decode : C → Challenge} {ratio : ENNReal}
    (h : ∀ E : Challenge → Prop, Pr{let c ← ($ᵗ C : ProbComp C)}[E (decode c)] ≤
      ratio * Pr{let x ← law}[E x]) :
    (Draw.plain decode).Bounded law ratio := fun E =>
  (prEvent_mono _ _ _ fun _ hc => hc.2).trans (h E)

/-- **Grinding.** A grinding draw whose proof-of-work sample passes with probability at most
`pass`, independently of the decoded challenge, is bounded by `pass` times its decoder's ratio. -/
theorem Draw.Bounded.grind [SampleableType C] {law : ProbComp Challenge}
    (Witness : Type) [DecidableEq Witness] (bits : ℕ) {sample : C → ℕ} {decode : C → Challenge}
    {pass ratio : ENNReal}
    (independent : ∀ E : Challenge → Prop,
      Pr{let c ← ($ᵗ C : ProbComp C)}[sample c % 2 ^ bits = 0 ∧ E (decode c)] =
        Pr{let c ← ($ᵗ C : ProbComp C)}[sample c % 2 ^ bits = 0] *
          Pr{let c ← ($ᵗ C : ProbComp C)}[E (decode c)])
    (passes : Pr{let c ← ($ᵗ C : ProbComp C)}[sample c % 2 ^ bits = 0] ≤ pass)
    (h : ∀ E : Challenge → Prop, Pr{let c ← ($ᵗ C : ProbComp C)}[E (decode c)] ≤
      ratio * Pr{let x ← law}[E x]) :
    (Draw.grind Witness bits sample decode).Bounded law (pass * ratio) := fun E => by
  simp only [Draw.grind, beq_iff_eq]
  rw [independent E, mul_assoc]
  exact mul_le_mul' passes (h E)

/-- The probability that the `bits` low bits of a uniform residue modulo `p` vanish:
`((p - 1) / 2 ^ bits + 1) / p`, the multiples of `2 ^ bits` below `p`. -/
noncomputable def powFraction (p bits : ℕ) : ENNReal :=
  (((p - 1) / 2 ^ bits + 1 : ℕ) : ENNReal) / p

/-- The multiples of `d` up to `n` are `n / d + 1`, zero among them. -/
private theorem card_range_dvd (n d : ℕ) :
    (Finset.filter (fun e => d ∣ e) (Finset.range (n + 1))).card = n / d + 1 := by
  induction n with
  | zero => simp [Finset.filter_singleton]
  | succ n ih =>
      rw [Finset.range_add_one, Finset.filter_insert, Nat.succ_div]
      by_cases h : d ∣ n + 1
      · simp only [h, ↓reduceIte]
        rw [Finset.card_insert_of_notMem (by simp), ih]
      · simp only [h, ↓reduceIte, add_zero, ih]

/-- The `bits` low bits of a uniform residue modulo `n + 1` vanish with probability
`powFraction (n + 1) bits`. -/
theorem prEvent_lowBits_eq_powFraction (n bits : ℕ) :
    Pr{let x ← ($ᵗ Fin (n + 1) : ProbComp (Fin (n + 1)))}[x.val % 2 ^ bits = 0] =
      powFraction (n + 1) bits := by
  rw [SampleableType.prEvent_uniformSample, Fintype.card_fin, powFraction, Nat.add_sub_cancel,
    ← card_range_dvd n (2 ^ bits)]
  congr 2
  rw [← Finset.card_map Fin.valEmbedding]
  congr 1
  ext e
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
    Finset.mem_range, Nat.dvd_iff_mod_eq_zero]
  exact ⟨fun ⟨x, hx, he⟩ => he ▸ ⟨x.isLt, hx⟩, fun ⟨he, hx⟩ => ⟨⟨e, he⟩, hx, rfl⟩⟩

/-- No grinding passes every residue. -/
theorem powFraction_zero (p : ℕ) [NeZero p] : powFraction p 0 = 1 := by
  rw [powFraction, pow_zero, Nat.div_one, Nat.sub_add_cancel NeZero.one_le]
  exact ENNReal.div_self (Nat.cast_ne_zero.mpr (NeZero.ne p)) (ENNReal.natCast_ne_top p)

/-- Grinding by `bits` passes at most `2⁻ᵇⁱᵗˢ + 1/p` of the residues. -/
theorem powFraction_le (p bits : ℕ) [NeZero p] :
    powFraction p bits ≤ 2⁻¹ ^ bits + (p : ENNReal)⁻¹ := by
  have hp : (p : ENNReal) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  rw [powFraction, Nat.cast_add, Nat.cast_one, ENNReal.add_div, one_div]
  refine add_le_add ?_ le_rfl
  rw [ENNReal.div_le_iff hp (ENNReal.natCast_ne_top p), ← ENNReal.inv_pow, mul_comm,
    ← div_eq_mul_inv, ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp))]
  exact_mod_cast (Nat.div_mul_le_self (p - 1) (2 ^ bits)).trans (Nat.sub_le p 1)

end PublicCoin

namespace Security

open PublicCoin StateRestoration

/-! ### The empty knowledge state -/

/-- The knowledge state no witness satisfies: the state after coins the verifier rejects. -/
def KnowledgeState.empty : KnowledgeState.{w} where
  Witness := PEmpty
  holds _ := False

/-- Witness maps in which every state is empty. -/
def RoundExtractor.empty : (tree : TypeTree.{0}) → RoundExtractor tree KnowledgeState.empty.{w}
  | .done => PUnit.unit
  | .public _ next => fun move => ⟨KnowledgeState.empty, id, RoundExtractor.empty (next move)⟩
  | .oracle _ next => fun _ => ⟨KnowledgeState.empty, id, RoundExtractor.empty (next PUnit.unit)⟩

/-- Every state of the empty witness maps is empty. -/
theorem RoundExtractor.terminalState_empty : (tree : TypeTree.{0}) →
    (path : tree.ExecutionPath) →
    (RoundExtractor.empty.{w} tree).terminalState path = KnowledgeState.empty
  | .done, _ => rfl
  | .public _ next, path => RoundExtractor.terminalState_empty (next path.1) path.2
  | .oracle _ next, path => RoundExtractor.terminalState_empty (next PUnit.unit) path.2

/-- No witness holds at the end of the empty witness maps. -/
theorem RoundExtractor.not_holds_empty : (tree : TypeTree.{0}) → (path : tree.ExecutionPath) →
    (witness : ((RoundExtractor.empty.{w} tree).terminalState path).Witness) →
    ¬ ((RoundExtractor.empty.{w} tree).terminalState path).holds witness
  | .done, _, _, h => h
  | .public _ next, path, witness, h =>
      RoundExtractor.not_holds_empty (next path.1) path.2 witness h
  | .oracle _ next, path, witness, h =>
      RoundExtractor.not_holds_empty (next PUnit.unit) path.2 witness h

/-- The empty witness maps are prover-preserving. -/
theorem RoundExtractor.isProverPreserving_empty : (tree : TypeTree.{0}) →
    (roles : tree.RoleDecoration) → (RoundExtractor.empty.{w} tree).IsProverPreserving roles
  | .done, _ => trivial
  | .public _ next, roles => ⟨fun _ _ witness => witness.elim, fun move =>
      RoundExtractor.isProverPreserving_empty (next move) (roles.2 move)⟩
  | .oracle _ next, roles => ⟨fun _ witness => witness.elim, fun _ =>
      RoundExtractor.isProverPreserving_empty (next PUnit.unit) (roles.2 PUnit.unit)⟩

/-- The empty witness maps have no bad challenge, so any schedule bounds them. -/
theorem RoundExtractor.isLocallyBounded_empty : (tree : TypeTree.{0}) →
    (roles : tree.RoleDecoration) → (schedule : RoundExtractor.ChallengeSchedule tree roles) →
    (RoundExtractor.empty.{w} tree).IsLocallyBounded roles schedule
  | .done, _, _ => trivial
  | .public _ next, ⟨.sender, roles⟩, schedule => fun move =>
      RoundExtractor.isLocallyBounded_empty (next move) (roles move) (schedule.2 move)
  | .public _ next, ⟨.receiver, roles⟩, schedule => by
      refine ⟨?_, fun move => RoundExtractor.isLocallyBounded_empty (next move) (roles move)
        (schedule.2 move)⟩
      rw [_root_.RoundByRound.GameFamily.isBounded_iff]
      intro _ _
      refine le_of_eq_of_le (prEvent_eq_zero_of_forall_not _ _ fun _ bad => ?_) zero_le
      obtain ⟨witness, -⟩ := bad
      exact witness.elim
  | .oracle _ next, roles, schedule => fun message =>
      RoundExtractor.isLocallyBounded_empty (next PUnit.unit) (roles.2 PUnit.unit)
        (schedule message)

/-! ### The pulled-back certificate -/

variable {C : Type}

/-- The witness maps after coins: the given ones if the verifier accepts the coins, the empty ones
if it rejects them. -/
def drawChild {state : KnowledgeState.{w}} {tree : TypeTree.{0}} (accepted : Bool)
    (child : (after : KnowledgeState.{w}) × ((after.Witness → state.Witness) ×
      RoundExtractor tree after)) :
    (after : KnowledgeState.{w}) × ((after.Witness → state.Witness) × RoundExtractor tree after) :=
  bif accepted then child else ⟨KnowledgeState.empty, PEmpty.elim, RoundExtractor.empty tree⟩

theorem isProverPreserving_drawChild {state : KnowledgeState.{w}} {tree : TypeTree.{0}}
    (roles : tree.RoleDecoration) (accepted : Bool)
    (child : (after : KnowledgeState.{w}) × ((after.Witness → state.Witness) ×
      RoundExtractor tree after))
    (h : child.2.2.IsProverPreserving roles) :
    (drawChild accepted child).2.2.IsProverPreserving roles := by
  cases accepted
  · exact RoundExtractor.isProverPreserving_empty tree roles
  · exact h

theorem isLocallyBounded_drawChild {state : KnowledgeState.{w}} {tree : TypeTree.{0}}
    (roles : tree.RoleDecoration) (schedule : RoundExtractor.ChallengeSchedule tree roles)
    (accepted : Bool)
    (child : (after : KnowledgeState.{w}) × ((after.Witness → state.Witness) ×
      RoundExtractor tree after))
    (h : child.2.2.IsLocallyBounded roles schedule) :
    (drawChild accepted child).2.2.IsLocallyBounded roles schedule := by
  cases accepted
  · exact RoundExtractor.isLocallyBounded_empty tree roles schedule
  · exact h

/-- Rejected coins lead to no witness: knowledge after coins is knowledge after accepted ones. -/
theorem exists_drawChild {state : KnowledgeState.{w}} {tree : TypeTree.{0}} (accepted : Bool)
    (child : (after : KnowledgeState.{w}) × ((after.Witness → state.Witness) ×
      RoundExtractor tree after))
    (P : (child : (after : KnowledgeState.{w}) × ((after.Witness → state.Witness) ×
      RoundExtractor tree after)) → child.1.Witness → Prop)
    (h : ∃ witness, P (drawChild accepted child) witness) :
    accepted = true ∧ ∃ witness, P child witness := by
  cases accepted
  · obtain ⟨witness, -⟩ := h
    exact witness.elim
  · exact ⟨rfl, h⟩

/-- A terminal witness after coins is one after accepted coins. -/
theorem exists_terminal_drawChild {state : KnowledgeState.{w}} {tree : TypeTree.{0}}
    (accepted : Bool)
    (child : (after : KnowledgeState.{w}) × ((after.Witness → state.Witness) ×
      RoundExtractor tree after))
    (path : tree.ExecutionPath) (P : state.Witness → Prop) :
    (∃ witness, ((drawChild accepted child).2.2.terminalState path).holds witness ∧
      P ((drawChild accepted child).2.1
        ((drawChild accepted child).2.2.extractWitness path witness))) ↔
    accepted = true ∧ ∃ witness, (child.2.2.terminalState path).holds witness ∧
      P (child.2.1 (child.2.2.extractWitness path witness)) := by
  cases accepted
  · exact ⟨fun ⟨witness, holds, _⟩ =>
      (RoundExtractor.not_holds_empty tree path witness holds).elim, fun h => nomatch h.1⟩
  · exact ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩

/-- The witness maps of the decoded presentation: after accepted coins `c`, the protocol's after
the challenge decoded from `c`; after rejected coins, the empty state. -/
def decodeExtractor : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    (dec : Decoder C coin) → {state : KnowledgeState.{w}} →
    RoundExtractor protocol.tree state →
    RoundExtractor (decodedProtocol C coin dec).tree state
  | _, .done, _, _, _ => PUnit.unit
  | _, @PublicCoin.sender _ _ _ next, dec, _, extractor => fun move =>
      ⟨(extractor move).1, (extractor move).2.1,
        decodeExtractor (next move) (dec move) (extractor move).2.2⟩
  | _, @PublicCoin.oracle _ _ _ _ next, dec, _, extractor => fun message =>
      ⟨(extractor message).1, (extractor message).2.1,
        decodeExtractor next dec (extractor message).2.2⟩
  | _, @PublicCoin.challenge _ _ _ next, dec, state, extractor => fun _ =>
      ⟨state, id, fun c => drawChild (dec.1.accept c)
        ⟨(extractor (dec.1.decode c)).1, (extractor (dec.1.decode c)).2.1,
          decodeExtractor next dec.2 (extractor (dec.1.decode c)).2.2⟩⟩

/-- Prover messages, the draws' witnesses among them, preserve the decoded states as they
preserve the protocol's. -/
theorem isProverPreserving_decodeExtractor : {protocol : Protocol.{0}} →
    (coin : PublicCoin protocol) → (dec : Decoder C coin) → {state : KnowledgeState.{w}} →
    (extractor : RoundExtractor protocol.tree state) →
    extractor.IsProverPreserving protocol.roles →
    (decodeExtractor coin dec extractor).IsProverPreserving
      (decodedProtocol C coin dec).roles
  | _, .done, _, _, _, _ => trivial
  | _, @PublicCoin.sender _ _ _ next, dec, _, _, h =>
      ⟨fun move hs w hw => h.1 move hs w hw, fun move =>
        isProverPreserving_decodeExtractor (next move) (dec move) _ (h.2 move)⟩
  | _, @PublicCoin.challenge _ _ _ next, dec, _, _, h =>
      ⟨fun _ _ _ hw => hw, fun _ => ⟨fun _ hs => (nomatch hs), fun c =>
        isProverPreserving_drawChild _ _ _
          (isProverPreserving_decodeExtractor next dec.2 _ (h.2 (dec.1.decode c)))⟩⟩
  | _, @PublicCoin.oracle _ _ _ _ next, dec, _, _, h =>
      ⟨fun message w hw => h.1 message w hw, fun message =>
        isProverPreserving_decodeExtractor next dec _ (h.2 message)⟩

/-- Every draw is bounded by the ratio at its node (`ratio`, indexed by the protocol's erased
prefixes) against the law the schedule samples there. -/
def Decoder.Bounded [SampleableType C] : {protocol : Protocol.{0}} →
    (coin : PublicCoin protocol) → Decoder C coin → Errors coin →
    RoundExtractor.ChallengeSchedule protocol.tree protocol.roles → Prop
  | _, .done, _, _, _ => True
  | _, @PublicCoin.sender _ _ _ next, dec, ratio, schedule =>
      ∀ move, Decoder.Bounded (next move) (dec move) (fun node => ratio ⟨move, node⟩)
        (schedule.2 move)
  | _, @PublicCoin.oracle _ _ _ _ next, dec, ratio, schedule =>
      ∀ message, Decoder.Bounded next dec (fun node => ratio ⟨message, node⟩) (schedule message)
  | _, @PublicCoin.challenge _ _ _ next, dec, ratio, schedule =>
      dec.1.Bounded schedule.1.1 (ratio (.inl PUnit.unit)) ∧ ∀ challenge,
        Decoder.Bounded next dec.2 (fun node => ratio (.inr ⟨PUnit.unit, node⟩))
          (schedule.2 challenge)

/-- The challenge schedule of the decoded presentation: uniform coins, with the node's ratio
times the protocol's error at the node; the schedule after rejected coins is the one after the
challenge they decode to. -/
noncomputable def decodeSchedule [SampleableType C] : {protocol : Protocol.{0}} →
    (coin : PublicCoin protocol) → (dec : Decoder C coin) → (ratio : Errors coin) →
    RoundExtractor.ChallengeSchedule protocol.tree protocol.roles →
    RoundExtractor.ChallengeSchedule (decodedProtocol C coin dec).tree
      (decodedProtocol C coin dec).roles
  | _, .done, _, _, _ => PUnit.unit
  | _, @PublicCoin.sender _ _ _ next, dec, ratio, schedule =>
      ⟨PUnit.unit, fun move =>
        decodeSchedule (next move) (dec move) (fun node => ratio ⟨move, node⟩) (schedule.2 move)⟩
  | _, @PublicCoin.oracle _ _ _ _ next, dec, ratio, schedule => fun message =>
      decodeSchedule next dec (fun node => ratio ⟨message, node⟩) (schedule message)
  | _, @PublicCoin.challenge _ _ _ next, dec, ratio, schedule =>
      ⟨PUnit.unit, fun _ => ⟨($ᵗ C, ratio (.inl PUnit.unit) * schedule.1.2), fun c =>
        decodeSchedule next dec.2 (fun node => ratio (.inr ⟨PUnit.unit, node⟩))
          (schedule.2 (dec.1.decode c))⟩⟩

/-- The pulled-back witness maps are locally bounded by each node's ratio times the protocol's
error there, when each draw is bounded against the law the schedule samples at its node. -/
theorem isLocallyBounded_decodeExtractor [SampleableType C] :
    {protocol : Protocol.{0}} → (coin : PublicCoin protocol) → (dec : Decoder C coin) →
    (ratio : Errors coin) → {state : KnowledgeState.{w}} →
    (extractor : RoundExtractor protocol.tree state) →
    (schedule : RoundExtractor.ChallengeSchedule protocol.tree protocol.roles) →
    Decoder.Bounded coin dec ratio schedule → extractor.IsLocallyBounded protocol.roles schedule →
    (decodeExtractor coin dec extractor).IsLocallyBounded (decodedProtocol C coin dec).roles
      (decodeSchedule coin dec ratio schedule)
  | _, .done, _, _, _, _, _, _, _ => trivial
  | _, @PublicCoin.sender _ _ _ next, dec, _, _, _, _, hdec, bounded =>
      fun move => isLocallyBounded_decodeExtractor (next move) (dec move) _ _ _
        (hdec move) (bounded move)
  | _, @PublicCoin.oracle _ _ _ _ next, dec, _, _, _, _, hdec, bounded =>
      fun message => isLocallyBounded_decodeExtractor next dec _ _ _
        (hdec message) (bounded message)
  | _, @PublicCoin.challenge Challenge _ _ next, dec, ratio, state, extractor, schedule,
      hdec, bounded => fun w => by
      refine ⟨?_, fun c => ?_⟩
      · have here := bounded.1
        rw [_root_.RoundByRound.GameFamily.isBounded_iff] at here ⊢
        intro round context
        have h := here round context
        change Pr{let x ← schedule.1.1}[
          RoundExtractor.badChallenge extractor x] ≤ schedule.1.2 at h
        change Pr{let c ← ($ᵗ C : ProbComp C)}[RoundExtractor.badChallenge
          (decodeExtractor (.challenge next) dec extractor w).2.2 c] ≤
          ratio (.inl PUnit.unit) * schedule.1.2
        exact (prEvent_mono _ _ (fun c => dec.1.accept c = true ∧
          RoundExtractor.badChallenge extractor (dec.1.decode c)) fun c bad =>
            exists_drawChild (dec.1.accept c) ⟨(extractor (dec.1.decode c)).1,
              (extractor (dec.1.decode c)).2.1,
              decodeExtractor next dec.2 (extractor (dec.1.decode c)).2.2⟩
              (fun child witness => ¬ state.holds (child.2.1 witness) ∧ child.1.holds witness)
              bad).trans
          ((hdec.1 _).trans (by gcongr))
      · exact isLocallyBounded_drawChild _ _ _ _ (isLocallyBounded_decodeExtractor next dec.2 _
          _ _ (hdec.2 (dec.1.decode c)) (bounded.2 (dec.1.decode c)))

/-- **A certificate pulled back along draws.** A knowledge certificate whose challenge laws bound
the draws is a certificate of the decoded presentation, with every node's error multiplied by its
draw's ratio. -/
noncomputable def decodeCertificate [SampleableType C] {protocol : Protocol.{0}}
    (coin : PublicCoin protocol) (dec : Decoder C coin) (ratio : Errors coin)
    {state : KnowledgeState.{w}} (certificate : KnowledgeCertificate protocol.tree protocol.roles
      state)
    (hdec : Decoder.Bounded coin dec ratio certificate.challenges) :
    KnowledgeCertificate (decodedProtocol C coin dec).tree (decodedProtocol C coin dec).roles
      state where
  extractor := decodeExtractor coin dec certificate.extractor
  challenges := decodeSchedule coin dec ratio certificate.challenges
  prover_preserving := isProverPreserving_decodeExtractor coin dec _ certificate.prover_preserving
  local_bound := isLocallyBounded_decodeExtractor coin dec ratio certificate.extractor
    certificate.challenges hdec certificate.local_bound

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
      obtain ⟨_, _ | ⟨_, pre⟩⟩ :=
        (pre : (_ : dec.1.Witness) × (Salt ⊕ (Salt × Prefix Salt (decoded C next dec.2))))
      · rfl
      · exact challenge_decoded next dec.2 pre

/-- The decoded presentations of an input-indexed protocol answer every key with coins: the
common challenge carrier is the coins themselves. -/
def decodedCommon [SampleableType C] {Input Salt : Type} {protocol : Input → Protocol.{0}}
    (coin : (z : Input) → PublicCoin (protocol z)) (dec : (z : Input) → Decoder C (coin z)) :
    CommonChallenge Input Salt C (fun z => decoded C (coin z) (dec z)) where
  challengeEquiv key := Equiv.cast (challenge_decoded (coin key.1) (dec key.1) key.2)

/-- The prefix of the protocol a prefix of the decoded presentation stands for: the draws'
witnesses forgotten. -/
@[reducible] noncomputable def Prefix.undecode [SampleableType C] {Salt : Type}
    {protocol : Protocol.{0}}
    (coin : PublicCoin protocol) :
    (dec : Decoder C coin) → Prefix Salt (decoded C coin dec) → Prefix Salt coin :=
  PublicCoin.rec (motive := fun _ coin =>
      (dec : Decoder C coin) → Prefix Salt (decoded C coin dec) → Prefix Salt coin)
    (fun _ pre => nomatch pre)
    (fun _ undecode dec pre => ⟨pre.1, undecode pre.1 (dec pre.1) pre.2⟩)
    (fun _ undecode dec pre => ⟨pre.1, undecode dec pre.2⟩)
    (fun _ undecode dec pre => Sum.casesOn (motive := fun _ => Salt ⊕ (Salt × _)) pre.2
      (fun salt => .inl salt) fun pre => .inr ⟨pre.1, undecode dec.2 pre.2⟩) coin

/-- The decoded schedule samples uniform coins. -/
theorem uniformChallenges_decodeSchedule [SampleableType C] :
    {protocol : Protocol.{0}} → (coin : PublicCoin protocol) → (dec : Decoder C coin) →
    (ratio : Errors coin) →
    (schedule : RoundExtractor.ChallengeSchedule protocol.tree protocol.roles) →
    UniformChallenges (decoded C coin dec) (decodeSchedule coin dec ratio schedule)
  | _, .done, _, _, _ => trivial
  | _, @PublicCoin.sender _ _ _ next, dec, _, schedule => fun move =>
      uniformChallenges_decodeSchedule (next move) (dec move) _ (schedule.2 move)
  | _, @PublicCoin.oracle _ _ _ _ next, dec, _, schedule => fun message =>
      uniformChallenges_decodeSchedule next dec _ (schedule message)
  | _, @PublicCoin.challenge _ _ _ next, dec, _, schedule => fun _ => ⟨rfl, fun c =>
      uniformChallenges_decodeSchedule next dec.2 _ (schedule.2 (dec.1.decode c))⟩

/-- A node error of the decoded schedule is at most the ratio times the protocol's error at the
node it stands for. -/
theorem supErrors_decodeSchedule_le [SampleableType C] :
    {protocol : Protocol.{0}} → (coin : PublicCoin protocol) → (dec : Decoder C coin) →
    (ratio : Errors coin) →
    (schedule : RoundExtractor.ChallengeSchedule protocol.tree protocol.roles) →
    (node : Prefix PUnit (decoded C coin dec)) →
    supErrors (decoded C coin dec) (decodeSchedule coin dec ratio schedule) node ≤
      ratio (Prefix.undecode coin dec node) *
        supErrors coin schedule (Prefix.undecode coin dec node)
  | _, .done, _, _, _, node => nomatch node
  | _, @PublicCoin.sender Moves _ _ next, dec, ratio, schedule, node => by
      obtain ⟨move, node⟩ :=
        (node : (move : Moves) × Prefix PUnit (decoded C (next move) (dec move)))
      exact supErrors_decodeSchedule_le (next move) (dec move) _ (schedule.2 move) node
  | _, @PublicCoin.oracle Messages _ _ _ next, dec, ratio, schedule, node => by
      obtain ⟨message, node⟩ := (node : Messages × Prefix PUnit (decoded C next dec))
      exact supErrors_decodeSchedule_le next dec _ (schedule message) node
  | _, @PublicCoin.challenge _ _ _ next, dec, ratio, schedule, node => by
      obtain ⟨_, _ | ⟨_, node⟩⟩ :=
        (node : (_ : dec.1.Witness) × (PUnit ⊕ (PUnit × Prefix PUnit (decoded C next dec.2))))
      · exact le_rfl
      · exact iSup_le fun c => (supErrors_decodeSchedule_le next dec.2 _
          (schedule.2 (dec.1.decode c)) node).trans (by
            gcongr
            exact le_iSup (fun x => supErrors next (schedule.2 x) _) (dec.1.decode c))

/-- The path sum of errors read through `undecode` is at most the protocol's path sum. -/
theorem pathError_undecode_le [SampleableType C] :
    {protocol : Protocol.{0}} → (coin : PublicCoin protocol) → (dec : Decoder C coin) →
    (errors : Errors coin) →
    pathError (decoded C coin dec) (fun node => errors (Prefix.undecode coin dec node)) ≤
      pathError coin errors
  | _, .done, _, _ => le_rfl
  | _, @PublicCoin.sender _ _ _ next, dec, errors =>
      iSup_mono fun move => pathError_undecode_le (next move) (dec move) fun q => errors ⟨move, q⟩
  | _, @PublicCoin.oracle _ _ _ _ next, dec, errors =>
      iSup_mono fun message => pathError_undecode_le next dec fun q => errors ⟨message, q⟩
  | _, @PublicCoin.challenge _ _ _ next, dec, errors =>
      iSup_le fun _ => add_le_add le_rfl
        (pathError_undecode_le next dec.2 fun q => errors (.inr ⟨PUnit.unit, q⟩))

/-- A terminal knowledge failure of the decoded presentation is one of the protocol on the decoded
path: the verifier accepts every coin, and the decoded path has a valid terminal witness whose
backward extraction fails. -/
theorem badTerminal_decode : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    (dec : Decoder C coin) → {state : KnowledgeState.{w}} →
    (extractor : RoundExtractor protocol.tree state) →
    (path : (decodedProtocol C coin dec).tree.ExecutionPath) → (P : state.Witness → Prop) →
    (∃ w, ((decodeExtractor coin dec extractor).terminalState path).holds w ∧
      P ((decodeExtractor coin dec extractor).extractWitness path w)) ↔
    (∃ p, decodePath coin dec path = some p ∧
      ∃ w, (extractor.terminalState p).holds w ∧ P (extractor.extractWitness p w))
  | _, .done, _, _, _, _, _ =>
      ⟨fun h => ⟨PUnit.unit, rfl, h⟩, fun ⟨_, hp, h⟩ => by cases hp; exact h⟩
  | _, @PublicCoin.sender _ _ _ next, dec, _, extractor, path, P => by
      rw [decodePath]
      refine (badTerminal_decode (next path.1) (dec path.1) (extractor path.1).2.2 path.2
        (P ∘ (extractor path.1).2.1)).trans ⟨?_, ?_⟩
      · rintro ⟨p, hp, w, hw⟩
        exact ⟨⟨path.1, p⟩, by rw [hp]; rfl, w, hw⟩
      · rintro ⟨q, hq, w, hw⟩
        obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hq
        exact ⟨p, hp, w, hw⟩
  | _, @PublicCoin.oracle _ _ _ _ next, dec, _, extractor, path, P => by
      rw [decodePath]
      refine (badTerminal_decode next dec (extractor path.1).2.2 path.2
        (P ∘ (extractor path.1).2.1)).trans ⟨?_, ?_⟩
      · rintro ⟨p, hp, w, hw⟩
        exact ⟨⟨path.1, p⟩, by rw [hp]; rfl, w, hw⟩
      · rintro ⟨q, hq, w, hw⟩
        obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hq
        exact ⟨p, hp, w, hw⟩
  | _, @PublicCoin.challenge _ _ _ next, dec, _, extractor, path, P => by
      refine (exists_terminal_drawChild (dec.1.accept path.2.1) _ path.2.2 P).trans ?_
      rw [decodePath]
      cases hc : dec.1.accept path.2.1
      · simp only [Bool.cond_false, Bool.false_eq_true, false_and, reduceCtorEq, exists_false]
      · simp only [Bool.cond_true, true_and]
        refine (badTerminal_decode next dec.2 (extractor (dec.1.decode path.2.1)).2.2 path.2.2
          (P ∘ (extractor (dec.1.decode path.2.1)).2.1)).trans ⟨?_, ?_⟩
        · rintro ⟨p, hp, w, hw⟩
          exact ⟨⟨dec.1.decode path.2.1, p⟩, by rw [hp]; rfl, w, hw⟩
        · rintro ⟨q, hq, w, hw⟩
          obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hq
          exact ⟨p, hp, w, hw⟩

end Security

end Interaction.Oracle
