/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.Interaction.Oracle.Security.BcsProtocol

/-!
# Knowledge certificates of the snapshot protocol

A knowledge certificate of a public-coin protocol pulls back to its snapshot protocol
(`snapCertificate`): a commitment `c` is read as the message `open T c` it opens to on the latest
snapshot `T`, and a snapshot move keeps the knowledge state with the identity map. Every
construction is parametrized by the snapshot in force until the next snapshot move, as `openPath`
is.

A prefix of the snapshot protocol opens to a prefix of the protocol (`openPrefix`). The pulled-back
certificate has, at every node, the protocol's error at the opened node (`supErrors_snapSchedule`),
and its terminal knowledge failures are the protocol's on the opened path
(`badTerminal_snapCertificate`). Draws bounded against the certificate's laws stay bounded
(`bounded_snapDecoder`), and draws reading the layout's squeezes read the snapshot observer's
(`reads_snapObserver`).
-/

@[expose] public section

namespace Interaction.Oracle.Security.Bcs

open PublicCoin StateRestoration HashChain

universe w

variable {F Snap C : Type}

/-! ### Witness maps and challenge schedules -/

/-- Witness maps after a snapshot move: the identity map at the snapshot move, then the maps for
the snapshot it records. Without a snapshot move, the maps for the current snapshot `T`. -/
def snapWrapExtractor {P : Protocol.{0}} {state : KnowledgeState.{w}} :
    (start : Bool) → Snap → (Snap → RoundExtractor P.tree state) →
    RoundExtractor (snapWrap Snap start P).tree state
  | true, _, extractor => fun T => ⟨state, id, extractor T⟩
  | false, T, extractor => extractor T

/-- The witness maps of the snapshot protocol: a commitment `c` is read as the message `open T c`
on the latest snapshot `T`, a snapshot move keeps the state with the identity map. -/
def snapExtractor : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    (dec : Decoder C coin) → (lay : Layout F Snap coin dec) → (start : Bool) → Snap →
    {state : KnowledgeState.{w}} → RoundExtractor protocol.tree state →
    RoundExtractor (snapProtocol Snap coin dec lay start).tree state
  | _, .done, _, _, _, _, _, _ => PUnit.unit
  | _, @PublicCoin.sender _ _ _ next, dec, lay, start, T, _, extractor =>
      snapWrapExtractor start T fun T move =>
        ⟨(extractor move).1, (extractor move).2.1,
          snapExtractor (next move) (dec move) (lay.2 move) false T (extractor move).2.2⟩
  | _, @PublicCoin.oracle _ _ _ _ next, _, lay, start, T, _, extractor =>
      snapWrapExtractor start T fun T c =>
        ⟨(extractor (lay.1.open T c)).1, (extractor (lay.1.open T c)).2.1,
          snapExtractor next _ lay.2 false T (extractor (lay.1.open T c)).2.2⟩
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, start, T, _, extractor =>
      snapWrapExtractor start T fun T challenge =>
        ⟨(extractor challenge).1, (extractor challenge).2.1,
          snapExtractor next dec.2 lay.2.2 (lay.1 != 0) T (extractor challenge).2.2⟩

/-- A challenge schedule after a snapshot move: nothing at the snapshot move, then the schedule
for the snapshot it records. Without a snapshot move, the schedule for the current snapshot. -/
def snapWrapSchedule {P : Protocol.{0}} : (start : Bool) → Snap →
    (Snap → RoundExtractor.ChallengeSchedule P.tree P.roles) →
    RoundExtractor.ChallengeSchedule (snapWrap Snap start P).tree (snapWrap Snap start P).roles
  | true, _, schedule => ⟨PUnit.unit, schedule⟩
  | false, T, schedule => schedule T

/-- The challenge schedule of the snapshot protocol: the protocol's law and error at each
challenge, the schedule after a commitment `c` the protocol's after the message `open T c`. -/
def snapSchedule : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    (dec : Decoder C coin) → (lay : Layout F Snap coin dec) → (start : Bool) → Snap →
    RoundExtractor.ChallengeSchedule protocol.tree protocol.roles →
    RoundExtractor.ChallengeSchedule (snapProtocol Snap coin dec lay start).tree
      (snapProtocol Snap coin dec lay start).roles
  | _, .done, _, _, _, _, _ => PUnit.unit
  | _, @PublicCoin.sender _ _ _ next, dec, lay, start, T, schedule =>
      snapWrapSchedule start T fun T => ⟨PUnit.unit, fun move =>
        snapSchedule (next move) (dec move) (lay.2 move) false T (schedule.2 move)⟩
  | _, @PublicCoin.oracle _ _ _ _ next, _, lay, start, T, schedule =>
      snapWrapSchedule start T fun T => ⟨PUnit.unit, fun c =>
        snapSchedule next _ lay.2 false T (schedule (lay.1.open T c))⟩
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, start, T, schedule =>
      snapWrapSchedule start T fun T => ⟨schedule.1, fun challenge =>
        snapSchedule next dec.2 lay.2.2 (lay.1 != 0) T (schedule.2 challenge)⟩

/-- A snapshot move preserves the state. -/
theorem isProverPreserving_snapWrapExtractor {P : Protocol.{0}} {state : KnowledgeState.{w}} :
    (start : Bool) → (T : Snap) → (extractor : Snap → RoundExtractor P.tree state) →
    (∀ T, (extractor T).IsProverPreserving P.roles) →
    (snapWrapExtractor start T extractor).IsProverPreserving (snapWrap Snap start P).roles
  | true, _, _, h => ⟨fun _ _ _ hw => hw, h⟩
  | false, T, _, h => h T

/-- The snapshot protocol's witness maps are prover-preserving when the protocol's are. -/
theorem isProverPreserving_snapExtractor : {protocol : Protocol.{0}} →
    (coin : PublicCoin protocol) → (dec : Decoder C coin) → (lay : Layout F Snap coin dec) →
    (start : Bool) → (T : Snap) → {state : KnowledgeState.{w}} →
    (extractor : RoundExtractor protocol.tree state) →
    extractor.IsProverPreserving protocol.roles →
    (snapExtractor coin dec lay start T extractor).IsProverPreserving
      (snapProtocol Snap coin dec lay start).roles
  | _, .done, _, _, _, _, _, _, _ => trivial
  | _, @PublicCoin.sender _ _ _ next, dec, lay, start, T, _, _, h =>
      isProverPreserving_snapWrapExtractor start T _ fun T =>
        ⟨fun move hs w hw => h.1 move hs w hw, fun move =>
          isProverPreserving_snapExtractor (next move) (dec move) (lay.2 move) false T _
            (h.2 move)⟩
  | _, @PublicCoin.oracle _ _ _ _ next, _, lay, start, T, _, _, h =>
      isProverPreserving_snapWrapExtractor start T _ fun T =>
        ⟨fun c _ w hw => h.1 (lay.1.open T c) w hw, fun c =>
          isProverPreserving_snapExtractor next _ lay.2 false T _ (h.2 (lay.1.open T c))⟩
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, start, T, _, _, h =>
      isProverPreserving_snapWrapExtractor start T _ fun T =>
        ⟨fun _ hs => (nomatch hs), fun challenge =>
          isProverPreserving_snapExtractor next dec.2 lay.2.2 (lay.1 != 0) T _
            (h.2 challenge)⟩

/-- A snapshot move has no challenge to bound. -/
theorem isLocallyBounded_snapWrapExtractor {P : Protocol.{0}} {state : KnowledgeState.{w}} :
    (start : Bool) → (T : Snap) → (extractor : Snap → RoundExtractor P.tree state) →
    (schedule : Snap → RoundExtractor.ChallengeSchedule P.tree P.roles) →
    (∀ T, (extractor T).IsLocallyBounded P.roles (schedule T)) →
    (snapWrapExtractor start T extractor).IsLocallyBounded (snapWrap Snap start P).roles
      (snapWrapSchedule start T schedule)
  | true, _, _, _, h => h
  | false, T, _, _, h => h T

/-- The snapshot protocol's witness maps are locally bounded by the pulled-back schedule when the
protocol's are by the schedule. -/
theorem isLocallyBounded_snapExtractor : {protocol : Protocol.{0}} →
    (coin : PublicCoin protocol) → (dec : Decoder C coin) → (lay : Layout F Snap coin dec) →
    (start : Bool) → (T : Snap) → {state : KnowledgeState.{w}} →
    (extractor : RoundExtractor protocol.tree state) →
    (schedule : RoundExtractor.ChallengeSchedule protocol.tree protocol.roles) →
    extractor.IsLocallyBounded protocol.roles schedule →
    (snapExtractor coin dec lay start T extractor).IsLocallyBounded
      (snapProtocol Snap coin dec lay start).roles (snapSchedule coin dec lay start T schedule)
  | _, .done, _, _, _, _, _, _, _, _ => trivial
  | _, @PublicCoin.sender _ _ _ next, dec, lay, start, T, _, _, _, h =>
      isLocallyBounded_snapWrapExtractor start T _ _ fun T move =>
        isLocallyBounded_snapExtractor (next move) (dec move) (lay.2 move) false T _ _ (h move)
  | _, @PublicCoin.oracle _ _ _ _ next, _, lay, start, T, _, _, _, h =>
      isLocallyBounded_snapWrapExtractor start T _ _ fun T c =>
        isLocallyBounded_snapExtractor next _ lay.2 false T _ _ (h (lay.1.open T c))
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, start, T, _, _, _, h =>
      isLocallyBounded_snapWrapExtractor start T _ _ fun T =>
        ⟨h.1, fun challenge => isLocallyBounded_snapExtractor next dec.2 lay.2.2 (lay.1 != 0) T
          _ _ (h.2 challenge)⟩

/-- **A certificate pulled back to the snapshot protocol.** Commitments are read as the messages
they open to on the latest snapshot; snapshot moves keep the state. -/
def snapCertificate {protocol : Protocol.{0}} (coin : PublicCoin protocol) (dec : Decoder C coin)
    (lay : Layout F Snap coin dec) (start : Bool) (T : Snap) {state : KnowledgeState.{w}}
    (certificate : KnowledgeCertificate protocol.tree protocol.roles state) :
    KnowledgeCertificate (snapProtocol Snap coin dec lay start).tree
      (snapProtocol Snap coin dec lay start).roles state where
  extractor := snapExtractor coin dec lay start T certificate.extractor
  challenges := snapSchedule coin dec lay start T certificate.challenges
  prover_preserving := isProverPreserving_snapExtractor coin dec lay start T _
    certificate.prover_preserving
  local_bound := isLocallyBounded_snapExtractor coin dec lay start T _ _ certificate.local_bound

/-! ### Terminal states -/

/-- A terminal witness of the snapshot protocol's witness maps is one of the protocol's on the
opened path, with the same extracted witness. -/
theorem exists_terminal_snapExtractor : {protocol : Protocol.{0}} →
    (coin : PublicCoin protocol) → (dec : Decoder C coin) → (lay : Layout F Snap coin dec) →
    (start : Bool) → (T : Snap) → {state : KnowledgeState.{w}} →
    (extractor : RoundExtractor protocol.tree state) →
    (path : (snapProtocol Snap coin dec lay start).tree.ExecutionPath) →
    (P : state.Witness → Prop) →
    ((∃ w, ((snapExtractor coin dec lay start T extractor).terminalState path).holds w ∧
      P ((snapExtractor coin dec lay start T extractor).extractWitness path w)) ↔
    ∃ w, (extractor.terminalState (openPath coin dec lay start T path)).holds w ∧
      P (extractor.extractWitness (openPath coin dec lay start T path) w))
  | _, .done, _, _, _, _, _, _, _, _ => Iff.rfl
  | _, @PublicCoin.sender _ _ _ next, dec, lay, true, _, _, extractor, path, P =>
      exists_terminal_snapExtractor (next path.2.1) (dec path.2.1) (lay.2 path.2.1) false path.1
        (extractor path.2.1).2.2 path.2.2 (P ∘ (extractor path.2.1).2.1)
  | _, @PublicCoin.sender _ _ _ next, dec, lay, false, T, _, extractor, path, P =>
      exists_terminal_snapExtractor (next path.1) (dec path.1) (lay.2 path.1) false T
        (extractor path.1).2.2 path.2 (P ∘ (extractor path.1).2.1)
  | _, @PublicCoin.oracle _ _ _ _ next, _, lay, true, _, _, extractor, path, P =>
      exists_terminal_snapExtractor next _ lay.2 false path.1
        (extractor (lay.1.open path.1 path.2.1)).2.2 path.2.2
        (P ∘ (extractor (lay.1.open path.1 path.2.1)).2.1)
  | _, @PublicCoin.oracle _ _ _ _ next, _, lay, false, T, _, extractor, path, P =>
      exists_terminal_snapExtractor next _ lay.2 false T (extractor (lay.1.open T path.1)).2.2
        path.2 (P ∘ (extractor (lay.1.open T path.1)).2.1)
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, true, _, _, extractor, path, P =>
      exists_terminal_snapExtractor next dec.2 lay.2.2 (lay.1 != 0) path.1
        (extractor path.2.1).2.2 path.2.2 (P ∘ (extractor path.2.1).2.1)
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, false, T, _, extractor, path, P =>
      exists_terminal_snapExtractor next dec.2 lay.2.2 (lay.1 != 0) T
        (extractor path.1).2.2 path.2 (P ∘ (extractor path.1).2.1)

/-- A terminal knowledge failure of the pulled-back certificate is one of the certificate on the
opened path. -/
theorem badTerminal_snapCertificate {protocol : Protocol.{0}} (coin : PublicCoin protocol)
    (dec : Decoder C coin) (lay : Layout F Snap coin dec) (start : Bool) (T : Snap)
    {state : KnowledgeState.{w}}
    (certificate : KnowledgeCertificate protocol.tree protocol.roles state)
    (path : (snapProtocol Snap coin dec lay start).tree.ExecutionPath) :
    (∃ w, ((snapCertificate coin dec lay start T certificate).extractor.terminalState
        path).holds w ∧
      ¬ state.holds ((snapCertificate coin dec lay start T certificate).extractor.extractWitness
        path w)) ↔
    ∃ w, (certificate.extractor.terminalState (openPath coin dec lay start T path)).holds w ∧
      ¬ state.holds (certificate.extractor.extractWitness (openPath coin dec lay start T path) w) :=
  exists_terminal_snapExtractor coin dec lay start T certificate.extractor path
    fun w => ¬ state.holds w

/-! ### Prefixes and errors -/

/-- The number of squeezes the layout gives each challenge node. -/
def Layout.squeezes : {protocol : Protocol.{0}} → {coin : PublicCoin protocol} →
    {dec : Decoder C coin} → Layout F Snap coin dec → Prefix PUnit coin → ℕ
  | _, .done, _, _, node => nomatch node
  | _, @PublicCoin.sender _ _ _ next, dec, lay, ⟨move, node⟩ =>
      Layout.squeezes (coin := next move) (dec := dec move) (lay.2 move) node
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay, ⟨_, node⟩ =>
      Layout.squeezes (coin := next) (dec := dec) lay.2 node
  | _, @PublicCoin.challenge _ _ _ _, _, lay, .inl _ => lay.1
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, .inr ⟨_, node⟩ =>
      Layout.squeezes (coin := next) (dec := dec.2) lay.2.2 node

variable [DecidableEq Snap]

/-- A prefix of the snapshot protocol opened to a prefix of the protocol: each commitment opened
on the latest snapshot `T`, the snapshot moves dropped. -/
def openPrefix {Salt : Type} : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    (dec : Decoder C coin) → (lay : Layout F Snap coin dec) → (start : Bool) → Snap →
    Prefix Salt (snapCoin coin dec lay start) → Prefix Salt coin
  | _, .done, _, _, _, _, pre => by obtain ⟨⟩ := pre
  | _, @PublicCoin.sender _ _ _ next, dec, lay, true, _, pre => by
      obtain ⟨T, move, pre⟩ := pre
      exact ⟨move, openPrefix (next move) (dec move) (lay.2 move) false T pre⟩
  | _, @PublicCoin.sender _ _ _ next, dec, lay, false, T, pre => by
      obtain ⟨move, pre⟩ := pre
      exact ⟨move, openPrefix (next move) (dec move) (lay.2 move) false T pre⟩
  | _, @PublicCoin.oracle _ _ _ _ next, _, lay, true, _, pre => by
      obtain ⟨T, c, pre⟩ := pre
      exact ⟨lay.1.open T c, openPrefix next _ lay.2 false T pre⟩
  | _, @PublicCoin.oracle _ _ _ _ next, _, lay, false, T, pre => by
      obtain ⟨c, pre⟩ := pre
      exact ⟨lay.1.open T c, openPrefix next _ lay.2 false T pre⟩
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, true, _, pre => by
      obtain ⟨T, salt | ⟨salt, pre⟩⟩ := pre
      · exact .inl salt
      · exact .inr ⟨salt, openPrefix next dec.2 lay.2.2 (lay.1 != 0) T pre⟩
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, false, T, pre => by
      obtain salt | ⟨salt, pre⟩ := pre
      · exact .inl salt
      · exact .inr ⟨salt, openPrefix next dec.2 lay.2.2 (lay.1 != 0) T pre⟩

/-- The snapshot observer squeezes at each node as the layout does at the opened node. -/
theorem squeezes_snapObserver : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    (dec : Decoder C coin) → (lay : Layout F Snap coin dec) → (start : Bool) → (T : Snap) →
    (node : Prefix PUnit (snapCoin coin dec lay start)) →
    Observer.squeezes (snapCoin coin dec lay start) (snapDecoder coin dec lay start)
      (snapObserver coin dec lay start) node = lay.squeezes (openPrefix coin dec lay start T node)
  | _, .done, _, _, _, _, node => by obtain ⟨⟩ := node
  | _, @PublicCoin.sender _ _ _ next, dec, lay, true, _, node => by
      obtain ⟨T, move, node⟩ := node
      exact squeezes_snapObserver (next move) (dec move) (lay.2 move) false T node
  | _, @PublicCoin.sender _ _ _ next, dec, lay, false, T, node => by
      obtain ⟨move, node⟩ := node
      exact squeezes_snapObserver (next move) (dec move) (lay.2 move) false T node
  | _, @PublicCoin.oracle _ _ _ _ next, _, lay, true, _, node => by
      obtain ⟨T, _, node⟩ := node
      exact squeezes_snapObserver next _ lay.2 false T node
  | _, @PublicCoin.oracle _ _ _ _ next, _, lay, false, T, node => by
      obtain ⟨_, node⟩ := node
      exact squeezes_snapObserver next _ lay.2 false T node
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, true, _, node => by
      obtain ⟨T, _ | ⟨_, node⟩⟩ := node
      · rfl
      · exact squeezes_snapObserver next dec.2 lay.2.2 (lay.1 != 0) T node
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, false, T, node => by
      obtain _ | ⟨_, node⟩ := node
      · rfl
      · exact squeezes_snapObserver next dec.2 lay.2.2 (lay.1 != 0) T node

/-- Node errors of the snapshot protocol: the protocol's at the opened node. -/
abbrev snapErrors {protocol : Protocol.{0}} (coin : PublicCoin protocol) (dec : Decoder C coin)
    (lay : Layout F Snap coin dec) (start : Bool) (T : Snap) (errors : Errors coin) :
    Errors (snapCoin coin dec lay start) :=
  fun node => errors (openPrefix coin dec lay start T node)

/-- The pulled-back schedule's error at each node is the schedule's at the opened node. -/
theorem supErrors_snapSchedule : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    (dec : Decoder C coin) → (lay : Layout F Snap coin dec) → (start : Bool) → (T : Snap) →
    (schedule : RoundExtractor.ChallengeSchedule protocol.tree protocol.roles) →
    (node : Prefix PUnit (snapCoin coin dec lay start)) →
    supErrors (snapCoin coin dec lay start) (snapSchedule coin dec lay start T schedule) node =
      supErrors coin schedule (openPrefix coin dec lay start T node)
  | _, .done, _, _, _, _, _, node => by obtain ⟨⟩ := node
  | _, @PublicCoin.sender _ _ _ next, dec, lay, true, _, schedule, node => by
      obtain ⟨T, move, node⟩ := node
      exact supErrors_snapSchedule (next move) (dec move) (lay.2 move) false T (schedule.2 move)
        node
  | _, @PublicCoin.sender _ _ _ next, dec, lay, false, T, schedule, node => by
      obtain ⟨move, node⟩ := node
      exact supErrors_snapSchedule (next move) (dec move) (lay.2 move) false T (schedule.2 move)
        node
  | _, @PublicCoin.oracle _ _ _ _ next, _, lay, true, _, schedule, node => by
      obtain ⟨T, c, node⟩ := node
      exact supErrors_snapSchedule next _ lay.2 false T (schedule (lay.1.open T c)) node
  | _, @PublicCoin.oracle _ _ _ _ next, _, lay, false, T, schedule, node => by
      obtain ⟨c, node⟩ := node
      exact supErrors_snapSchedule next _ lay.2 false T (schedule (lay.1.open T c)) node
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, true, _, schedule, node => by
      obtain ⟨T, _ | ⟨_, node⟩⟩ := node
      · rfl
      · exact iSup_congr fun challenge => supErrors_snapSchedule next dec.2 lay.2.2 (lay.1 != 0)
          T (schedule.2 challenge) node
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, false, T, schedule, node => by
      obtain _ | ⟨_, node⟩ := node
      · rfl
      · exact iSup_congr fun challenge => supErrors_snapSchedule next dec.2 lay.2.2 (lay.1 != 0)
          T (schedule.2 challenge) node

/-- The path sum of errors read through `openPrefix` is at most the protocol's path sum. -/
theorem pathError_snapErrors_le : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    (dec : Decoder C coin) → (lay : Layout F Snap coin dec) → (start : Bool) → (T : Snap) →
    (errors : Errors coin) →
    pathError (snapCoin coin dec lay start) (snapErrors coin dec lay start T errors) ≤
      pathError coin errors
  | _, .done, _, _, _, _, _ => le_rfl
  | _, @PublicCoin.sender _ _ _ next, dec, lay, true, _, errors =>
      iSup_le fun T => iSup_le fun move =>
        (pathError_snapErrors_le (next move) (dec move) (lay.2 move) false T
          fun q => errors ⟨move, q⟩).trans
        (le_iSup (fun move => pathError (next move) fun q => errors ⟨move, q⟩) move)
  | _, @PublicCoin.sender _ _ _ next, dec, lay, false, T, errors =>
      iSup_mono fun move => pathError_snapErrors_le (next move) (dec move) (lay.2 move) false T
        fun q => errors ⟨move, q⟩
  | _, @PublicCoin.oracle _ _ _ _ next, _, lay, true, _, errors =>
      iSup_le fun T => iSup_le fun c =>
        (pathError_snapErrors_le next _ lay.2 false T fun q => errors ⟨lay.1.open T c, q⟩).trans
        (le_iSup (fun message => pathError next fun q => errors ⟨message, q⟩) (lay.1.open T c))
  | _, @PublicCoin.oracle _ _ _ _ next, _, lay, false, T, errors =>
      iSup_le fun c =>
        (pathError_snapErrors_le next _ lay.2 false T fun q => errors ⟨lay.1.open T c, q⟩).trans
        (le_iSup (fun message => pathError next fun q => errors ⟨message, q⟩) (lay.1.open T c))
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, true, _, errors =>
      iSup_le fun T => add_le_add le_rfl
        (pathError_snapErrors_le next dec.2 lay.2.2 (lay.1 != 0) T
          fun q => errors (.inr ⟨PUnit.unit, q⟩))
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, false, T, errors =>
      add_le_add le_rfl (pathError_snapErrors_le next dec.2 lay.2.2 (lay.1 != 0) T
        fun q => errors (.inr ⟨PUnit.unit, q⟩))

/-- The pulled-back certificate's node errors, scaled by pulled-back ratios, are the protocol's
scaled node errors at the opened nodes. -/
theorem snapErrors_mul_supErrors {protocol : Protocol.{0}} (coin : PublicCoin protocol)
    (dec : Decoder C coin) (lay : Layout F Snap coin dec) (start : Bool) (T : Snap)
    (ratio : Errors coin)
    (schedule : RoundExtractor.ChallengeSchedule protocol.tree protocol.roles) :
    (fun node => snapErrors coin dec lay start T ratio node *
      supErrors (snapCoin coin dec lay start) (snapSchedule coin dec lay start T schedule) node) =
    snapErrors coin dec lay start T fun node => ratio node * supErrors coin schedule node :=
  funext fun node => by rw [supErrors_snapSchedule]

section Family

variable {Input : Type} {protocol : Input → Protocol.{0}}

/-- The largest scaled node error of the pulled-back certificates is at most the protocol's. -/
theorem maxError_snapCertificate_le (coin : (z : Input) → PublicCoin (protocol z))
    (dec : (z : Input) → Decoder C (coin z))
    (lay : (z : Input) → Layout F Snap (coin z) (dec z))
    (T : Snap) (ratio : (z : Input) → Errors (coin z)) {state : Input → KnowledgeState.{w}}
    (certificate : (z : Input) → KnowledgeCertificate (protocol z).tree (protocol z).roles
      (state z)) :
    maxError (fun z node => snapErrors (coin z) (dec z) (lay z) true T (ratio z) node *
      supErrors (snapCoin (coin z) (dec z) (lay z) true)
        (snapCertificate (coin z) (dec z) (lay z) true T (certificate z)).challenges node) ≤
    maxError (fun z node => ratio z node * supErrors (coin z) (certificate z).challenges node) :=
  iSup_le fun z => iSup_le fun node =>
    (congrFun (snapErrors_mul_supErrors (coin z) (dec z) (lay z) true T (ratio z)
      (certificate z).challenges) node).trans_le
    ((le_iSup (fun node => ratio z node * supErrors (coin z) (certificate z).challenges node)
      (openPrefix (coin z) (dec z) (lay z) true T node)).trans
    (le_iSup (fun z => ⨆ node, ratio z node * supErrors (coin z) (certificate z).challenges node)
      z))

/-- The largest scaled path error of the pulled-back certificates is at most the protocol's. -/
theorem sumError_snapCertificate_le (coin : (z : Input) → PublicCoin (protocol z))
    (dec : (z : Input) → Decoder C (coin z))
    (lay : (z : Input) → Layout F Snap (coin z) (dec z))
    (T : Snap) (ratio : (z : Input) → Errors (coin z)) {state : Input → KnowledgeState.{w}}
    (certificate : (z : Input) → KnowledgeCertificate (protocol z).tree (protocol z).roles
      (state z)) :
    sumError (fun z node => snapErrors (coin z) (dec z) (lay z) true T (ratio z) node *
      supErrors (snapCoin (coin z) (dec z) (lay z) true)
        (snapCertificate (coin z) (dec z) (lay z) true T (certificate z)).challenges node) ≤
    sumError (fun z node => ratio z node * supErrors (coin z) (certificate z).challenges node) :=
  iSup_mono fun z =>
    (congrArg (pathError (snapCoin (coin z) (dec z) (lay z) true))
      (snapErrors_mul_supErrors (coin z) (dec z) (lay z) true T (ratio z)
        (certificate z).challenges)).trans_le
    (pathError_snapErrors_le (coin z) (dec z) (lay z) true T _)

end Family

/-! ### Draws -/

/-- Draws bounded against the schedule's laws are bounded against the pulled-back schedule's, with
the pulled-back ratios. -/
theorem bounded_snapDecoder [SampleableType C] : {protocol : Protocol.{0}} →
    (coin : PublicCoin protocol) → (dec : Decoder C coin) → (lay : Layout F Snap coin dec) →
    (start : Bool) → (T : Snap) → (ratio : Errors coin) →
    (schedule : RoundExtractor.ChallengeSchedule protocol.tree protocol.roles) →
    Decoder.Bounded coin dec ratio schedule →
    Decoder.Bounded (snapCoin coin dec lay start) (snapDecoder coin dec lay start)
      (snapErrors coin dec lay start T ratio) (snapSchedule coin dec lay start T schedule)
  | _, .done, _, _, _, _, _, _, _ => trivial
  | _, @PublicCoin.sender _ _ _ next, dec, lay, true, _, _, schedule, h => fun T move =>
      bounded_snapDecoder (next move) (dec move) (lay.2 move) false T _ (schedule.2 move) (h move)
  | _, @PublicCoin.sender _ _ _ next, dec, lay, false, T, _, schedule, h => fun move =>
      bounded_snapDecoder (next move) (dec move) (lay.2 move) false T _ (schedule.2 move) (h move)
  | _, @PublicCoin.oracle _ _ _ _ next, _, lay, true, _, _, schedule, h => fun T c =>
      bounded_snapDecoder next _ lay.2 false T _ (schedule (lay.1.open T c)) (h (lay.1.open T c))
  | _, @PublicCoin.oracle _ _ _ _ next, _, lay, false, T, _, schedule, h => fun c =>
      bounded_snapDecoder next _ lay.2 false T _ (schedule (lay.1.open T c)) (h (lay.1.open T c))
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, true, _, _, schedule, h => fun T =>
      ⟨h.1, fun challenge => bounded_snapDecoder next dec.2 lay.2.2 (lay.1 != 0) T _
        (schedule.2 challenge) (h.2 challenge)⟩
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, false, T, _, schedule, h =>
      ⟨h.1, fun challenge => bounded_snapDecoder next dec.2 lay.2.2 (lay.1 != 0) T _
        (schedule.2 challenge) (h.2 challenge)⟩

section Reads

variable {C₀ : Type} {m : ℕ}

/-- Draws reading their node's squeezes read the squeezes at the opened node. -/
theorem reads_snapDecoder : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    (dec : Decoder (Fin m → C₀) coin) → (lay : Layout F Snap coin dec) → (start : Bool) →
    (T : Snap) → (squeezes : Prefix PUnit coin → ℕ) → Decoder.Reads coin dec squeezes →
    Decoder.Reads (snapCoin coin dec lay start) (snapDecoder coin dec lay start)
      fun node => squeezes (openPrefix coin dec lay start T node)
  | _, .done, _, _, _, _, _, _ => trivial
  | _, @PublicCoin.sender _ _ _ next, dec, lay, true, _, _, h => fun T move =>
      reads_snapDecoder (next move) (dec move) (lay.2 move) false T _ (h move)
  | _, @PublicCoin.sender _ _ _ next, dec, lay, false, T, _, h => fun move =>
      reads_snapDecoder (next move) (dec move) (lay.2 move) false T _ (h move)
  | _, @PublicCoin.oracle _ _ _ _ next, _, lay, true, _, _, h => fun T c =>
      reads_snapDecoder next _ lay.2 false T _ (h (lay.1.open T c))
  | _, @PublicCoin.oracle _ _ _ _ next, _, lay, false, T, _, h => fun c =>
      reads_snapDecoder next _ lay.2 false T _ (h (lay.1.open T c))
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, true, _, _, h => fun T =>
      ⟨h.1, reads_snapDecoder next dec.2 lay.2.2 (lay.1 != 0) T _ h.2⟩
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, false, T, _, h =>
      ⟨h.1, reads_snapDecoder next dec.2 lay.2.2 (lay.1 != 0) T _ h.2⟩

/-- Draws reading the layout's squeezes read the snapshot observer's. -/
theorem reads_snapObserver {protocol : Protocol.{0}} (coin : PublicCoin protocol)
    (dec : Decoder (Fin m → C₀) coin) (lay : Layout F Snap coin dec) (start : Bool) (T : Snap)
    (h : Decoder.Reads coin dec lay.squeezes) :
    Decoder.Reads (snapCoin coin dec lay start) (snapDecoder coin dec lay start)
      (Observer.squeezes (snapCoin coin dec lay start) (snapDecoder coin dec lay start)
        (snapObserver coin dec lay start)) := by
  rw [funext (squeezes_snapObserver coin dec lay start T)]
  exact reads_snapDecoder coin dec lay start T _ h

end Reads

/-- The snapshot observer squeezes at most as often as the layout does anywhere. -/
theorem squeezes_snapObserver_le {protocol : Protocol.{0}} (coin : PublicCoin protocol)
    (dec : Decoder C coin) (lay : Layout F Snap coin dec) (start : Bool) (T : Snap) {m : ℕ}
    (h : ∀ node, lay.squeezes node ≤ m) (node : Prefix PUnit (snapCoin coin dec lay start)) :
    Observer.squeezes (snapCoin coin dec lay start) (snapDecoder coin dec lay start)
      (snapObserver coin dec lay start) node ≤ m :=
  (squeezes_snapObserver coin dec lay start T node).trans_le (h _)

end Interaction.Oracle.Security.Bcs
