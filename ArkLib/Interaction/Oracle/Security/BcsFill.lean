/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.Interaction.Oracle.Security.BcsCodec

/-!
# Filling the snapshots of a transcript

The ideal chain absorbs the blocks of `F ⊕ Snap` the snapshot observer reads off a key of the
decoded snapshot protocol (`idealEncode`); the duplex verifier absorbs the same blocks with the
snapshots erased (`realEncode`). A real chain query `(s, x)` stands for the ideal query
`(s, enc T x)`, `T` the snapshot taken at the query.

Given the snapshot `snapAt` and the answer `answerAt` of each real chain query, `idealOf` reads
the ideal inputs a key's real inputs stand for, following the answers from `s₀`. A transcript
whose squeezing keys are read that way has consistent snapshots (`SnapsOK`). Filling a transcript
(`fill`) sets the snapshot move at the start of each block to the snapshot of the block's real
chain query; the filled transcript has consistent snapshots (`snapsOK_fill`) when every first
squeeze absorbs a nonempty real input (`Layout.Fills`), and its completion makes the same chain
queries as the original one, with the snapshot moves of its path set alike
(`squeezeCompletionAfter_setSnaps`).
-/

@[expose] public section

namespace Interaction.Oracle.Security.Bcs

open OracleComp OracleSpec PublicCoin StateRestoration HashChain

variable {F Snap Com C S O : Type}

/-! ### Ideal inputs of real inputs -/

/-- The ideal chain input a real chain input `x` stands for, with the snapshot `T` of its query:
the empty input of an extra squeeze stays empty, any other input is prefixed by `T`. -/
def enc (T : Snap) (x : List F) : List (F ⊕ Snap) :=
  if x = [] then [] else .inr T :: x.map .inl

/-- The real inputs of ideal inputs: their snapshots erased. -/
def eraseInputs (r : List (F ⊕ Snap) × List (List (F ⊕ Snap))) : List F × List (List F) :=
  (erase r.1, r.2.map erase)

/-- The chain state after absorbing `blocks`, oldest first, from `s`, each answered by
`answerAt`. -/
def chainState (answerAt : S × List F → S × O) (s : S) (blocks : List (List F)) : S :=
  blocks.foldl (fun s b => (answerAt (s, b)).1) s

/-- The ideal inputs of real inputs `blocks`, oldest first, absorbed from `s`: each block with
the snapshot `snapAt` of its query. -/
def idealBlocks (snapAt : S × List F → Snap) (answerAt : S × List F → S × O) :
    S → List (List F) → List (List (F ⊕ Snap))
  | _, [] => []
  | s, b :: bs => enc (snapAt (s, b)) b :: idealBlocks snapAt answerAt (answerAt (s, b)).1 bs

/-- The ideal inputs a key's real inputs stand for: its first squeeze's input `r.1` and the inputs
before it `r.2`, latest first, each with the snapshot of its query from `s₀`. -/
def idealOf (snapAt : S × List F → Snap) (answerAt : S × List F → S × O) (s₀ : S)
    (r : List F × List (List F)) : List (F ⊕ Snap) × List (List (F ⊕ Snap)) :=
  (enc (snapAt (chainState answerAt s₀ r.2.reverse, r.1)) r.1,
    (idealBlocks snapAt answerAt s₀ r.2.reverse).reverse)

/-- Ideal inputs are those their real inputs stand for. -/
def SnapConsistent (snapAt : S × List F → Snap) (answerAt : S × List F → S × O) (s₀ : S)
    (r : List (F ⊕ Snap) × List (List (F ⊕ Snap))) : Prop :=
  r = idealOf snapAt answerAt s₀ (eraseInputs r)

variable [DecidableEq Snap] [DecidableEq Com] [SampleableType C]

/-! ### Snapshot moves along a transcript -/

/-- The real input of the next squeeze along the messages, after the real elements `pending`
observed since the last squeeze, `tail` observed at the first squeeze: none if no challenge ahead
squeezes. -/
def blockInput : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    (dec : Decoder C coin) → (lay : Layout F Snap Com coin dec) → (start : Bool) →
    (pending tail : List F) →
    Messages PUnit (decoded C (snapCoin coin dec lay start) (snapDecoder coin dec lay start)) →
    Option (List F)
  | _, .done, _, _, _, _, _, _ => none
  | _, @PublicCoin.sender _ _ _ next, dec, lay, true, pending, tail, msgs =>
      blockInput (next msgs.2.1) (dec msgs.2.1) (lay.2 msgs.2.1) false
        (pending ++ lay.1 msgs.2.1) tail msgs.2.2
  | _, @PublicCoin.sender _ _ _ next, dec, lay, false, pending, tail, msgs =>
      blockInput (next msgs.1) (dec msgs.1) (lay.2 msgs.1) false (pending ++ lay.1 msgs.1) tail
        msgs.2
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay, true, pending, tail, msgs =>
      blockInput next dec lay.2.2 false (pending ++ lay.1 msgs.2.1) tail msgs.2.2
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay, false, pending, tail, msgs =>
      blockInput next dec lay.2.2 false (pending ++ lay.1 msgs.1) tail msgs.2
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, true, pending, tail, msgs =>
      if lay.1 = 0 then
        blockInput next dec.2 lay.2.2 (lay.1 != 0) (pending ++ lay.2.1 msgs.2.1) tail msgs.2.2.2
      else some (pending ++ tail ++ lay.2.1 msgs.2.1)
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, false, pending, tail, msgs =>
      if lay.1 = 0 then
        blockInput next dec.2 lay.2.2 (lay.1 != 0) (pending ++ lay.2.1 msgs.1) tail msgs.2.2
      else some (pending ++ tail ++ lay.2.1 msgs.1)

/-- The snapshots of the blocks along the messages, oldest first: each block's the snapshot
`snapAt` of its real chain query, from the state `s` reached by following `answerAt` over the
earlier blocks and their extra squeezes. A block that no challenge squeezes keeps its snapshot. -/
def fillSnaps (snapAt : S × List F → Snap) (answerAt : S × List F → S × O) :
    {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    (dec : Decoder C coin) → (lay : Layout F Snap Com coin dec) → (start : Bool) → (s : S) →
    (pending tail : List F) →
    Messages PUnit (decoded C (snapCoin coin dec lay start) (snapDecoder coin dec lay start)) →
    List Snap
  | _, .done, _, _, _, _, _, _, _ => []
  | _, @PublicCoin.sender _ _ _ next, dec, lay, true, s, pending, tail, msgs =>
      (blockInput (next msgs.2.1) (dec msgs.2.1) (lay.2 msgs.2.1) false
          (pending ++ lay.1 msgs.2.1) tail msgs.2.2).elim msgs.1 (fun b => snapAt (s, b)) ::
        fillSnaps snapAt answerAt (next msgs.2.1) (dec msgs.2.1) (lay.2 msgs.2.1) false s
          (pending ++ lay.1 msgs.2.1) tail msgs.2.2
  | _, @PublicCoin.sender _ _ _ next, dec, lay, false, s, pending, tail, msgs =>
      fillSnaps snapAt answerAt (next msgs.1) (dec msgs.1) (lay.2 msgs.1) false s
        (pending ++ lay.1 msgs.1) tail msgs.2
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay, true, s, pending, tail, msgs =>
      (blockInput next dec lay.2.2 false (pending ++ lay.1 msgs.2.1) tail msgs.2.2).elim msgs.1
          (fun b => snapAt (s, b)) ::
        fillSnaps snapAt answerAt next dec lay.2.2 false s (pending ++ lay.1 msgs.2.1) tail
          msgs.2.2
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay, false, s, pending, tail, msgs =>
      fillSnaps snapAt answerAt next dec lay.2.2 false s (pending ++ lay.1 msgs.1) tail msgs.2
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, true, s, pending, tail, msgs =>
      (if lay.1 = 0 then
          blockInput next dec.2 lay.2.2 (lay.1 != 0) (pending ++ lay.2.1 msgs.2.1) tail
            msgs.2.2.2
        else some (pending ++ tail ++ lay.2.1 msgs.2.1)).elim msgs.1 (fun b => snapAt (s, b)) ::
        if lay.1 = 0 then
          fillSnaps snapAt answerAt next dec.2 lay.2.2 (lay.1 != 0) s
            (pending ++ lay.2.1 msgs.2.1) tail msgs.2.2.2
        else fillSnaps snapAt answerAt next dec.2 lay.2.2 (lay.1 != 0)
          (chainState answerAt s
            ((pending ++ tail ++ lay.2.1 msgs.2.1) :: List.replicate (lay.1 - 1) [])) [] []
          msgs.2.2.2
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, false, s, pending, tail, msgs =>
      if lay.1 = 0 then
        fillSnaps snapAt answerAt next dec.2 lay.2.2 (lay.1 != 0) s (pending ++ lay.2.1 msgs.1)
          tail msgs.2.2
      else fillSnaps snapAt answerAt next dec.2 lay.2.2 (lay.1 != 0)
        (chainState answerAt s
          ((pending ++ tail ++ lay.2.1 msgs.1) :: List.replicate (lay.1 - 1) [])) [] [] msgs.2.2

/-- The messages with their snapshot moves set to `l`, in order; a snapshot move past the end of
`l` is kept. -/
def setSnaps : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    (dec : Decoder C coin) → (lay : Layout F Snap Com coin dec) → (start : Bool) → List Snap →
    Messages PUnit (decoded C (snapCoin coin dec lay start) (snapDecoder coin dec lay start)) →
    Messages PUnit (decoded C (snapCoin coin dec lay start) (snapDecoder coin dec lay start))
  | _, .done, _, _, _, _, msgs => msgs
  | _, @PublicCoin.sender _ _ _ next, dec, lay, true, l, msgs =>
      ⟨l.headD msgs.1, msgs.2.1,
        setSnaps (next msgs.2.1) (dec msgs.2.1) (lay.2 msgs.2.1) false l.tail msgs.2.2⟩
  | _, @PublicCoin.sender _ _ _ next, dec, lay, false, l, msgs =>
      ⟨msgs.1, setSnaps (next msgs.1) (dec msgs.1) (lay.2 msgs.1) false l msgs.2⟩
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay, true, l, msgs =>
      ⟨l.headD msgs.1, msgs.2.1, setSnaps next dec lay.2.2 false l.tail msgs.2.2⟩
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay, false, l, msgs =>
      ⟨msgs.1, setSnaps next dec lay.2.2 false l msgs.2⟩
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, true, l, msgs =>
      ⟨l.headD msgs.1, msgs.2.1, msgs.2.2.1,
        setSnaps next dec.2 lay.2.2 (lay.1 != 0) l.tail msgs.2.2.2⟩
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, false, l, msgs =>
      ⟨msgs.1, msgs.2.1, setSnaps next dec.2 lay.2.2 (lay.1 != 0) l msgs.2.2⟩

/-- A prefix with its snapshot moves set to `l`, in order. -/
def setSnapsPre : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    (dec : Decoder C coin) → (lay : Layout F Snap Com coin dec) → (start : Bool) → List Snap →
    Prefix PUnit (decoded C (snapCoin coin dec lay start) (snapDecoder coin dec lay start)) →
    Prefix PUnit (decoded C (snapCoin coin dec lay start) (snapDecoder coin dec lay start))
  | _, .done, _, _, _, _, pre => pre
  | _, @PublicCoin.sender _ _ _ next, dec, lay, true, l, pre =>
      ⟨l.headD pre.1, pre.2.1,
        setSnapsPre (next pre.2.1) (dec pre.2.1) (lay.2 pre.2.1) false l.tail pre.2.2⟩
  | _, @PublicCoin.sender _ _ _ next, dec, lay, false, l, pre =>
      ⟨pre.1, setSnapsPre (next pre.1) (dec pre.1) (lay.2 pre.1) false l pre.2⟩
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay, true, l, pre =>
      ⟨l.headD pre.1, pre.2.1, setSnapsPre next dec lay.2.2 false l.tail pre.2.2⟩
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay, false, l, pre =>
      ⟨pre.1, setSnapsPre next dec lay.2.2 false l pre.2⟩
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, true, l, pre =>
      ⟨l.headD pre.1, pre.2.1, pre.2.2.map id fun q =>
        (q.1, setSnapsPre next dec.2 lay.2.2 (lay.1 != 0) l.tail q.2)⟩
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, false, l, pre =>
      ⟨pre.1, pre.2.map id fun q => (q.1, setSnapsPre next dec.2 lay.2.2 (lay.1 != 0) l q.2)⟩

/-- A path with its snapshot moves set to `l`, in order. -/
def setSnapsPath : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    (dec : Decoder C coin) → (lay : Layout F Snap Com coin dec) → (start : Bool) → List Snap →
    (decodedProtocol C (snapCoin coin dec lay start)
      (snapDecoder coin dec lay start)).tree.ExecutionPath →
    (decodedProtocol C (snapCoin coin dec lay start)
      (snapDecoder coin dec lay start)).tree.ExecutionPath
  | _, .done, _, _, _, _, path => path
  | _, @PublicCoin.sender _ _ _ next, dec, lay, true, l, path =>
      ⟨l.headD path.1, path.2.1,
        setSnapsPath (next path.2.1) (dec path.2.1) (lay.2 path.2.1) false l.tail path.2.2⟩
  | _, @PublicCoin.sender _ _ _ next, dec, lay, false, l, path =>
      ⟨path.1, setSnapsPath (next path.1) (dec path.1) (lay.2 path.1) false l path.2⟩
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay, true, l, path =>
      ⟨l.headD path.1, path.2.1, setSnapsPath next dec lay.2.2 false l.tail path.2.2⟩
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay, false, l, path =>
      ⟨path.1, setSnapsPath next dec lay.2.2 false l path.2⟩
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, true, l, path =>
      ⟨l.headD path.1, path.2.1, path.2.2.1,
        setSnapsPath next dec.2 lay.2.2 (lay.1 != 0) l.tail path.2.2.2⟩
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, false, l, path =>
      ⟨path.1, path.2.1, setSnapsPath next dec.2 lay.2.2 (lay.1 != 0) l path.2.2⟩

/-! ### Lists of inputs -/

section Lists

omit [DecidableEq Snap] [DecidableEq Com] [SampleableType C]

/-- Erasing nothing leaves nothing. -/
@[simp] theorem erase_nil : erase ([] : List (F ⊕ Snap)) = [] := rfl

/-- Erasing distributes over appending. -/
@[simp] theorem erase_append (x y : List (F ⊕ Snap)) : erase (x ++ y) = erase x ++ erase y :=
  List.filterMap_append

/-- Erasing drops a snapshot. -/
@[simp] theorem erase_cons_inr (T : Snap) (x : List (F ⊕ Snap)) :
    erase (.inr T :: x) = erase x := rfl

/-- Erasing keeps elements of `F`. -/
@[simp] theorem erase_map_inl (x : List F) : erase (x.map (.inl : F → F ⊕ Snap)) = x := by
  induction x with
  | nil => rfl
  | cons a x ih => exact congrArg (a :: ·) ih

/-- A nonempty real input stands for its snapshot followed by its elements. -/
theorem enc_of_ne_nil (T : Snap) {x : List F} (hx : x ≠ []) :
    enc T x = .inr T :: x.map .inl := by
  simp only [enc, hx, ↓reduceIte]

/-- The empty real input stands for the empty ideal input. -/
@[simp] theorem enc_nil (T : Snap) : enc T ([] : List F) = [] := by
  simp only [enc, ↓reduceIte]

/-- Erasing the ideal input of a real input gives the real input. -/
@[simp] theorem erase_enc (T : Snap) (x : List F) : erase (enc T x) = x := by
  by_cases hx : x = []
  · subst hx
    rfl
  · rw [enc_of_ne_nil T hx, erase_cons_inr, erase_map_inl]

/-- Absorbing blocks one list after another. -/
theorem chainState_append (answerAt : S × List F → S × O) (s : S) (xs ys : List (List F)) :
    chainState answerAt s (xs ++ ys) = chainState answerAt (chainState answerAt s xs) ys :=
  List.foldl_append

/-- Erasing ideal inputs of real inputs gives the real inputs. -/
theorem map_erase_idealBlocks (snapAt : S × List F → Snap) (answerAt : S × List F → S × O) :
    (s : S) → (bs : List (List F)) → (idealBlocks snapAt answerAt s bs).map erase = bs
  | _, [] => rfl
  | s, b :: bs => by
      rw [idealBlocks, List.map_cons, erase_enc, map_erase_idealBlocks snapAt answerAt _ bs]

/-- The ideal inputs of blocks one list after another. -/
theorem idealBlocks_append (snapAt : S × List F → Snap) (answerAt : S × List F → S × O) :
    (s : S) → (xs ys : List (List F)) →
    idealBlocks snapAt answerAt s (xs ++ ys) =
      idealBlocks snapAt answerAt s xs ++
        idealBlocks snapAt answerAt (chainState answerAt s xs) ys
  | _, [], _ => rfl
  | s, x :: xs, ys => by
      rw [List.cons_append, idealBlocks, idealBlocks, List.cons_append,
        idealBlocks_append snapAt answerAt _ xs ys]
      rfl

/-- Extra squeezes absorb the empty ideal input. -/
theorem idealBlocks_replicate_nil (snapAt : S × List F → Snap)
    (answerAt : S × List F → S × O) : (s : S) → (n : ℕ) →
    idealBlocks snapAt answerAt s (List.replicate n []) = List.replicate n []
  | _, 0 => rfl
  | s, n + 1 => by
      rw [List.replicate_succ, idealBlocks, enc_nil, idealBlocks_replicate_nil,
        ← List.replicate_succ]

/-- The ideal inputs of a block whose snapshot is that of its real query are consistent. -/
theorem snapConsistent_block (snapAt : S × List F → Snap) (answerAt : S × List F → S × O)
    (s₀ : S) {b : List F} (hb : b ≠ []) (ra : List (List F)) {T : Snap}
    (hT : T = snapAt (chainState answerAt s₀ ra.reverse, b)) :
    SnapConsistent snapAt answerAt s₀
      (.inr T :: b.map .inl, (idealBlocks snapAt answerAt s₀ ra.reverse).reverse) := by
  simp only [SnapConsistent, eraseInputs, idealOf, erase_cons_inr, erase_map_inl,
    List.map_reverse, map_erase_idealBlocks, List.reverse_reverse, enc_of_ne_nil _ hb, hT]

/-- Squeezing a block from `s` and squeezing `k - 1` more times appends its ideal inputs. -/
theorem idealBlocks_squeeze (snapAt : S × List F → Snap) (answerAt : S × List F → S × O)
    (s₀ : S) {b : List F} (hb : b ≠ []) (ra : List (List F)) (k : ℕ) :
    (idealBlocks snapAt answerAt s₀ (List.replicate k [] ++ b :: ra).reverse).reverse =
      List.replicate k [] ++
        (.inr (snapAt (chainState answerAt s₀ ra.reverse, b)) :: b.map .inl) ::
          (idealBlocks snapAt answerAt s₀ ra.reverse).reverse := by
  rw [List.reverse_append, List.reverse_cons, List.reverse_replicate, List.append_assoc,
    List.singleton_append, idealBlocks_append, idealBlocks, idealBlocks_replicate_nil,
    enc_of_ne_nil _ hb, List.reverse_append, List.reverse_cons, List.reverse_replicate,
    List.append_assoc, List.singleton_append]

/-- A squeezed block is nonempty when the layout fills it. -/
theorem ne_nil_of_fills {filled : Prop} {rp t x : List F} (h : filled → rp ++ t ≠ [])
    (hx : filled ∨ x ≠ []) : rp ++ t ++ x ≠ [] := by
  simp only [ne_eq, List.append_eq_nil_iff] at h hx ⊢
  tauto

/-- A block stays nonempty after observing more elements. -/
theorem fills_step {filled : Prop} {rp t x : List F} (h : filled → rp ++ t ≠ [])
    (hx : filled ∨ x ≠ []) : rp ++ x ++ t ≠ [] := by
  simp only [ne_eq, List.append_eq_nil_iff] at h hx ⊢
  tauto

end Lists

/-! ### Filled snapshots are consistent -/

/-- The snapshot observer's inputs past a challenge inside a block. -/
theorem encodeFrom_snap_challenge {Challenge : Type} [SampleableType Challenge]
    {rest : Protocol.{0}} (next : PublicCoin rest)
    (dec : Decoder C (.challenge (Challenge := Challenge) next))
    (lay : Layout F Snap Com (.challenge next) dec) (pending tail : List (F ⊕ Snap))
    (acc : List (List (F ⊕ Snap))) (w : dec.1.Witness) (u : PUnit)
    (q : Prefix PUnit
      (decoded C (snapCoin next dec.2 lay.2.2 (lay.1 != 0)) (snapDecoder next dec.2 lay.2.2 _))) :
    (snapObserver (.challenge next) dec lay false).encodeFrom
        (snapCoin (.challenge next) dec lay false) (snapDecoder (.challenge next) dec lay false)
        pending tail acc ⟨w, .inr ⟨u, q⟩⟩ =
      if lay.1 = 0 then
        (snapObserver next dec.2 lay.2.2 (lay.1 != 0)).encodeFrom _ _
          (pending ++ (lay.2.1 w).map .inl) tail acc q
      else (snapObserver next dec.2 lay.2.2 (lay.1 != 0)).encodeFrom _ _ [] []
        (List.replicate (lay.1 - 1) [] ++ (pending ++ tail ++ (lay.2.1 w).map .inl) :: acc) q :=
  rfl

/-- The ideal inputs of a prefix of filled messages are consistent, after the completed real
inputs `ra` (latest first) reaching the state `s`, inside a block (`start = false`) begun by the
snapshot `T` of the block's real query and observing the real elements `rp` so far, or at the
start of a block (`start = true`). -/
def FillGoal (snapAt : S × List F → Snap) (answerAt : S × List F → S × O) (s₀ : S)
    {protocol : Protocol.{0}} (coin : PublicCoin protocol) (dec : Decoder C coin)
    (lay : Layout F Snap Com coin dec) (start : Bool) : Prop :=
  ∀ (filled : Prop), Layout.Fills coin dec lay filled →
  ∀ (s : S) (pending : List (F ⊕ Snap)) (rp t : List F) (ra : List (List F))
    (msgs : Messages PUnit
      (decoded C (snapCoin coin dec lay start) (snapDecoder coin dec lay start)))
    (pre : Prefix PUnit
      (decoded C (snapCoin coin dec lay start) (snapDecoder coin dec lay start))),
    pre ∈ prefixKeys (decoded C (snapCoin coin dec lay start) (snapDecoder coin dec lay start))
      msgs →
    (snapObserver coin dec lay start).squeezes (snapCoin coin dec lay start)
      (snapDecoder coin dec lay start)
      (Prefix.undecode (snapCoin coin dec lay start) (snapDecoder coin dec lay start) pre) ≠ 0 →
    s = chainState answerAt s₀ ra.reverse → (filled → rp ++ t ≠ []) →
    (start = true ∧ pending = [] ∧ rp = [] ∨
      start = false ∧ ∃ T, pending = .inr T :: rp.map .inl ∧
        ∀ b, blockInput coin dec lay start rp t msgs = some b → T = snapAt (s, b)) →
    SnapConsistent snapAt answerAt s₀
      ((snapObserver coin dec lay start).encodeFrom (snapCoin coin dec lay start)
        (snapDecoder coin dec lay start) pending (t.map .inl)
        (idealBlocks snapAt answerAt s₀ ra.reverse).reverse
        (setSnapsPre coin dec lay start (fillSnaps snapAt answerAt coin dec lay start s rp t msgs)
          pre))

/-- **Filled snapshots are consistent** at every node of the snapshot protocol. -/
theorem fillGoal (snapAt : S × List F → Snap) (answerAt : S × List F → S × O) (s₀ : S) :
    {protocol : Protocol.{0}} → (coin : PublicCoin protocol) → (dec : Decoder C coin) →
    (lay : Layout F Snap Com coin dec) → (start : Bool) →
    FillGoal snapAt answerAt s₀ coin dec lay start
  | _, .done, _, _, _ => by
      intro _ _ _ _ _ _ _ _ pre hpre
      exact absurd hpre List.not_mem_nil
  | _, @PublicCoin.sender _ _ _ next, dec, lay, start => by
      have hf : FillGoal snapAt answerAt s₀ (.sender next) dec lay false := by
        intro filled hfills s pending rp t ra msgs pre hpre hsq hs hfilled hpend
        obtain ⟨move, msgs⟩ := msgs
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hpre
        obtain ⟨-, T, rfl, hT⟩ := hpend.resolve_left (by simp)
        exact fillGoal snapAt answerAt s₀ (next move) (dec move) (lay.2 move) false _
          (hfills move) s _ (rp ++ lay.1 move) t ra msgs q hq hsq hs
          (fun h => fills_step hfilled h)
          (Or.inr ⟨rfl, T, by rw [List.map_append, List.cons_append]; rfl, hT⟩)
      cases start
      · exact hf
      · intro filled hfills s pending rp t ra msgs pre hpre hsq hs hfilled hpend
        obtain ⟨-, rfl, rfl⟩ := hpend.resolve_right (by simp)
        obtain ⟨T₀, msgs⟩ := msgs
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hpre
        refine hf filled hfills s _ [] t ra msgs q hq hsq hs hfilled (Or.inr ⟨rfl, _, rfl, ?_⟩)
        intro b hb
        exact congrArg (fun o => Option.elim o T₀ fun b => snapAt (s, b)) hb
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay, start => by
      have hf : FillGoal snapAt answerAt s₀ (.oracle next) dec lay false := by
        intro filled hfills s pending rp t ra msgs pre hpre hsq hs hfilled hpend
        obtain ⟨c, msgs⟩ := msgs
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hpre
        obtain ⟨-, T, rfl, hT⟩ := hpend.resolve_left (by simp)
        exact fillGoal snapAt answerAt s₀ next dec lay.2.2 false _ (hfills c) s _ (rp ++ lay.1 c)
          t ra msgs q hq hsq hs (fun h => fills_step hfilled h)
          (Or.inr ⟨rfl, T, by rw [List.map_append, List.cons_append]; rfl, hT⟩)
      cases start
      · exact hf
      · intro filled hfills s pending rp t ra msgs pre hpre hsq hs hfilled hpend
        obtain ⟨-, rfl, rfl⟩ := hpend.resolve_right (by simp)
        obtain ⟨T₀, msgs⟩ := msgs
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hpre
        refine hf filled hfills s _ [] t ra msgs q hq hsq hs hfilled (Or.inr ⟨rfl, _, rfl, ?_⟩)
        intro b hb
        exact congrArg (fun o => Option.elim o T₀ fun b => snapAt (s, b)) hb
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, start => by
      have hf : FillGoal snapAt answerAt s₀ (.challenge next) dec lay false := by
        intro filled hfills s pending rp t ra msgs pre hpre hsq hs hfilled hpend
        obtain ⟨-, T, rfl, hT⟩ := hpend.resolve_left (by simp)
        obtain ⟨w, u, msgs⟩ := msgs
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hpre
        rcases List.mem_cons.1 hx with rfl | hx
        · have hk : lay.1 ≠ 0 := hsq
          have hb := ne_nil_of_fills hfilled (hfills.1 hk w)
          have hT' := hT (rp ++ t ++ lay.2.1 w) (by simp only [blockInput, eq_false hk, ↓reduceIte])
          have key := snapConsistent_block snapAt answerAt s₀ hb ra (hs ▸ hT')
          rw [List.map_append, List.map_append, ← List.cons_append, ← List.cons_append] at key
          exact key
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
          simp only [setSnapsPre, fillSnaps, Sum.map_inr]
          refine (congrArg (SnapConsistent snapAt answerAt s₀)
            (encodeFrom_snap_challenge next dec lay _ _ _ w u _)).mpr ?_
          split_ifs with hk
          · refine fillGoal snapAt answerAt s₀ next dec.2 lay.2.2 (lay.1 != 0) _ (hfills.2 w) s _
              (rp ++ lay.2.1 w) t ra msgs q hq hsq hs
              (fun h => fills_step hfilled (by simpa only [eq_true hk, ↓reduceIte] using h))
              (Or.inr ⟨by simp [hk], T, by rw [List.map_append, List.cons_append], fun b hb => ?_⟩)
            exact hT b (by simp only [blockInput, eq_true hk, ↓reduceIte]; exact hb)
          · have hb := ne_nil_of_fills hfilled (hfills.1 hk w)
            have hT' := hT (rp ++ t ++ lay.2.1 w)
              (by simp only [blockInput, eq_false hk, ↓reduceIte])
            have key := fillGoal snapAt answerAt s₀ next dec.2 lay.2.2 (lay.1 != 0) _ (hfills.2 w)
              (chainState answerAt s ((rp ++ t ++ lay.2.1 w) :: List.replicate (lay.1 - 1) []))
              [] [] [] (List.replicate (lay.1 - 1) [] ++ (rp ++ t ++ lay.2.1 w) :: ra) msgs q hq
              hsq (by
                rw [hs, ← chainState_append]
                simp only [List.reverse_append, List.reverse_cons, List.reverse_replicate,
                  List.append_assoc, List.singleton_append])
              (fun h => by simp only [eq_false hk, ↓reduceIte] at h)
              (Or.inl ⟨by simpa using hk, rfl, rfl⟩)
            rw [idealBlocks_squeeze snapAt answerAt s₀ hb ra, ← hs, ← hT', List.map_append,
              List.map_append, ← List.cons_append, ← List.cons_append] at key
            exact key
      cases start
      · exact hf
      · intro filled hfills s pending rp t ra msgs pre hpre hsq hs hfilled hpend
        obtain ⟨-, rfl, rfl⟩ := hpend.resolve_right (by simp)
        obtain ⟨T₀, msgs⟩ := msgs
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hpre
        refine hf filled hfills s _ [] t ra msgs q hq hsq hs hfilled (Or.inr ⟨rfl, _, rfl, ?_⟩)
        intro b hb
        exact congrArg (fun o => Option.elim o T₀ fun b => snapAt (s, b)) hb

/-! ### Setting snapshots changes no real input -/

/-- A key of messages with their snapshots set is a key of the messages with its snapshots set. -/
theorem mem_prefixKeys_setSnaps : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    (dec : Decoder C coin) → (lay : Layout F Snap Com coin dec) → (start : Bool) →
    (l : List Snap) →
    (msgs : Messages PUnit
      (decoded C (snapCoin coin dec lay start) (snapDecoder coin dec lay start))) →
    (pre : Prefix PUnit
      (decoded C (snapCoin coin dec lay start) (snapDecoder coin dec lay start))) →
    pre ∈ prefixKeys _ (setSnaps coin dec lay start l msgs) →
    ∃ q ∈ prefixKeys _ msgs, pre = setSnapsPre coin dec lay start l q
  | _, .done, _, _, _, _, _, _, h => absurd h List.not_mem_nil
  | _, @PublicCoin.sender _ _ _ next, dec, lay, start, l, msgs, pre, h => by
      have hf : ∀ l msgs pre, pre ∈ prefixKeys _ (setSnaps (.sender next) dec lay false l msgs) →
          ∃ q ∈ prefixKeys _ msgs, pre = setSnapsPre (.sender next) dec lay false l q := by
        intro l msgs pre h
        obtain ⟨move, msgs⟩ := msgs
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
        obtain ⟨q, hq, rfl⟩ :=
          mem_prefixKeys_setSnaps (next move) (dec move) (lay.2 move) false l msgs p hp
        exact ⟨Sigma.mk move q, List.mem_map.2 ⟨q, hq, rfl⟩, rfl⟩
      cases start
      · exact hf l msgs pre h
      · obtain ⟨T, msgs⟩ := msgs
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
        obtain ⟨q, hq, rfl⟩ := hf l.tail msgs p hp
        exact ⟨Sigma.mk T q, List.mem_map.2 ⟨q, hq, rfl⟩, rfl⟩
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay, start, l, msgs, pre, h => by
      have hf : ∀ l msgs pre, pre ∈ prefixKeys _ (setSnaps (.oracle next) dec lay false l msgs) →
          ∃ q ∈ prefixKeys _ msgs, pre = setSnapsPre (.oracle next) dec lay false l q := by
        intro l msgs pre h
        obtain ⟨c, msgs⟩ := msgs
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
        obtain ⟨q, hq, rfl⟩ := mem_prefixKeys_setSnaps next dec lay.2.2 false l msgs p hp
        exact ⟨Sigma.mk c q, List.mem_map.2 ⟨q, hq, rfl⟩, rfl⟩
      cases start
      · exact hf l msgs pre h
      · obtain ⟨T, msgs⟩ := msgs
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
        obtain ⟨q, hq, rfl⟩ := hf l.tail msgs p hp
        exact ⟨Sigma.mk T q, List.mem_map.2 ⟨q, hq, rfl⟩, rfl⟩
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, start, l, msgs, pre, h => by
      have hf : ∀ l msgs pre,
          pre ∈ prefixKeys _ (setSnaps (.challenge next) dec lay false l msgs) →
          ∃ q ∈ prefixKeys _ msgs, pre = setSnapsPre (.challenge next) dec lay false l q := by
        intro l msgs pre h
        obtain ⟨w, u, msgs⟩ := msgs
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
        rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨Sigma.mk w (Sum.inl u), List.mem_map.2 ⟨_, List.mem_cons_self .., rfl⟩, rfl⟩
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
          obtain ⟨q, hq, rfl⟩ :=
            mem_prefixKeys_setSnaps next dec.2 lay.2.2 (lay.1 != 0) l msgs p hp
          exact ⟨Sigma.mk w (Sum.inr (u, q)),
            List.mem_map.2 ⟨_, List.mem_cons_of_mem _ (List.mem_map.2 ⟨q, hq, rfl⟩), rfl⟩, rfl⟩
      cases start
      · exact hf l msgs pre h
      · obtain ⟨T, msgs⟩ := msgs
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
        obtain ⟨q, hq, rfl⟩ := hf l.tail msgs p hp
        exact ⟨Sigma.mk T q, List.mem_map.2 ⟨q, hq, rfl⟩, rfl⟩

/-- Setting snapshots changes no node's squeezes. -/
theorem squeezes_setSnapsPre : {protocol : Protocol.{0}} → (coin : PublicCoin protocol) →
    (dec : Decoder C coin) → (lay : Layout F Snap Com coin dec) → (start : Bool) →
    (l : List Snap) →
    (pre : Prefix PUnit
      (decoded C (snapCoin coin dec lay start) (snapDecoder coin dec lay start))) →
    (snapObserver coin dec lay start).squeezes _ _
        (Prefix.undecode _ _ (setSnapsPre coin dec lay start l pre)) =
      (snapObserver coin dec lay start).squeezes _ _ (Prefix.undecode _ _ pre)
  | _, .done, _, _, _, _, pre => nomatch pre
  | _, @PublicCoin.sender _ _ _ next, dec, lay, true, l, pre => by
      obtain ⟨_, move, pre⟩ := pre
      exact squeezes_setSnapsPre (next move) (dec move) (lay.2 move) false l.tail pre
  | _, @PublicCoin.sender _ _ _ next, dec, lay, false, l, pre => by
      obtain ⟨move, pre⟩ := pre
      exact squeezes_setSnapsPre (next move) (dec move) (lay.2 move) false l pre
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay, true, l, pre => by
      obtain ⟨_, _, pre⟩ := pre
      exact squeezes_setSnapsPre next dec lay.2.2 false l.tail pre
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay, false, l, pre => by
      obtain ⟨_, pre⟩ := pre
      exact squeezes_setSnapsPre next dec lay.2.2 false l pre
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, true, l, pre => by
      obtain ⟨_, _, _ | ⟨_, pre⟩⟩ := pre
      · rfl
      · exact squeezes_setSnapsPre next dec.2 lay.2.2 (lay.1 != 0) l.tail pre
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, false, l, pre => by
      obtain ⟨_, _ | ⟨_, pre⟩⟩ := pre
      · rfl
      · exact squeezes_setSnapsPre next dec.2 lay.2.2 (lay.1 != 0) l pre

omit [DecidableEq Snap] in
/-- Inputs with equal erasures have equal real inputs. -/
theorem eraseInputs_congr {x x' : List (F ⊕ Snap)} {acc acc' : List (List (F ⊕ Snap))}
    (hx : erase x = erase x') (hacc : acc.map erase = acc'.map erase) :
    eraseInputs (x, acc) = eraseInputs (x', acc') := by
  simp only [eraseInputs, hx, hacc]

/-- The real inputs of a prefix do not depend on its snapshot moves, nor on the snapshots among
the pending and completed inputs. -/
theorem eraseInputs_encodeFrom_setSnapsPre : {protocol : Protocol.{0}} →
    (coin : PublicCoin protocol) → (dec : Decoder C coin) → (lay : Layout F Snap Com coin dec) →
    (start : Bool) → (l : List Snap) → (pending pending' tail : List (F ⊕ Snap)) →
    (acc acc' : List (List (F ⊕ Snap))) →
    (pre : Prefix PUnit
      (decoded C (snapCoin coin dec lay start) (snapDecoder coin dec lay start))) →
    erase pending = erase pending' → acc.map erase = acc'.map erase →
    eraseInputs ((snapObserver coin dec lay start).encodeFrom _ _ pending tail acc
        (setSnapsPre coin dec lay start l pre)) =
      eraseInputs ((snapObserver coin dec lay start).encodeFrom _ _ pending' tail acc' pre)
  | _, .done, _, _, _, _, _, _, _, _, _, pre, _, _ => nomatch pre
  | _, @PublicCoin.sender _ _ _ next, dec, lay, true, l, pending, pending', tail, acc, acc',
      pre, hp, hacc => by
      obtain ⟨T, move, pre⟩ := pre
      exact eraseInputs_encodeFrom_setSnapsPre (next move) (dec move) (lay.2 move) false l.tail
        (pending ++ [.inr (l.headD T)] ++ (lay.1 move).map .inl)
        (pending' ++ [.inr T] ++ (lay.1 move).map .inl) tail acc acc' pre
        (by simp only [erase_append, hp]; rfl) hacc
  | _, @PublicCoin.sender _ _ _ next, dec, lay, false, l, pending, pending', tail, acc, acc',
      pre, hp, hacc => by
      obtain ⟨move, pre⟩ := pre
      exact eraseInputs_encodeFrom_setSnapsPre (next move) (dec move) (lay.2 move) false l
        (pending ++ (lay.1 move).map .inl) (pending' ++ (lay.1 move).map .inl) tail acc acc' pre
        (by simp only [erase_append, hp]) hacc
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay, true, l, pending, pending', tail, acc, acc',
      pre, hp, hacc => by
      obtain ⟨T, c, pre⟩ := pre
      exact eraseInputs_encodeFrom_setSnapsPre next dec lay.2.2 false l.tail
        (pending ++ [.inr (l.headD T)] ++ (lay.1 c).map .inl)
        (pending' ++ [.inr T] ++ (lay.1 c).map .inl) tail acc acc' pre
        (by simp only [erase_append, hp]; rfl) hacc
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay, false, l, pending, pending', tail, acc, acc',
      pre, hp, hacc => by
      obtain ⟨c, pre⟩ := pre
      exact eraseInputs_encodeFrom_setSnapsPre next dec lay.2.2 false l
        (pending ++ (lay.1 c).map .inl) (pending' ++ (lay.1 c).map .inl) tail acc acc' pre
        (by simp only [erase_append, hp]) hacc
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, start, l, pending, pending', tail, acc, acc',
      pre, hp, hacc => by
      have hf : ∀ (l : List Snap) (pending pending' : List (F ⊕ Snap))
          (acc acc' : List (List (F ⊕ Snap)))
          (pre : Prefix PUnit (decoded C (snapCoin (.challenge next) dec lay false)
            (snapDecoder (.challenge next) dec lay false))),
          erase pending = erase pending' → acc.map erase = acc'.map erase →
          eraseInputs ((snapObserver (.challenge next) dec lay false).encodeFrom _ _ pending tail
              acc (setSnapsPre (.challenge next) dec lay false l pre)) =
            eraseInputs ((snapObserver (.challenge next) dec lay false).encodeFrom _ _ pending'
              tail acc' pre) := by
        intro l pending pending' acc acc' pre hp hacc
        obtain ⟨w, _ | ⟨u, q⟩⟩ := pre
        · exact eraseInputs_congr (by simp only [erase_append, hp]) hacc
        · refine (congrArg eraseInputs (encodeFrom_snap_challenge next dec lay _ _ _ w u _)).trans
            (Eq.trans ?_ (congrArg eraseInputs
              (encodeFrom_snap_challenge next dec lay _ _ _ w u _)).symm)
          split_ifs
          · exact eraseInputs_encodeFrom_setSnapsPre next dec.2 lay.2.2 (lay.1 != 0) l _ _ tail
              acc acc' q (by simp only [erase_append, hp]) hacc
          · exact eraseInputs_encodeFrom_setSnapsPre next dec.2 lay.2.2 (lay.1 != 0) l [] []
              [] _ _ q rfl (by simp only [List.map_append, List.map_cons, erase_append, hp, hacc])
      cases start
      · exact hf l pending pending' acc acc' pre hp hacc
      · obtain ⟨T, pre⟩ := pre
        exact hf l.tail (pending ++ [.inr (l.headD T)]) (pending' ++ [.inr T]) acc acc' pre
          (by simp only [erase_append, hp]; rfl) hacc

/-! ### Completing messages with their snapshots set -/

section Completion

universe v

/-- Answer each prefix of a decoded presentation with coins `Q`. -/
def coinQueries {ι : Type} {spec : OracleSpec ι} {protocol : Protocol.{0}}
    (coin : PublicCoin protocol) (dec : Decoder C coin)
    (Q : Prefix PUnit (decoded C coin dec) → OracleComp spec C) :
    QueryImpl (prefixSpec PUnit (decoded C coin dec)) (OracleComp spec) :=
  fun pre => (Equiv.cast (challenge_decoded coin dec pre)).symm <$> Q pre

omit [DecidableEq Snap] [DecidableEq Com] in
/-- Completing messages at a sender node completes the rest after its move. -/
theorem simulateQ_coinQueries_sender {ι : Type} {spec : OracleSpec ι} {Moves : Type}
    [DecidableEq Moves] {rest : Moves → Protocol.{0}}
    (next : (move : Moves) → PublicCoin (rest move)) (dec : Decoder C (.sender next))
    (Q : Prefix PUnit (decoded C (.sender next) dec) → OracleComp spec C)
    (msgs : Messages PUnit (decoded C (.sender next) dec)) :
    simulateQ (coinQueries (.sender next) dec Q)
        (stoppedCompletePrefix (decoded C (.sender next) dec) (GuardSchedule.pass _) msgs) =
      Option.map (fun path =>
          (⟨msgs.1, path⟩ : (decodedProtocol C (.sender next) dec).tree.ExecutionPath)) <$>
        simulateQ (coinQueries (next msgs.1) (dec msgs.1) fun pre => Q ⟨msgs.1, pre⟩)
          (stoppedCompletePrefix (decoded C (next msgs.1) (dec msgs.1)) (GuardSchedule.pass _)
            msgs.2) := by
  simp only [stoppedCompletePrefix, simulateQ_bind, simulateQ_pure, simulateQ_reindexQuery,
    map_eq_bind_pure_comp]
  rfl

omit [DecidableEq Snap] [DecidableEq Com] in
/-- Completing messages at a challenge node reads the node's coins, then completes the rest. -/
theorem simulateQ_coinQueries_challenge {ι : Type} {spec : OracleSpec ι} {Challenge : Type}
    [SampleableType Challenge] {rest : Protocol.{0}} (next : PublicCoin rest)
    (dec : Decoder C (.challenge (Challenge := Challenge) next))
    (Q : Prefix PUnit (decoded C (.challenge next) dec) → OracleComp spec C)
    (msgs : Messages PUnit (decoded C (.challenge next) dec)) :
    simulateQ (coinQueries (.challenge next) dec Q)
        (stoppedCompletePrefix (decoded C (.challenge next) dec) (GuardSchedule.pass _) msgs) =
      Q ⟨msgs.1, .inl msgs.2.1⟩ >>= fun c => Option.map (fun path =>
          (⟨msgs.1, c, path⟩ : (decodedProtocol C (.challenge next) dec).tree.ExecutionPath)) <$>
        simulateQ (coinQueries next dec.2 fun pre => Q ⟨msgs.1, .inr ⟨msgs.2.1, pre⟩⟩)
          (stoppedCompletePrefix (decoded C next dec.2) (GuardSchedule.pass _) msgs.2.2) := by
  have hpass : GuardSchedule.pass (Salt := PUnit) (decoded C (.challenge next) dec) msgs.1 =
      (fun _ => true, fun _ _ => GuardSchedule.pass (decoded C next dec.2)) := rfl
  unfold coinQueries
  simp only [stoppedCompletePrefix, simulateQ_bind, simulateQ_pure, simulateQ_reindexQuery,
    hpass, Bool.not_true, Bool.false_eq_true, ↓reduceIte, simulateQ_reindexQuery_comp, bind_assoc,
    pure_bind]
  simp only [simulateQ_spec_query, map_eq_bind_pure_comp,
    Function.comp_apply, bind_assoc, pure_bind]
  apply bind_congr
  intro c
  apply bind_congr
  intro x
  cases x <;> rfl

omit [DecidableEq Snap] [DecidableEq Com] [SampleableType C] in
/-- Mapping twice inside `Option` maps by the composite. -/
theorem map_option_map {M : Type → Type v} [Monad M] [LawfulMonad M] {α β γ : Type} (f : β → γ)
    (g : α → β) (x : M (Option α)) :
    Option.map f <$> (Option.map g <$> x) = Option.map (f ∘ g) <$> x := by
  simp only [Functor.map_map, Option.map_map]

omit [DecidableEq Snap] [DecidableEq Com] [SampleableType C] in
/-- A completion step, mapped, matches another completion step, mapped. -/
theorem map_option_step {M : Type → Type v} [Monad M] [LawfulMonad M] {α α' β γ : Type}
    {x : M (Option α')} {y : M (Option α)} {f : α' → γ} {k₀ : α → α'} {k : α → β} {h : β → γ}
    (hx : x = Option.map k₀ <$> y) (hfg : ∀ a, f (k₀ a) = h (k a)) :
    Option.map f <$> x = Option.map h <$> (Option.map k <$> y) := by
  subst hx
  rw [map_option_map, map_option_map, show f ∘ k₀ = h ∘ k from funext hfg]

omit [DecidableEq Snap] [DecidableEq Com] [SampleableType C] in
/-- Equal first steps and mapped continuations give a mapped bind. -/
theorem bind_map_step {M : Type → Type v} [Monad M] [LawfulMonad M] {α β γ : Type} {x y : M α}
    {f : α → M γ} {g : α → M β} {h : β → γ} (hxy : x = y) (hfg : ∀ a, f a = h <$> g a) :
    x >>= f = h <$> (y >>= g) := by
  subst hxy
  rw [map_bind]
  exact bind_congr hfg

/-- **Completing messages with their snapshots set.** When the coins `QA` at each prefix with its
snapshots set are the coins `QB` at the prefix, completing the messages with their snapshots set
on `QA` is completing them on `QB`, the path's snapshots set. -/
theorem simulateQ_setSnaps {ι : Type} {spec : OracleSpec ι} : {protocol : Protocol.{0}} →
    (coin : PublicCoin protocol) → (dec : Decoder C coin) → (lay : Layout F Snap Com coin dec) →
    (start : Bool) → (l : List Snap) →
    (QA QB : Prefix PUnit
      (decoded C (snapCoin coin dec lay start) (snapDecoder coin dec lay start)) →
      OracleComp spec C) →
    (∀ pre, QA (setSnapsPre coin dec lay start l pre) = QB pre) →
    (msgs : Messages PUnit
      (decoded C (snapCoin coin dec lay start) (snapDecoder coin dec lay start))) →
    simulateQ (coinQueries _ _ QA) (stoppedCompletePrefix _ (GuardSchedule.pass _)
        (setSnaps coin dec lay start l msgs)) =
      Option.map (setSnapsPath coin dec lay start l) <$>
        simulateQ (coinQueries _ _ QB) (stoppedCompletePrefix _ (GuardSchedule.pass _) msgs)
  | _, .done, _, _, _, _, _, _, _, _ => by
      change simulateQ _ (pure (some PUnit.unit)) =
        Option.map _ <$> simulateQ _ (pure (some PUnit.unit))
      simp only [simulateQ_pure, map_pure]
      rfl
  | _, @PublicCoin.sender _ _ _ next, dec, lay, start, l, QA, QB, hQ, msgs => by
      have hf : ∀ (l : List Snap) (QA QB : Prefix PUnit (decoded C
            (snapCoin (.sender next) dec lay false) (snapDecoder (.sender next) dec lay false)) →
            OracleComp spec C),
          (∀ pre, QA (setSnapsPre (.sender next) dec lay false l pre) = QB pre) →
          ∀ msgs, simulateQ (coinQueries _ _ QA) (stoppedCompletePrefix _ (GuardSchedule.pass _)
              (setSnaps (.sender next) dec lay false l msgs)) =
            Option.map (setSnapsPath (.sender next) dec lay false l) <$>
              simulateQ (coinQueries _ _ QB)
                (stoppedCompletePrefix _ (GuardSchedule.pass _) msgs) := by
        intro l QA QB hQ msgs
        refine (simulateQ_coinQueries_sender (fun m => snapCoin (next m) (dec m) (lay.2 m) false)
          (snapDecoder (.sender next) dec lay false) QA
          (setSnaps (.sender next) dec lay false l msgs)).trans ?_
        refine Eq.trans ?_ (congrArg
          (fun x => Option.map (setSnapsPath (.sender next) dec lay false l) <$> x)
          (simulateQ_coinQueries_sender (fun m => snapCoin (next m) (dec m) (lay.2 m) false)
            (snapDecoder (.sender next) dec lay false) QB msgs)).symm
        have ih := simulateQ_setSnaps (next msgs.1) (dec msgs.1) (lay.2 msgs.1) false l
          (fun q => QA (Sigma.mk msgs.1 q))
          (fun q => QB (Sigma.mk msgs.1 q)) (fun q => hQ (Sigma.mk msgs.1 q)) msgs.2
        exact map_option_step ih fun _ => rfl
      cases start
      · exact hf l QA QB hQ msgs
      · refine (simulateQ_coinQueries_sender (fun _ : Snap => snapCoin (.sender next) dec lay false)
          (snapDecoder (.sender next) dec lay true) QA
          (setSnaps (.sender next) dec lay true l msgs)).trans ?_
        refine Eq.trans ?_ (congrArg
          (fun x => Option.map (setSnapsPath (.sender next) dec lay true l) <$> x)
          (simulateQ_coinQueries_sender (fun _ : Snap => snapCoin (.sender next) dec lay false)
            (snapDecoder (.sender next) dec lay true) QB msgs)).symm
        have ih := hf l.tail (fun q => QA (Sigma.mk (l.headD msgs.1) q))
          (fun q => QB (Sigma.mk msgs.1 q)) (fun q => hQ (Sigma.mk msgs.1 q)) msgs.2
        exact map_option_step ih fun _ => rfl
  | _, @PublicCoin.oracle _ _ _ _ next, dec, lay, start, l, QA, QB, hQ, msgs => by
      have hf : ∀ (l : List Snap) (QA QB : Prefix PUnit (decoded C
            (snapCoin (.oracle next) dec lay false) (snapDecoder (.oracle next) dec lay false)) →
            OracleComp spec C),
          (∀ pre, QA (setSnapsPre (.oracle next) dec lay false l pre) = QB pre) →
          ∀ msgs, simulateQ (coinQueries _ _ QA) (stoppedCompletePrefix _ (GuardSchedule.pass _)
              (setSnaps (.oracle next) dec lay false l msgs)) =
            Option.map (setSnapsPath (.oracle next) dec lay false l) <$>
              simulateQ (coinQueries _ _ QB)
                (stoppedCompletePrefix _ (GuardSchedule.pass _) msgs) := by
        intro l QA QB hQ msgs
        refine (simulateQ_coinQueries_sender (fun _ : Com => snapCoin next dec lay.2.2 false)
          (snapDecoder (.oracle next) dec lay false) QA
          (setSnaps (.oracle next) dec lay false l msgs)).trans ?_
        refine Eq.trans ?_ (congrArg
          (fun x => Option.map (setSnapsPath (.oracle next) dec lay false l) <$> x)
          (simulateQ_coinQueries_sender (fun _ : Com => snapCoin next dec lay.2.2 false)
            (snapDecoder (.oracle next) dec lay false) QB msgs)).symm
        have ih := simulateQ_setSnaps next dec lay.2.2 false l (fun q => QA (Sigma.mk msgs.1 q))
          (fun q => QB (Sigma.mk msgs.1 q)) (fun q => hQ (Sigma.mk msgs.1 q)) msgs.2
        exact map_option_step ih fun _ => rfl
      cases start
      · exact hf l QA QB hQ msgs
      · refine (simulateQ_coinQueries_sender (fun _ : Snap => snapCoin (.oracle next) dec lay false)
          (snapDecoder (.oracle next) dec lay true) QA
          (setSnaps (.oracle next) dec lay true l msgs)).trans ?_
        refine Eq.trans ?_ (congrArg
          (fun x => Option.map (setSnapsPath (.oracle next) dec lay true l) <$> x)
          (simulateQ_coinQueries_sender (fun _ : Snap => snapCoin (.oracle next) dec lay false)
            (snapDecoder (.oracle next) dec lay true) QB msgs)).symm
        have ih := hf l.tail (fun q => QA (Sigma.mk (l.headD msgs.1) q))
          (fun q => QB (Sigma.mk msgs.1 q)) (fun q => hQ (Sigma.mk msgs.1 q)) msgs.2
        exact map_option_step ih fun _ => rfl
  | _, @PublicCoin.challenge _ _ _ next, dec, lay, start, l, QA, QB, hQ, msgs => by
      have hf : ∀ (l : List Snap) (QA QB : Prefix PUnit (decoded C
            (snapCoin (.challenge next) dec lay false) (snapDecoder (.challenge next) dec lay
                false)) →
            OracleComp spec C),
          (∀ pre, QA (setSnapsPre (.challenge next) dec lay false l pre) = QB pre) →
          ∀ msgs, simulateQ (coinQueries _ _ QA) (stoppedCompletePrefix _ (GuardSchedule.pass _)
              (setSnaps (.challenge next) dec lay false l msgs)) =
            Option.map (setSnapsPath (.challenge next) dec lay false l) <$>
              simulateQ (coinQueries _ _ QB)
                (stoppedCompletePrefix _ (GuardSchedule.pass _) msgs) := by
        intro l QA QB hQ msgs
        refine (simulateQ_coinQueries_challenge (snapCoin next dec.2 lay.2.2 (lay.1 != 0))
          (snapDecoder (.challenge next) dec lay false) QA
          (setSnaps (.challenge next) dec lay false l msgs)).trans ?_
        refine Eq.trans ?_ (congrArg
          (fun x => Option.map (setSnapsPath (.challenge next) dec lay false l) <$> x)
          (simulateQ_coinQueries_challenge (snapCoin next dec.2 lay.2.2 (lay.1 != 0))
            (snapDecoder (.challenge next) dec lay false) QB msgs)).symm
        refine bind_map_step (hQ (Sigma.mk msgs.1 (Sum.inl msgs.2.1))) fun c => ?_
        have ih := simulateQ_setSnaps next dec.2 lay.2.2 (lay.1 != 0) l
          (fun q => QA (Sigma.mk msgs.1 (Sum.inr (msgs.2.1, q))))
          (fun q => QB (Sigma.mk msgs.1 (Sum.inr (msgs.2.1, q))))
          (fun q => hQ (Sigma.mk msgs.1 (Sum.inr (msgs.2.1, q)))) msgs.2.2
        exact map_option_step ih fun _ => rfl
      cases start
      · exact hf l QA QB hQ msgs
      · refine (simulateQ_coinQueries_sender
          (fun _ : Snap => snapCoin (.challenge next) dec lay false)
          (snapDecoder (.challenge next) dec lay true) QA (setSnaps (.challenge next) dec lay true
              l msgs)).trans ?_
        refine Eq.trans ?_ (congrArg
          (fun x => Option.map (setSnapsPath (.challenge next) dec lay true l) <$> x)
          (simulateQ_coinQueries_sender (fun _ : Snap => snapCoin (.challenge next) dec lay false)
            (snapDecoder (.challenge next) dec lay true) QB msgs)).symm
        have ih := hf l.tail (fun q => QA (Sigma.mk (l.headD msgs.1) q))
          (fun q => QB (Sigma.mk msgs.1 q)) (fun q => hQ (Sigma.mk msgs.1 q)) msgs.2
        exact map_option_step ih fun _ => rfl

end Completion

/-! ### Keys of the snapshot protocols -/

section Keys

variable {Input : Type} {protocol : Input → Protocol.{0}}

/-- The ideal chain inputs of a key of the decoded snapshot protocols: the snapshot observer's
inputs, the statement's elements `tail` observed at the first squeeze. -/
def idealEncode (coin : (z : Input) → PublicCoin (protocol z))
    (dec : (z : Input) → Decoder C (coin z))
    (lay : (z : Input) → Layout F Snap Com (coin z) (dec z))
    (tail : Input → List F)
    (key : Key Input PUnit fun z =>
      decoded C (snapCoin (coin z) (dec z) (lay z) true)
        (snapDecoder (coin z) (dec z) (lay z) true)) :
    List (F ⊕ Snap) × List (List (F ⊕ Snap)) :=
  (snapObserver (coin key.1) (dec key.1) (lay key.1) true).encodeFrom _ _ []
    ((tail key.1).map .inl) [] key.2

/-- The duplex verifier's chain inputs of a key: its ideal inputs with the snapshots erased. -/
def realEncode (coin : (z : Input) → PublicCoin (protocol z))
    (dec : (z : Input) → Decoder C (coin z))
    (lay : (z : Input) → Layout F Snap Com (coin z) (dec z))
    (tail : Input → List F)
    (key : Key Input PUnit fun z =>
      decoded C (snapCoin (coin z) (dec z) (lay z) true)
        (snapDecoder (coin z) (dec z) (lay z) true)) :
    List F × List (List F) :=
  eraseInputs (idealEncode coin dec lay tail key)

/-- The messages have consistent snapshots: every key of their completion that squeezes has the
ideal inputs its real inputs stand for. -/
def SnapsOK (coin : (z : Input) → PublicCoin (protocol z))
    (dec : (z : Input) → Decoder C (coin z))
    (lay : (z : Input) → Layout F Snap Com (coin z) (dec z))
    (tail : Input → List F) (snapAt : S × List F → Snap) (answerAt : S × List F → S × O) (s₀ : S)
    (z : Input)
    (messages : Messages PUnit
      (decoded C (snapCoin (coin z) (dec z) (lay z) true)
        (snapDecoder (coin z) (dec z) (lay z) true))) :
    Prop :=
  ∀ key ∈ completionKeys (fun z => decoded C (snapCoin (coin z) (dec z) (lay z) true)
      (snapDecoder (coin z) (dec z) (lay z) true)) z messages,
    (snapObserver (coin key.1) (dec key.1) (lay key.1) true).squeezes _ _
        (Prefix.undecode _ _ key.2) ≠ 0 →
      idealEncode coin dec lay tail key =
        idealOf snapAt answerAt s₀ (realEncode coin dec lay tail key)

/-- The messages with the snapshot move of each block set to the snapshot `snapAt` of the block's
real chain query, following the answers `answerAt` from `s₀`. -/
def fill (coin : (z : Input) → PublicCoin (protocol z))
    (dec : (z : Input) → Decoder C (coin z))
    (lay : (z : Input) → Layout F Snap Com (coin z) (dec z))
    (tail : Input → List F) (snapAt : S × List F → Snap) (answerAt : S × List F → S × O) (s₀ : S)
    (z : Input)
    (messages : Messages PUnit
      (decoded C (snapCoin (coin z) (dec z) (lay z) true)
        (snapDecoder (coin z) (dec z) (lay z) true))) :
    Messages PUnit
      (decoded C (snapCoin (coin z) (dec z) (lay z) true)
        (snapDecoder (coin z) (dec z) (lay z) true)) :=
  setSnaps (coin z) (dec z) (lay z) true
    (fillSnaps snapAt answerAt (coin z) (dec z) (lay z) true s₀ [] (tail z) messages) messages

/-- The real inputs of a key do not depend on its snapshot moves. -/
theorem realEncode_setSnapsPre (coin : (z : Input) → PublicCoin (protocol z))
    (dec : (z : Input) → Decoder C (coin z))
    (lay : (z : Input) → Layout F Snap Com (coin z) (dec z))
    (tail : Input → List F) (l : List Snap) (z : Input)
    (pre : Prefix PUnit
      (decoded C (snapCoin (coin z) (dec z) (lay z) true)
        (snapDecoder (coin z) (dec z) (lay z) true))) :
    realEncode coin dec lay tail ⟨z, setSnapsPre (coin z) (dec z) (lay z) true l pre⟩ =
      realEncode coin dec lay tail ⟨z, pre⟩ :=
  eraseInputs_encodeFrom_setSnapsPre (coin z) (dec z) (lay z) true l [] [] _ [] [] pre rfl rfl

/-- **Filled messages have consistent snapshots**, when every first squeeze absorbs a nonempty
real input. -/
theorem snapsOK_fill (coin : (z : Input) → PublicCoin (protocol z))
    (dec : (z : Input) → Decoder C (coin z))
    (lay : (z : Input) → Layout F Snap Com (coin z) (dec z))
    (tail : Input → List F) (snapAt : S × List F → Snap) (answerAt : S × List F → S × O) (s₀ : S)
    (z : Input) (hfills : Layout.Fills (coin z) (dec z) (lay z) False)
    (messages : Messages PUnit
      (decoded C (snapCoin (coin z) (dec z) (lay z) true)
        (snapDecoder (coin z) (dec z) (lay z) true))) :
    SnapsOK coin dec lay tail snapAt answerAt s₀ z
      (fill coin dec lay tail snapAt answerAt s₀ z messages) := by
  intro key hkey hsq
  obtain ⟨pre, hpre, rfl⟩ := List.mem_map.1 hkey
  obtain ⟨q, hq, rfl⟩ := mem_prefixKeys_setSnaps _ _ _ true _ messages pre hpre
  have hsq' := (squeezes_setSnapsPre (coin z) (dec z) (lay z) true _ q).symm.trans_ne hsq
  exact fillGoal snapAt answerAt s₀ (coin z) (dec z) (lay z) true False hfills s₀ [] [] (tail z) []
    messages q hq hsq' rfl False.elim (Or.inl ⟨rfl, rfl, rfl⟩)

/-- An outcome of the snapshot protocols with its path's snapshot moves set to `l`. -/
def setSnapsOutcome {W : Type} (coin : (z : Input) → PublicCoin (protocol z))
    (dec : (z : Input) → Decoder C (coin z))
    (lay : (z : Input) → Layout F Snap Com (coin z) (dec z))
    (l : List Snap)
    (o : Outcome Input W fun z => decodedProtocol C (snapCoin (coin z) (dec z) (lay z) true)
      (snapDecoder (coin z) (dec z) (lay z) true)) :
    Outcome Input W fun z => decodedProtocol C (snapCoin (coin z) (dec z) (lay z) true)
      (snapDecoder (coin z) (dec z) (lay z) true) :=
  ⟨o.1, setSnapsPath (coin o.1) (dec o.1) (lay o.1) true l o.2.1, o.2.2⟩

/-- **Completing messages with their snapshots set.** The duplex verifier's completion of a
selection with its snapshots set makes the same chain queries as its completion of the selection,
and its outcome is that outcome with the path's snapshots set. -/
theorem squeezeCompletionAfter_setSnaps [SampleableType S] [SampleableType O] [Inhabited S]
    [Inhabited O] {m : ℕ} {W : Type}
    (coin : (z : Input) → PublicCoin (protocol z))
    (dec : (z : Input) → Decoder (Fin m → S × O) (coin z))
    (lay : (z : Input) → Layout F Snap Com (coin z) (dec z)) (tail : Input → List F) (s₀ : S)
    (l : List Snap) (z : Input)
    (messages : Messages PUnit
      (decoded (Fin m → S × O) (snapCoin (coin z) (dec z) (lay z) true)
        (snapDecoder (coin z) (dec z) (lay z) true))) (w : W) :
    squeezeCompletionAfter s₀ [] (fun z => snapDecoder (coin z) (dec z) (lay z) true)
        (fun z => (snapObserver (coin z) (dec z) (lay z) true).squeezes _ _)
        (realEncode coin dec lay tail)
        (some ⟨z, setSnaps (coin z) (dec z) (lay z) true l messages, w⟩) =
      Option.map (setSnapsOutcome coin dec lay l) <$>
        squeezeCompletionAfter s₀ [] (fun z => snapDecoder (coin z) (dec z) (lay z) true)
          (fun z => (snapObserver (coin z) (dec z) (lay z) true).squeezes _ _)
          (realEncode coin dec lay tail) (some ⟨z, messages, w⟩) := by
  have h := simulateQ_setSnaps (spec := unifSpec + (chainSpec S (List F) O + []ₒ)) (coin z) (dec z)
    (lay z) true l
    (fun pre => coinsOf <$> squeezeAnswers (squeezeAt s₀ []
        (realEncode coin dec lay tail ⟨z, pre⟩).1 (realEncode coin dec lay tail ⟨z, pre⟩).2)
      (keySqueezes (fun z => snapDecoder (coin z) (dec z) (lay z) true)
        (fun z => (snapObserver (coin z) (dec z) (lay z) true).squeezes _ _) ⟨z, pre⟩))
    _ (fun pre => by
      simp only [keySqueezes]
      rw [realEncode_setSnapsPre, squeezes_setSnapsPre]) messages
  simp only [squeezeCompletionAfter, stoppedComplete, simulateQ_reindexQuery]
  exact map_option_step h fun _ => rfl

/-- **Completing filled messages.** The duplex verifier's completion of a selection with filled
snapshots makes the same chain queries as its completion of the selection, and its outcome is
that outcome with the path's snapshots filled alike. -/
theorem squeezeCompletionAfter_fill [SampleableType S] [SampleableType O] [Inhabited S]
    [Inhabited O] {m : ℕ} {W : Type}
    (coin : (z : Input) → PublicCoin (protocol z))
    (dec : (z : Input) → Decoder (Fin m → S × O) (coin z))
    (lay : (z : Input) → Layout F Snap Com (coin z) (dec z)) (tail : Input → List F)
    (snapAt : S × List F → Snap) (answerAt : S × List F → S × O) (s₀ : S) (z : Input)
    (messages : Messages PUnit
      (decoded (Fin m → S × O) (snapCoin (coin z) (dec z) (lay z) true)
        (snapDecoder (coin z) (dec z) (lay z) true))) (w : W) :
    squeezeCompletionAfter s₀ [] (fun z => snapDecoder (coin z) (dec z) (lay z) true)
        (fun z => (snapObserver (coin z) (dec z) (lay z) true).squeezes _ _)
        (realEncode coin dec lay tail)
        (some ⟨z, fill coin dec lay tail snapAt answerAt s₀ z messages, w⟩) =
      Option.map (setSnapsOutcome coin dec lay
          (fillSnaps snapAt answerAt (coin z) (dec z) (lay z) true s₀ [] (tail z) messages)) <$>
        squeezeCompletionAfter s₀ [] (fun z => snapDecoder (coin z) (dec z) (lay z) true)
          (fun z => (snapObserver (coin z) (dec z) (lay z) true).squeezes _ _)
          (realEncode coin dec lay tail) (some ⟨z, messages, w⟩) :=
  squeezeCompletionAfter_setSnaps coin dec lay tail s₀ _ z messages w

end Keys

end Interaction.Oracle.Security.Bcs
