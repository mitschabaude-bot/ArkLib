/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
import ArkLib.ProofSystem.Whir.WitnessCertificate
import ArkLib.Interaction.Oracle.Security.WitnessAppend
import ArkLib.ProofSystem.Sumcheck.Interaction.CompressedBadEvents

/-!
# WHIR transcript execution fixtures

Small rational fixtures exercise transcript parsing, finite candidate searches, full two-level
backward extraction and constructive Sumcheck prefix inverses. Noncomputable analytical data
occurs only in erased predicates. The fixtures do not instantiate the binary encoding contract
or any security theorem.
-/

open Whir Interaction Interaction.Oracle

/-- Monomial column weights on a small rational domain for transcript execution. -/
private def toyEncoding (vars : ℕ) : Encoding ℚ vars where
  rate := 1
  domain := ⟨fun x => (x.val : ℚ), fun x y h =>
    Fin.ext (Nat.cast_injective (show (x.val : ℚ) = (y.val : ℚ) from h))⟩
  weight x u := ∏ i, if u i then (x.val : ℚ) ^ (2 ^ i.val) else 1

/-- One encoded level with a constant plaintext tail. -/
private def lastSchedule : Schedule ℚ 1 := .last 1 0 (toyEncoding 0) 1

/-- A constant-one fold followed by the supplied plaintext value. -/
private def lastPath (table : ℚ) : (opening ℚ lastSchedule).tree.ExecutionPath :=
  ⟨(0 : ℚ), ((1, fun _ => 0) : Quadratic ℚ), (0 : ℚ), (fun _ => table),
    (fun _ => 0), (0 : ℚ), PUnit.unit⟩

/-- A zero pair with nonzero batching and fold challenges to expose inherited claims. -/
private def zeroPath : (opening ℚ lastSchedule).tree.ExecutionPath :=
  ⟨(1 : ℚ), ((0, fun _ => 0) : Quadratic ℚ), (1 : ℚ), (fun _ => (0 : ℚ)),
    (fun _ => 0), (0 : ℚ), PUnit.unit⟩

/-- Two encoded levels, including their OOD interface. -/
private def twoSchedule : Schedule ℚ 2 := .more 1 (toyEncoding 1) 1 lastSchedule

/-- A zero transcript with an explicit OOD answer. -/
private def twoPath (answer : ℚ) : (opening ℚ twoSchedule).tree.ExecutionPath :=
  ⟨(0 : ℚ), ((0, fun _ => 0) : Quadratic ℚ), (0 : ℚ), (fullWord (fun _ _ => (0 : ℚ))),
    (fun _ => (0 : ℚ)), answer, (fun _ => 0), zeroPath⟩

/-- A constant-one transcript carries a nonzero witness through both levels. -/
private def twoOnePath : (opening ℚ twoSchedule).tree.ExecutionPath :=
  ⟨(0 : ℚ), ((2, fun _ => 0) : Quadratic ℚ), (0 : ℚ), (fullWord (fun _ _ => (1 : ℚ))),
    (fun _ => (0 : ℚ)), (1 : ℚ), (fun _ => 0), lastPath 1⟩

/-- Real-valued security data is confined to the extraction fixture's erased predicates. -/
private noncomputable def toySecurity : SecurityParameters twoSchedule :=
  (⟨1 / 10⟩, ⟨1 / 10⟩)

/-- Two compressed rounds whose second polynomial depends on the first decoded value. -/
private def roundPath : (scalarRounds ℚ 2 .done).tree.ExecutionPath :=
  ⟨((1, fun _ => 2) : Quadratic ℚ), (3 : ℚ),
    ((4, fun _ => 5) : Quadratic ℚ), (2 : ℚ), PUnit.unit⟩

/-- A level with one closing round and no encoded folds or queries. -/
private def closingSchedule : Schedule ℚ 1 := .last 0 1 (toyEncoding 1) 0

/-- A plaintext affine table and a compressed closing polynomial evaluated away from zero. -/
private def closingPath (quadratic : ℚ) : (opening ℚ closingSchedule).tree.ExecutionPath :=
  ⟨(0 : ℚ), (fun u => if u 0 then 2 else 1), Fin.elim0, (0 : ℚ),
    ((1, fun _ => quadratic) : Quadratic ℚ), (2 : ℚ), PUnit.unit⟩

/-- Ordered finite candidates with their materialized reference encodings. -/
private def toyDecoder (vars lanes : ℕ) : ListDecoder (E := ℚ) (toyEncoding vars) lanes :=
  ⟨fun _ => [0, 1], fun f => Vector.ofFn ((toyEncoding vars).interleave (RingHom.id ℚ) f)⟩

/-- Ordered finite candidate lists for both levels and every fold row count. -/
private def toyDecoders : DecoderFamily (E := ℚ) twoSchedule :=
  (toyDecoder 1, toyDecoder 0)

/-- A semantic polynomial model used only to index the retained knowledge predicate. -/
private noncomputable def toySummand (_ : Nat) : Sumcheck.Spec.OracleStatement ℚ 1 2 () := 0

/-- A concrete prefix traverses a Sumcheck message and its continuation or abort. -/
private def sumcheckCarrier (choice : Option ℚ) :=
  Sumcheck.Interaction.Knowledge.prefixWitnessEquiv
    (W := Nat) (n := 1) (Sumcheck.compressedOps 1)
    (Sumcheck.Interaction.Knowledge.claimPredicate
      (⟨Fin.elim0, fun x => Fin.elim0 x⟩ : Fin 0 ↪ ℚ) (fun _ => True) toySummand)
    1 0 rfl ⟨0, Fin.elim0⟩ true
    (TypeTree.ExecutionPrefix.ofExecutionPath
      (tree := (Sumcheck.Interaction.Knowledge.protocol (Sumcheck.compressedOps (R := ℚ) 1) 1).tree)
      (match choice with
      | none => ⟨((0, fun _ => 0) : Quadratic ℚ), none, PUnit.unit⟩
      | some r => ⟨((0, fun _ => 0) : Quadratic ℚ), some r, PUnit.unit⟩))

/-- Fail execution when an expected transcript behavior is absent. -/
private def check (name : String) (ok : Bool) : IO Unit := do
  if !ok then throw (IO.userError name)
  IO.println name

/-- Execute accepted and rejected transcripts and both total list-selection outcomes. -/
private def smoke : IO Unit := do
  check "last level accepts the consistent plaintext table"
    (accepts (RingHom.id ℚ) lastSchedule (fullWord (fun _ _ => 1)) [⟨1, 2⟩] (lastPath 1))
  check "last level rejects a wrong plaintext table"
    (!(accepts (RingHom.id ℚ) lastSchedule (fullWord (fun _ _ => 1)) [⟨1, 2⟩] (lastPath 0)))
  check "closing check includes the residual weight"
    (!(accepts (RingHom.id ℚ) lastSchedule (fullWord (fun _ _ => 1)) [⟨2, 2⟩] (lastPath 1)))
  check "two levels accept consistent zero messages"
    (accepts (RingHom.id ℚ) twoSchedule (fullWord (fun _ _ => 0)) [⟨0, 0⟩] (twoPath 0))
  check "two levels route the OOD claim into the next sumcheck"
    (!(accepts (RingHom.id ℚ) twoSchedule (fullWord (fun _ _ => 0)) [⟨0, 0⟩] (twoPath 1)))
  check "compressed rounds propagate the decoded running claim"
    (decide ((readRounds .done 2 (10 : ℚ) roundPath).1 = 72) &&
      decide ((readRounds .done 2 (10 : ℚ) roundPath).2.1 = ![3, 2]) &&
      (readRounds .done 2 (10 : ℚ) roundPath).2.2.1)
  check "closing accepts the decoded affine polynomial"
    (accepts (RingHom.id ℚ) closingSchedule (fullWord (fun _ _ => 0)) [⟨1, 3⟩] (closingPath 0))
  check "closing rejects a wrong transmitted quadratic coefficient"
    (!(accepts (RingHom.id ℚ) closingSchedule (fullWord (fun _ _ => 0)) [⟨1, 3⟩] (closingPath 1)))
  let decoder := toyDecoder 0 1
  check "initial extractor selects the satisfying list member"
    (decide (initialExtractor decoder (RingHom.id ℚ) (fullWord (fun _ _ => 1)) [⟨1, 2⟩] = 1))
  check "initial extractor returns zero when no member satisfies the claim"
    (decide (initialExtractor decoder (RingHom.id ℚ) (fullWord (fun _ _ => 1)) [⟨1, 3⟩] = 0))
  let candidates : List (Table ℚ 1) := [0, 1]
  check "list lift prefers a valid preimage over an earlier invalid preimage"
    (decide (listLift candidates (fun _ => (0 : Table ℚ 0))
      (fun f => f (fun _ => false) = 1) 0 = 1))
  check "list lift uses the first preimage when validity fails"
    (decide (listLift [1, 0] id (fun _ : Table ℚ 1 => False) 1 = 1))
  check "list lift returns zero when the list has no preimage"
    (decide (listLift candidates id (fun _ => True) 2 = 0))
  check "OOD answer selects the first matching candidate"
    (decide (oodCandidate candidates (fun _ => 0) 1 = 1))
  check "OOD answer without a match returns zero"
    (decide (oodCandidate candidates (fun _ => 0) 2 = 0))
  let affine : Table ℚ 1 := fun u => if u 0 then 1 else 0
  let colliding : List (Table ℚ 1) := [0, affine]
  check "boundary search carries an ordered collision pair"
    (decide (boundaryLift [] id (fun _ => True) colliding (fun _ => 0) 1 =
      .inr (0, affine)))
  check "boundary preimage takes priority over a new-list collision"
    (decide (boundaryLift [1] id (fun _ => True) colliding (fun _ => 0) 1 = .inl 1))
  check "boundary without preimage or collision returns the zero image"
    (decide (boundaryLift [] id (fun _ => True) candidates (fun _ => 0) 2 = .inl 0))
  let level := levelExtractor (RingHom.id ℚ) twoSchedule
    (proximityFamily (RingHom.id ℚ) twoSchedule toySecurity)
    toyDecoders (fullWord (fun _ _ => 1)) [⟨1, 4⟩] true
  check "full two-level backward extraction executes folds and the OOD boundary"
    (decide ((show Table ℚ 2 from level.extractWitness twoOnePath PUnit.unit) = 1))
  let opening := openingExtractor (RingHom.id ℚ) twoSchedule
    (proximityFamily (RingHom.id ℚ) twoSchedule toySecurity)
    (openingState (RingHom.id ℚ) twoSchedule toySecurity (fullWord (fun _ _ => 1)) [⟨1, 4⟩]).holds
    toyDecoders (fullWord (fun _ _ => 1)) [⟨1, 4⟩] (toyDecoder 1 1)
  check "full opening extraction executes the supplied decoder family"
    (decide ((show Table ℚ 2 from opening.extractWitness twoOnePath PUnit.unit) = 1))
  check "Sumcheck prefix equivalence executes its inverse after continuation"
    (decide (sumcheckCarrier (some 0) ((sumcheckCarrier (some 0)).symm 37) = 37))
  check "Sumcheck prefix equivalence executes its inverse after abort"
    (decide (sumcheckCarrier none ((sumcheckCarrier none).symm 19) = 19))

/-- Hidden columns reject queries and are excluded by the executable zero-fill decoder filter. -/
private def maskedSmoke : IO Unit := do
  let hidden : MaskedWord ℚ 1 2 := fun _ => none
  check "hidden columns never agree with zero"
    (decide ((agreement hidden (fun _ _ => 0)).card = 0))
  check "hidden query columns reject the transcript"
    (!(accepts (RingHom.id ℚ) lastSchedule hidden [⟨0, 0⟩] (lastPath 0)))
  let masked : MaskedWord ℚ 1 2 := fun x => if x.val = 0 then some 0 else none
  let decoder := ListDecoder.ofZeroFill (enc := toyEncoding 0) (lanes := 1)
    (RingHom.id ℚ) 1 (fun _ => [0, 1])
  check "zero-fill decoding filters by masked agreement"
    (decide (decoder.decode masked = [0]))
  check "folding preserves hidden columns"
    ((foldMaskedRowsOne masked 7 1).isNone)

/-- Guarded suffix checkers and compressed coefficients execute on fixed plaintext examples. -/
private def witnessSmoke : IO Unit := do
  let pre : PlaintextPrefix ℚ 0 2 1 :=
    ⟨⟨0, [⟨0, 1⟩], (fun _ => 0), (fun _ => 0)⟩, fun _ => some (fun _ => -1)⟩
  check "guarded final batching detects a false-claim cancellation"
    (checkPrefixBadFinalBatch pre 1)
  check "guarded final batching rejects hidden queried columns"
    (!(checkPrefixBadFinalBatch { pre with word := fun _ => none } 1))
  let history : Table ℚ 0 → List (Claim ℚ 0) → Table ℚ 1 × Claim ℚ 1 :=
    fun _ _ => (0, ⟨0, 1⟩)
  check "guarded closing detects a quadratic root"
    (checkPrefixBadClosing history pre (0, fun _ => 0) 0)
  check "guarded closing rejects hidden queried columns"
    (!(checkPrefixBadClosing history { pre with word := fun _ => none } (0, fun _ => 0) 0))
  let q : Quadratic ℚ := (3, fun _ => 5)
  let coeffs := Sumcheck.Interaction.Knowledge.compressedCoefficients 17 q
  check "compressed Sumcheck coefficients reconstruct the omitted linear term"
    (decide (coeffs = ![3, 6, 5]) &&
      decide (Sumcheck.Interaction.Knowledge.evalCoefficients coeffs 2 = evalQuadratic 17 q 2))

/--
info: guarded final batching detects a false-claim cancellation
guarded final batching rejects hidden queried columns
guarded closing detects a quadratic root
guarded closing rejects hidden queried columns
compressed Sumcheck coefficients reconstruct the omitted linear term
-/
#guard_msgs in
#eval witnessSmoke

/--
info: hidden columns never agree with zero
hidden query columns reject the transcript
zero-fill decoding filters by masked agreement
folding preserves hidden columns
-/
#guard_msgs in
#eval maskedSmoke

/--
info: last level accepts the consistent plaintext table
last level rejects a wrong plaintext table
closing check includes the residual weight
two levels accept consistent zero messages
two levels route the OOD claim into the next sumcheck
compressed rounds propagate the decoded running claim
closing accepts the decoded affine polynomial
closing rejects a wrong transmitted quadratic coefficient
initial extractor selects the satisfying list member
initial extractor returns zero when no member satisfies the claim
list lift prefers a valid preimage over an earlier invalid preimage
list lift uses the first preimage when validity fails
list lift returns zero when the list has no preimage
OOD answer selects the first matching candidate
OOD answer without a match returns zero
boundary search carries an ordered collision pair
boundary preimage takes priority over a new-list collision
boundary without preimage or collision returns the zero image
full two-level backward extraction executes folds and the OOD boundary
full opening extraction executes the supplied decoder family
Sumcheck prefix equivalence executes its inverse after continuation
Sumcheck prefix equivalence executes its inverse after abort
-/
#guard_msgs in
#eval smoke

namespace PrefixIndexedAppend
set_option backward.isDefEq.respectTransparency false
open Interaction.Oracle.Security Interaction.Oracle.Security.StandardBcs
open Interaction.Oracle.Security.StateRestoration

/-- A constant true knowledge state for testing causal prefix parsing. -/
private def state : KnowledgeState.{0} := ⟨PUnit, fun _ => True⟩

/-- The first protocol commits one Boolean oracle message. -/
private def first : Protocol := .oracleWith Bool
  ⟨PUnit, ⟨fun _ => Bool, fun _ word => word⟩⟩ .done

/-- Its public-coin presentation hides the oracle message from the key. -/
private def firstCoin : PublicCoin first := .oracle .done

/-- The first extractor retains that message in its execution path. -/
private def firstExtractor : RoundExtractor first.tree state :=
  fun _ => ⟨state, id, PUnit.unit⟩

/-- The suffix has one challenge independent of the oracle's masked value. -/
private def second : Protocol := .public .receiver Bool fun _ => .done

/-- The suffix's single public draw. -/
private def secondCoin : PublicCoin second := .challenge .done

/-- The test event depends on the extracted message and the suffix challenge. -/
private def schema : BadSchema Bool where
  Input := Bool
  equality := inferInstance
  isQuery := false
  MaskLE := Eq
  Bad input challenge := input = true ∧ challenge = true
  check input challenge := input && challenge
  check_iff _ _ := Bool.and_eq_true_iff
  monotone _ _ equal _ bad := equal ▸ bad
  error := Erased.mk ⊤
  bad_bound _ _ := by
    simp only [Erased.out_mk]
    exact le_top

/-- The suffix extractor has no false-knowledge transition. -/
private def secondExtractor (path : first.tree.ExecutionPath) :
    RoundExtractor second.tree (firstExtractor.terminalState path) :=
  fun _ => ⟨state, id, PUnit.unit⟩

/-- The suffix input reads the earlier extracted word rather than fixing it externally. -/
private def annotation : BadAnnotation (firstCoin.append (fun _ => secondCoin))
    (BadSchemas.append secondCoin (schema, PUnit.unit) firstCoin PUnit.unit)
    (firstExtractor.append (fun _ => second.tree) secondExtractor) :=
  BadAnnotation.append secondCoin (schema, PUnit.unit) firstCoin PUnit.unit firstExtractor
    (fun _ => PUnit.unit) secondExtractor (fun path =>
      ⟨path.1, (fun _ _ escape => by
        obtain ⟨w, bad, _⟩ := escape
        exact (bad trivial).elim), fun _ => PUnit.unit⟩)

/-- Parsing the same public key with different extracted prefixes changes the suffix event input. -/
private def parsed (word : Bool) : Bool :=
  annotatedInput (Com := Bool) (firstCoin.append (fun _ => secondCoin))
    (BadSchemas.append secondCoin (schema, PUnit.unit) firstCoin PUnit.unit)
    (firstExtractor.append (fun _ => second.tree) secondExtractor) annotation
    ⟨false, .inl PUnit.unit⟩ ⟨word, PUnit.unit⟩

/-- Prefix indexing executes for both values under the same public key. -/
private def appendSmoke : IO Unit := do
  check "prefix-indexed suffix reads false" (!parsed false)
  check "prefix-indexed suffix reads true" (parsed true)

/--
info: prefix-indexed suffix reads false
prefix-indexed suffix reads true
-/
#guard_msgs in
#eval appendSmoke

end PrefixIndexedAppend
