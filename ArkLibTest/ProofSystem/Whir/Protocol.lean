/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
import ArkLib.ProofSystem.Whir.Knowledge

/-!
# WHIR transcript execution fixtures

Small rational fixtures exercise the algebra-independent transcript parser and initial
selection. They do not instantiate the binary encoding contract or any security theorem.
The checks execute the definitions without evaluating admitted proof bodies.
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
  ⟨(0 : ℚ), (![1, 0, 0] : Quadratic ℚ), (0 : ℚ), (fun _ => table),
    (fun _ => 0), (0 : ℚ), PUnit.unit⟩

/-- A constant-zero transcript with nonzero initial batching to expose inherited claims. -/
private def zeroPath : (opening ℚ lastSchedule).tree.ExecutionPath :=
  ⟨(1 : ℚ), (![0, 0, 0] : Quadratic ℚ), (0 : ℚ), (fun _ => (0 : ℚ)),
    (fun _ => 0), (0 : ℚ), PUnit.unit⟩

/-- Two encoded levels, including their OOD interface. -/
private def twoSchedule : Schedule ℚ 2 := .more 1 (toyEncoding 1) 1 lastSchedule

/-- A zero transcript with an explicit OOD answer. -/
private def twoPath (answer : ℚ) : (opening ℚ twoSchedule).tree.ExecutionPath :=
  ⟨(0 : ℚ), (![0, 0, 0] : Quadratic ℚ), (0 : ℚ), (fun _ _ => (0 : ℚ)),
    (fun _ => (0 : ℚ)), answer, (fun _ => 0), zeroPath⟩

/-- Fail execution when an expected transcript behavior is absent. -/
private def check (name : String) (ok : Bool) : IO Unit := do
  if !ok then throw (IO.userError name)
  IO.println name

/-- Execute accepted and rejected transcripts and both total list-selection outcomes. -/
private def smoke : IO Unit := do
  check "last level accepts the consistent plaintext table"
    (accepts (RingHom.id ℚ) lastSchedule (fun _ _ => 1) [⟨1, 2⟩] (lastPath 1))
  check "last level rejects a wrong plaintext table"
    (!(accepts (RingHom.id ℚ) lastSchedule (fun _ _ => 1) [⟨1, 2⟩] (lastPath 0)))
  check "two levels accept consistent zero messages"
    (accepts (RingHom.id ℚ) twoSchedule (fun _ _ => 0) [⟨0, 0⟩] (twoPath 0))
  check "two levels route the OOD claim into the next sumcheck"
    (!(accepts (RingHom.id ℚ) twoSchedule (fun _ _ => 0) [⟨0, 0⟩] (twoPath 1)))
  let decoder : ListDecoder (E := ℚ) (toyEncoding 0) 1 := ⟨fun _ => [0, 1]⟩
  check "initial extractor selects the satisfying list member"
    (decide (initialExtractor decoder (RingHom.id ℚ) (fun _ _ => 1) [⟨1, 2⟩] = 1))
  check "initial extractor returns zero when no member satisfies the claim"
    (decide (initialExtractor decoder (RingHom.id ℚ) (fun _ _ => 1) [⟨1, 3⟩] = 0))

/--
info: last level accepts the consistent plaintext table
last level rejects a wrong plaintext table
two levels accept consistent zero messages
two levels route the OOD claim into the next sumcheck
initial extractor selects the satisfying list member
initial extractor returns zero when no member satisfies the claim
-/
#guard_msgs in
#eval smoke
