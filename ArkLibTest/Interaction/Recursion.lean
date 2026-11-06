/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
import ArkLib.Interaction.Oracle.Security.Recursion

/-!
# Explicit-coins recursive extraction

A decreasing natural-number relation exercises ordered children, bounded depth and the fixed
fallback. The extractor and its traversal require no sampling or probability record.
-/

open Interaction.Oracle.Security.Recursion

private def argument : RecursiveRelation Nat Nat Nat where
  verify _ proof := proof = 0
  localCheck statement witness := statement = witness
  children witness := if witness = 0 then [] else [(witness - 1, 0)]

private def extract : ExtractorFamily Nat Nat Nat := fun A c => (A c).1

private def threeWitnesses : WitnessTree Nat Nat → List Nat
  | .node first [(_, .node second [(_, .node third [])])] => [first, second, third]
  | _ => []

/-- info: [3, 2, 1] -/
#guard_msgs in
#eval threeWitnesses (treeExtractor argument extract (0, 0) 2 (fun c : Nat => (c, 0)) 3)

/-- info: (0, 0) -/
#guard_msgs in
#eval childAdversary argument extract (0, 0) (fun c : Nat => (c, 0)) 1 3

/-- info: (1, 0) -/
#guard_msgs in
#eval derivedAdversary argument extract (0, 0) (fun c : Nat => (c, 0)) [0, 0] 3
