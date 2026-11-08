/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.Interaction.Oracle.Security.WitnessRefinement
public import ArkLib.Interaction.Oracle.Security.KnowledgeComposition

/-! # Prefix-indexed composition of witness refinements -/

@[expose] public section

open Interaction.Oracle Interaction.Oracle.Security
open Interaction.Oracle.Security.StateRestoration

namespace Interaction.Oracle.Security.StandardBcs

/-- Append schemas with suffix inputs supplied by the extracted prefix. -/
def BadSchemas.append {second : Protocol} (secondCoin : PublicCoin second)
    (secondSchemas : BadSchemas secondCoin) :
    {first : Protocol} → (firstCoin : PublicCoin first) → BadSchemas firstCoin →
      BadSchemas (firstCoin.append (fun _ => secondCoin))
  | _, .done, _ => secondSchemas
  | _, @PublicCoin.sender _ _ _ next, schemas =>
      fun move => append secondCoin secondSchemas (next move) (schemas move)
  | _, @PublicCoin.oracle _ _ _ _ next, schemas =>
      append secondCoin secondSchemas next schemas
  | _, @PublicCoin.challenge _ _ _ next, schemas =>
      (schemas.1, append secondCoin secondSchemas next schemas.2)

/-- Choose the suffix refinement from the extracted first path, including its masks. -/
def BadAnnotation.append {second : Protocol} (secondCoin : PublicCoin second)
    (secondSchemas : BadSchemas secondCoin) :
    {first : Protocol} → (firstCoin : PublicCoin first) → (firstSchemas : BadSchemas firstCoin) →
    {state : KnowledgeState} → (firstExtractor : RoundExtractor first.tree state) →
    BadAnnotation firstCoin firstSchemas firstExtractor →
    (secondExtractor : (path : first.tree.ExecutionPath) →
      RoundExtractor second.tree (firstExtractor.terminalState path)) →
    ((path : first.tree.ExecutionPath) →
      BadAnnotation secondCoin secondSchemas (secondExtractor path)) →
    BadAnnotation (firstCoin.append (fun _ => secondCoin))
      (BadSchemas.append secondCoin secondSchemas firstCoin firstSchemas)
      (firstExtractor.append (fun _ => second.tree) secondExtractor)
  | _, .done, _, _, _, _, _, annotation => annotation PUnit.unit
  | _, @PublicCoin.sender _ _ _ next, schemas, _, extractor, annotation, second, suffix =>
      fun move => append secondCoin secondSchemas (next move) (schemas move)
        (extractor move).2.2 (annotation move)
        (fun path => second ⟨move, path⟩) (fun path => suffix ⟨move, path⟩)
  | _, @PublicCoin.oracle _ _ _ _ next, schemas, _, extractor, annotation, second, suffix =>
      fun word => append secondCoin secondSchemas next schemas
        (extractor word).2.2 (annotation word)
        (fun path => second ⟨word, path⟩) (fun path => suffix ⟨word, path⟩)
  | _, @PublicCoin.challenge _ _ _ next, schemas, _, extractor, annotation, second, suffix =>
      ⟨annotation.1, annotation.2.1, fun challenge =>
        append secondCoin secondSchemas next schemas.2 (extractor challenge).2.2
          (annotation.2.2 challenge) (fun path => second ⟨challenge, path⟩)
          (fun path => suffix ⟨challenge, path⟩)⟩

/-- Authenticate an appended refinement indexed by the extracted first path. -/
def BadAnnotation.appendCertificate {Statement Com : Type} [DecidableEq Com]
    {first second : Statement → Protocol}
    (firstCoin : (s : Statement) → PublicCoin (first s))
    (secondCoin : (s : Statement) → PublicCoin (second s))
    (state : Statement → KnowledgeState)
    (certificate : Erased ((s : Statement) → KnowledgeCertificate
      ((firstCoin s).appendProtocol (fun _ => second s)).tree
      ((firstCoin s).appendProtocol (fun _ => second s)).roles (state s)))
    (firstExtractor : (s : Statement) → RoundExtractor (first s).tree (state s))
    (secondExtractor : (s : Statement) → (path : (first s).tree.ExecutionPath) →
      RoundExtractor (second s).tree ((firstExtractor s).terminalState path))
    (extractor_eq : ∀ s, (certificate.out s).extractor =
      (firstExtractor s).append (fun _ => (second s).tree) (secondExtractor s))
    (firstSchemas : (s : Statement) → BadSchemas (firstCoin s))
    (secondSchemas : (s : Statement) → BadSchemas (secondCoin s))
    (firstAnnotation : (s : Statement) →
      BadAnnotation (firstCoin s) (firstSchemas s) (firstExtractor s))
    (secondAnnotation : (s : Statement) → (path : (first s).tree.ExecutionPath) →
      BadAnnotation (secondCoin s) (secondSchemas s) (secondExtractor s path))
    (Authentication : Key Statement PUnit
      (fun s => compiledCoin Com ((firstCoin s).append (fun _ => secondCoin s))) → Type)
    (authenticate : (key : Key Statement PUnit
      (fun s => compiledCoin Com ((firstCoin s).append (fun _ => secondCoin s)))) →
      PrefixMessages ((firstCoin key.1).append (fun _ => secondCoin key.1)) key.2 →
        Authentication key → Bool) :
    WitnessKnowledgeCertificate (Com := Com)
      (fun s => (firstCoin s).append (fun _ => secondCoin s)) state certificate.out :=
  BadAnnotation.certificate _ state certificate
    (fun s => (firstExtractor s).append (fun _ => (second s).tree) (secondExtractor s))
    extractor_eq
    (fun s => BadSchemas.append (secondCoin s) (secondSchemas s) (firstCoin s) (firstSchemas s))
    (fun s => BadAnnotation.append (secondCoin s) (secondSchemas s)
      (firstCoin s) (firstSchemas s) (firstExtractor s) (firstAnnotation s)
      (secondExtractor s) (secondAnnotation s))
    Authentication authenticate

end Interaction.Oracle.Security.StandardBcs
