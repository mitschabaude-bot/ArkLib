/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.Interaction.Oracle.Security.StandardBcs

/-! # Compositional local bad-event refinements of public-coin extractors -/

@[expose] public section

open Interaction.Oracle Interaction.Oracle.Security OracleComp OracleSpec
open Interaction.Oracle.Security.StateRestoration

namespace Interaction.Oracle.Security.StandardBcs

/-- A local round has an executable bad relation on ordered masked inputs and its uniform bound. -/
structure BadSchema (Challenge : Type) [SampleableType Challenge] where
  /-- The masked data preceding this challenge. -/
  Input : Type
  /-- Challenge equality used by prefix consistency. -/
  equality : DecidableEq Challenge
  /-- Query rounds retain their extractor-relative residual. -/
  isQuery : Bool
  /-- Hiding order on this round's masked input. -/
  MaskLE : Input → Input → Prop
  /-- The mathematical bad event. -/
  Bad : Input → Challenge → Prop
  /-- Its executable decision procedure. -/
  check : Input → Challenge → Bool
  /-- The checker is exact. -/
  check_iff : ∀ input α, check input α = true ↔ Bad input α
  /-- Revealing consistent columns preserves badness. -/
  monotone : ∀ small large, MaskLE small large → ∀ α, Bad small α → Bad large α
  /-- The local algebraic error. -/
  error : Erased ENNReal
  /-- Each fixed masked input has the stated uniform bound. -/
  bad_bound : ∀ input, isQuery = false → Pr{let α ←$ᵗ Challenge}[Bad input α] ≤ error.out

/-- Round schemas follow public syntax and are independent of extracted oracle messages. -/
def BadSchemas {protocol : Protocol} (coin : PublicCoin protocol) : Type 1 :=
  PublicCoin.rec (motive := fun _ _ => Type 1) PUnit
    (fun {Moves} {_} {_} _ next => (move : Moves) → next move)
    (fun _ next => next)
    (fun {Challenge} {_} {_} _ next => BadSchema Challenge × next) coin

/-- Annotating an extractor supplies its current masked input and every local escape containment. -/
def BadAnnotation : {protocol : Protocol} → (coin : PublicCoin protocol) → BadSchemas coin →
    {state : KnowledgeState} → RoundExtractor protocol.tree state → Type
  | _, .done, _, _, _ => PUnit
  | _, @PublicCoin.sender _ _ _ next, schemas, _, extractor =>
      (move : _) → BadAnnotation (next move) (schemas move) (extractor move).2.2
  | _, @PublicCoin.oracle Messages _ _ _ next, schemas, _, extractor =>
      (word : Messages) → BadAnnotation next schemas (extractor word).2.2
  | _, @PublicCoin.challenge _ _ _ next, schemas, _, extractor =>
      (input : schemas.1.Input) ×
        PProd (∀ α, schemas.1.isQuery = false → extractor.badChallenge α → schemas.1.Bad input α)
          ((α : _) → BadAnnotation next schemas.2 (extractor α).2.2)

/-- The schema at a compiled key reads public syntax but no extracted words. -/
def schemaAt {Com : Type} [DecidableEq Com] :
    {protocol : Protocol} → (coin : PublicCoin protocol) → BadSchemas coin →
    (pre : Prefix PUnit (compiledCoin Com coin)) → BadSchema pre.Challenge
  | _, .done, _, pre => nomatch pre
  | _, @PublicCoin.sender _ _ _ next, schemas, pre => schemaAt (next pre.1) (schemas pre.1) pre.2
  | _, @PublicCoin.oracle _ _ _ _ next, schemas, pre => schemaAt next schemas pre.2
  | _, @PublicCoin.challenge _ _ _ next, schemas, pre => match pre with
      | .inl _ => schemas.1
      | .inr ⟨_, pre⟩ => schemaAt next schemas.2 pre

/-- Parse the local input using only earlier oracle messages and actual earlier challenges. -/
def annotatedInput {Com : Type} [DecidableEq Com] :
    {protocol : Protocol} → (coin : PublicCoin protocol) → (schemas : BadSchemas coin) →
    {state : KnowledgeState} → (extractor : RoundExtractor protocol.tree state) →
    BadAnnotation coin schemas extractor → (pre : Prefix PUnit (compiledCoin Com coin)) →
    PrefixMessages coin pre → (schemaAt coin schemas pre).Input
  | _, .done, _, _, _, _, pre, _ => nomatch pre
  | _, @PublicCoin.sender _ _ _ next, schemas, _, extractor, annotation, pre, words =>
      annotatedInput (next pre.1) (schemas pre.1) (extractor pre.1).2.2
        (annotation pre.1) pre.2 words
  | _, @PublicCoin.oracle _ _ _ _ next, schemas, _, extractor, annotation, pre, words =>
      annotatedInput next schemas (extractor words.1).2.2 (annotation words.1) pre.2 words.2
  | _, @PublicCoin.challenge _ _ _ next, schemas, _, extractor, annotation, pre, words =>
      match pre with
      | .inl _ => annotation.1
      | .inr ⟨_, pre⟩ => annotatedInput next schemas.2 (extractor words.1).2.2
          (annotation.2.2 words.1) pre words.2

/-- Annotated local containment transports through the selected strict-prefix parser. -/
theorem annotated_escape_subset {Com : Type} [DecidableEq Com] {protocol : Protocol}
    (coin : PublicCoin protocol) (schemas : BadSchemas coin) {state : KnowledgeState}
    (extractor : RoundExtractor protocol.tree state)
    (annotation : BadAnnotation coin schemas extractor)
    (path : (compile Com coin).tree.ExecutionPath) (messages : ExtractedMessages coin path)
    (table : PrefixTable PUnit (compiledCoin Com coin)) (r : ℕ) selected
    (hs : selectedPrefix coin path messages r = some selected)
    (hq : (schemaAt coin schemas selected.1).isQuery = false)
    (escape : escapeAt coin extractor path messages table r) :
    (schemaAt coin schemas selected.1).Bad
      (annotatedInput coin schemas extractor annotation selected.1 selected.2)
      (table selected.1) := by
  induction coin generalizing state r with
  | done => exact escape.elim
  | sender next ih =>
      simp only [selectedPrefix, Option.map_eq_some_iff] at hs
      obtain ⟨⟨pre, words⟩, hs, heq⟩ := hs
      cases heq
      exact ih path.1 (schemas path.1) (extractor path.1).2.2 (annotation path.1)
        path.2 messages _ r _ hs hq escape
  | oracle next ih =>
      simp only [selectedPrefix, Option.map_eq_some_iff] at hs
      obtain ⟨⟨pre, words⟩, hs, heq⟩ := hs
      cases heq
      exact ih schemas (extractor (messages (.inl ()))).2.2 (annotation (messages (.inl ())))
        path.2 (fun i => messages (.inr i)) _ r _ hs hq escape
  | challenge next ih =>
      cases r with
      | zero =>
          simp only [selectedPrefix, Option.some.injEq] at hs
          cases hs
          change schemas.1.Bad annotation.1 (table (.inl PUnit.unit))
          rw [← escape.1]
          exact annotation.2.1 path.1 hq escape.2
      | succ r =>
          simp only [selectedPrefix, Option.map_eq_some_iff] at hs
          obtain ⟨⟨pre, words⟩, hs, heq⟩ := hs
          cases heq
          exact ih schemas.2 (extractor path.1).2.2 (annotation.2.2 path.1)
            path.2 messages _ r _ hs hq escape.2

/-- Parse executable local inputs without carrying an analytical challenge schedule. -/
def BadAnnotation.relation {Statement Com : Type} [DecidableEq Com]
    {protocol : Statement → Protocol} (coin : (s : Statement) → PublicCoin (protocol s))
    (state : Statement → KnowledgeState)
    (extractor : (s : Statement) → RoundExtractor (protocol s).tree (state s))
    (schemas : (s : Statement) → BadSchemas (coin s))
    (annotation : (s : Statement) → BadAnnotation (coin s) (schemas s) (extractor s))
    (Authentication : Key Statement PUnit (fun s => compiledCoin Com (coin s)) → Type)
    (authenticate : (key : Key Statement PUnit (fun s => compiledCoin Com (coin s))) →
      PrefixMessages (coin key.1) key.2 → Authentication key → Bool) :
    WitnessCIRelation (Com := Com) coin where
  challengeEq key := (schemaAt (coin key.1) (schemas key.1) key.2).equality
  isQuery key := (schemaAt (coin key.1) (schemas key.1) key.2).isQuery
  Authentication := Authentication
  authenticate := authenticate
  MaskLE key small large := (schemaAt (coin key.1) (schemas key.1) key.2).MaskLE
    (annotatedInput (coin key.1) (schemas key.1) _ (annotation key.1) key.2 small)
    (annotatedInput (coin key.1) (schemas key.1) _ (annotation key.1) key.2 large)
  Bad key words := (schemaAt (coin key.1) (schemas key.1) key.2).Bad
    (annotatedInput (coin key.1) (schemas key.1) _ (annotation key.1) key.2 words)
  check key words := (schemaAt (coin key.1) (schemas key.1) key.2).check
    (annotatedInput (coin key.1) (schemas key.1) _ (annotation key.1) key.2 words)
  check_iff key _words := (schemaAt (coin key.1) (schemas key.1) key.2).check_iff _
  monotone key _small _large := (schemaAt (coin key.1) (schemas key.1) key.2).monotone _ _
  error key := (schemaAt (coin key.1) (schemas key.1) key.2).error
  bad_bound key _words := (schemaAt (coin key.1) (schemas key.1) key.2).bad_bound _

/-- Local schemas and annotated escape proofs assemble a witness knowledge certificate. -/
def BadAnnotation.certificate {Statement Com : Type} [DecidableEq Com]
    {protocol : Statement → Protocol} (coin : (s : Statement) → PublicCoin (protocol s))
    (state : Statement → KnowledgeState)
    (certificate : Erased ((s : Statement) → KnowledgeCertificate
      (protocol s).tree (protocol s).roles (state s)))
    (extractor : (s : Statement) → RoundExtractor (protocol s).tree (state s))
    (extractor_eq : ∀ s, (certificate.out s).extractor = extractor s)
    (schemas : (s : Statement) → BadSchemas (coin s))
    (annotation : (s : Statement) → BadAnnotation (coin s) (schemas s) (extractor s))
    (Authentication : Key Statement PUnit (fun s => compiledCoin Com (coin s)) → Type)
    (authenticate : (key : Key Statement PUnit (fun s => compiledCoin Com (coin s))) →
      PrefixMessages (coin key.1) key.2 → Authentication key → Bool) :
    WitnessKnowledgeCertificate (Com := Com) coin state certificate.out where
  toWitnessCIRelation := BadAnnotation.relation coin state extractor schemas annotation
    Authentication authenticate
  escape_subset s path messages table r selected hs hq escape := by
    rw [extractor_eq s] at escape
    exact annotated_escape_subset (coin s) (schemas s) _ (annotation s)
      path messages table r selected hs hq escape

end Interaction.Oracle.Security.StandardBcs
