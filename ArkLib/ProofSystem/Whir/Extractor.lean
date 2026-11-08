/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.ProofSystem.Whir.LocalBounds
public import ArkLib.ProofSystem.Sumcheck.Interaction.Knowledge

/-!
# List-lifting WHIR opening knowledge certificate

Each encoded state concerns the current word. Batching and folding lift successor polynomials
through its proximity list, preferring preimages satisfying the old claims. At a level boundary,
the OOD state carries either an old polynomial or a colliding pair from the new list. After a
separating OOD point, the answer fixes the candidate before queries. The final plaintext is fixed
before queries and closing Sumcheck. Only the root map selects a base-field input polynomial.

With `q = |E|`, the local error schedule is:

| Message | Local error |
| --- | --- |
| Batching at level i | `(J_i - 1)L_i/q` |
| Each fold at level i | `2L_i/q + ε_i` |
| OOD entering level i ≥ 1 | `binom(L_i,2)n_i/q` |
| Queries at level i | `(1 - γ_i)^t_i` |
| Final batching | `t_last/q` |
| Each closing Sumcheck round | `2/q` |

The concrete maps preserve prover knowledge and satisfy the uniform challenge schedule's local
probability bounds.

## Open obligations

- Dimension-one MCA requires a separate bound.
- CompPoly's strict `< r` domain hypothesis requires an adapter.
-/

@[expose] public section

open Interaction Interaction.Oracle Interaction.Oracle.Security OracleComp OracleSpec

namespace Whir

/-- A fixed plaintext candidate satisfies the running claims and all preceding checks. -/
def plaintextState {E : Type} [Semiring E] {n : ℕ} (candidate : Table E n)
    (claims : List (Claim E n)) (active : Bool) : KnowledgeState where
  Witness := PUnit
  holds _ := active = true ∧ ∀ c ∈ claims, c.Holds candidate

/-- Closing Sumcheck restricts a fixed plaintext and weight; the terminal carrier is `PUnit`. -/
def closingExtractor {E : Type} [CommRing E] [DecidableEq E] :
    (count : ℕ) → (candidate : Table E count) → (claim : Claim E count) → (active : Bool) →
      RoundExtractor (scalarRounds E count .done).tree
        (plaintextState candidate [claim] active)
  | 0, _, _, _ => PUnit.unit
  | count + 1, candidate, claim, active => fun q =>
      let checked := active && (Sumcheck.compressedOps 1).accept claim.value q
      ⟨plaintextState candidate [claim] checked, id, fun r =>
        ⟨plaintextState (foldMessageOne (vars := 0) candidate r)
          [⟨foldMessageOne (vars := 0) claim.weight r, evalQuadratic claim.value q r⟩] checked,
          id, closingExtractor count (foldMessageOne (vars := 0) candidate r)
            ⟨foldMessageOne (vars := 0) claim.weight r, evalQuadratic claim.value q r⟩ checked⟩⟩

/-- Final power batching has a fixed candidate, followed by its closing Sumcheck. -/
def finalBatchExtractor {E : Type} [CommRing E] [DecidableEq E] {n : ℕ}
    (candidate : Table E n) (claims : List (Claim E n)) (active : Bool) :
    RoundExtractor (.public E fun _ => (scalarRounds E n .done).tree)
      (plaintextState candidate claims active) :=
  fun r => ⟨plaintextState candidate [batch claims r] active, id,
    closingExtractor n candidate (batch claims r) active⟩

/-- Each fold lifts from the current folded list, preferring a claim-satisfying preimage. -/
def foldExtractor {K E : Type} [CommRing E] [DecidableEq E]
    {vars : ℕ} (enc : Encoding K vars) (nearby : (lanes : ℕ) →
      MaskedWord E lanes (2 ^ (vars + enc.rate)) → Table E (lanes + vars) → Prop)
    (decoders : (lanes : ℕ) → ListDecoder (E := E) enc lanes)
    {rest : Protocol}
    (finish : (word : MaskedWord E 0 (2 ^ (vars + enc.rate))) →
      (claim : Claim E (0 + vars)) → (active : Bool) →
      RoundExtractor rest.tree (relationState (nearby 0) word [claim] active)) :
    (lanes : ℕ) → (word : MaskedWord E lanes (2 ^ (vars + enc.rate))) →
      (claim : Claim E (lanes + vars)) → (active : Bool) →
      RoundExtractor (scalarRounds E lanes rest).tree
        (relationState (nearby _) word [claim] active)
  | 0, word, claim, active => finish word claim active
  | lanes + 1, word, claim, active =>
    let candidates := (decoders (lanes + 1)).decode word
    fun q =>
      let checked := active && (Sumcheck.compressedOps 1).accept claim.value q
      ⟨relationState (nearby _) word [claim] checked, id, fun r =>
        let word' := foldMaskedRowsOne word r
        let claim' : Claim E (lanes + vars) :=
          ⟨foldMessageOne claim.weight r, evalQuadratic claim.value q r⟩
        ⟨relationState (nearby _) word' [claim'] checked,
          listLift candidates
            (fun f => foldMessageOne f r) claim.Holds,
          foldExtractor enc nearby decoders finish lanes word' claim' checked⟩⟩

/-- After a plaintext message, knowledge means that this fixed table was an old-list member. -/
def plaintextProximityState {K E : Type} [Semiring E]
    {tail : ℕ} (enc : Encoding K tail)
    (nearby : MaskedWord E 0 (2 ^ (tail + enc.rate)) → Table E (0 + tail) → Prop)
    (word : MaskedWord E 0 (2 ^ (tail + enc.rate))) (claim : Claim E (0 + tail))
    (candidate : Table E tail) (active : Bool) : KnowledgeState where
  Witness := PUnit
  holds _ := (relationState nearby word [claim] active).holds
    (castTable (Nat.zero_add tail).symm candidate)

/-- The last-level message lifts the fixed plaintext; queries then test that one candidate. -/
def lastExtractor {K E : Type} [Semiring K] [CommRing E] [DecidableEq E]
    {tail : ℕ} (lanes queries : ℕ) (enc : Encoding K tail) (ι : K →+* E)
    (nearby : MaskedWord E 0 (2 ^ (tail + enc.rate)) → Table E (0 + tail) → Prop)
    (decoder : ListDecoder (E := E) enc 0) (word : MaskedWord E 0 (2 ^ (tail + enc.rate)))
    (claim : Claim E (0 + tail)) (active : Bool) :
    RoundExtractor (transition E (.last lanes tail enc queries)).tree
      (relationState nearby word [claim] active) :=
  let candidates := decoder.decode word
  fun candidate =>
    ⟨plaintextProximityState enc nearby word claim candidate active,
      (fun _ => listLift candidates
        (castTable (Nat.zero_add tail)) claim.Holds candidate), fun xs =>
      let claims : List (Claim E tail) :=
        ⟨castTable (Nat.zero_add tail) claim.weight, claim.value⟩ ::
          List.ofFn (fun q : Fin queries =>
            ⟨fun u => ι (enc.weight (xs q) u), zeroFill word (xs q) Fin.elim0⟩)
      ⟨plaintextState candidate claims (active && queriesKnown word xs), (fun _ => PUnit.unit),
        finalBatchExtractor candidate claims (active && queriesKnown word xs)⟩⟩

/-- The collision predicate uses only the new oracle and the OOD point, before its answer. -/
def OodCollision {E : Type} [CommRing E] {n : ℕ}
    (candidates : List (Table E n)) (z : Fin n → E) : Prop :=
  ∃ f ∈ candidates, ∃ g ∈ candidates, f ≠ g ∧ mle f z = mle g z

/-- The OOD answer fixes this candidate before the independent query vector is sampled. -/
def oodCandidate {E : Type} [CommRing E] [DecidableEq E] {n : ℕ}
    (candidates : List (Table E n)) (z : Fin n → E) (answer : E) : Table E n :=
  (candidates.find? (fun f => decide (mle f z = answer))).getD 0

/-- A matching answer selects a member of the fixed list with that evaluation. -/
theorem oodCandidate_spec {E : Type} [CommRing E] [DecidableEq E] {n : ℕ}
    (candidates : List (Table E n)) (z : Fin n → E) (answer : E)
    (exists_answer : ∃ f ∈ candidates, mle f z = answer) :
    oodCandidate candidates z answer ∈ candidates ∧
      mle (oodCandidate candidates z answer) z = answer := by
  unfold oodCandidate
  cases found : candidates.find? (fun f => decide (mle f z = answer)) with
  | some f => exact ⟨List.mem_of_find?_eq_some found, by simpa using List.find?_some found⟩
  | none =>
    obtain ⟨f, hf, good⟩ := exists_answer
    exact (List.find?_eq_none.mp found f hf (by simpa using good)).elim

/-- Search the ordered pairs of the fixed new list for an OOD collision. -/
def oodCollisionPair {E : Type} [CommRing E] [DecidableEq E] {n : ℕ}
    (candidates : List (Table E n)) (z : Fin n → E) : Option (Table E n × Table E n) :=
  (candidates.product candidates).find? (fun p => decide (p.1 ≠ p.2 ∧ mle p.1 z = mle p.2 z))

/-- Successful collision search returns two distinct list members with equal evaluations. -/
theorem oodCollisionPair_spec {E : Type} [CommRing E] [DecidableEq E] {n : ℕ}
    (candidates : List (Table E n)) (z : Fin n → E) (f g : Table E n)
    (found : oodCollisionPair candidates z = some (f, g)) :
    f ∈ candidates ∧ g ∈ candidates ∧ f ≠ g ∧ mle f z = mle g z := by
  exact ⟨(List.mem_product.mp (List.mem_of_find?_eq_some found)).1,
    (List.mem_product.mp (List.mem_of_find?_eq_some found)).2,
    by simpa using List.find?_some found⟩

/-- Collision search fails exactly when the fixed list has no OOD collision. -/
theorem oodCollisionPair_eq_none {E : Type} [CommRing E] [DecidableEq E] {n : ℕ}
    (candidates : List (Table E n)) (z : Fin n → E) :
    oodCollisionPair candidates z = none ↔ ¬ OodCollision candidates z := by
  simp only [oodCollisionPair, List.find?_eq_none, Bool.not_eq_true, decide_eq_false_iff_not,
    OodCollision]
  constructor
  · rintro absent ⟨f, hf, g, hg, good⟩
    exact absent (f, g) (List.mem_product.mpr ⟨hf, hg⟩) good
  · rintro absent ⟨f, g⟩ member good
    obtain ⟨hf, hg⟩ := List.mem_product.mp member
    exact absent ⟨f, hf, g, hg, good⟩

/-- OOD backward failure is contained entirely in the new-list collision event. -/
theorem ood_lift_failure_subset {E : Type} [CommRing E] {n : ℕ}
    (old : Table E n → Prop) (candidates : List (Table E n))
    (z : Fin n → E) (active : Bool)
    (bad : ∃ witness, (oodState old candidates z active).holds witness ∧
      ¬ (active = true ∧ old (match witness with | .inl f => f | .inr _ => 0))) :
    OodCollision candidates z := by
  obtain ⟨witness, hgood, hbad⟩ := bad
  rcases witness with f | ⟨f, g⟩
  · exact (hbad hgood).elim
  · exact ⟨f, hgood.2.1, g, hgood.2.2.1, hgood.2.2.2⟩

/-- Lift by polynomial equality when an old-list preimage exists; otherwise carry a collision.
The remaining case returns the image of the fixed zero default. -/
def boundaryLift {E : Type} [CommRing E] [DecidableEq E] {n m : ℕ}
    (oldList : List (Table E m)) (view : Table E m → Table E n)
    (valid : Table E m → Prop) [DecidablePred valid]
    (newList : List (Table E n)) (z : Fin n → E)
    (successor : Table E n) : Sum (Table E n) (Table E n × Table E n) :=
  if oldList.any (fun f => decide (view f = successor)) then
    .inl (view (listLift oldList view valid successor))
  else match oodCollisionPair newList z with
    | some pair => .inr pair
    | none => .inl (view 0)

/-- A level boundary returns the identical polynomial whenever the old list contains it. -/
theorem boundaryLift_of_preimage {E : Type} [CommRing E] [DecidableEq E] {n m : ℕ}
    (oldList : List (Table E m)) (view : Table E m → Table E n)
    (valid : Table E m → Prop) [DecidablePred valid]
    (newList : List (Table E n)) (z : Fin n → E)
    (successor : Table E n) (preimage : ∃ f ∈ oldList, view f = successor) :
    boundaryLift oldList view valid newList z successor = .inl successor := by
  have present : oldList.any (fun f => decide (view f = successor)) = true := by
    simpa only [List.any_eq_true, decide_eq_true_eq] using preimage
  simp only [boundaryLift, present, ite_true,
    (listLift_of_preimage oldList view valid successor preimage).2]

/-- A failed query lift is a far fixed candidate passing every sampled consistency check.
The candidate depends on the new list, OOD point and answer, but not on `xs`. -/
theorem boundary_query_failure_subset {K E : Type} [Semiring K] [CommRing E]
    [DecidableEq E] {tail queries : ℕ} (enc : Encoding K tail) (ι : K →+* E) (γ L : ℝ)
    (decoder : ListDecoder (E := E) enc 0) (correct : decoder.Correct ι γ L)
    (word : MaskedWord E 0 (2 ^ (tail + enc.rate))) (claim : Claim E (0 + tail))
    (candidates : List (Table E tail)) (z : Fin tail → E) (answer : E)
    (xs : Fin queries → enc.Columns) (active : Bool)
    (bad : ∃ f ∈ candidates, active = true ∧
      claim.Holds (castTable (Nat.zero_add tail).symm f) ∧ mle f z = answer ∧
      (∀ q, word (xs q) = some (fun _ => enc.encode ι f (xs q))) ∧
      ¬ (oodState (fun g => (candidateState enc ι γ word [claim] active).holds
          (castTable (Nat.zero_add tail).symm g)) candidates z active).holds
        (boundaryLift (decoder.decode word) (castTable (Nat.zero_add tail))
          claim.Holds candidates z f)) :
    ¬ Close γ word (enc.interleave ι
      (castTable (Nat.zero_add tail).symm (oodCandidate candidates z answer))) ∧
    ∀ q, word (xs q) = some (fun _ => enc.encode ι (oodCandidate candidates z answer) (xs q)) := by
  classical
  obtain ⟨f, hf, ha, hclaim, hanswer, hqueries, hbad⟩ := bad
  have no_collision : ¬ OodCollision candidates z := by
    intro collision
    have absent : ¬ ∃ g ∈ decoder.decode word, castTable (Nat.zero_add tail) g = f := by
      intro preimage
      rw [boundaryLift_of_preimage _ _ _ _ _ _ preimage] at hbad
      obtain ⟨g, hg, hgf⟩ := preimage
      have hgf' : g = castTable (Nat.zero_add tail).symm f := by
        rw [← hgf, castTable_inverse]
      exact hbad ⟨ha, ha, (correct.mem_iff _ _).mp (hgf' ▸ hg),
        by simpa only [List.mem_singleton, forall_eq] using hclaim⟩
    have absent' : (decoder.decode word).any
        (fun g => decide (castTable (Nat.zero_add tail) g = f)) = false := by
      simpa only [List.any_eq_false, decide_eq_true_eq, not_exists, not_and] using absent
    have found : ∃ pair, oodCollisionPair candidates z = some pair := by
      cases h : oodCollisionPair candidates z with
      | none => exact (((oodCollisionPair_eq_none candidates z).mp h) collision).elim
      | some pair => exact ⟨pair, rfl⟩
    obtain ⟨⟨g, h⟩, found⟩ := found
    apply hbad
    simp only [boundaryLift, absent', Bool.false_eq_true, ite_false, found, oodState]
    exact ⟨ha, oodCollisionPair_spec candidates z g h found⟩
  have selected : oodCandidate candidates z answer = f := by
    have chosen := oodCandidate_spec candidates z answer ⟨f, hf, hanswer⟩
    by_contra hne
    exact no_collision ⟨_, chosen.1, f, hf, hne, chosen.2.trans hanswer.symm⟩
  rw [selected]
  refine ⟨?_, hqueries⟩
  intro close
  have hg := (correct.mem_iff _ _).mpr close
  have preimage : ∃ g ∈ decoder.decode word, castTable (Nat.zero_add tail) g = f :=
    ⟨_, hg, castTable_inverse _ _⟩
  rw [boundaryLift_of_preimage _ _ _ _ _ _ preimage] at hbad
  exact hbad ⟨ha, ha, close,
    by simpa only [List.mem_singleton, forall_eq] using hclaim⟩

/-- A new oracle preserves the old state; OOD introduces collisions and queries lift equality. -/
def boundaryExtractor {K E : Type} [Semiring K] [CommRing E]
    [DecidableEq E] {tail : ℕ} (lanes queries : ℕ) (enc : Encoding K tail)
    (ι : K →+* E)
    (nearby : MaskedWord E 0 (2 ^ (tail + enc.rate)) → Table E (0 + tail) → Prop)
    (rest : Schedule K tail) (nextNearby : ProximityFamily K E)
    (decoder : ListDecoder (E := E) enc 0) (decoders : DecoderFamily (E := E) rest)
    (suffixExtractor : (word : oracleMessage E rest) → (claims : List (Claim E tail)) →
      (active : Bool) → RoundExtractor (opening E rest).tree
        (relationLevelState rest nextNearby word claims active))
    (word : MaskedWord E 0 (2 ^ (tail + enc.rate))) (claim : Claim E (0 + tail))
    (active : Bool) :
    RoundExtractor (transition E (.more lanes enc queries rest)).tree
      (relationState nearby word [claim] active) :=
  let oldList := decoder.decode word
  fun nextWord =>
    let oldState := relationState nearby word [claim] active
    let old := fun f : Table E tail => oldState.holds (castTable (Nat.zero_add tail).symm f)
    let newList := levelList rest decoders nextWord
    ⟨oldState, id, fun z =>
      let separatedState := oodState old newList z active
      ⟨separatedState, (fun w => match w with
        | .inl f => castTable (Nat.zero_add tail).symm f
        | .inr _ => (0 : Table E (0 + tail))), fun answer =>
        ⟨separatedState, id, fun xs =>
          let residual : Claim E tail :=
            ⟨castTable (Nat.zero_add tail) claim.weight, claim.value⟩
          let claims := nextClaims enc ι residual z answer xs (fun x => zeroFill word x Fin.elim0)
          ⟨relationLevelState rest nextNearby nextWord claims (active && queriesKnown word xs),
            boundaryLift oldList
              (castTable (Nat.zero_add tail)) claim.Holds newList z,
            suffixExtractor nextWord claims (active && queriesKnown word xs)⟩⟩⟩⟩

/-- The E-valued opening lifts the current witness through each batching and fold challenge. -/
def levelExtractor {K E : Type} [Semiring K] [CommRing E]
    [DecidableEq E] (ι : K →+* E) :
    {n : ℕ} → (s : Schedule K n) → (nearby : ProximityFamily K E) →
      (decoders : DecoderFamily (E := E) s) →
      (word : oracleMessage E s) → (claims : List (Claim E n)) → (active : Bool) →
      RoundExtractor (opening E s).tree (relationLevelState s nearby word claims active)
  | _, .last lanes tail enc queries, nearby, decoders, word, claims, active =>
    let candidates := (decoders lanes).decode word
    fun r =>
      ⟨relationState (nearby 0 enc lanes) word [batch claims r] active,
        listLift candidates id
          (fun f => ∀ c ∈ claims, c.Holds f),
        foldExtractor enc (nearby 0 enc) decoders
          (lastExtractor lanes queries enc ι (nearby 0 enc 0) (decoders 0))
          lanes word (batch claims r) active⟩
  | _, .more lanes enc queries rest, nearby, decoders, word, claims, active =>
    let candidates := (decoders.1 lanes).decode word
    fun r =>
      ⟨relationState (nearby 0 enc lanes) word [batch claims r] active,
        listLift candidates id
          (fun f => ∀ c ∈ claims, c.Holds f),
        foldExtractor enc (nearby 0 enc) decoders.1
          (boundaryExtractor lanes queries enc ι (nearby 0 enc 0)
            rest (fun level => nearby (level + 1)) (decoders.1 0) decoders.2
            (levelExtractor ι rest (fun level => nearby (level + 1)) decoders.2))
          lanes word (batch claims r) active⟩

/-- Replace only the first backward map by a fixed root selection, retaining the concrete suffix. -/
def rootSelection {Moves : Type} {next : Moves → Oracle.TypeTree} {state : KnowledgeState}
    (extractor : RoundExtractor (.public Moves next) state) (input : KnowledgeState)
    (selected : input.Witness) : RoundExtractor (.public Moves next) input :=
  fun move => ⟨(extractor move).1, (fun _ => selected), (extractor move).2.2⟩

/-- The opening's root map is the first satisfying decoded base-field message, else zero. -/
def openingExtractor {K E : Type} [Semiring K] [CommRing E]
    [DecidableEq K] [DecidableEq E] (ι : K →+* E) :
    {n : ℕ} → (s : Schedule K n) → (nearby : ProximityFamily K E) →
      (input : Table K n → Prop) →
      (decoders : DecoderFamily (E := E) s) →
      (word : oracleMessage K s) → (claims : List (Claim E n)) → (decoder : InitialDecoder s) →
      RoundExtractor (opening E s).tree (⟨Table K n, input⟩)
  | _, .last lanes tail enc queries, nearby, input, decoders, word, claims, decoder =>
      rootSelection (levelExtractor ι (.last lanes tail enc queries) nearby decoders
        (mapMasked ι word) claims true)
        ⟨Table K (lanes + tail), input⟩
        (selectInitial ι (.last lanes tail enc queries) decoder word claims)
  | _, .more lanes enc queries rest, nearby, input, decoders, word, claims, decoder =>
      rootSelection (levelExtractor ι (.more lanes enc queries rest) nearby decoders
        (mapMasked ι word) claims true)
        ⟨_, input⟩
        (selectInitial ι (.more lanes enc queries rest) decoder word claims)

end Whir
