/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.ProofSystem.Fri.Interaction.Schedule
public import ArkLib.ProofSystem.Fri.RoundConsistency
public import ArkLib.Interaction.Oracle.Execution
public import ArkLib.Interaction.Oracle.PublicCoin

/-!
# FRI on the interaction layer

FRI as Plonky3 runs it, on a domain `ω` of `2 ^ top` points, along a `Schedule`. The inputs are
oracles: `inputs m` is the word of log height `m`, read through `inputAccess`. The verifier's
word at the first layer is the tallest input `inputs top`, and after a fold by `2 ^ k` at `β` it
is the fold of the prover's word there, plus `β ^ 2 ^ k` times the input of the folded domain's
height if the fold injects it. Each fold round is the prover's oracle message, its word at the
layer (meant to be the verifier's word), followed by the verifier's challenge `β`; the first
message is the word Plonky3 commits before its first folding challenge. After the folds the
prover sends the final polynomial's `d` coefficients in the clear, without a word for the last
layer, and the verifier samples `t` positions of the top domain (`queryPhase`). At each position
it checks every committed word against the verifier's word on the point the position reduces to,
and the verifier's word at the last layer against the final polynomial.

The verifier never sees a word: it reads them through oracle queries. Its local state
(`Reader`) holds query programs for the inputs, for its word at the current layer and for the
checks so far at each top position; an oracle message extends the access signature, and the
programs move to it by `extendAccess`. `honestProver` sends the verifier's words.
-/
@[expose] public section

open Interaction Interaction.Oracle OracleComp OracleSpec Domain

namespace Fri.Interaction

variable (K : Type)

/-- A word on the domain of `2 ^ m` points. -/
abbrev Word (m : ℕ) : Type := Fin (2 ^ m) → K

/-- Access to FRI's inputs: the query `⟨m, x⟩` reads the input of log height `m` at `x`. -/
def inputAccess : PFunctor := ⟨(m : ℕ) × Fin (2 ^ m), fun _ => K⟩

/-- The inputs' oracle behavior. -/
def inputImpl (inputs : (m : ℕ) → Fin (2 ^ m) → K) :
    QueryImpl (OracleSpec.ofPFunctor (inputAccess K)) Id :=
  fun q => inputs q.1 q.2

/-- The query phase: the verifier samples `t` positions of the top domain. -/
def queryPhase (top t : ℕ) : Protocol :=
  .public .receiver (Fin t → Fin (2 ^ top)) fun _ => .done

/-- FRI from a layer of log height `n`: a fold round is the prover's word at the layer as an
oracle message, then the verifier's challenge; after the folds the prover sends the final
polynomial's `d` coefficients, then the query phase. -/
def protocol (top d t : ℕ) : {n : ℕ} → Schedule n → Protocol
  | _, .final => .public .sender (Fin d → K) fun _ => queryPhase top t
  | n, .fold _ _ _ rest =>
      .oracle (Word K n) (.public .receiver K fun _ => protocol top d t rest)

/-- FRI is public-coin: after each word comes the folding challenge, and after the final
polynomial the query positions, whatever the challenge. -/
def publicCoin [Fintype K] [DecidableEq K] [SampleableType K] (top d t : ℕ) :
    {n : ℕ} → (s : Schedule n) → PublicCoin (protocol K top d t s)
  | _, .final => .sender fun _ => .challenge .done
  | _, .fold _ _ _ rest => .oracle (.challenge (publicCoin top d t rest))

variable {K}

/-- The point of the domain of `2 ^ m` points that the folds map a top position to. -/
def proj {top : ℕ} (m : ℕ) (x : Fin (2 ^ top)) : Fin (2 ^ m) :=
  ⟨x % 2 ^ m, Nat.mod_lt _ (Nat.two_pow_pos m)⟩

/-- The `q`th point above `y` of a fold by `2 ^ k`: the positions of the domain of `2 ^ n` points
whose `2 ^ k`th powers are the point `y` of the folded domain are `y + q · 2 ^ (n - k)`. -/
def fiberPoint {n k : ℕ} (hk : k ≤ n) (y : Fin (2 ^ (n - k))) (q : Fin (2 ^ k)) : Fin (2 ^ n) :=
  ⟨y + q * 2 ^ (n - k), by
    have hn : 2 ^ n = 2 ^ k * 2 ^ (n - k) := by rw [← pow_add, Nat.add_sub_of_le hk]
    have hy := y.isLt
    have hq : (q : ℕ) + 1 ≤ 2 ^ k := q.isLt
    rw [hn]
    nlinarith⟩

/-- The evaluation of `d` coefficients at a point. -/
def evalCoeffs [Semiring K] {d : ℕ} (c : Fin d → K) (z : K) : K :=
  ∑ i, c i * z ^ (i : ℕ)

variable [Field K] [DecidableEq K]

/-- The folded value at `y` of a fold by `2 ^ k` at `β`, from the word's values `vals` on the
fiber above `y`: the interpolant of the fiber evaluated at `β`. -/
def foldFiber {n k : ℕ} (hk : k ≤ n) (ω : SmoothCosetFftDomain n K) (y : Fin (2 ^ (n - k)))
    (β : K) (vals : Fin (2 ^ k) → K) : K :=
  (CompPoly.CPolynomial.CLagrange.interpolate Finset.univ
    (fun q => ω (fiberPoint hk y q)) vals).eval β

/-- The injected word of a fold onto log height `m`: the input of that height, or zero. -/
def injected (inputs : (m : ℕ) → Fin (2 ^ m) → K) (m : ℕ) : Bool → Word K m
  | true => inputs m
  | false => 0

/-- The verifier's word after a fold: `f` folded by `2 ^ k` at `β`, plus `β ^ 2 ^ k g`. -/
def foldNext {n k : ℕ} (hk : k ≤ n) (ω : SmoothCosetFftDomain n K) (f : Word K n) (β : K)
    (g : Word K (n - k)) : Word K (n - k) :=
  fun y => foldFiber hk ω y β (fun q => f (fiberPoint hk y q)) + β ^ 2 ^ k * g y

/-- The final polynomial's `d` coefficients of the word at the last layer: the low coefficients
of its interpolant. -/
def finalCoeffs {n : ℕ} (ω : SmoothCosetFftDomain n K) (f : Word K n) (d : ℕ) : Fin d → K :=
  fun i => (CompPoly.CPolynomial.CLagrange.interpolate Finset.univ (fun x => ω x) f).coeff i

/-! ### The verifier -/

/-- Lift a query program to the signature extended by an oracle message. -/
def extendAccess {A : PFunctor} {M : Type} (I : OracleInterface M) {α : Type}
    (oa : OracleComp (OracleSpec.ofPFunctor A) α) :
    OracleComp (OracleSpec.ofPFunctor (Access.extend A I)) α :=
  simulateQ (Access.queryPrior A I) oa

/-- Lift a query program to the verifier's signature, beside the ambient oracles. -/
def withAmbient {ι : Type} (ambient : OracleSpec ι) {A : PFunctor} {α : Type}
    (oa : OracleComp (OracleSpec.ofPFunctor A) α) :
    OracleComp (ambient + OracleSpec.ofPFunctor A) α :=
  simulateQ (fun q => liftM ((ambient + OracleSpec.ofPFunctor A).query (.inr q))) oa

/-- Run `m` programs in order and collect their values. -/
def readAll {ι : Type} {spec : OracleSpec ι} {α : Type} :
    (m : ℕ) → (Fin m → OracleComp spec α) → OracleComp spec (Fin m → α)
  | 0, _ => pure Fin.elim0
  | m + 1, read => do
      let v ← read 0
      let rest ← readAll m fun i => read i.succ
      return Fin.cons v rest

/-- The verifier's query programs at a layer of log height `n`, over the access signature `A`:
reading the inputs, reading the verifier's word at the layer, and checking the committed words so
far at a top position. -/
structure Reader (top : ℕ) (A : PFunctor) (n : ℕ) where
  /-- Read the input of log height `m`. -/
  input : (m : ℕ) → Fin (2 ^ m) → OracleComp (OracleSpec.ofPFunctor A) K
  /-- Read the verifier's word at the layer. -/
  word : Fin (2 ^ n) → OracleComp (OracleSpec.ofPFunctor A) K
  /-- Check every committed word so far at a top position. -/
  check : Fin (2 ^ top) → OracleComp (OracleSpec.ofPFunctor A) Bool

namespace Reader

variable {top : ℕ}

/-- The reader before any fold: the verifier's word is the input `inputs top`. -/
def root (top : ℕ) : Reader (K := K) top (inputAccess K) top where
  input m x := liftM ((OracleSpec.ofPFunctor (inputAccess K)).query ⟨m, x⟩)
  word x := liftM ((OracleSpec.ofPFunctor (inputAccess K)).query ⟨top, x⟩)
  check _ := pure true

/-- Read the injected word of a fold onto log height `m`. -/
def readInjected {A : PFunctor} {n : ℕ} (r : Reader (K := K) top A n) (m : ℕ) (y : Fin (2 ^ m)) :
    Bool → OracleComp (OracleSpec.ofPFunctor A) K
  | true => r.input m y
  | false => pure 0

/-- The reader after the prover's word at the layer: the check at a top position adds the
committed word against the verifier's word at the point the position reduces to, and the word
read from then on is the committed one. -/
def commit {A : PFunctor} {n : ℕ} (r : Reader (K := K) top A n) :
    Reader (K := K) top (Access.extend A (OracleInterface.instFunction (α := Fin (2 ^ n))
      (β := K))) n where
  input m x := extendAccess _ (r.input m x)
  word y := Access.queryLatest A _ y
  check x := do
    let ok ← extendAccess _ (r.check x)
    let v ← extendAccess _ (r.word (proj n x))
    let committed : K ← Access.queryLatest A _ (proj n x)
    return ok && v == committed

/-- The reader after a fold by `2 ^ k` at `β`: the verifier's word at the folded layer is the
fold of the word on the fiber above each point, plus `β ^ 2 ^ k` times the injected input. -/
def fold {A : PFunctor} {n : ℕ} (r : Reader (K := K) top A n) (ω : SmoothCosetFftDomain n K)
    (k : ℕ) (hk : k ≤ n) (inject : Bool) (β : K) : Reader (K := K) top A (n - k) where
  input := r.input
  word y := do
    let vals ← readAll (2 ^ k) fun q => r.word (fiberPoint hk y q)
    let g ← r.readInjected (n - k) y inject
    return foldFiber hk ω y β vals + β ^ 2 ^ k * g
  check := r.check

/-- The check at a top position once the final polynomial `c` is known: the committed words, and
the verifier's word at the last layer against the final polynomial. -/
def finalCheck {A : PFunctor} {n d : ℕ} (r : Reader (K := K) top A n)
    (ω : SmoothCosetFftDomain n K) (c : Fin d → K) (x : Fin (2 ^ top)) :
    OracleComp (OracleSpec.ofPFunctor A) Bool := do
  let ok ← r.check x
  let v ← r.word (proj n x)
  return ok && v == evalCoeffs c (ω (proj n x))

/-- Check every queried position. -/
def checkAll {A : PFunctor} {n d t : ℕ} (r : Reader (K := K) top A n)
    (ω : SmoothCosetFftDomain n K) (c : Fin d → K) (xs : Fin t → Fin (2 ^ top)) :
    OracleComp (OracleSpec.ofPFunctor A) Bool := do
  let passed ← readAll t fun i => r.finalCheck ω c (xs i)
  return decide (∀ i, passed i = true)

end Reader

variable {ι : Type} (ambient : OracleSpec ι) (top d t : ℕ)

/-- The verifier from a layer of log height `n`, sampling the folding challenges with `sample`
and the query positions with `sampleQueries`; it returns whether every check passed. -/
def verifier (sample : OracleComp ambient K)
    (sampleQueries : OracleComp ambient (Fin t → Fin (2 ^ top))) :
    {n : ℕ} → (ω : SmoothCosetFftDomain n K) → (A : PFunctor) → Reader (K := K) top A n →
      (s : Schedule n) → Verifier.Strategy ambient (protocol K top d t s).tree
        (protocol K top d t s).roles (protocol K top d t s).oracles A (fun _ => Bool)
  | _, ω, _, r, .final => fun c => pure (do
      let xs ← liftComp sampleQueries _
      return ⟨xs, withAmbient ambient (r.checkAll ω c xs)⟩)
  | _, ω, _, r, .fold k hk inject rest => pure (do
      let β ← liftComp sample _
      return ⟨β, verifier sample sampleQueries (ω.subdomain k) _
        (r.commit.fold ω k hk inject β) rest⟩)

omit [Field K] [DecidableEq K] in
set_option backward.isDefEq.respectTransparency false in
/-- Executing the last round: the prover's final polynomial, the verifier's query positions, and
its final action on them. -/
theorem executeStrategies_final {n : ℕ} (A : PFunctor)
    (impl : QueryImpl (OracleSpec.ofPFunctor A) Id)
    {OutP : (protocol K top d t (.final (n := n))).tree.ExecutionPath → Type}
    {OutV : (protocol K top d t (.final (n := n))).tree.BranchPath → Type}
    (prover : Prover.Strategy ambient (protocol K top d t (.final (n := n))).tree
      (protocol K top d t (.final (n := n))).roles OutP)
    (verifier : Verifier.Strategy ambient (protocol K top d t (.final (n := n))).tree
      (protocol K top d t (.final (n := n))).roles
      (protocol K top d t (.final (n := n))).oracles A OutV) :
    executeStrategies ambient (protocol K top d t (.final (n := n))).tree
      (protocol K top d t (.final (n := n))).roles
      (protocol K top d t (.final (n := n))).oracles A impl prover verifier = (do
        let chosen ← prover
        let next ← simulateQ (Verifier.liftAccessImpl ambient A impl) (verifier chosen.1)
        let picked ← simulateQ (Verifier.liftAccessImpl ambient A impl) next
        let outP ← chosen.2 picked.1
        let outV ← simulateQ (Verifier.liftAccessImpl ambient A impl) picked.2
        return ⟨⟨chosen.1, picked.1, PUnit.unit⟩, outP, outV⟩) := by
  refine (executeStrategies_public_sender ambient (Moves := Fin d → K)
    (rest := fun _ => (queryPhase top t).tree) _ _ A impl prover verifier).trans ?_
  refine bind_congr fun chosen => bind_congr fun next => ?_
  refine (congrArg (· >>= _) (executeStrategies_public_receiver ambient
    (Moves := Fin t → Fin (2 ^ top)) (rest := fun _ => TypeTree.done) (fun _ => PUnit.unit)
    ⟨PUnit.unit, fun _ => PUnit.unit⟩ A impl (OutP := fun path => OutP ⟨chosen.1, path⟩)
    (OutV := fun path => OutV ⟨chosen.1, path⟩) chosen.2 next)).trans ?_
  simp only [executeStrategies_done, bind_assoc, pure_bind]
  rfl

omit [Field K] [DecidableEq K] in
set_option backward.isDefEq.respectTransparency false in
/-- Executing a fold round: the prover's word, the verifier's challenge, and the rest. -/
theorem executeStrategies_fold {n k : ℕ} (hk : k ≤ n) (inject : Bool) (rest : Schedule (n - k))
    (A : PFunctor) (impl : QueryImpl (OracleSpec.ofPFunctor A) Id)
    {OutP : (protocol K top d t (.fold k hk inject rest)).tree.ExecutionPath → Type}
    {OutV : (protocol K top d t (.fold k hk inject rest)).tree.BranchPath → Type}
    (prover : Prover.Strategy ambient (protocol K top d t (.fold k hk inject rest)).tree
      (protocol K top d t (.fold k hk inject rest)).roles OutP)
    (verifier : Verifier.Strategy ambient (protocol K top d t (.fold k hk inject rest)).tree
      (protocol K top d t (.fold k hk inject rest)).roles
      (protocol K top d t (.fold k hk inject rest)).oracles A OutV) :
    executeStrategies ambient (protocol K top d t (.fold k hk inject rest)).tree
      (protocol K top d t (.fold k hk inject rest)).roles
      (protocol K top d t (.fold k hk inject rest)).oracles A impl prover verifier = (do
        let sent ← prover
        let next ← simulateQ (Verifier.liftAccessImpl ambient
          (Access.extend A (OracleInterface.instFunction (α := Fin (2 ^ n)) (β := K)))
          (Access.extendImpl A _ impl sent.1)) verifier
        let chosen ← simulateQ (Verifier.liftAccessImpl ambient
          (Access.extend A (OracleInterface.instFunction (α := Fin (2 ^ n)) (β := K)))
          (Access.extendImpl A _ impl sent.1)) next
        let after ← sent.2 chosen.1
        let result ← executeStrategies ambient (protocol K top d t rest).tree
          (protocol K top d t rest).roles (protocol K top d t rest).oracles
          (Access.extend A (OracleInterface.instFunction (α := Fin (2 ^ n)) (β := K)))
          (Access.extendImpl A _ impl sent.1)
          (OutP := fun path => OutP ⟨sent.1, chosen.1, path⟩)
          (OutV := fun path => OutV ⟨PUnit.unit, chosen.1, path⟩) after chosen.2
        return ⟨⟨sent.1, chosen.1, result.1⟩, result.2.1, result.2.2⟩) := by
  refine (executeStrategies_oracle ambient (Messages := Word K n)
    (rest := fun _ => TypeTree.public K fun _ => (protocol K top d t rest).tree)
    _ _ A impl prover verifier).trans ?_
  refine bind_congr fun sent => bind_congr fun next => ?_
  refine (congrArg (· >>= _) (executeStrategies_public_receiver ambient (Moves := K)
    (rest := fun _ => (protocol K top d t rest).tree) _ _ _ _
    (OutP := fun path => OutP ⟨sent.1, path⟩) (OutV := fun path => OutV ⟨PUnit.unit, path⟩)
    sent.2 next)).trans ?_
  simp only [bind_assoc, pure_bind]
  rfl

/-! ### The honest prover -/

/-- The honest prover from a layer of log height `n` where the verifier's word is `f`: it sends
`f`, continues at the folded layer with the fold of `f` at the challenge, injecting the inputs the
schedule injects, and at the last layer sends the word's coefficients. -/
def honestProver (inputs : (m : ℕ) → Fin (2 ^ m) → K) :
    {n : ℕ} → SmoothCosetFftDomain n K → Word K n → (s : Schedule n) →
      Prover.Strategy ambient (protocol K top d t s).tree (protocol K top d t s).roles
        (fun _ => Unit)
  | _, ω, f, .final => pure ⟨finalCoeffs ω f d, fun _ => pure ()⟩
  | _, ω, f, .fold k hk inject rest =>
      pure ⟨f, fun β => pure (f := OracleComp ambient)
        (honestProver inputs (ω.subdomain k) (foldNext hk ω f β (injected inputs _ inject)) rest)⟩

end Fri.Interaction
