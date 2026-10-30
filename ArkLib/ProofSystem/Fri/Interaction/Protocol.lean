/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import ArkLib.ProofSystem.Fri.Interaction.Schedule
public import ArkLib.ProofSystem.Fri.RoundConsistency
public import ArkLib.Interaction.Oracle.Execution

/-!
# FRI on the interaction layer

FRI as Plonky3 runs it, on a domain `ω` of `2 ^ top` points, along a `Schedule`. The inputs are
oracles: `inputs m` is the word of log height `m`, read through `inputAccess`; the first fold
folds `inputs top`. Each fold round is a verifier challenge `β` followed by the prover's oracle
message, the next word: meant to be the current word folded by `2 ^ k` at `β`, plus
`β ^ 2 ^ k` times the input of the folded domain's height if the fold injects it. After the folds
the prover sends the final polynomial's `d` coefficients in the clear, and the verifier samples
`t` positions of the top domain (`queryPhase`). At each position it checks every fold on the
fiber the position reduces to, and the last word against the final polynomial.

The verifier never sees a word: it reads them through oracle queries. Its local state
(`Reader`) holds query programs for the inputs, for the current word and for the checks of the
folds so far at each top position; an oracle message extends the access signature, and the
programs move to it by `extendAccess`. `honestProver` folds the words it sends.
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

/-- FRI from a layer of log height `n`: a fold round is the verifier's challenge, then the next
word as an oracle message; after the folds the prover sends the final polynomial's `d`
coefficients, then the query phase. -/
def protocol (top d t : ℕ) : {n : ℕ} → Schedule n → Protocol
  | _, .final => .public .sender (Fin d → K) fun _ => queryPhase top t
  | n, .fold k _ _ rest =>
      .public .receiver K fun _ => .oracle (Word K (n - k)) (protocol top d t rest)

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

/-- The next word of an honest fold: `f` folded by `2 ^ k` at `β`, plus `β ^ 2 ^ k g`. -/
def foldNext {n k : ℕ} (hk : k ≤ n) (ω : SmoothCosetFftDomain n K) (f : Word K n) (β : K)
    (g : Word K (n - k)) : Word K (n - k) :=
  fun y => foldFiber hk ω y β (fun q => f (fiberPoint hk y q)) + β ^ 2 ^ k * g y

/-- The final polynomial's `d` coefficients of an honest last word: the low coefficients of its
interpolant. -/
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
reading the inputs, reading the current word, and checking the folds so far at a top position. -/
structure Reader (top : ℕ) (A : PFunctor) (n : ℕ) where
  /-- Read the input of log height `m`. -/
  input : (m : ℕ) → Fin (2 ^ m) → OracleComp (OracleSpec.ofPFunctor A) K
  /-- Read the current word. -/
  word : Fin (2 ^ n) → OracleComp (OracleSpec.ofPFunctor A) K
  /-- Check every fold so far at a top position. -/
  check : Fin (2 ^ top) → OracleComp (OracleSpec.ofPFunctor A) Bool

namespace Reader

variable {top : ℕ}

/-- The reader before any fold: the current word is the input `inputs top`. -/
def root (top : ℕ) : Reader (K := K) top (inputAccess K) top where
  input m x := liftM ((OracleSpec.ofPFunctor (inputAccess K)).query ⟨m, x⟩)
  word x := liftM ((OracleSpec.ofPFunctor (inputAccess K)).query ⟨top, x⟩)
  check _ := pure true

/-- Read the injected word of a fold onto log height `m`. -/
def readInjected {A : PFunctor} {n : ℕ} (r : Reader (K := K) top A n) (m : ℕ) (y : Fin (2 ^ m)) :
    Bool → OracleComp (OracleSpec.ofPFunctor A) K
  | true => r.input m y
  | false => pure 0

/-- The reader after a fold by `2 ^ k` at `β` and the next word: the next word is the latest
message, and the check at a top position adds this fold's check on the fiber it reduces to. -/
def fold {A : PFunctor} {n : ℕ} (r : Reader (K := K) top A n) (ω : SmoothCosetFftDomain n K)
    (k : ℕ) (hk : k ≤ n) (inject : Bool) (β : K) :
    Reader (K := K) top (Access.extend A (OracleInterface.instFunction (α := Fin (2 ^ (n - k)))
      (β := K))) (n - k) where
  input m x := extendAccess _ (r.input m x)
  word y := Access.queryLatest A _ y
  check x := do
    let ok ← extendAccess _ (r.check x)
    let y := proj (n - k) x
    let vals ← extendAccess _ (readAll (2 ^ k) fun q => r.word (fiberPoint hk y q))
    let g ← extendAccess _ (r.readInjected (n - k) y inject)
    let next : K ← Access.queryLatest A _ y
    return ok && foldFiber hk ω y β vals + β ^ 2 ^ k * g == next

/-- The check at a top position once the final polynomial `c` is known: the folds, and the
current word against the final polynomial. -/
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
  | _, ω, _, r, .fold k hk inject rest => do
      let β ← liftComp sample _
      return ⟨β, pure (verifier sample sampleQueries (ω.subdomain k) _
        (r.fold ω k hk inject β) rest)⟩

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
/-- Executing a fold round: the verifier's challenge, the prover's next word, and the rest. -/
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
        let chosen ← simulateQ (Verifier.liftAccessImpl ambient A impl) verifier
        let next ← prover chosen.1
        let sent ← next
        let after ← simulateQ (Verifier.liftAccessImpl ambient
          (Access.extend A (OracleInterface.instFunction (α := Fin (2 ^ (n - k))) (β := K)))
          (Access.extendImpl A _ impl sent.1)) chosen.2
        let result ← executeStrategies ambient (protocol K top d t rest).tree
          (protocol K top d t rest).roles (protocol K top d t rest).oracles
          (Access.extend A (OracleInterface.instFunction (α := Fin (2 ^ (n - k))) (β := K)))
          (Access.extendImpl A _ impl sent.1)
          (OutP := fun path => OutP ⟨chosen.1, sent.1, path⟩)
          (OutV := fun path => OutV ⟨chosen.1, PUnit.unit, path⟩) sent.2 after
        return ⟨⟨chosen.1, sent.1, result.1⟩, result.2.1, result.2.2⟩) := by
  refine (executeStrategies_public_receiver ambient (Moves := K)
    (rest := fun _ => TypeTree.oracle (Word K (n - k)) fun _ => (protocol K top d t rest).tree)
    _ _ A impl prover verifier).trans ?_
  simp only [executeStrategies_oracle, bind_assoc, pure_bind]
  rfl

/-! ### The honest prover -/

/-- The honest prover from a layer of log height `n` with current word `f`: it sends each fold of
the current word, injecting the inputs the schedule injects, and the final word's coefficients. -/
def honestProver (inputs : (m : ℕ) → Fin (2 ^ m) → K) :
    {n : ℕ} → SmoothCosetFftDomain n K → Word K n → (s : Schedule n) →
      Prover.Strategy ambient (protocol K top d t s).tree (protocol K top d t s).roles
        (fun _ => Unit)
  | _, ω, f, .final => pure ⟨finalCoeffs ω f d, fun _ => pure ()⟩
  | _, ω, f, .fold k hk inject rest => fun β =>
      let next := foldNext hk ω f β (injected inputs _ inject)
      pure (f := OracleComp ambient) (pure (f := OracleComp ambient)
        ⟨next, honestProver inputs (ω.subdomain k) next rest⟩)

end Fri.Interaction
