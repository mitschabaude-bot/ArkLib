/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.FiatShamir.PublicMessage
public import ArkLib.Interaction.Oracle.Security.StateRestorationRandomized

/-!
# Single-salt proof and induced restoration adversary

The rounds of a proof are a function of its statement. The public proof carries one global salt.
Repackaging the selected statement and proof gives the native restoration experiment input
`(statement, salt)`, whose rounds are the statement's rounds, and a complete sequence with trivial
per-round salts. This transformation runs no oracle query, so the adversary's ordered challenge
log and final lazy cache are identical, including when it returns failure.
-/

@[expose] public section

open Interaction.Oracle OracleComp OracleSpec

namespace Interaction.Oracle.FiatShamir

open Security.StateRestoration

/-- The rounds of a restoration input `(statement, salt)` are the statement's rounds. -/
abbrev saltedRounds (GlobalSalt : Type) {Statement : Type} (rounds : Statement → List Round) :
    Statement × GlobalSalt → List Round :=
  fun z => rounds z.1

/-- The challenge oracle of single-salt Fiat–Shamir: the restoration keys of `(statement, salt)`
inputs. -/
abbrev saltedSpec (Statement GlobalSalt : Type) (rounds : Statement → List Round) :=
  oracleSpec (Statement × GlobalSalt) PUnit (saltedRounds GlobalSalt rounds)

/-- A single global salt followed by every public prover message. -/
abbrev SaltedProof (GlobalSalt : Type) (rounds : List Round) :=
  GlobalSalt × PublicMessages rounds

/-- A malicious prover's selection: a statement, a salted proof for its rounds, and a terminal
witness. -/
abbrev SaltedSelection (Statement GlobalSalt Witness : Type) (rounds : Statement → List Round) :=
  (statement : Statement) × SaltedProof GlobalSalt (rounds statement) × Witness

/-- The output rearrangement of a malicious single-salt proof producer. -/
def toRestorationSelection {Statement GlobalSalt Witness : Type}
    {rounds : Statement → List Round} :
    Option (SaltedSelection Statement GlobalSalt Witness rounds) →
      Option (Selection (Statement × GlobalSalt) PUnit Witness (saltedRounds GlobalSalt rounds))
  | none => none
  | some ⟨statement, (salt, messages), witness⟩ =>
      some ⟨(statement, salt), withUnitSalts (rounds statement) messages, witness⟩

/-- The induced native restoration adversary shares the typed challenge oracle verbatim. -/
def inducedAdversary {Statement GlobalSalt Witness : Type} {rounds : Statement → List Round}
    (adversary : OracleComp
      (unifSpec + saltedSpec Statement GlobalSalt rounds)
      (Option (SaltedSelection Statement GlobalSalt Witness rounds))) :
    RandomizedRestorationAdversary (Statement × GlobalSalt) PUnit Witness
      (saltedRounds GlobalSalt rounds) :=
  toRestorationSelection <$> adversary

/-- Output mapping does not change the ordered oracle log or the final lazy cache. -/
theorem inducedAdversary_loggedRun {Statement GlobalSalt Witness : Type}
    {rounds : Statement → List Round} [DecidableEq Statement] [DecidableEq GlobalSalt]
    (adversary : OracleComp
      (unifSpec + saltedSpec Statement GlobalSalt rounds)
      (Option (SaltedSelection Statement GlobalSalt Witness rounds)))
    (cache : (saltedSpec Statement GlobalSalt rounds).QueryCache) :
    randomOracleLoggedRun (inducedAdversary adversary) cache =
      (fun result => ((toRestorationSelection result.1.1, result.1.2), result.2)) <$>
        randomOracleLoggedRun adversary cache := by
  exact randomOracleLoggedRun_map _ adversary cache

end Interaction.Oracle.FiatShamir
