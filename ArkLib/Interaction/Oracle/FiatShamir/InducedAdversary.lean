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

The protocol of a proof is a function of its statement. The public proof carries one global salt.
Repackaging the selected statement and proof gives the native restoration experiment input
`(statement, salt)`, whose protocol is the statement's protocol, and the proof's messages with
their trivial per-challenge salts. This transformation runs no oracle query, so the adversary's
ordered challenge log and final lazy cache are identical, including when it returns failure.
-/

@[expose] public section

open Interaction.Oracle OracleComp OracleSpec

namespace Interaction.Oracle.FiatShamir

open Security.StateRestoration

/-- The protocol of a restoration input `(statement, salt)` is the statement's protocol. -/
abbrev saltedProtocol (GlobalSalt : Type) {Statement : Type} (protocol : Statement → Protocol) :
    Statement × GlobalSalt → Protocol :=
  fun z => protocol z.1

/-- The public-coin presentation of a restoration input `(statement, salt)` is the statement's. -/
abbrev saltedCoin (GlobalSalt : Type) {Statement : Type} {protocol : Statement → Protocol}
    (coin : (statement : Statement) → PublicCoin (protocol statement)) :
    (z : Statement × GlobalSalt) → PublicCoin (saltedProtocol GlobalSalt protocol z) :=
  fun z => coin z.1

/-- The challenge oracle of single-salt Fiat–Shamir: the restoration keys of `(statement, salt)`
inputs. -/
abbrev saltedSpec (Statement GlobalSalt : Type) {protocol : Statement → Protocol}
    (coin : (statement : Statement) → PublicCoin (protocol statement)) :=
  oracleSpec (Statement × GlobalSalt) PUnit (saltedCoin GlobalSalt coin)

/-- A single global salt followed by every public prover message. -/
abbrev SaltedProof (GlobalSalt : Type) {protocol : Protocol} (coin : PublicCoin protocol) :=
  GlobalSalt × Messages PUnit coin

/-- A malicious prover's selection: a statement, a salted proof for its protocol, and a terminal
witness. -/
abbrev SaltedSelection (Statement GlobalSalt Witness : Type) {protocol : Statement → Protocol}
    (coin : (statement : Statement) → PublicCoin (protocol statement)) :=
  (statement : Statement) × SaltedProof GlobalSalt (coin statement) × Witness

/-- The output rearrangement of a malicious single-salt proof producer. -/
def toRestorationSelection {Statement GlobalSalt Witness : Type} {protocol : Statement → Protocol}
    {coin : (statement : Statement) → PublicCoin (protocol statement)} :
    Option (SaltedSelection Statement GlobalSalt Witness coin) →
      Option (Selection (Statement × GlobalSalt) PUnit Witness (saltedCoin GlobalSalt coin))
  | none => none
  | some ⟨statement, (salt, messages), witness⟩ => some ⟨(statement, salt), messages, witness⟩

/-- The induced native restoration adversary shares the typed challenge oracle verbatim. -/
def inducedAdversary {Statement GlobalSalt Witness : Type} {protocol : Statement → Protocol}
    {coin : (statement : Statement) → PublicCoin (protocol statement)}
    (adversary : OracleComp
      (unifSpec + saltedSpec Statement GlobalSalt coin)
      (Option (SaltedSelection Statement GlobalSalt Witness coin))) :
    RandomizedRestorationAdversary (Statement × GlobalSalt) PUnit Witness
      (saltedCoin GlobalSalt coin) :=
  toRestorationSelection <$> adversary

/-- Output mapping does not change the ordered oracle log or the final lazy cache. -/
theorem inducedAdversary_loggedRun {Statement GlobalSalt Witness : Type}
    {protocol : Statement → Protocol}
    {coin : (statement : Statement) → PublicCoin (protocol statement)}
    [DecidableEq Statement] [DecidableEq GlobalSalt]
    (adversary : OracleComp
      (unifSpec + saltedSpec Statement GlobalSalt coin)
      (Option (SaltedSelection Statement GlobalSalt Witness coin)))
    (cache : (saltedSpec Statement GlobalSalt coin).QueryCache) :
    randomOracleLoggedRun (inducedAdversary adversary) cache =
      (fun result => ((toRestorationSelection result.1.1, result.1.2), result.2)) <$>
        randomOracleLoggedRun adversary cache := by
  exact randomOracleLoggedRun_map _ adversary cache

end Interaction.Oracle.FiatShamir
