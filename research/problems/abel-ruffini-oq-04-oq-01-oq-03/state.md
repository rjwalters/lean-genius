# Research State: abel-ruffini-oq-04-oq-01-oq-03

## Current State
**Phase**: ACT — generic Sylow-elim core done (arbitrary prime); abstract inversion step + huniq helper added
**Path**: full
**Since**: 2026-04-23T11:58:30+02:00
**Iteration**: 3
**Last Updated**: 2026-07-07 (researcher-7, S3 ACT)

## S3 ACT (researcher-7, 2026-07-07) — abstract involution step + huniq_of_lt, 0-axiom

Added the abstract form of the *final* `S₅`-specific bullet ("a transposition cannot
normalize a 5-cycle") to `Proofs/AbelRuffiniOQ04OQ01OQ03.lean`, unconditionally (0-axiom):
- `involution_conj_eq_self_or_inv` : under the `zpowers_sylow_normal` hypotheses
  (`⟨c⟩` normal of prime order `p`), any involution `g` (`g*g = 1`) conjugates `c` to
  `c` or `c⁻¹`. Proof: `g c g⁻¹ = c^k ∈ ⟨c⟩`; conjugating again with `g*g=1` gives
  `c^(k·k) = c`, so `k·k ≡ 1 (mod p)`; `p` prime ⇒ `p ∣ (1-k)(1+k)` ⇒ `k ≡ ±1 (mod p)`
  ⇒ `c^k = c` or `c⁻¹`. This is the abstract heart of the Abel–Ruffini contradiction;
  the *concrete* step then notes a genuine transposition conjugates a 5-cycle to a
  different 5-cycle, ruling out both — that part needs permutation structure and stays
  in the concrete proof.
- `huniq_of_lt` : reusable sufficient condition for the `huniq` divisor hypothesis — if
  `m < p` then the only divisor `d ∣ m` with `d ≡ 1 (mod p)` is `d = 1` (`d ≤ m < p`).
  Discharges `m = 2, 4` uniformly; the three `example`s for orders `10, 20` now use it,
  while `40 = 5·8` (`8 > 5`) still needs the divisibility explicitly (`6 ≡ 1 mod 5`, `6 ∤ 8`).

Docker build VERIFIED (`Proofs.AbelRuffiniOQ04OQ01OQ03`, 7743 jobs, EXIT 0; one cosmetic
`unnecessarySimpa` lint). File stays 0-sorry / 0-axiom. leanFile 4→6 theorems, 185→259 lines.

v4.26 gotchas hit: `Int.coe_nat_prime` REMOVED → use
`Int.prime_iff_natAbs_prime.mpr (by simpa using hp.out)`; name the `[hp : Fact p.Prime]`
instance to reach `hp.out`; exponent step via `zpow_eq_zpow_iff_modEq` + `Int.modEq_iff_dvd`.
INFRA: shared Mathlib volume corruption (line-less exit-135 + "invalid header" on
`Pow/Asymptotics.olean.private` and `Ring/Action/ConjAct.ir`) — fix = `rm` the named
corrupt file inside docker + `lake exe cache get!`, rebuild; rotates under concurrent load.

## Prior work (context)
- #35245 (researcher-11): factored `gal_card_ne_10/20/40` into generic `zpowers_order5_normal`.
- #35268 / oq-03-oq-01 (researcher-11): lifted the core from fixed prime 5 to arbitrary `p`
  (`zpowers_sylow_normal`, `conj_mem_zpowers_sylow`).

## Assessment
The parent goal — a single reusable Sylow-elimination lemma subsuming the three `private`
lemmas — is achieved and prime-generalized. This session adds the abstract inversion
consequence and an application-convenience helper. Remaining "open" content (a fully
abstract restatement tying back to `Polynomial.Gal` / permutation transpositions) needs
the permutation layer and is out of scope for this file's deliberately abstract design.

## Blockers
None (elementary group theory; the concrete `S₅` bridge is intentionally left to the
concrete Abel–Ruffini proof file).

## Attempt Count
- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0
