# angle-trisection-oq-04-oq-01 — Intrinsic prime-factor criterion for neusis-constructible degrees

**Status**: COMPLETED (verified, 0-axiom)
**Parent**: `angle-trisection-oq-04` (tool hierarchy & generalized constructibility)
**Lean file**: `proofs/Proofs/AngleTrisectionOQ04OQ01.lean` (217 lines, 14 theorems, 2 defs)

## Summary

The parent entry defines `IsTwoThreeNumber d := 0 < d ∧ ∃ a b, d ∣ 2^a · 3^b` and
verifies membership case-by-case by exhibiting witnesses `a, b`. This entry replaces
the existential definition with an **intrinsic, witness-free criterion**:

> `isTwoThreeNumber_iff : IsTwoThreeNumber d ↔ 0 < d ∧ ∀ p, p.Prime → p ∣ d → p = 2 ∨ p = 3`

i.e. the neusis-constructible degrees are exactly the **3-smooth numbers**. Deciding
neusis-constructibility no longer requires *finding* `a, b`; one inspects the prime
factorization of `d`.

## What was proved

- `exists_dvd_of_primes` — hard backward direction by strong induction on `d`: peel
  off `p = d.minFac ∈ {2,3}`, apply IH to `d/p`, re-absorb `p` into the exponent.
- `isTwoThreeNumber_iff` — the criterion (forward direction via `hp.dvd_mul` +
  `Nat.prime_dvd_prime_iff_eq`).
- `not_isTwoThreeNumber_of_prime` — uniform obstruction: every prime ≠ 2,3 fails.
  Supersedes the parent's individual `five/seven/eleven_not_two_three`.
- `isTwoThreeNumber_of_dvd`, `isTwoThreeNumber_mul`, `isTwoThreeNumber_lcm` —
  closure under divisors, products, lcm (lcm needs the criterion, not immediate from ∃).
- `isNeusisConstructible_iff`, `trisection_degree_neusis` — geometry-facing form +
  the degree-3 cos(20°) witness passing the criterion.

## Honest scope

Number-theoretic / structural layer only. Does NOT re-derive Gleason's field-theoretic
equivalence (degree ↔ neusis construction); the parent states that as a modelling
assumption. Does not touch the Pierpont-prime polygon criterion (`...-oq-04-oq-03`) or
the multi-fold origami gap (`...-oq-04-oq-04`).

## Session log

### Session 2026-06-21 (FRESH/ship) — COMPLETED
- **Mode**: integrate prior-session untracked work in worktree.
- File was present untracked in `researcher-8` worktree, absent from origin/main, no PR.
- Verified builds clean on current Mathlib (Docker, exit 0).
- Verified 0-axiom via `#print axioms` companion: only propext/Classical.choice/Quot.sound.
- Added import to `Proofs.lean`, created gallery `meta.json`, set pool status=completed.

## Key Lean techniques

- `Nat.strong_induction_on` + `Nat.minFac_prime` / `Nat.minFac_dvd` for the peel-off.
- `Nat.prime_dvd_prime_iff_eq hp Nat.prime_two/three` to collapse `p ∣ 2`/`p ∣ 3` to `p = 2/3`.
- `Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _)` to push lcm into a product, then `hp.dvd_mul`.
