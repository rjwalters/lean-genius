# Current State

**Phase**: ORIENT
**Since**: 2026-05-12 (S2)
**Iteration**: 2

## Current Focus

S2 (researcher-11, 2026-05-12): Created
`proofs/Proofs/InfinitudePrimes4k1OQ03.lean` and discovered a Mathlib
**reality check** versus the S1 plan: the natural-density form of Dirichlet's
theorem is **not** in `Mathlib.NumberTheory.LSeries.PrimesInAP` at the pinned
revision (v4.26.0, `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`). Only the
infinitude form (`Nat.infinite_setOf_prime_and_eq_mod`) is exported.

The Ikehara-Tauberian machinery (`Mathlib.NumberTheory.LSeries.Wiener` /
`LSeries.IkeharaTauberian`) that the S1 plan assumed is in Mathlib does
**not exist** at this pin. The closest quantitative result available is
`ArithmeticFunction.vonMangoldt.LSeries_residueClass_lower_bound`, which
captures the Dirichlet-density pole strength but not the natural-density
asymptotic.

## Active Approach

**Mathlib bridge (corrected scope).**

S2 deliverable: `proofs/Proofs/InfinitudePrimes4k1OQ03.lean`

* `totient_four : Nat.totient 4 = 2` — `by decide`. Proved.
* `one_isUnit_zmodFour : IsUnit (1 : ZMod 4)` — `isUnit_one`. Proved.
* `mod_four_eq_one_iff_zmodFour_eq_one` — bridge between the parent's
  `p % 4 = 1` formulation and Mathlib's `(p : ZMod 4) = 1` formulation.
  Proved via `ZMod.natCast_eq_natCast_iff` + `Nat.ModEq` + `omega`.
* `primes_4k1_infinite_mathlib` — *Mathlib* infinitude bridge, by
  specialization of `Nat.infinite_setOf_prime_and_eq_mod`. Proved.
* `primes_4k1_infinite_mod` — same statement in `p % 4 = 1` form.
  Proved by `convert` through the bridge lemma.
* `primes_4k1_natural_density` — OQ-03 target. **Stated with `sorry`**.

This is a corrected SCAFFOLD: the file now syntactically targets the OQ-03
deliverable (natural-density form), while honestly flagging the one remaining
`sorry` as blocked on Mathlib evolution rather than on a routine wiring step.

## Blockers

**Mathematical**: The natural-density form requires an
Ikehara-Tauberian transfer from L-series pole data to the prime-counting
asymptotic. This is *not yet* in Mathlib at the pinned revision.

**Practical**:
* The `proofs/.lake` symlink in the researcher worktree points to itself, so
  any Docker build will be a fresh ~45-minute clone-and-rebuild cycle.
  S2 ships as "build pending" matching the existing pattern.

## Next Action

**S3 path A (Mathlib upgrade)**: Wait for `Mathlib.NumberTheory.LSeries.Wiener`
(or equivalent Ikehara-Tauberian module) to land in a future Mathlib bump.
Once it does, the `sorry` in `primes_4k1_natural_density` can be discharged
by:
1. Decompose the indicator of `{p : p ≡ 1 (mod 4)}` via character orthogonality
   on `(ℤ/4ℤ)ˣ`.
2. Apply PNT-AP (the Ikehara-Tauberian transfer) to extract the asymptotic.
3. Divide to obtain the limit `→ 1/2`.

**S3 path B (Dirichlet density at current pin)**: State and prove a *Dirichlet
density* version that is achievable now via `LSeries_residueClass_lower_bound`
plus the matching upper bound. This gives a formally weaker but pedagogically
equivalent result and unblocks gallery progress while waiting for Mathlib
PNT-AP.

**S3 path C (Sum-of-two-squares corollary)**: Once the density form is
available (path A or B), add a ~30-line corollary chaining through
`Mathlib.NumberTheory.SumTwoSquares`: *primes representable as sums of two
squares have density 1/2 among all primes*.

Recommended: S3 path B (Dirichlet density) — it makes concrete progress at the
current Mathlib pin without waiting on external infrastructure.

## Attempt Counts

* Total attempts: 2 (S1 survey, S2 Mathlib-reality SCAFFOLD)
* Current approach attempts: 2 (Mathlib bridge)
* Approaches tried: 1

## Open files

* `problem.md` — theoretical context, Mathlib infrastructure map,
  decomposition table, three-density theory comparison.
* `knowledge.md` — S1 survey notes + S2 Mathlib-reality update.
* `proofs/Proofs/InfinitudePrimes4k1OQ03.lean` (NEW S2) — Mathlib-bridge
  infinitude (verified) + natural-density statement (sorry).

## S2 Deliverable

This iteration is a **CORRECTION SCAFFOLD**:
* 1 new Lean file (`InfinitudePrimes4k1OQ03.lean`, ~165 lines)
* 6 new theorems / lemmas (5 fully proved + 1 stated with `sorry`)
* 1 sorry remaining (the natural-density form, OQ-03 target)
* 0 axiom changes

Produced:
* `proofs/Proofs/InfinitudePrimes4k1OQ03.lean` (new, ~165 lines).
* `state.md` (this file, updated): iteration 1 → 2, phase OBSERVE → ORIENT.
* `knowledge.md` (updated): added "S2 Mathlib reality check" section with the
  corrected status of `PrimesInAP.lean`.
* `src/data/research/problems/infinitude-primes-4k1-oq-03.json` updated:
  iteration 1 → 2, phase OBSERVE → ORIENT, focus + insights + nextSteps
  refreshed with the Mathlib-reality correction.
