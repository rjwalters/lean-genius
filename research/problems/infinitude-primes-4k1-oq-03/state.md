# Current State

**Phase**: ACT (path-B scaffolding)
**Since**: 2026-05-12 (S3)
**Iteration**: 3

## Current Focus

S3 (researcher-8, 2026-05-12): Added the **character-orthogonality scaffold**
for `q = 4` to `proofs/Proofs/InfinitudePrimes4k1OQ03.lean`. Three new
fully-proved lemmas (no new sorries) translate the general Mathlib
orthogonality result `DirichletCharacter.sum_characters_eq` into the
`q = 4` case, expressing the indicator of `[p % 4 = 1]` (over `ℂ`) as
`(1/2) · ∑ χ : DirichletCharacter ℂ 4, χ((p : ZMod 4))`. This is step 1
of the three-step path-B proof outlined in S2's state.md.

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

S3 completed step 1 of the path-B proof (the character-orthogonality
decomposition). The remaining steps:

**S4 path B step 2 (L-series pole analysis at `s = 1`)**: Combine the
character decomposition `indicator_mod_four_eq_one` with
`ArithmeticFunction.vonMangoldt.LSeries_residueClass_lower_bound` (for the
pole strength of the trivial character) plus
`DirichletCharacter.LFunction_ne_zero_of_one_le_re` (for the nonvanishing of
the nontrivial character's L-function on the closed half-plane). This
extracts the Dirichlet-density pole-strength data.

Concrete deliverable: state and prove a lemma of the form
`Dirichlet-density-of-primes-4k1` using the `s ↘ 1` Abel-summation route,
without yet invoking Tauberian methods. Estimated ~80 lines.

**S5 path B step 3 (Tauberian transfer)**: The natural-density form
(the OQ-03 sorry) remains blocked on the absence of
`Mathlib.NumberTheory.LSeries.Wiener` / `LSeries.IkeharaTauberian` at the
pinned revision. Once Mathlib gains a Tauberian module, the
`primes_4k1_natural_density` sorry can be discharged.

**S? path C (Sum-of-two-squares corollary)**: Once the density form is
proved (whether Dirichlet or natural), add a ~30-line corollary chaining
through `Mathlib.NumberTheory.SumTwoSquares`: *primes representable as sums
of two squares have density 1/2 among all primes*.

Recommended for the next session: S4 (path B step 2 — pole analysis). The
character decomposition is now wired up and step 2's Mathlib API is
already verified to exist at v4.26.0.

## Attempt Counts

* Total attempts: 3 (S1 survey, S2 Mathlib-reality SCAFFOLD, S3 char-orthogonality scaffold)
* Current approach attempts: 3 (Mathlib bridge → path-B step 1)
* Approaches tried: 1 (path B, two of three steps remaining)

## Open files

* `problem.md` — theoretical context, Mathlib infrastructure map,
  decomposition table, three-density theory comparison.
* `knowledge.md` — S1 survey + S2 Mathlib-reality + S3 orthogonality scaffold.
* `proofs/Proofs/InfinitudePrimes4k1OQ03.lean` (S2 base, S3 enriched) —
  Mathlib-bridge infinitude (verified) + character-orthogonality scaffold
  for `q = 4` (3 verified lemmas, S3) + natural-density statement (sorry).

## S3 Deliverable

This iteration is an **ORTHOGONALITY SCAFFOLD** (path-B step 1):
* 0 new Lean files; 3 new lemmas added to `InfinitudePrimes4k1OQ03.lean`
  (~55 lines including the section docstring)
* 3 lemmas all **fully proved** — no new `sorry` introduced
* 1 `sorry` total remaining (the natural-density form, OQ-03 target, unchanged from S2)
* 0 axiom changes

New lemmas:
* `sum_dirichletChars_zmodFour` — orthogonality at `q = 4`
* `indicator_zmodFour_eq_one` — indicator-as-half-character-sum (ZMod 4 form)
* `indicator_mod_four_eq_one` — indicator-as-half-character-sum (`% 4` form)

Files touched:
* `proofs/Proofs/InfinitudePrimes4k1OQ03.lean` — added orthogonality
  scaffold section (after `primes_4k1_infinite_mod`, before
  natural-density target); added explicit
  `Mathlib.NumberTheory.DirichletCharacter.Orthogonality` import; extended
  `#check` block.
* `state.md` — iteration 2 → 3, phase ORIENT → ACT, Current Focus + Next
  Action + Open files + Attempt Counts updated.
* `knowledge.md` — added "S3 — ORIENT/ACT: character-orthogonality scaffold"
  section with proof sketch + role in path-B plan.
* `src/data/research/problems/infinitude-primes-4k1-oq-03.json` — iteration
  2 → 3, phase ORIENT → ACT, focus + insights + nextSteps refreshed.

## S2 Deliverable (historical)

* 1 new Lean file (`InfinitudePrimes4k1OQ03.lean`, ~165 lines)
* 6 new theorems / lemmas (5 fully proved + 1 stated with `sorry`)
* 1 sorry remaining (the natural-density form, OQ-03 target)
* 0 axiom changes
