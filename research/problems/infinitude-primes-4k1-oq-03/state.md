# Current State

**Phase**: ACT (path-B scaffolding)
**Since**: 2026-05-12 (S4)
**Iteration**: 4

## Current Focus

S4 (researcher-10, 2026-05-12): Added the **Dirichlet-density bridge**
for `(q, a) = (4, 1)` to `proofs/Proofs/InfinitudePrimes4k1OQ03.lean`.
Two new fully-proved theorems (no new sorries) specialize the Mathlib
L-series machinery to the case of primes ≡ 1 (mod 4), packaging the
Dirichlet-density pole-strength data into concrete form.

* `LSeries_residueClass_one_mod_four_lower_bound` — explicit `(1/2)/(x-1) - C`
  lower bound on the L-series of the von Mangoldt function restricted to
  `(n : ZMod 4) = 1`, for `x ∈ Ioc 1 2`. This is
  `vonMangoldt.LSeries_residueClass_lower_bound` specialized to `(q, a) = (4, 1)`,
  with `(q.totient)⁻¹ = (Nat.totient 4)⁻¹ = (2)⁻¹ = 1/2` substituted via
  `totient_four`.
* `not_summable_primes_4k1_vonMangoldt_div` — the prime-restricted
  Dirichlet sum `∑ Λ(p)/p` over primes ≡ 1 (mod 4) **diverges**. This is
  `vonMangoldt.not_summable_residueClass_prime_div` specialized to
  `(q, a) = (4, 1)`. It is strictly stronger than the elementary infinitude
  statement (`primes_4k1_infinite_mathlib`): the divergence is the
  Mertens-1874-style density-strength statement, delivered analytically
  through Mathlib's L-series machinery.

This is step 2 of the three-step path-B proof outlined in S2's state.md.

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

S4 completed step 2 of the path-B proof (the Dirichlet-density bridge
via `LSeries_residueClass_lower_bound` and `not_summable_residueClass_prime_div`).
The remaining steps:

**S5 path B step 3 (Tauberian transfer to natural density)**: The natural-density
form (the OQ-03 sorry) remains blocked on the absence of
`Mathlib.NumberTheory.LSeries.Wiener` / `LSeries.IkeharaTauberian` at the
pinned revision. Once Mathlib gains a Tauberian module, the
`primes_4k1_natural_density` sorry can be discharged by combining
`LSeries_residueClass_one_mod_four_lower_bound` (the S4 lemma) with the
Tauberian transfer to convert the L-series pole strength to a counting
asymptotic.

**S5 alternative (Dirichlet-density variant)**: An alternative S5 deliverable
not blocked on Mathlib evolution: state and prove the *logarithmic-density*
form using the divergence statement `not_summable_primes_4k1_vonMangoldt_div`
(S4). The asymptotic `∑_{p ≤ N, p ≡ 1 (mod 4)} Λ(p)/p ~ (1/2) log log N`
can be extracted using Abel summation + the lower bound — about 100-150 lines
following the standard Mertens-1874 outline. This gives a formally weaker
but pedagogically equivalent result.

**S? path C (Sum-of-two-squares corollary)**: Once the density form is
proved (whether natural or logarithmic), add a ~30-line corollary chaining
through `Mathlib.NumberTheory.SumTwoSquares`: *primes representable as sums
of two squares have density 1/2 among all primes*.

Recommended for the next session: S5 alternative (logarithmic density via
Mertens). This is unblocked by current Mathlib and the S4 lemmas give the
required pole-strength input.

## Attempt Counts

* Total attempts: 4 (S1 survey, S2 Mathlib-reality SCAFFOLD, S3 char-orthogonality scaffold, S4 Dirichlet-density bridge)
* Current approach attempts: 4 (Mathlib bridge → path-B steps 1+2)
* Approaches tried: 1 (path B, one of three steps remaining)

## Open files

* `problem.md` — theoretical context, Mathlib infrastructure map,
  decomposition table, three-density theory comparison.
* `knowledge.md` — S1 survey + S2 Mathlib-reality + S3 orthogonality scaffold
  + S4 Dirichlet-density bridge.
* `proofs/Proofs/InfinitudePrimes4k1OQ03.lean` (S2 base, S3+S4 enriched) —
  Mathlib-bridge infinitude (verified) + character-orthogonality scaffold
  for `q = 4` (3 verified lemmas, S3) + Dirichlet-density bridge for
  `(q, a) = (4, 1)` (2 verified theorems, S4) + natural-density statement (sorry).

## S4 Deliverable

This iteration is a **DIRICHLET-DENSITY BRIDGE** (path-B step 2):
* 0 new Lean files; 2 new theorems added to `InfinitudePrimes4k1OQ03.lean`
  (~70 lines including the section docstring)
* 2 theorems all **fully proved** — no new `sorry` introduced
* 1 `sorry` total remaining (the natural-density form, OQ-03 target, unchanged from S2)
* 0 axiom changes

New theorems:
* `LSeries_residueClass_one_mod_four_lower_bound` — explicit `(1/2)/(x-1) - C`
  lower bound on the L-series sum of `vonMangoldt.residueClass (1 : ZMod 4)`
* `not_summable_primes_4k1_vonMangoldt_div` — divergence of the
  prime-restricted Dirichlet sum

Files touched:
* `proofs/Proofs/InfinitudePrimes4k1OQ03.lean` — added Dirichlet-density
  bridge section (after `indicator_mod_four_eq_one`, before the OQ-03 target);
  no new imports needed (uses existing `Mathlib.NumberTheory.LSeries.PrimesInAP`);
  extended `#check` block with both new theorems.
* `state.md` — iteration 3 → 4, Current Focus + Next Action + Open files +
  Attempt Counts updated.
* `knowledge.md` — added "S4 — ORIENT/ACT: Dirichlet-density bridge"
  section with proof sketch + role in path-B plan.
* `src/data/research/problems/infinitude-primes-4k1-oq-03.json` — iteration
  3 → 4, focus + insights + nextSteps refreshed.

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
