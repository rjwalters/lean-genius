# Current State

**Phase**: ACT (S2 SCAFFOLD landed)
**Since**: 2026-05-12T12:50:00Z
**Iteration**: 2

## Current Focus

S2 SCAFFOLD — **Tetrahedral refutation infrastructure landed.** Created
`proofs/Proofs/KeplerConjectureOQ04.lean` (120 lines, 0 sorries, 0
axioms, 1 def + 3 theorems) and wired it into `proofs/Proofs.lean`.
Gallery entry registered at `src/data/proofs/kepler-conjecture-oq-04/`.

The new file introduces

  `tetrahedronDimerDensity : ℝ := 4000 / 4671`

— the Chen–Engel–Glotzer (2010) tetrahedral dimer packing density,
`≈ 0.8563` — and discharges three basic real-number bounds via
`norm_num`:

1. `tetrahedronDimerDensity_pos`        : `0 < tetrahedronDimerDensity`
2. `tetrahedronDimerDensity_lt_one`     : `tetrahedronDimerDensity < 1`
3. `tetrahedronDimerDensity_gt_8563`    : `(8563 : ℝ) / 10000 < tetrahedronDimerDensity`
   (Chen–Engel–Glotzer literature anchor in rational form, independent
   of `π` and `Real.sqrt 2`)

This delivers the S2 milestone laid out in the S1 OBSERVE plan
(PR #18043, researcher-5) and prepares the API surface for the S3
numerical inequality `tetrahedronDimerDensity > fccDensity`, which
will refute shape-universality of the Kepler upper bound — namely, by
exhibiting a value of the parent `PackingDensity.density` type
strictly above `fccDensity`.

### Build status

**Build verification pending.** The proof file uses only `norm_num`
plus the standard `Mathlib` import, so the build should succeed cleanly.
Docker build to be triggered as a follow-up; per the `proofs/.lake`
symlink trap (memory: `feedback_researcher_lake_symlink_broken.md`),
plan ≥ 45 min for the fresh-clone Mathlib + cache get. Per the
build-pending precedent of similar S2 SCAFFOLD PRs across the gallery,
this PR is submitted as "(build pending)" for deployer verification.

### Stats

- New file: `proofs/Proofs/KeplerConjectureOQ04.lean` (120 lines).
- New gallery entry: `src/data/proofs/kepler-conjecture-oq-04/` (meta.json,
  annotations.json, index.ts).
- New definitions: 1 (`tetrahedronDimerDensity`).
- New theorems: 3 (positivity, less-than-one, rational literature anchor).
- New sorries: 0.
- New axioms: 0.
- Wired into `proofs/Proofs.lean` import list.

## Previous focus (S1 — three-flagship survey)

S1 OBSERVE (PR #18043, researcher-5) — Initial survey of the three
flagship non-spherical packing sub-questions:

1. Tetrahedral packing (Chen–Engel–Glotzer 2010: `δ ≥ 4000/4671`).
2. Ellipsoid packing (Donev–Stillinger–Chaikin–Torquato 2004:
   `δ ≈ 0.7707`; Bezdek–Kuperberg 2007 lattice case `= π/(3√2)`).
3. Ulam's conjecture (1972, open): every symmetric convex body in
   `ℝ³` packs with density `≥ π/(3√2)`; the unit ball is the LEAST
   dense convex body to pack.

S1 was documentation-only (`problem.md` + `knowledge.md`, no Lean
changes); the S2 SCAFFOLD (this iteration) is the first iteration to
add Lean code.

## Active Approach

**Tetrahedral refutation first — axiom-free deliverable.**

The cleanest formalisable result is `4000/4671 > π/(3√2)` — a pure
real-number numerical computation provable using `Real.pi_lt_315`
without any new axioms. This establishes that the parent's
`PackingDensity` type admits values strictly above `fccDensity`,
demonstrating that the Kepler upper bound is **shape-specific**
(spheres only) rather than universal.

The ellipsoid and Ulam statements (S4/S5) are deferred to later
sessions and require axiomatization, since their proofs are
respectively (a) a substantial published theorem (Bezdek–Kuperberg)
and (b) genuinely open since 1972 (Ulam).

## Blockers

None mathematical. Practical: the `proofs/.lake` symlink trap in
researcher worktrees still costs ~30–45 min per Docker build; S3 is
short enough that one end-of-S3 Docker build is feasible.

## Next Action

**S3 (next iteration)**: prove the numerical inequality
`tetrahedronDimerDensity_gt_fccDensity`.

Sketch (~50 lines):

```lean
theorem tetrahedronDimerDensity_gt_fccDensity :
    fccDensity < tetrahedronDimerDensity := by
  -- 4000/4671 > π/(3√2)
  -- ⇔ 12000 * Real.sqrt 2 > 4671 * π   (both sides > 0)
  -- ⇐ (12000)^2 * 2 > 4671^2 * π^2   (square, both > 0)
  -- ⇔ 288_000_000 > 21_818_241 * π^2
  -- ⇐ π^2 < 13.2002
  -- ⇐ π < 3.15 (Real.pi_lt_315) so π^2 < 9.9225 < 13.2002
  …
```

Key Mathlib lemmas:
- `Real.pi_lt_315`         (or `Real.pi_lt_3141593`)
- `Real.sq_sqrt`           (for `(Real.sqrt 2)^2 = 2`)
- `Real.sqrt_nonneg`
- `mul_pos`, `div_lt_div_iff`, `pow_lt_pow_left`
- `nlinarith` for the final squaring step

After S3 lands, the gallery's `PackingDensity` type will witness a
density strictly above `fccDensity` — clean axiom-free refutation of
shape-universality.

**S4 (followup)**: ellipsoid axioms and statements (Donev–Stillinger
+ Bezdek–Kuperberg). Requires careful axiomatization of "ellipsoid
packing" since Mathlib has no `Ellipsoid` type.

**S5 (followup)**: Ulam conjecture statement. Open since 1972 —
will require axiomatization of the symmetric-convex-body type and
the conjecture itself as an `axiom`.

## Attempt Counts

- Total attempts: 2 (S1 OBSERVE, S2 SCAFFOLD).
- Current approach attempts: 1 (tetrahedral refutation track).
- Approaches tried:
  - S1: survey-only, no Lean changes (PR #18043, researcher-5).
  - S2: SCAFFOLD — `tetrahedronDimerDensity` + positivity / bound /
    Chen–Engel–Glotzer literature anchor; gallery entry + import
    wiring (this iteration, researcher-11).

## Open files

- `proofs/Proofs/KeplerConjectureOQ04.lean` — **new in S2** (120 lines):
  one definition (`tetrahedronDimerDensity`), three theorems
  (positivity, less-than-one, Chen–Engel–Glotzer literature anchor),
  0 sorries, 0 axioms.
- `src/data/proofs/kepler-conjecture-oq-04/` — **new in S2**:
  gallery entry (meta.json + annotations.json + index.ts).
- `problem.md` — Plain statement, why-it-matters, Mathlib infrastructure
  map, S2-through-S7 decomposition, risk notes, references.
- `knowledge.md` — S1 session note: tetrahedral refutation arithmetic
  (worked out in detail), Ulam conjecture context, worked numerics,
  Mathlib gap inventory, next-action priority table.
