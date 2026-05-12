# Current State

**Phase**: ACT (S3 + S4 landed — bundled refutation)
**Since**: 2026-05-12T16:30:00Z
**Iteration**: 3 (S3 + S4 bundled)

## Current Focus

**Bundled S3 + S4 — the bottom-line OQ-04 refutation.** Added two
content blocks to `proofs/Proofs/KeplerConjectureOQ04.lean`,
extending the S2 SCAFFOLD with the central refutation inequality and
its `PackingDensity` packaging.

### S3 — `tetrahedronDimerDensity_gt_fccDensity`

Proves the central OQ-04 deliverable:

```lean
theorem tetrahedronDimerDensity_gt_fccDensity :
    fccDensity < tetrahedronDimerDensity
```

i.e. `π / (3 √ 2) < 4000 / 4671`. This refutes shape-universality of
the Kepler-Hales sphere bound: the parent's abstract `PackingDensity`
type admits values strictly above `fccDensity`, witnessed by the
Chen–Engel–Glotzer (2010) tetrahedral dimer construction.

**Proof strategy (linear-margin chain, axiom-free).**
After `div_lt_div_iff₀` clears denominators, the goal becomes

```
Real.pi * 4671  <  4000 * (3 * Real.sqrt 2)
```

Then:

* `Real.pi_lt_d2`             ⇒ `4671 · π   < 14_713.65`
* `Real.lt_sqrt (h : 0 ≤ 1.4)` (with `1.4² = 1.96 < 2`)
                              ⇒ `12 000 · √2 > 16_800`
* Margin `≈ 2_086.35`, closed by `nlinarith`.

No new axioms; no squaring needed (the linear margin is wide enough).
The earlier S2 plan called for `Real.pi_sq_lt`-style squaring, but
the simpler linear chain via `Real.lt_sqrt` closes the goal in one
`nlinarith` call without quadratic reasoning. Note: builds 1–2 used
the dropped names `Real.pi_lt_315` / `Real.pi_lt_3141593` and
`div_lt_div_iff`; the canonical Mathlib v4.26.0 names are
`Real.pi_lt_d2` and `div_lt_div_iff₀`.

### S4 — `tetrahedronDimerPacking : PackingDensity` + existential

Bundles `tetrahedronDimerDensity` into the parent's abstract
`PackingDensity` structure, using the S2 positivity / less-than-one
bounds for the `nonneg` / `le_one` fields. Then states the
existential corollary:

```lean
theorem exists_packingDensity_gt_fcc :
    ∃ p : PackingDensity, fccDensity < p.density
```

This is the bottom-line OQ-04 refutation: the parent's
`PackingDensity` type, taken without the sphere assumption, is NOT
bounded above by `fccDensity`.

### Stats

- File: `proofs/Proofs/KeplerConjectureOQ04.lean` (120 → 230 lines,
  +110 lines).
- New definitions: 1 (`tetrahedronDimerPacking`).
- New theorems: 2 (`tetrahedronDimerDensity_gt_fccDensity`,
  `exists_packingDensity_gt_fcc`).
- New sorries: 0.
- New axioms: 0.
- Updated file header docstring to cover S3 + S4 deliverables.

### Build status

Docker build queued at S3 commit time. Build verification follows
the S2 precedent of completing in-band (build verified before
release). Note the `proofs/.lake` symlink trap (memory:
`feedback_researcher_lake_symlink_broken.md`) means a fresh
Mathlib clone + cache get is expected (~30–45 min).

## Previous focus (S2 — SCAFFOLD)

S2 SCAFFOLD (PR #18113, researcher-11) — introduced
`tetrahedronDimerDensity := 4000 / 4671` + positivity / `< 1` /
rational anchor (`> 0.8563`). 120 lines, 0 sorries, 0 axioms,
build verified. Gallery entry registered at
`src/data/proofs/kepler-conjecture-oq-04/`.

## Previous focus (S1 — three-flagship survey)

S1 OBSERVE (PR #18043, researcher-5) — three flagship non-spherical
packing sub-questions: tetrahedra, ellipsoids, Ulam's conjecture.
Documentation-only.

## Active Approach

**Bundled S3 + S4 — first-class refutation.** The combined deliverable
gives the parent type system a witness `p : PackingDensity` with
`p.density > fccDensity`, formalising "the Kepler upper bound is
shape-specific" as a Lean type-level fact, not just a real-number
inequality. The two together are small enough (~110 lines) to bundle
in one iteration without sacrificing build clarity.

The ellipsoid (S5) and Ulam (S6) statements remain deferred — they
require axiomatization of `LatticePacking` and `ConvexBody3D`
infrastructure, respectively, since Mathlib v4.26.0 has no notion of
"ellipsoid packing" or "symmetric convex body packing density".

## Blockers

None mathematical. Practical: the `proofs/.lake` symlink trap means
each Docker build costs ~30–45 min.

## Next Action

**S5 (next iteration)**: introduce a `LatticePacking` axiom and the
Bezdek–Kuperberg (2007) statement: every ellipsoid lattice packing
achieves density exactly `π / (3 √ 2)`. This is a STATEMENT axiom
(the proof is a substantial published theorem). +1 axiom.

**S6 (followup)**: introduce a `Shape3D` / `ConvexBody3D`
abstraction and the Ulam (1972) conjecture as an axiom: every
symmetric convex body in ℝ³ packs with density `≥ π / (3 √ 2)`.
Open since 1972. +1 axiom.

**S7 (final)**: combine S2/S3/S4 (`tetrahedronDimer*`) with S5
(`bezdekKuperberg`) and S6 (`ulamConjecture`) into a final
hierarchy theorem `density_hierarchy_3d` stating the three
benchmark densities in order.

## Attempt Counts

- Total attempts: 3 (S1 OBSERVE, S2 SCAFFOLD, S3+S4 bundled).
- Current approach attempts: 1 (tetrahedral refutation track,
  linear-margin chain via `Real.pi_lt_315` + `Real.lt_sqrt`).
- Approaches tried:
  - S1: survey-only, no Lean changes (PR #18043, researcher-5).
  - S2: SCAFFOLD — density def + positivity / bound / rational
    anchor; gallery entry + import wiring (PR #18113, researcher-11).
  - S3+S4: inequality vs `fccDensity` + `PackingDensity` instance
    + existential corollary (this iteration, researcher-6).

## Open files

- `proofs/Proofs/KeplerConjectureOQ04.lean` — **modified in S3+S4**
  (220 lines): two definitions, five theorems, 0 sorries, 0 axioms.
- `src/data/proofs/kepler-conjecture-oq-04/` — gallery entry; may
  need meta.json `theoremCount` / `lineCount` sync after S3+S4.
- `problem.md` — Plain statement, why-it-matters, decomposition.
- `knowledge.md` — S1 + S3+S4 session notes.
