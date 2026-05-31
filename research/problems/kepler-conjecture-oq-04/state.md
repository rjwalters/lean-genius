# Current State

**Phase**: ACT (S7 landed — final hierarchy aggregation `density_hierarchy_3d`, no new axioms)
**Since**: 2026-05-31T07:10:00Z (S7 ACT, this iteration)
**Iteration**: 6 (S7 — `density_hierarchy_3d`)

## Iteration 6 (researcher-1, 2026-05-31)

**Focus**: S7 — final hierarchy aggregation. Per the prior iteration's
"Next Action" block, this ships a pure `And.intro` aggregation of the
three benchmark facts proved across S3+S4 (axiom-free), S5 (Bezdek–
Kuperberg axiom), and S6 (Ulam axiom). No new axioms expected; closes
the OQ-04 hierarchy as a single quantified theorem.

### Outcome (1 new theorem, 0 new axioms)

Added to `proofs/Proofs/KeplerConjectureOQ04.lean` (399 → 456 lines,
+57):

* **`theorem density_hierarchy_3d`** — for every `EllipsoidLatticePacking e`
  and `SymmetricConvexBody3DPacking p`:
  ```
  e.density ≤ fccPacking.density ∧
  fccDensity < tetrahedronDimerDensity ∧
  fccPacking.density ≤ p.density
  ```
  Pure `And.intro` over `ellipsoid_lattice_le_fccPacking e`,
  `tetrahedronDimerDensity_gt_fccDensity`, and
  `ulam_le_fccPacking_density p`. No new axioms.
* Header docstring updated: now lists S7 ACT description, `theoremCount`
  7 → 8 (mechanic to sync after CI green).

### Hierarchy now formalised (after S7 ACT)

| Side | k = 0 lattice | k > 0 lattice | non-lattice |
|---|---|---|---|
| Sphere | `fccDensity = π/(3√2)` (Gauss 1831, parent axiom) | — | `kepler_conjecture` (Hales 1998, parent axiom) |
| Tetrahedron | — | `tetrahedronDimerDensity > fccDensity` (S3, axiom-free) | construction is non-lattice; gallery records as the bottom-line refutation |
| Ellipsoid | `bezdek_kuperberg_…_upper_bound` (S5, +1 axiom) | — | Donev et al. δ ≈ 0.7707 (deferred, S8+) |
| Centrally symmetric convex body | — | — | `ulam_conjecture` (S6, +1 axiom — OPEN since 1972) |

**S7 `density_hierarchy_3d`** quantifies over `(e, p)` and aggregates
the three shape-dependent benchmarks into a single theorem,
realising the bottom-line OQ-04 conclusion: the FCC bound is *neither
universal nor optimal* across shape classes.

### Counts (build verified pending Docker)

* `proofs/Proofs/KeplerConjectureOQ04.lean`: **399 → 456** lines (+57).
* `theoremCount`: 7 → 8 (+1; mechanic to sync after CI green).
* `axiomCount`: 2 (unchanged).
* `defCount`: 4 (unchanged).
* `lineCount`: 399 → 456 (mechanic to sync).
* `sorries`: 0 (unchanged).

**meta.json deliberately unchanged** in this PR, mirroring the
S3+S4, S5, S6 build-verified convention.

### Build status

**Build verified.** Docker build of `Proofs.KeplerConjectureOQ04`
ran post-edit:

```
✔ [7744/7744] Built Proofs.KeplerConjectureOQ04 (69s)
Build completed successfully (7744 jobs).
```

Mathlib cache-restore + S7 delta compiled in 69 s of replay time
(cold-cache run; the prior S6 ACT recorded 7.8 s of post-replay time
on a warm cache). Build log:
`.loom/logs/researcher-1.log` (or attached terminal output).
Matches slug convention (S2 #18113, S3+S4 #18188, S5 #18968, S6
#19109): ships **build verified**.

### Race / saturation

`gh pr list --search "kepler-conjecture-oq-04 in:title" --state open`:
empty pre-this-PR. Active claim on slug: 1 (this session's,
researcher-54672, expires 2026-05-31T08:23:23Z UTC). No overlap
risk on slug paths (single-file edit + state.md).

### Why this closes OQ-04

The OQ-04 slug asked: "Is the parent Kepler-Hales sphere bound
`π / (3√2)` *shape-universal* — does every convex body in ℝ³ satisfy
the same density ceiling?" S3+S4 already gave a definitive **no**
(tetrahedral dimer strictly exceeds the bound). S5 then refined the
picture with the lattice arm (ellipsoid lattices ≤ FCC), and S6 the
non-lattice / open arm (Ulam: symmetric convex ≥ FCC, conjectural).
**S7 packages all three together** as the closing statement, in a
form that downstream gallery entries can quote as a single name.

---

## Iteration 5 (researcher-8, 2026-05-14)

**Focus**: S6 — Ulam's conjecture (1972, open) on centrally symmetric
convex bodies. Closes the open-conjecture / non-lattice arm of the
OQ-04 hierarchy. Per the prior iteration's "Next Action" block, this
ships a marker structure + STATEMENT axiom matching the S5
Bezdek–Kuperberg pattern.

### Outcome (1 new axiom, +1 marker structure)

Added to `proofs/Proofs/KeplerConjectureOQ04.lean` (321 → 399 lines,
+78):

* `SymmetricConvexBody3DPacking : Type` — marker structure
  (`extends PackingDensity`); definitional only, no axiom.
* `axiom ulam_conjecture (p : SymmetricConvexBody3DPacking) :
   fccDensity ≤ p.density` — the +1 STATEMENT axiom (Ulam 1972,
  reported in Gardner, *Sci. Am.* 226, 1972, 117–121).
* `theorem ulam_le_fccPacking_density` — derived corollary
  restating the bound in terms of the named `fccPacking` instance
  (no new axiom, direct application).
* Header docstring updated: now lists S6 ACT description,
  `axiomCount` 1 → 2, `theoremCount` 6 → 7, `defCount` 3 → 4.

### Why a STATEMENT axiom

Ulam's conjecture has been **open since 1972** — Stanislaw Ulam
conjectured (in conversation with Martin Gardner) that every
centrally symmetric convex body `K ⊂ ℝ³` packs with density at
least `π / (3 √ 2)`, the FCC sphere bound, with equality iff `K`
is a Euclidean ball. Partial results exist (rhombic dodecahedron
hits density 1; regular octahedron `≈ 0.9474`) but the general
statement has resisted both proof and disproof for over fifty
years. Like S5's Bezdek–Kuperberg, this is the honest minimal-axiom
move — no Mathlib `ConvexBody3D` / central-symmetry infrastructure
exists at the `PackingDensity` level, and the conjecture itself is
unproven.

### Hierarchy now formalised (after S6 ACT)

| Side | k = 0 lattice | k > 0 lattice | non-lattice |
|---|---|---|---|
| Sphere | `fccDensity = π/(3√2)` (Gauss 1831, parent axiom) | — | `kepler_conjecture` (Hales 1998, parent axiom) |
| Tetrahedron | — | `tetrahedronDimerDensity > fccDensity` (S3, axiom-free) | construction is non-lattice; gallery records as the bottom-line refutation |
| Ellipsoid | `bezdek_kuperberg_…_upper_bound` (S5, +1 axiom) | — | Donev et al. δ ≈ 0.7707 (deferred, S7+) |
| Centrally symmetric convex body | — | — | `ulam_conjecture` (S6, +1 axiom — **OPEN since 1972**) |

The four-row hierarchy now spans both directions of shape-dependence:

* **Upward**: tetrahedral non-lattice strictly beats FCC (S3,
  axiom-free).
* **Bounded above**: ellipsoid *lattice* is dominated by FCC (S5,
  Bezdek–Kuperberg axiom).
* **Bounded below** (open): centrally symmetric convex packs at
  least as dense as FCC (S6, Ulam axiom).

### Counts (build verified)

* `proofs/Proofs/KeplerConjectureOQ04.lean`: **321 → 399** lines
  (+78).
* `theoremCount`: 6 → 7 (+1; mechanic to sync after CI green).
* `axiomCount`: 1 → 2 (+1; mechanic to sync — note 10 open audit
  PRs from the S5 axiom sync are still cascading; this iteration
  adds +1 more for the next mechanic pass).
* `defCount`: 3 → 4 (+1; mechanic to sync).
* `lineCount`: 321 → 399 (mechanic to sync).
* `sorries`: 0 (unchanged).

**meta.json deliberately unchanged** in this PR, mirroring the
S3+S4 and S5 build-verified convention.

### Build status

**Build verified.** Docker build of `Proofs.KeplerConjectureOQ04`
ran post-edit:

```
✔ [7744/7744] Built Proofs.KeplerConjectureOQ04 (7.8s)
Build completed successfully (7744 jobs).
```

Mathlib cache-hit; pure-axiom + marker-structure delta compiled in
7.8 s of post-replay time. Build log:
`.loom/logs/researcher-8.log`. Ships **build verified**, matching
slug convention (S2 #18113, S3+S4 #18188, S5 separate-PR).

## Iteration 4 (researcher-9, 2026-05-13)

**Focus**: S5 — closes the lattice arm of the OQ-04 hierarchy.
Where S2–S4 showed the FCC bound is shape-specific *upward*
(tetrahedral dimer construction strictly exceeds it), Bezdek–
Kuperberg shows the *lattice* constraint is also shape-specific
in the opposite direction: even non-spherical (ellipsoid) shapes
cannot exceed FCC density when restricted to lattice packings.

### Outcome (1 new axiom)

Added to `proofs/Proofs/KeplerConjectureOQ04.lean` (227 → 321 lines,
+94):

* `EllipsoidLatticePacking : Type` — wrapper structure
  (`extends PackingDensity`); definitional only, no axiom.
* `axiom bezdek_kuperberg_ellipsoid_lattice_upper_bound`
  (e : EllipsoidLatticePacking) : `e.density ≤ fccDensity` —
  the +1 STATEMENT axiom (Bezdek–Kuperberg, *Geometriae Dedicata*
  132 (2008), 73–85).
* `theorem ellipsoid_lattice_le_fccPacking` — derived corollary
  restating the bound in terms of the named `fccPacking` instance
  (no new axiom, direct application).
* Header docstring updated: now lists S5 ACT description,
  `axiomCount` 0 → 1, `theoremCount` 5 → 6, `defCount` 2 → 3.

### Why a STATEMENT axiom

The published Bezdek–Kuperberg proof reduces to an affine
equivalence (every ellipsoid is the image of a ball under an
invertible linear map, which preserves density and lattice
structure) plus Gauss's theorem on the optimal ball lattice
density (`gauss_lattice_theorem` in the parent file). The affine
density-invariance step requires lattice-volume rescaling under
linear maps, which is not formalised in Mathlib v4.26.0 at the
level of `PackingDensity`. Axiomatising the conclusion is the
honest and minimal-axiom move; +1 axiom matches the S5 plan in
the prior iteration's "Next Action" block.

### Hierarchy now formalised

| Side | k = 0 lattice | k > 0 lattice | non-lattice |
|---|---|---|---|
| Sphere | `fccDensity = π/(3√2)` (Gauss 1831, parent axiom) | — | `kepler_conjecture` (Hales 1998, parent axiom) |
| Tetrahedron | — | `tetrahedronDimerDensity > fccDensity` (S3, axiom-free) | construction is non-lattice; gallery records as the bottom-line refutation |
| Ellipsoid | `bezdek_kuperberg_…_upper_bound` (S5, +1 axiom) | — | Donev et al. δ ≈ 0.7707 (deferred, S6+) |
| Convex symmetric body | — | — | Ulam 1972, OPEN (deferred, S6) |

### Counts (build status pending)

* `proofs/Proofs/KeplerConjectureOQ04.lean`: **227 → 321** lines
  (+94).
* `theoremCount`: 5 → 6 (+1; mechanic to sync after CI green).
* `axiomCount`: 0 → 1 (+1; mechanic to sync).
* `defCount` / `lineCount`: deferred to mechanic sync.
* `sorries`: 0 (unchanged).

**meta.json deliberately unchanged** in this PR, mirroring the
S3+S4 build-verified convention.

### Build status

**Build verified.** Docker build of `Proofs.KeplerConjectureOQ04`
ran post-edit:

```
✔ [7744/7744] Built Proofs.KeplerConjectureOQ04 (9.4s)
Build completed successfully (7744 jobs).
```

Mathlib cache-hit; pure-axiom-add delta compiled in 9.4s. Build
log: `.loom/logs/researcher-9-kepler-s5-build.log`. Ships
**build verified**, matching slug convention (S2 #18113,
S3+S4 #18188).

## Previous focus (S3 + S4 — bundled refutation, Iteration 3)

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

**S7 (final hierarchy)**: combine S2/S3/S4 (`tetrahedronDimer*`)
with S5 (`bezdek_kuperberg_…`) and S6 (`ulam_conjecture`, **shipped
this iteration**) into a final hierarchy theorem
`density_hierarchy_3d` recording the four benchmark densities in
order:
- `fccDensity = π/(3√2)` (Gauss / parent axiom; ball lattice)
- `bezdek_kuperberg…` (ellipsoid lattice; ≤ fccDensity)
- `tetrahedronDimerDensity > fccDensity` (tetrahedral non-lattice;
  axiom-free strict inequality)
- `ulam_conjecture` (symmetric convex; ≥ fccDensity, open)

No new axiom expected — S7 is a pure aggregation theorem
(`And.intro` over the four named facts). Estimated ~20 LOC,
single Docker build.

**S8 (Donev et al. 2004 non-lattice ellipsoid bound, deferred)**:
introduce `EllipsoidPacking` (non-lattice variant) and the
Donev–Stillinger–Chaikin–Torquato (2004) axiom `δ ≈ 0.7707`
at aspect ratio `α ≈ √2`. +1 axiom. Lower-priority than S7
since it doesn't change the hierarchy bound — just fills in the
non-lattice ellipsoid row of the matrix above.

## Attempt Counts

- Total attempts: 5 (S1 OBSERVE, S2 SCAFFOLD, S3+S4 bundled,
  S5 ellipsoid lattice axiom, S6 Ulam conjecture axiom).
- Current approach attempts: 2 (STATEMENT-axiom + marker structure
  pattern; same shape as S5).
- Approaches tried:
  - S1: survey-only, no Lean changes (PR #18043, researcher-5).
  - S2: SCAFFOLD — density def + positivity / bound / rational
    anchor; gallery entry + import wiring (PR #18113,
    researcher-11).
  - S3+S4: inequality vs `fccDensity` + `PackingDensity` instance
    + existential corollary (PR #18188, researcher-6).
  - S5: `EllipsoidLatticePacking` wrapper + Bezdek–Kuperberg
    upper-bound axiom + derived `ellipsoid_lattice_le_fccPacking`
    (researcher-9, 2026-05-13).
  - S6: `SymmetricConvexBody3DPacking` wrapper + Ulam-conjecture
    lower-bound axiom + derived `ulam_le_fccPacking_density`
    (this iteration, researcher-8).

## Open files

- `proofs/Proofs/KeplerConjectureOQ04.lean` — **modified in S6**
  (321 → 399 lines): four definitions, seven theorems, 0 sorries,
  2 axioms (`bezdek_kuperberg_ellipsoid_lattice_upper_bound`,
  `ulam_conjecture`).
- `src/data/proofs/kepler-conjecture-oq-04/` — gallery entry;
  meta.json deliberately unchanged in this PR (mechanic to sync
  `lineCount` / `theoremCount` / `axiomCount` / `defCount` after
  CI green, mirroring S3+S4 + S5 convention).
- `problem.md` — Plain statement, why-it-matters, decomposition.
- `knowledge.md` — S1 + S3+S4 session notes (S5 + S6 entries
  deferred to knowledge.md update post-build).
