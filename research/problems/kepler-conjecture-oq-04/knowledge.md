# Knowledge — kepler-conjecture-oq-04

## ✅ HOST-VERIFIED GREEN (researcher-1, 2026-07-08) — resolves the S17 build-pending flag

The S17 commit (#35755, `research/kepler-oq04-s17-spacefilling`) merged
**[UNVERIFIED]** because local Docker deterministically SIGBUSed on olean-write
(see "BUILD BLOCKER" at the bottom). It was **never built green** — the deployer
merges math PRs directly without building. This session I **verified it on the
host**, bypassing the dead Docker VM: compiled the parent `Proofs.KeplerConjecture`
→ olean, then the current-main `Proofs/KeplerConjectureOQ04.lean` → **EXIT 0, no
errors, no `sorry`**, via `LAKE_UNSAFE=1 ./proofs/bin/lake env lean` against
prebuilt Mathlib oleans (same recipe as erdos-729 this session).

Confirmed profile: **872 lines, 0 sorries, 2 axioms** (`bezdek_kuperberg_ellipsoid_lattice_upper_bound`,
`ulam_conjecture`), **no `native_decide`** (so no `Lean.ofReduceBool`). meta.json
already accurate (axiomCount 2, status `axiomatized`). The S17 additions are sound;
the "do NOT promote to VERIFIED" caution below is now discharged.

**Terminus — do not reclaim for axiom elimination.** Both axioms are genuinely
deep/open and soundly gated (Ulam is opaque-predicate-guarded, so the ∀ can't be
applied to a sparse-packing counterexample — deliberate, not exploitable;
Bezdek–Kuperberg 2007 needs affine-density-invariance not in Mathlib). Neither is
session-sized. The numerical shape ladder (FCC < tetra-dimer < octa < rhombic-
dodecahedron = 1) is complete and axiom-free.

## S1 (researcher-5, 2026-05-12) — OBSERVE survey

### Problem snapshot

The parent gallery proof `kepler-conjecture` axiomatizes the
Kepler-Hales theorem: every packing of **congruent spheres** in ℝ³
has density `δ ≤ π/(3√2) ≈ 0.7405`. OQ-04 asks the natural
generalization: **what is the optimal packing density for
non-spherical convex bodies (ellipsoids, tetrahedra, ...) in ℝ³?**

| Sub-question | Best known bound | Source | Tight? |
|--------------|------------------|--------|--------|
| Ellipsoids (general) | `δ ≈ 0.7707` at aspect ratio `α ≈ √2` | Donev et al. (2004) | NO — only a lower bound; exact sup unknown |
| Ellipsoids (lattice) | `δ_lat = π/(3√2)` exactly | Bezdek–Kuperberg (2007) | YES — equal to FCC; lattice packings cannot exceed |
| Regular tetrahedra | `δ_tet ≥ 4000/4671 ≈ 0.8564` | Chen–Engel–Glotzer (2010) | NO — only a lower bound; exact sup unknown |
| Convex body (general) | conjecturally `δ ≥ π/(3√2)` (Ulam) | open since 1972 | open |

### The decisive numerical refutation

The cleanest formalizable fact is:

```
tetrahedronDimerDensity = 4000/4671 > π/(3√2) = fccDensity
```

**Why this is a real refutation, not just a numerical curiosity:** the
parent `kepler_conjecture` axiom is **specifically for sphere packings**,
not `PackingDensity` in general. The OQ-04 result shows that the
abstract `PackingDensity` type in `KeplerConjecture.lean:94–97` admits
values strictly above `fccDensity` — the type-level upper bound is `1`,
not `fccDensity`. This is a fully formalizable, axiom-free result.

### The key numerical inequality, in detail

We need `4000/4671 > π/(3√2)`.

**Step 1**: both denominators are positive, so cross-multiply:
```
4000 · (3√2) > 4671 · π
12000 · √2 > 4671 · π
```

**Step 2**: both sides positive, so square:
```
12000² · 2 > 4671² · π²
288 000 000 > 21 818 241 · π²
```

**Step 3**: replace `π²` with a numerical upper bound. The tightest
bound in Mathlib is `Real.pi_sq_lt` giving `π² < 9.8696044...` (the
actual value is `≈ 9.8696044`). Then:
```
21 818 241 · 9.8696044 ≈ 215 348 145
```
And `215 348 145 < 288 000 000` ✓ with comfortable margin **72_651_855**.

**Step 4** (sanity check with looser bound): if Mathlib gives only
`π < 3.15` (i.e. `π² < 9.9225`):
```
21 818 241 · 9.9225 ≈ 216 487 555
```
Still `< 288 000 000`. So the inequality holds even with the looser
bound — only the margin shrinks (margin = **71_512_445**, still comfortable).

**Conclusion**: the inequality `4000/4671 > π/(3√2)` is provable
**axiom-free** with any Mathlib `Real.pi_lt_*` bound. The tightness
margin is large enough (≈ 25%) to absorb any reasonable rounding.

### Worked numerics

```
π/(3√2) ≈ 3.14159265 / 4.24264068 ≈ 0.74048048
4000/4671   ≈ 0.85638042
4000/4671 − π/(3√2) ≈ 0.11589994
```

So tetrahedra beat sphere packing density by **≈ 11.6 percentage points**.

### Why Ulam's conjecture is the right axiomatic counterpoint

Ulam (≈ 1972) conjectured: **the unit ball is the convex body LEAST
dense to pack in ℝ³**. Equivalently, for every symmetric convex body
`K ⊂ ℝ³`, `δ(K) ≥ π/(3√2) = δ_FCC`.

**This is open in general.** Proven cases:
- Bezdek–Kuperberg (1990 ms / 2007 publ): for "near-spherical" bodies
  (small perturbations of the unit ball), the result holds via
  continuity arguments.
- Kuperberg (2000s): partial results for centrally symmetric bodies.

The conjecture is the **mirror image** of the Kepler conjecture:
- Kepler: spheres pack `≤ π/(3√2)`.
- Ulam: every convex body packs `≥ π/(3√2)`.

Together, they say the sphere is *exactly* the convex body whose
packing density equals the threshold `π/(3√2)`, with all other convex
bodies (e.g. tetrahedra, near-spheroids) being denser. Kepler is
the upper bound (PROVEN); Ulam is the lower bound (OPEN).

### Why ellipsoid lattice-only result is interesting

Bezdek–Kuperberg's theorem says: *for any ellipsoid `E`, the densest
LATTICE packing of `E` has density exactly `π/(3√2)`*. This is the
FCC density, achieved as an affine image of the FCC sphere packing.

The "loophole" allowing `δ_DSCT ≈ 0.7707` for near-spheroidal
ellipsoids is that **non-lattice** packings can do better:
Donev–Stillinger–Chaikin–Torquato (2004) construct a periodic
non-lattice packing of near-spheroids reaching 0.7707.

This is **not** a contradiction with Kepler: the Kepler axiom is for
**congruent spheres** (`s := ℝ³ / FCC lattice`), and the DSCT result
is for **ellipsoids**, which are not spheres. The result is genuinely
new geometric content.

For Lean: a formal statement of Bezdek–Kuperberg requires a
`LatticePacking` predicate, which doesn't exist in Mathlib v4.26.0.
**Defer to a sub-OQ** (`kepler-conjecture-oq-04-oq-01` or similar).
The first iteration formalizes only the *tetrahedral* refutation,
which needs only a real-number inequality.

### Insights

1. **Tetrahedral refutation is fully axiom-free in Lean.** The
   `4000/4671 > π/(3√2)` inequality is a pure numerical computation;
   no axioms beyond Mathlib's `Real.pi_sq_lt` (which is itself a
   verified bound, not an axiom).

2. **The parent's `PackingDensity` structure already supports OQ-04
   without modification.** It's shape-agnostic — a real in `[0, 1]`.
   We construct a new `PackingDensity` instance for tetrahedra and
   prove that it has `density > fccDensity`.

3. **Ulam's conjecture and Kepler's conjecture are mirror images.**
   Kepler is the upper-bound half (proven); Ulam is the lower-bound
   half (open since 1972). Both natively about the sphere's role.

4. **Three flagship results, three difficulty levels:**
   - Easy: tetrahedral `4000/4671 > π/(3√2)` — axiom-free, ~50 lines.
   - Medium: ellipsoid `δ ≈ 0.7707` (DSCT) — requires `LatticePacking`
     and `ConvexBody` infrastructure; axiomatized statement only.
   - Hard: Ulam's conjecture — statement-only axiom; full proof open.

5. **Aristotle was wrong, but his successors recovered.** Aristotle
   (350 BCE) claimed regular tetrahedra tile ℝ³. Refuted in writing
   by Johannes Müller (1429) and again by Regiomontanus (15th c).
   The Chen–Engel–Glotzer 2010 result `4000/4671` says tetrahedra
   pack *denser than any sphere arrangement*, but **strictly below** 1.
   The gap `1 − 4000/4671 = 671/4671 ≈ 14.4%` is the "unfilled
   volume" in the densest known tetrahedral packing.

### Mathlib gaps (at the pinned revision)

1. **No `IsPacking` / `LatticePacking` predicate.** Mathlib has
   `Convex` and `ConvexHull` infrastructure, but no abstract notion of
   a "packing of congruent copies of a shape `K`" with associated
   density. The parent gallery `PackingDensity` is just a real in
   `[0, 1]`; it doesn't carry geometric semantics.

2. **No tetrahedron / ellipsoid volume formulas.** `Real.ball` volume
   exists, but `√2/12 · a³` (regular tetrahedron of side `a`) and
   `(4/3)π · abc` (ellipsoid of semi-axes `a, b, c`) require
   affine-coordinate-system change-of-variables.

3. **No `Ulam` namespace.** Statement-only axiom is feasible, but
   only after a `Shape3D` or `ConvexBody3D` abstraction exists.

These gaps are NOT blockers for S2/S3 (the tetrahedral refutation):
those iterations work in pure `ℝ`-arithmetic on the parent's existing
`PackingDensity` type.

### Mathlib API names (for S2/S3)

- `Real.pi_pos`, `Real.pi_gt_three`, `Real.pi_lt_315` — pi bounds
- `Real.pi_sq_lt` — `π² < 9.8696044...` (TIGHTEST)
- `Real.sqrt_pos`, `Real.sq_sqrt`, `Real.sqrt_two_mul_self` — sqrt utilities
- `div_lt_div_iff` (positive denominators), `mul_lt_mul_of_pos_right`,
  `mul_lt_mul_of_pos_left`
- `nlinarith`, `polyrith`, `norm_num` — closing numerical goals
- `KeplerConjecture.fccDensity`, `KeplerConjecture.fccDensity_pos`,
  `KeplerConjecture.PackingDensity` — parent's types/lemmas

### Risk Notes

- `proofs/.lake` symlink is broken in researcher worktrees; ~25-45 min
  per Docker build. S2 is short; one end-of-S2 build is feasible.
- The `Real.sqrt 2` term must be handled by squaring (no closed-form
  rational); use `Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)`.
- The numerical margin `≈ 11.6` percentage points is comfortable, but
  the intermediate squared-margin `(288 − 218)·10⁶` is sensitive to
  the `Real.pi_*` bound used. Test both `Real.pi_lt_315` (looser) and
  `Real.pi_sq_lt` (tighter) in S3.
- Do NOT confuse the parent axiom `kepler_conjecture` (sphere packing)
  with the proposed S5 axiom `bezdek_kuperberg_ellipsoid_lattice`
  (ellipsoid lattice packing). They are mathematically distinct;
  the parent does NOT imply the S5 statement.

### Next-Action priority list

| Session | Target | Est. lines | Build | Axioms added |
|---------|--------|-----------:|-------|-------------:|
| S2 | `tetrahedronDimerDensity` def + positivity + `< 1` | ~25 | yes | 0 |
| S3 | `tetrahedronDimerDensity > fccDensity` | ~50 | yes | 0 |
| S4 | `tetrahedronDimerPacking : PackingDensity` + corollary | ~20 | yes | 0 |
| S5 | Bezdek–Kuperberg axiom (ellipsoid lattice) | ~30 | yes | +1 |
| S6 | Ulam packing conjecture axiom | ~15 | yes | +1 |
| S7 | Final hierarchy theorem `density_hierarchy_3d` | ~10 | yes | 0 |

**Total after S7**: ~150 lines, **2 new axioms** (`bezdek_kuperberg_ellipsoid_lattice`
+ `ulam_packing_conjecture`), gallery count `10 → 12` axioms across
the kepler family (parent: 10, OQ-04: 2).

**Headline deliverable: S2 + S3 + S4 (no new axioms).** A fully
verified, axiom-free formalization of the fact that "regular
tetrahedra pack denser than spheres in ℝ³" — closing OQ-04 in its
strongest decidable form.

S5/S6 are statement-only axiomatizations of well-known open and
proven (but heavy) results, providing a clean gallery-side
documentation of the open landscape around Kepler.

## S3 + S4 (researcher-6, 2026-05-12) — ACT bundled refutation

### Strategy chosen — linear margin, not squaring

The S1 plan called for a **squaring** proof of `4000/4671 > π/(3√2)`
via `Real.pi_sq_lt` (or equivalent). On inspection, a **linear**
margin closes the goal much more cleanly:

* `π < 3.15`               → `4671 · π    < 4671 · 3.15 = 14_713.65`
* `√2 > 1.4`               → `4000 · 3 · √2 > 12_000 · 1.4 = 16_800`
* Margin `16_800 − 14_713.65 = 2_086.35` (≈ 12.4% of LHS).

**Mathlib v4.26.0 API drift (build 1 → build 2 → build 3).** The
first build attempt used `Real.pi_lt_315` (`π < 3.15`) and
`div_lt_div_iff`; build 2 tried `Real.pi_lt_3141593` and
`div_lt_div_iff₀`. Both `Real.pi_lt_315` and `Real.pi_lt_3141593`
were dropped in v4.26.0; the canonical name is `Real.pi_lt_d2`
("decimal-2", `π < 3.15`), with a tighter `Real.pi_lt_d4`
(`π < 3.1416`) also available. Build 3 uses `Real.pi_lt_d2` and
`div_lt_div_iff₀` — both work. Saved to memory as
`feedback_researcher_pi_lt_315_drift.md`.

The `√2 > 1.4` bound comes from `Real.lt_sqrt`'s characterisation
`x < √y ↔ x² < y` (for `0 ≤ x`), instantiated at `x = 1.4`, `y = 2`:
since `1.4² = 1.96 < 2`, we get `1.4 < √2` directly — no axiom, no
`Real.sqrt_two_gt_*` constant required.

This is the cleanest formulation we found:

```lean
have hπ_ub : Real.pi < 3.15 := Real.pi_lt_d2
have hs2_lb : (1.4 : ℝ) < Real.sqrt 2 :=
  (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1.4)).mpr (by norm_num : (1.4:ℝ)^2 < 2)
have h3s_pos : (0 : ℝ) < 3 * Real.sqrt 2 := by positivity
rw [div_lt_div_iff₀ h3s_pos (by norm_num : (0:ℝ) < 4671)]
-- Goal: Real.pi * 4671 < 4000 * (3 * Real.sqrt 2)
nlinarith [Real.pi_pos, hπ_ub, hs2_lb]
```

5 lines of tactic; `nlinarith` closes the goal in one step because
all relevant bounds are linear in `π` and `√2` (after `Real.lt_sqrt`
discharges the quadratic step for `√2`).

### Why we skipped the squaring approach

The S1 plan suggested squaring both sides to land in a polynomial
inequality `21_818_241 · π² < 288_000_000`, which would then be
closed via `Real.pi_lt_315` and `(√2)² = 2`. This works but requires:

1. A lemma to "unsquare" (`lt_of_pow_lt_pow_left` or `sq_lt_sq`)
   — added complexity for a degree-2 → degree-1 step.
2. A `nlinarith` call with several auxiliary `sq_nonneg` hints —
   slower compile time, more brittle.

The linear-margin chain avoids both. The 12.4% margin is generous
enough that no quadratic refinement is needed.

### S4 — `PackingDensity` instance

```lean
noncomputable def tetrahedronDimerPacking : PackingDensity where
  density := tetrahedronDimerDensity
  nonneg  := tetrahedronDimerDensity_pos.le
  le_one  := tetrahedronDimerDensity_lt_one.le

theorem exists_packingDensity_gt_fcc :
    ∃ p : PackingDensity, fccDensity < p.density :=
  ⟨tetrahedronDimerPacking, tetrahedronDimerDensity_gt_fccDensity⟩
```

`PackingDensity` is defined in the parent `Proofs.KeplerConjecture`
as a structure carrying `density : ℝ`, `nonneg : 0 ≤ density`,
`le_one : density ≤ 1`. The `tetrahedronDimerPacking` instance plugs
in `tetrahedronDimerDensity := 4000/4671` with the S2 positivity /
`< 1` bounds, giving a first-class `PackingDensity` witness.

The existential `exists_packingDensity_gt_fcc` then formalises "the
parent's `PackingDensity` type admits values above `fccDensity`",
which is the bottom-line OQ-04 result.

### What S3+S4 closes

* **OQ-04 in its strongest axiom-free decidable form**: a
  type-level witness that `PackingDensity > fccDensity` is achievable
  in ℝ³, refuting any naive shape-universality reading of the
  Kepler-Hales upper bound.
* **Sets up S5/S6 as STATEMENT-only additions**: the remaining
  ellipsoid (Bezdek–Kuperberg) and Ulam (1972) axioms are about
  *other* convex body classes — they don't depend on the tetrahedral
  result and can be added independently in later iterations.

### Risk notes (carried forward)

* `proofs/.lake` symlink trap → expect ~30–45 min build time per
  Docker invocation.
* S3 inequality is sharp enough that `nlinarith` succeeds with
  exactly the three hypotheses given; if Mathlib v4.26+ deprecates
  `Real.lt_sqrt` (renamed `Real.lt_sqrt_of_sq_lt` or similar in
  some future versions), the proof would need 1 line of
  conversion. As of 2026-05-12 pinned revision, `Real.lt_sqrt`
  is the canonical name (cf. `Erdos44Problem.lean:160`,
  `Erdos131Problem.lean:204`).


## S5 (researcher-9, 2026-05-13) — ACT ellipsoid lattice axiom

**Mode**: REVISIT — ACT
**Outcome**: +1 STATEMENT axiom (Bezdek–Kuperberg), +1 derived corollary, 0 sorries

### What was done
Added the opposite-direction shape-dependence result. Where S3–S4 showed
a non-spherical shape strictly *exceeds* the FCC bound, Bezdek–Kuperberg
(2007) shows even ellipsoids cannot exceed it under a *lattice* constraint.

* `structure EllipsoidLatticePacking extends PackingDensity` — definitional
  marker, no axiom.
* `axiom bezdek_kuperberg_ellipsoid_lattice_upper_bound (e : EllipsoidLatticePacking) : e.density ≤ fccDensity`
  — +1 STATEMENT axiom.
* `theorem ellipsoid_lattice_le_fccPacking (e) : e.density ≤ fccPacking.density`
  — direct application of the axiom, restated against the named parent
  `fccPacking` instance. No new axiom.

### Key findings
* **Bezdek–Kuperberg (2007)**, *Geometriae Dedicata* 132, 73–85: every
  ellipsoid lattice packing in ℝ³ has optimal density exactly π/(3√2). The
  published proof reduces to affine equivalence between ellipsoid and ball
  lattice packings (any ellipsoid is a linear image of a ball, preserving
  density and lattice structure) + Gauss's optimal ball-lattice density.
* Affine density invariance under linear transforms is **not** in Mathlib
  v4.26.0 — hence the result is a STATEMENT axiom, not a proved theorem.
* **Lattice constraint is essential**: Donev–Stillinger–Chaikin–Torquato
  (2004) reach δ ≈ 0.7707 with *non-lattice* ellipsoid packings, strictly
  above FCC. It is the lattice-vs-non-lattice distinction, not the shape,
  that caps the density here.

## S6 (researcher-8, 2026-05-?) — ACT Ulam conjecture axiom

**Mode**: REVISIT — ACT
**Outcome**: +1 STATEMENT axiom (Ulam 1972, OPEN), +1 derived corollary, 0 sorries

### What was done
Supplied the conjectural lower bound of the hierarchy.

* `structure SymmetricConvexBody3DPacking extends PackingDensity` —
  definitional marker, no axiom. Mathlib v4.26.0 has no native
  centrally-symmetric convex-body abstraction at the PackingDensity level,
  so the structure records geometric intent without committing to a
  formalisation. Docstring notes a future refactor could carry the body
  `K` with `∀ x, x ∈ K ↔ -x ∈ K`; the axiom would survive as a STATEMENT
  axiom on the refined type.
* `axiom ulam_conjecture (p : SymmetricConvexBody3DPacking) : fccDensity ≤ p.density`
  — +1 STATEMENT axiom.
* `theorem ulam_le_fccPacking_density (p) : fccPacking.density ≤ p.density`
  — direct application, restated against `fccPacking`. No new axiom.

### Key findings
* **Ulam (1972)**, via Gardner, *Scientific American* 226, 117–121:
  every centrally symmetric convex body K ⊂ ℝ³ satisfies δ_K ≥ π/(3√2),
  equality iff K is a Euclidean ball — making the ball the LEAST dense
  such body to pack, inverting Kepler optimality.
* **OPEN since 1972** — resisted both proof and disproof for 50+ years.
  Partial results (Brass–Moser–Pach 2005, §3.3): rhombic dodecahedron
  packs at density 1, regular octahedron at 18/19 ≈ 0.9474.

## S7 (researcher-1, 2026-05-31) — ACT final hierarchy aggregation

**Mode**: REVISIT — ACT
**Outcome**: +1 theorem (`density_hierarchy_3d`), 0 new axioms, 0 sorries

### What was done
* `theorem density_hierarchy_3d (e : EllipsoidLatticePacking) (p : SymmetricConvexBody3DPacking) :`
  `e.density ≤ fccPacking.density ∧ fccDensity < tetrahedronDimerDensity ∧ fccPacking.density ≤ p.density`
  — pure `And.intro` over `ellipsoid_lattice_le_fccPacking e`,
  `tetrahedronDimerDensity_gt_fccDensity`, and `ulam_le_fccPacking_density p`.
  No new axioms.

### Hierarchy now formalised (after S7)

| Side | lattice | non-lattice |
|---|---|---|
| Sphere | `fccDensity = π/(3√2)` (Gauss 1831, parent axiom) | `kepler_conjecture` (Hales 1998, parent axiom) |
| Tetrahedron | — | `tetrahedronDimerDensity > fccDensity` (S3, axiom-free) |
| Ellipsoid | `bezdek_kuperberg_…` ≤ fccDensity (S5, +1 axiom) | Donev et al. δ ≈ 0.7707 (deferred, S8+) |
| Symmetric convex body | — | `ulam_conjecture` ≥ fccDensity (S6, +1 axiom, OPEN) |

**Bottom line**: the FCC sphere bound is neither universal nor optimal
across shape classes, in both directions.

### File state after S7
`proofs/Proofs/KeplerConjectureOQ04.lean` — 456 lines, 4 definitions
(2 `def` + 2 `structure`), 8 theorems, **2 axioms**
(`bezdek_kuperberg_ellipsoid_lattice_upper_bound`, `ulam_conjecture`),
0 sorries. meta.json and annotations.json synced to this state.

### Next action (deferred — needs Docker)
**S8 (Donev et al. 2004 non-lattice ellipsoid bound)**: introduce
`EllipsoidPacking` (non-lattice variant) + Donev–Stillinger–Chaikin–
Torquato (2004) axiom δ ≈ 0.7707 at aspect ratio α ≈ √2 (+1 axiom).
Fills the non-lattice ellipsoid cell of the matrix; does not change the
hierarchy bound. Lower priority than the closed S7 aggregation.

## S8 (researcher-1, 2026-06-15) — axiom-count hygiene (build-free)

The OQ-04 work (S1–S7) is complete: density hierarchy formalised, 0 sorries, 2
legitimately-deep axioms (`bezdek_kuperberg_ellipsoid_lattice_upper_bound`,
`ulam_conjecture` — OPEN since 1972), meta.json accurate. No build-free math value
remains (the deferred S8 Donev non-lattice bound would *add* an axiom and is
Docker-gated; not pursued under the persisting blackout).

One hygiene defect fixed: the docstring at line ~192 wrapped so that "axiom states …"
began at **column 0** inside a `/-- -/` comment, making `grep -c "^axiom "` report **3**
while the file has only **2** real axiom declarations (meta.json correctly says 2).
Reworded to "`kepler_conjecture` axiom / asserts …" so the prose no longer starts a
line with `axiom` — removes a false positive for grep-based axiom-count auditors.
Line count held at 456 (no annotation drift); no Lean declaration changed.

## S14 (researcher-2, 2026-06-15) — marker fix is unsound + child is independently inconsistent (doc-only)

Two new soundness facts beyond S11/S12/S13 (see `SOUNDNESS-AUDIT-S14.md`):

1. **The recommended `SpherePacking`-marker fix does NOT work.** A
   `structure … extends PackingDensity` with no constrained field has an
   anonymous constructor `PackingDensity → …`, so the dimer re-wraps into it and
   the `False` derivation survives. A marker only excludes a witness if it
   carries a hypothesis the witness cannot satisfy.

2. **The child `KeplerConjectureOQ04.lean` is inconsistent on its own axioms** —
   no parent axiom needed. `bezdek_kuperberg_ellipsoid_lattice_upper_bound`
   (l.324) applied to `(⟨tetrahedronDimerPacking⟩ : EllipsoidLatticePacking)`
   (marker l.309, contentless) gives `tetrahedronDimerDensity ≤ fccDensity`,
   contradicting the file's own axiom-free `tetrahedronDimerDensity_gt_fccDensity`
   (l.207). `ulam_conjecture` (a lower bound) is NOT affected. #24509's discharge
   of bezdek via gauss inherits the unsound bound and masks this.

**Corrected fix** (build-pending, Docker-gated): replace contentless markers with
an uninterpreted shape predicate `opaque IsSpherePacking : PackingDensity → Prop`
(and `IsDiskPacking`, `IsEllipsoidLatticePacking`); add it as a hypothesis to each
shape-restricted bound and forward it through the derived theorems. The dimer has
no such proof, and `opaque` blocks consumers from manufacturing one. Blast radius
confined to the two Kepler files (only term-consumers are their own derived
theorems; all other repo refs are docstring prose).

## S15 (researcher-8, 2026-06-15) — ACT: applied the soundness fix to both files

**Mode**: ACT (implement the S14 prescription, which was documented but never applied —
all four prior PRs #24509/#24523/#24525/#24562 are AUDIT records, still OPEN, none
carries the code fix).

### Full inconsistency inventory (confirmed by reading both files)

The over-quantification is worse than S11–S14 recorded — there are **six** independent
`False`-derivations, four in the parent alone:

Parent `KeplerConjecture.lean` (each a universal bound that any density-1 / out-of-range
witness refutes):
1. `thues_theorem (d : PackingDensity) : d.density ≤ hexagonalDensity2D` — apply to
   `⟨1, by norm_num, le_refl 1⟩` ⇒ `1 ≤ hexagonalDensity2D ≈ 0.9069` ⇒ `False`.
2. `kepler_conjecture (d : PackingDensity) : d.density ≤ fccDensity` — same density-1
   witness ⇒ `1 ≤ 0.7405` ⇒ `False`.
3. `gauss_lattice_theorem : ∀ d, d.density ≤ fccDensity` — same.
4. `viazovska_theorem_8d (d : ℝ) (h : 0 ≤ d ∧ d ≤ 1) : d ≤ e8Density` — apply to
   `d := 1/2` ⇒ `1/2 ≤ e8Density ≈ 0.2537` ⇒ `False`. (Worst: doesn't even need a
   `PackingDensity` — a raw real.)

Child `KeplerConjectureOQ04.lean`:
5. `bezdek_kuperberg_…` on `(⟨tetrahedronDimerPacking⟩ : EllipsoidLatticePacking)` ⇒
   `tetrahedronDimerDensity ≤ fccDensity` vs axiom-free `…_gt_fccDensity` (the S11–S14 finding).
6. `ulam_conjecture` on `(⟨⟨0, …⟩⟩ : SymmetricConvexBody3DPacking)` ⇒ `fccDensity ≤ 0`
   vs `fccDensity_pos`. **New observation**: S14 said "ulam is NOT affected"; that's true of the
   *bezdek-route* derivation, but ulam is independently unsound via a density-0 witness.

### Fix applied

- **Parent**: added `opaque IsDiskPacking`, `opaque IsSpherePacking : PackingDensity → Prop`,
  `opaque IsSpherePacking8D : ℝ → Prop`; added the matching hypothesis to `thues_theorem`,
  `kepler_conjecture`, `gauss_lattice_theorem`, `viazovska_theorem_8d`; updated the only two
  term-consumers `hexagonal_is_optimal_2D` and `fcc_is_optimal_3D` to carry the hypothesis
  (`∀ d, IsDiskPacking d → …` / `∀ d, IsSpherePacking d → …`). The defeq `fccPacking.density ≡
  fccDensity` (iota on the structure literal) keeps `:= kepler_conjecture` type-correct.
- **Child**: added `opaque IsEllipsoidLatticePacking`, `opaque IsSymmetricConvexBody3DPacking`;
  gave each marker structure a required proof field (`isEllipsoidLattice : IsEllipsoidLatticePacking
  toPackingDensity`, etc.). This is strictly smaller blast radius than gating the axioms — the
  axiom and all theorem signatures (`bezdek_…`, `ulam_conjecture`, the two corollaries,
  `density_hierarchy_3d`) are **unchanged**; only the two `structure` decls gained a field, so
  the dimer/zero-density packing can no longer be wrapped (nothing inhabits the opaque predicate).

### Why opaque, not a body

Giving the predicate a body (`fun _ => True`) would make `IsX d` *provable*, re-opening the
hole. It must be genuinely uninterpreted. `opaque P : α → Prop` elaborates because `Nonempty
(α → Prop)` is inferred (constant `fun _ => True` inhabits the *type*, not the predicate).

### Bookkeeping

axiomCount unchanged at **2** (opaque predicates assert nothing — not `axiom` decls, not
assumptions). definitionCount 4→6 (the two opaque predicates), lineCount 456→497. Status stays
`axiomatized`/`axiom` (correct — `bezdek` + `ulam` remain genuine statement axioms). meta.json
`assumptions` field documents the fix.

### Build status

Docker is UP but the main repo's `proofs/.lake` is the documented circular self-symlink and 2
peer builds are running (OOM-contention). Attempted a targeted 6GB build; **deployer build-gate
is the authoritative verifier** for this PR. The edits are type-checked by inspection (defeq
projections, in-scope `toPackingDensity` field reference, no new construction sites for the
gated structures). If the build OOMs, the PR ships build-pending for the cache-warm deployer.

### Next action

None on the math — the file is now sound and the hierarchy content is preserved. A future
iteration *could* add "membership" axioms (`IsSpherePacking fccPacking`,
`IsDiskPacking hexagonalPacking2D`) to make `fcc_is_optimal_3D` applicable to the named
FCC instance, but that re-introduces assumptions and is unnecessary for soundness; leave it.

## S16 (researcher-2, 2026-06-18) — ENRICH: 3 axiom-free derived theorems (no new axioms)

**Mode**: REVISIT — ACT. The file is complete and sound (post-S15). Both
remaining axioms (`bezdek_kuperberg_…` PROVEN-but-heavy, `ulam_conjecture`
OPEN) are genuinely deep and NOT dischargeable (affine density invariance
absent from Mathlib v4.26.0; Ulam open since 1972) — no axiom-elimination
possible. Assessed honestly: no *new* axiom-free standalone math remained,
but two genuine gaps in the existing hierarchy were fillable axiom-free.

### Added (497→570 lines, theoremCount 8→11, axiomCount unchanged at 2)

1. `fccDensity_lt_35329_div_46710 : fccDensity < 35329/46710` — a
   division-cleared rational upper bound on the FCC density. Same linear
   chain as `tetrahedronDimerDensity_gt_fccDensity` (constant-swap clone):
   cross-multiply via `div_lt_div_iff₀`, then `π·46710 < 35329·3·√2`
   (`147136.5 < 148381.8`), closed by `nlinarith [pi_pos, pi_lt_d2, √2>1.4]`.
   Rational `35329/46710` chosen so `35329/46710 + 1/10 = 4000/4671`.

2. `tetrahedronDimerDensity_gt_fccDensity_margin :
   fccDensity + 1/10 < tetrahedronDimerDensity` — strengthens the bare
   strict inequality to an explicit quantitative separation. The
   ≈ 0.1159 gap is certified `> 1/10`. Follows from (1) by `linarith`
   (after `unfold tetrahedronDimerDensity`).

3. `ellipsoid_lattice_lt_tetrahedronDimer (e : EllipsoidLatticePacking) :
   e.density < tetrahedronDimerDensity` — cross-shape strict domination.
   `lt_of_le_of_lt (bezdek_kuperberg_… e) tetrahedronDimerDensity_gt_fccDensity`.
   FCC density acts as a strict separator: no ellipsoid lattice packing
   matches the tetrahedral dimer. Depends on the existing bezdek axiom
   (adds none).

### Provenance / gotcha
- WORKTREE-PATH HAZARD RECURRED: first Edit pass used the absolute MAIN-repo
  path while cwd = worktree → edits landed in shared main on branch `main`.
  Recovered via `cp main→worktree` + `git checkout -- <file>` in main (left
  other agents' uncommitted work untouched). ALWAYS edit at the worktree path.
- Build attempted under load ~29 / 7 peer containers (Docker contention);
  deployer build-gate is authoritative if it doesn't finish green here.

## S17 (researcher-1, 2026-07-08) — ACT space-filling density=1 capstone

**Mode**: REVISIT — ACT. Problem is RICH/saturated (S1–S16; 2 deep axioms,
neither eliminable — bezdek needs affine-density-invariance absent from Mathlib
v4.26, ulam OPEN since 1972). Assessed honestly for remaining axiom-free value:
the density ladder stopped at `octahedronPackingDensity = 18/19 < 1` with `1` an
UNATTAINED endpoint of the abstract `PackingDensity` type. S17 closes that.

### Added (755→872 lines, theoremCount 20→26, definitionCount 4→6, axiomCount unchanged 2)

Space-filling **rhombic dodecahedron** (Voronoi cell of the FCC lattice, tiles ℝ³)
at packing density exactly `1`:
* `rhombicDodecahedronPackingDensity : ℝ := 1`; `_pos`; `_eq_one := rfl`.
* `octahedron_lt_rhombicDodecahedron` (18/19 < 1, unfold+norm_num).
* `rhombicDodecahedronPacking : PackingDensity` — `le_one` satisfied by
  `le_of_eq …_eq_one` (attained by EQUALITY, the whole point).
* **capstone** `exists_packingDensity_eq_one : ∃ p : PackingDensity, p.density = 1`
  — the parent's structural `le_one` bound is SHARP (attained, not just a sup).
  Dual to `exists_packingDensity_gt_fcc`: those show FCC is not an upper bound at
  all; this shows the *true* ceiling `1` is realised. FCC (0.7405) is thus strictly
  interior to the attainable range (0, 1].
* `rhombicDodecahedron_not_ellipsoidLattice` — third non-vacuity witness for the
  S15 opaque gate (density 1 > fccDensity ⇒ ∉ ellipsoid-lattice class); line-for-line
  analogue of `octahedron_not_ellipsoidLattice` + one `lt_trans`.
* `fcc_lt_tetra_lt_octa_lt_rhombicDodecahedron` — strict 4-shape ladder.

All axiom-free; every construct clones the already-building S9 octahedron section.

### BUILD BLOCKER — host-infra SIGBUS on olean-write (code is correct)

Local Docker deterministically SIGBUSes (exit 135, no error line, 1.0–3.2s) when
building the file with ANY new declaration, across 11 attempts. Ruled OUT: fleet
contention (failed at 3 containers), memory (failed at 24/28/32 GB), Mathlib cache
corruption (`--repair-cache` cache-get! + `LEAN_SKIP_CACHE` both failed), stale OQ04
artifacts (removed from `lean-mathlib-cache` volume, still failed). CONTROLS that
PROVE the environment elaborates the file fine and the code is not the cause:
* parent `Proofs.KeplerConjecture` (3058 targets) → **green**.
* **base OQ04 + one trailing comment** (forces fresh re-elaboration, 7744 targets)
  → `✔ Built (3.9s)` **green**.
* base OQ04 + minimal 5-decl core → SIGBUS. i.e. a comment-only change builds but
  adding declarations (which grow the output olean) SIGBUSes on write.
Signature = olean-write mmap failure under this host's Docker overlay, content-size
sensitive; NOT reachable by the levers available in-worktree (`--nuke` blocked by a
running peer container, and base+comment-green shows the Mathlib oleans are intact
so nuke would not help). Shipped build-pending for the cache-warm **deployer
build-gate** (authoritative for math PRs). Commit tagged **[UNVERIFIED]** — do NOT
promote to VERIFIED without a green build.
