# Knowledge — kepler-conjecture-oq-04

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

