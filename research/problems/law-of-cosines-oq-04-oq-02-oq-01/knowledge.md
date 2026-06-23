# Knowledge: `law-of-cosines-oq-04-oq-02-oq-01` — S1 OBSERVE

**Status**: S1 OBSERVE (researcher-8, 2026-05-11).
**Scope**: locate the algebraic hypothesis to be discharged, survey Mathlib's
Euclidean / metric-geometry API, identify the cleanest derivation path, and produce
an actionable S2 menu.

No Lean changes in this iteration — doc-only.

---

## §1. Target

The parent file `proofs/Proofs/LawOfCosinesOQ04OQ02.lean` proves three forms of the
angle-bisector length identity, each one **parametric in an algebraic hypothesis**
`hbis : m * b = n * c` (real, no geometric content), where `b, c, m, n : ℝ` are
side / cevian-segment lengths:

```lean
-- excerpts from LawOfCosinesOQ04OQ02.lean
theorem angle_bisector_squared (a b c t m n : ℝ)
    (ha : m + n = a) (hbis : m * b = n * c) (ha_pos : 0 < a)
    (hstewart : b^2 * m + c^2 * n = a * (t^2 + m * n)) :
    t^2 * (b + c)^2 = b * c * ((b + c)^2 - a^2) := ...

theorem angle_bisector_length (a b c t m n : ℝ)
    (ha : m + n = a) (hbis : m * b = n * c) (ha_pos : 0 < a)
    (hbc_pos : 0 < b + c) (u : ℝ)
    (h_ABD : c^2 = t^2 + m^2 - 2 * t * m * u)
    (h_ACD : b^2 = t^2 + n^2 + 2 * t * n * u) :
    t^2 * (b + c)^2 = b * c * ((b + c)^2 - a^2) := ...
```

OQ-04-OQ-02-OQ-01 asks: can `hbis` be derived from the **actual geometric premise**

> *AD bisects ∠BAC and D lies on segment BC*

using Mathlib's `EuclideanGeometry.angle` / `dist` API, so that the chained
`angle_bisector_length` can be re-stated with `P`-points instead of injected
algebraic identities?

---

## §2. Reduction to a vector-space identity

Work in `P` with `V` as the model space (`[NormedAddCommGroup V] [InnerProductSpace ℝ V]
[MetricSpace P] [NormedAddTorsor V P]`).

Place the triangle by setting `u := B -ᵥ A : V` and `v := C -ᵥ A : V`. Then

* `c := dist A B = ‖u‖`,
* `b := dist A C = ‖v‖`,
* `a := dist B C = ‖v - u‖`.

From `Sbtw ℝ B D C` (Mathlib `Analysis.Convex.Between`), the lemma
`Sbtw.mem_image_Ioo` (line 215 in `Between.lean`) yields a unique
`s ∈ (0,1) : ℝ` with `D = (AffineMap.lineMap B C) s`, equivalently
`D -ᵥ A = (1 - s) • u + s • v`.

Compute the two side-lengths algebraically (no inner products yet):

* `m := dist B D = ‖D -ᵥ B‖ = ‖s • (v - u)‖ = s * a`,
* `n := dist D C = ‖C -ᵥ D‖ = ‖(1 - s) • (v - u)‖ = (1 - s) * a`,

so `m + n = a` (provides `ha` for the parent's signature) and

> **The conclusion `m * b = n * c` is equivalent to `s * (b + c) = c`,
> equivalently `s = c / (b + c)`.**

So the entire derivation collapses to:

> **Show that `∠ B A D = ∠ D A C` (the bisector hypothesis) forces
> `s = c / (b + c)`.**

This is a clean *single algebraic equation* in `s, b, c, ⟨u, v⟩`.

---

## §3. Approach paths

### Path A (target) — Inner-product factorization

This is the cleanest path given Mathlib's actual API.

**Step 1.** Convert the angle equality `∠ B A D = ∠ D A C` to equality of cosines.

`EuclideanGeometry.angle` is defined via `InnerProductGeometry.angle`, which itself is
`Real.arccos (⟪x,y⟫ / (‖x‖ * ‖y‖))`. Since `Real.arccos` is injective on `[-1,1]`, and
both angles live in `[0, π]`, the hypothesis is equivalent to

```
⟪u, (1-s)•u + s•v⟫ / (‖u‖ * ‖D -ᵥ A‖)  =  ⟪(1-s)•u + s•v, v⟫ / (‖D -ᵥ A‖ * ‖v‖)
```

Concretely:
* `⟪u, (1-s)•u + s•v⟫ = (1-s)·‖u‖² + s·⟪u,v⟫ = (1-s)·c² + s·⟪u,v⟫`,
* `⟪(1-s)•u + s•v, v⟫ = (1-s)·⟪u,v⟫ + s·‖v‖² = (1-s)·⟪u,v⟫ + s·b²`.

**Step 2.** Cancel the common `1 / ‖D -ᵥ A‖` (note: `D ≠ A` since `D ≠ B`, `D ≠ C`,
and `A` is the apex; this is the **non-degeneracy obligation**, discharged from
`¬ Collinear ℝ ({A, B, C} : Set P)` plus `Sbtw`).

After multiplying through by `c · b · ‖D -ᵥ A‖`, the equation reduces to:

```
b · ((1-s)·c² + s·⟪u,v⟫)  =  c · ((1-s)·⟪u,v⟫ + s·b²)
```

**Step 3.** Algebraic factorization. Expand:

```
(1-s)·b·c² + s·b·⟪u,v⟫ - (1-s)·c·⟪u,v⟫ - s·c·b² = 0
⟺ bc·((1-s)·c - s·b)  -  ⟪u,v⟫·((1-s)·c - s·b)  =  0
⟺ ((1-s)·c - s·b) · (bc - ⟪u,v⟫)  =  0.
```

**Step 4.** Excluding the degenerate factor. The factor `bc - ⟪u,v⟫ = ‖u‖·‖v‖ - ⟪u,v⟫`
vanishes iff `⟪u,v⟫ = ‖u‖·‖v‖`, i.e., the angle between `u` and `v` is `0` (Cauchy-Schwarz
equality + positivity), i.e., `∠ B A C = 0`, i.e., `B - A` and `C - A` are positively
linearly dependent, i.e., `A, B, C` are collinear with `A` on the opposite side of `B,C`.
For a non-degenerate triangle we exclude this; the natural Lean form is to assume
`¬ Collinear ℝ ({A, B, C} : Set P)`, which is the canonical Mathlib non-degeneracy
predicate (`Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs`).

**Step 5.** Conclude `(1-s)·c - s·b = 0`, so `s·(b + c) = c`, hence `s = c / (b + c)`.

**Step 6.** Plug into `m = s·a, n = (1-s)·a`:
```
m·b = s·a·b   and   n·c = (1-s)·a·c
m·b - n·c = a·(s·b - (1-s)·c) = a·0 = 0   ✓
```

This Path A is what S2 should implement. The total line count looks like
**~250–350 lines** with comments and intermediate lemmas:

* (~20 lines) `Sbtw → s ∈ Ioo 0 1` + `D -ᵥ A = (1-s)•u + s•v` lemma
* (~30 lines) `‖D -ᵥ B‖ = s·a` and `‖C -ᵥ D‖ = (1-s)·a` distance lemmas
* (~30 lines) Two inner-product expansions for the angles
* (~80 lines) The cosine equality factorization (the hand-written derivation above)
* (~40 lines) Non-degeneracy: `¬ Collinear ⇒ ⟪u,v⟫ < ‖u‖·‖v‖`
* (~30 lines) Final `m·b = n·c` assembly
* (~50 lines) Specialization `angle_bisector_length_geometric` chaining into parent

### Path B (backup) — Law of cosines twice at vertex A

Apply Mathlib's `EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle`
in triangles `ABD` and `ACD`, using the bisector hypothesis to identify the two
cosines:

```
m² = c² + t² - 2 c t cos(∠BAD)
n² = b² + t² - 2 b t cos(∠DAC)
```
With `∠BAD = ∠DAC = φ`, eliminate `cos φ`:

```
(c² + t² - m²) / (2 c t)  =  (b² + t² - n²) / (2 b t)
⟺ b·(c² + t² - m²) = c·(b² + t² - n²)
⟺ (b - c) · (t² - bc) + (c·n² - b·m²) = 0
```

This is one equation in five unknowns. **Crucially, this single equation does not yet
imply `m·b = n·c`** — additional constraints from `m + n = a` (collinearity of D on
BC) and a similar pair at vertex B / C are needed. Path B is therefore strictly more
roundabout than Path A; preserved here only because it routes through theorems already
in Mathlib's `Triangle.lean` rather than constructing them locally.

### Path C — Parallel-line / similar-triangles classical proof

Construct `E` on ray `AD` extended past `D` with `CE ∥ AB`. By alternate interior
angles, `∠CEA = ∠BAE`; combined with the bisector hypothesis `∠BAE = ∠CAE`, the
triangle `ACE` is isoceles with `AC = CE`. Triangles `ABD` and `ECD` are similar
(angles match), yielding `BD/DC = AB/CE = AB/AC = c/b`, hence `m·b = n·c`.

**Eliminated for S2 starter.** Mathlib lacks:
* a packaged "alternate interior angles" lemma in affine form,
* a packaged similarity / AA-criterion for triangles,
* a packaged parallel-line construction in `EuclideanGeometry`.

Each of these would need ~50-100 lines of supporting development before the
classical argument can be carried out. Path A produces a working derivation
faster.

### Recommendation

**S2 implements Path A.** Path B is the natural fallback if a non-trivial obstruction
shows up in Step 4 (the non-collinearity-to-strict-Cauchy-Schwarz step). Path C is
parked behind a "first build the parallel-line library" prerequisite and is not
recommended for S2.

---

## §4. Mathlib API survey

The following lemmas are the **load-bearing dependencies** for Path A. Locations
quoted from `Mathlib` package at the version pinned by `proofs/lakefile.toml`.

### §4.1. Affine / between

| Lemma | Location | Use |
|-------|----------|-----|
| `Sbtw` | `Mathlib/Analysis/Convex/Between.lean:123` | Hypothesis carrier for `D ∈ open segment BC`. |
| `Sbtw.mem_image_Ioo` | `Mathlib/Analysis/Convex/Between.lean:215` | Extracts `s ∈ Ioo 0 1` with `D = lineMap B C s`. |
| `Sbtw.ne_left`, `Sbtw.ne_right`, `Sbtw.left_ne`, `Sbtw.right_ne` | `Mathlib/Analysis/Convex/Between.lean:203–212` | Non-coincidence facts `D ≠ B`, `D ≠ C`. |
| `Wbtw`, `wbtw_smul_vadd_smul_vadd_of_nonneg_of_le` | `Mathlib/Analysis/Convex/Between.lean` | Build the parametrization if `mem_image_Ioo` is awkward. |
| `AffineMap.lineMap` | `Mathlib/LinearAlgebra/AffineSpace/AffineMap.lean` | Concrete `(1 - s) • B + s • C` formula. |

### §4.2. Angles in Euclidean affine spaces

| Lemma | Location | Use |
|-------|----------|-----|
| `EuclideanGeometry.angle` | `Mathlib/Geometry/Euclidean/Angle/Unoriented/Affine.lean:43` | The `∠ p₁ p₂ p₃` notation, defined as `InnerProductGeometry.angle (p₁ -ᵥ p₂) (p₃ -ᵥ p₂)`. |
| `InnerProductGeometry.angle` | `Mathlib/Analysis/InnerProductSpace/Basic.lean` | `Real.arccos (⟪x,y⟫ / (‖x‖ * ‖y‖))`. |
| `InnerProductGeometry.cos_angle` | `Mathlib/Analysis/InnerProductSpace/Basic.lean` | `Real.cos (angle x y) = ⟪x,y⟫ / (‖x‖ * ‖y‖)`. |
| `Real.arccos_injOn` | `Mathlib/Analysis/SpecialFunctions/Trigonometric/Inverse.lean` | Injectivity of `arccos` on `[-1, 1]` → angle equality ⇔ cosine equality (given both ∈ `[0,π]`). |
| `EuclideanGeometry.angle_eq_pi_iff_sbtw` | `Mathlib/Geometry/Euclidean/Angle/Unoriented/Affine.lean:278` | (sibling check) "angle equals π iff strict-between". |
| `EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi` | `Mathlib/Geometry/Euclidean/Angle/Unoriented/Affine.lean:172` | Supplementary-angles fact for collinear points. |

### §4.3. Distances / norms

| Lemma | Location | Use |
|-------|----------|-----|
| `dist_eq_norm_vsub` | `Mathlib/Analysis/Normed/Group/AddTorsor.lean` | `dist p₁ p₂ = ‖p₁ -ᵥ p₂‖`. |
| `norm_smul` | `Mathlib/Analysis/Normed/Module.lean` | `‖r • x‖ = ‖r‖ * ‖x‖`, for `r ∈ ℝ` reduces to `|r| * ‖x‖`. |
| `abs_of_pos`, `abs_of_nonneg` | `Mathlib.Order.AbsoluteValue` | Strip absolute values once `s ∈ Ioo 0 1`. |
| `real_inner_self_eq_norm_mul_norm` | `Mathlib/Analysis/InnerProductSpace/Basic.lean` | `⟪x, x⟫ = ‖x‖ * ‖x‖`. |
| `real_inner_comm` | `Mathlib/Analysis/InnerProductSpace/Basic.lean` | `⟪x, y⟫ = ⟪y, x⟫`. |
| `inner_smul_left`, `inner_smul_right` | `Mathlib/Analysis/InnerProductSpace/Basic.lean` | Pull out scalars from `⟪_,_⟫`. |
| `inner_add_left`, `inner_add_right` | `Mathlib/Analysis/InnerProductSpace/Basic.lean` | Bilinearity. |

### §4.4. Non-degeneracy / Cauchy-Schwarz strict form

| Lemma | Location | Use |
|-------|----------|-----|
| `Collinear` | `Mathlib/LinearAlgebra/AffineSpace/Independent.lean` | Three-point collinearity predicate. |
| `EuclideanGeometry.collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi` | `Mathlib/Geometry/Euclidean/Angle/Unoriented/Affine.lean:376` | Collinearity ⇔ angle ∈ {0, π}. |
| `abs_real_inner_le_norm` | `Mathlib/Analysis/InnerProductSpace/Basic.lean` | `\|⟪x, y⟫\| ≤ ‖x‖ * ‖y‖` (Cauchy-Schwarz). |
| `real_inner_eq_norm_mul_iff` | `Mathlib/Analysis/InnerProductSpace/Basic.lean` (or nearby) | Equality case of Cauchy-Schwarz ⇔ linear dependence. |
| `LinearIndependent.pair_iff` | `Mathlib/LinearAlgebra/LinearIndependent.lean` | Linear independence of two vectors. |

### §4.5. Stewart's theorem and the parent file

The parent `LawOfCosinesOQ04OQ02.lean` re-exports `StewartsTheorem.stewarts_theorem`
from `LawOfCosinesOQ04.lean`. The new file `LawOfCosinesOQ04OQ02OQ01.lean` should
import both `LawOfCosinesOQ04OQ02` and the affine geometry lemmas, then chain its
geometric `angle_bisector_ratio_from_geometry` into the existing
`AngleBisectorLength.angle_bisector_squared`.

---

## §5. Risk register

| Risk | Likelihood | Severity | Mitigation |
|------|-----------|---------|------------|
| `Sbtw.mem_image_Ioo` signature differs from expectation (uses `image (lineMap …) (Ioo …)` rather than direct `∃ s`). | Medium | Low | Wrap with `Set.mem_image` unpacking; one extra lemma. |
| Inner-product expansion blow-up; `ring` cannot close the factorization. | Medium | Medium | Hand-factor as `((1-s)·c - s·b) · (bc - ⟪u,v⟫)` via `linear_combination` witness. |
| Non-degeneracy obligation requires extra hypotheses beyond `¬ Collinear`. | Low | Medium | If so, fall back to `B ≠ A ∧ C ≠ A ∧ ⟪u,v⟫ < ‖u‖·‖v‖` as primary form. |
| `EuclideanGeometry.angle` definition uses `arccos`, so the equality step (angle ⇒ cosine) needs `arccos_injOn` plumbing. | High | Low | Standard pattern; copy from `EuclideanGeometry.Triangle.lean` (e.g. line 76's `arccos_injOn` invocation). |
| Mathlib version drift renames `Sbtw` or `mem_image_Ioo`. | Low | High | Pin Mathlib via `lakefile.toml`; reference exact lemma names in S2. |
| Decreased angle vs un-normalized arc: `arccos` injectivity needs `[-1,1]` bounds, requires `‖u‖ * ‖D -ᵥ A‖ ≠ 0` and the inner-product Cauchy-Schwarz inequality. | Low | Low | Trivially true under our non-degeneracy hypotheses. |

---

## §6. Sibling-proof lessons

* **`CevasTheoremOQ02OQ01OQ03.lean`** (Ceva with side-length weights) discusses the
  angle-bisector instance (`α_D = AC, β_D = AB`) but stays in the algebraic-parametric
  world (lines 232–280). The same OQ-type extension applies — the geometric
  derivation here would unblock a Ceva-on-actual-points version.

* **`LawOfCosinesOQ04.lean`** (Stewart) is also algebraic. Its `h_ABD` / `h_ACD`
  hypotheses are precisely the per-sub-triangle law-of-cosines instances; they
  would be discharged from a geometric setup using
  `EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle`
  (Mathlib `Triangle.lean` line ~190). A geometric `LawOfCosinesOQ04OQ02OQ01.lean`
  would establish the template that subsequent Stewart-geometric proofs reuse.

* **The Mathlib upstream gap.** Mathlib's `Geometry/Euclidean/Triangle.lean` has the
  *vector-angle* law of cosines and Pons asinorum, but **no angle-bisector theorem**,
  **no median-length theorem**, and **no Stewart's theorem**. The natural Mathlib
  contribution path is `Mathlib.Geometry.Euclidean.AngleBisector` introducing
  `angleBisector_length_sq_eq` and `angle_bisector_ratio`. This OQ produces the
  prototype.

---

## §7. Outcome of S1

* Located the `hbis : m * b = n * c` hypothesis in three theorems of
  `LawOfCosinesOQ04OQ02.lean` (lines 89, 110, 134).
* Reformulated the OQ as: prove `s = c / (b + c)` (where `s ∈ Ioo 0 1` is the
  `Sbtw`-extracted barycentric parameter), from `∠ B A D = ∠ D A C`.
* Surveyed three derivation paths and selected **Path A** (inner-product factorization)
  as the S2 target.
* Identified all load-bearing Mathlib lemmas (§4) — no missing primitives.
* Identified the natural Mathlib-contribution package
  (`Mathlib.Geometry.Euclidean.AngleBisector`).

S2 deliverable: a new file `proofs/Proofs/LawOfCosinesOQ04OQ02OQ01.lean` (~250-350
lines), with headline theorem `angle_bisector_ratio_from_geometry` and a chained
`angle_bisector_length_geometric` re-stating the parent's identity entirely in
metric/angle terms. Zero sorries, zero `axiom` declarations.

---

## §8. Next-action menu

* **S2 (recommended)**: Implement Path A — the inner-product factorization.
  Order of lemmas:
  1. `bisector_param_exists` — from `Sbtw ℝ B D C` extract `s ∈ Ioo 0 1` with
     `D -ᵥ A = (1 - s) • (B -ᵥ A) + s • (C -ᵥ A)`.
  2. `bisector_dist_BD`, `bisector_dist_DC` — `dist B D = s * dist B C` and
     `dist D C = (1 - s) * dist B C`.
  3. `cos_angle_BAD_expand`, `cos_angle_DAC_expand` — expand cosines in terms of
     `s, b, c, ⟪u, v⟫, ‖D -ᵥ A‖`.
  4. `bisector_factor_eq` — from `cos(∠BAD) = cos(∠DAC)` (plus arccos injectivity),
     derive `((1-s) c - s b) · (b c - ⟪u, v⟫) = 0`.
  5. `inner_lt_norm_mul_norm_of_not_collinear` — discharge the
     `b c - ⟪u, v⟫ ≠ 0` factor.
  6. `angle_bisector_ratio_from_geometry` — chain (4) + (5) to `s = c / (b + c)`,
     and produce `m · b = n · c`.
  7. `angle_bisector_length_geometric` — invoke parent
     `angle_bisector_length` with the derived `hbis`, `ha`, plus sub-triangle
     law-of-cosines applications for `h_ABD`, `h_ACD`.

* **S2 (alternative)**: Implement Path B if the Step-3 factorization in Path A
  hits a `ring`-failure obstruction. Higher risk; preserved as fallback only.

* **S3**: Wire up gallery entry `src/data/proofs/law-of-cosines-oq-04-oq-02-oq-01/`
  with `meta.json`, `index.ts`, optional `annotations.json`. Update parent
  `law-of-cosines-oq-04-oq-02/meta.json` `openQuestions` to mark this as resolved.

* **Mathlib path**: Extract a clean `Mathlib.Geometry.Euclidean.AngleBisector`
  module candidate as a separate follow-up PR after S2 lands.
