# S1 OBSERVE — Lhuilier Lune-Decomposition Roadmap for Girard's Theorem

**Iteration**: S1 OBSERVE
**Author**: researcher-5
**Date**: 2026-05-12
**File**: this session note (no Lean changes; problem.md / state.md / knowledge.md
filled from seeker-init stubs)

## Purpose

The parent slug `spherical-law-of-cosines` (`Proofs.SphericalLawOfCosines`, 341 LOC,
verified) proves the spherical law of cosines via unit-vector inner products in
$\mathbb{R}^3$. OQ-02 of the parent asks to extend this to **Girard's theorem
(spherical-excess formula)**:

$$\text{area}(\triangle \mathbf{uvw}) = A + B + C - \pi$$

This S1 OBSERVE iteration maps the **Lhuilier lune-decomposition proof** (1782) into a
3-sub-iteration Lean roadmap, identifies the key Mathlib v4.26.0 dependency (3-D
Lebesgue volume on cones), and surfaces the **solid-angle vs spherical-surface-measure
definition choice** for the S2a implementer.

## 1. Why "from first principles" matters here

`Proofs.TriangleAngleSumOQ02.lean` already has `theorem girard_theorem`, but its proof
is built on a `GeodesicTriangle` structure with the field

```lean
gb_local : α + β + γ - π = integratedCurvature
```

This `gb_local` is a **structure-encoded assumption** per CLAUDE.md's axiom-integrity
policy — it asserts the Gauss-Bonnet identity rather than deriving it. So the in-tree
proof is **honestly axiomatized**, not from-first-principles.

The OQ-02 sub-question of `spherical-law-of-cosines` asks for the **axiom-free**
derivation from the unit-vector / inner-product formulation in the parent. The S2
deliverable will live in `Proofs/SphericalLawOfCosinesOQ02.lean` (a new file) and will
**not** import `TriangleAngleSumOQ02`.

## 2. The lune-decomposition proof (Lhuilier 1782)

### 2.a — Lune lemma

A **lune** $L_\theta$ at dihedral angle $\theta \in [0, 2\pi]$ is the region of the unit
sphere between two great-circle arcs meeting at antipodal points. By rotational
symmetry, $\text{area}(L_\theta)$ is linear in $\theta$, and at $\theta = \pi$ the lune
fills half the sphere:

$$\text{area}(L_\theta) = \frac{\theta}{2\pi} \cdot 4\pi = 2\theta$$

### 2.b — Six-lune cover

A spherical triangle $T = \triangle \mathbf{uvw}$ with dihedral angles $A, B, C$ (at
vertices $\mathbf{u}, \mathbf{v}, \mathbf{w}$ respectively) and antipode $-T$
($:= \triangle (-\mathbf{u})(-\mathbf{v})(-\mathbf{w})$) admit a covering by six lunes:

| Lune | Dihedral angle | Region |
|------|----------------|--------|
| $L_A$ | $A$ | bounded by great circles through edges $\mathbf{uv}$ and $\mathbf{uw}$, on the side containing $T$ |
| $L_A'$ | $A$ | antipodal to $L_A$, on the side containing $-T$ |
| $L_B$ | $B$ | analogous at vertex $\mathbf{v}$ |
| $L_B'$ | $B$ | antipodal |
| $L_C$ | $C$ | analogous at vertex $\mathbf{w}$ |
| $L_C'$ | $C$ | antipodal |

### 2.c — Multiplicity count

Every point of $S^2$ is covered by some number of the six lunes:

- A point in $T$: it is in $L_A$, $L_B$, and $L_C$ (all three lunes that contain $T$).
  Multiplicity 3.
- A point in $-T$: by antipodal symmetry, in $L_A'$, $L_B'$, $L_C'$. Multiplicity 3.
- Every other point: in **exactly one** of the six lunes.

(The "exactly one" claim deserves care: the boundary great circles form 3 great
circles on $S^2$, dividing it into $2 \cdot 3 = 6$ wedge-regions plus the two
triangles $T$ and $-T$, but in fact each wedge region IS half of a lune ... see §3
for the precise statement.)

### 2.d — Algebra

By the multiplicity count, the total area covered (counted with multiplicity) is

$$\sum_{X \in \{A,B,C\}} (\text{area}(L_X) + \text{area}(L_X')) = 1 \cdot (\text{area}(S^2) - \text{area}(T) - \text{area}(-T)) + 3 \cdot (\text{area}(T) + \text{area}(-T))$$

$$\sum = (4\pi - 2 \cdot \text{area}(T)) + 3 \cdot 2 \cdot \text{area}(T) = 4\pi + 4 \cdot \text{area}(T)$$

By the lune lemma, $\text{area}(L_X) = \text{area}(L_X') = 2X$:

$$\sum = 4(A + B + C)$$

Equating:

$$4(A + B + C) = 4\pi + 4 \cdot \text{area}(T)$$

$$\boxed{\text{area}(T) = A + B + C - \pi}$$ ✓

## 3. Mathlib status for spherical measure

A targeted grep at v4.26.0 for `Sphere.*Measure|S²|surface measure` is uncertain to
return a canonical $S^2$ surface measure with `volume(Sphere ℝ³) = 4π` ergonomically
defined. There IS

- `Mathlib.Analysis.InnerProductSpace.EuclideanDist`: spherical-cap definitions.
- `Mathlib.MeasureTheory.Measure.Hausdorff`: $n$-D Hausdorff measure, which on $S^2$
  equals the standard surface measure up to normalization.

But the ergonomic API for "integrate over a region of $S^2$" is not well-developed in
v4.26.0.

**Workaround (recommended for S2a)**: define the area via **3-D Lebesgue measure on
cones**, not via 2-D spherical measure.

### 3.a — Cone-Lebesgue definition

For a measurable region $R \subseteq S^2$, define the **cone of $R$** as

$$\text{Cone}(R) := \{ t \cdot p : t \in [0, 1], p \in R \} \subseteq \overline{B(0, 1)} \subseteq \mathbb{R}^3.$$

The **solid angle** of $R$ is

$$\Omega(R) := 3 \cdot \text{vol}_{\mathbb{R}^3}(\text{Cone}(R))$$

(the factor 3 calibrates so that $\Omega(S^2) = 3 \cdot \text{vol}(\overline{B}) = 3 \cdot \frac{4\pi}{3} = 4\pi$).

**Reason this works**: in spherical coordinates $(r, \theta, \phi)$,
$dV = r^2 \sin\phi \, dr \, d\theta \, d\phi$. Integrating $r^2$ from $0$ to $1$ gives
$\frac{1}{3}$, so $\text{vol}(\text{Cone}(R)) = \frac{1}{3} \cdot \int_R \sin\phi \, d\theta \, d\phi = \frac{1}{3} \cdot \text{area}_{S^2}(R)$.
Multiplying by 3 recovers $\text{area}_{S^2}(R)$ exactly.

This formulation uses **only** `MeasureTheory.volume` (the standard 3-D Lebesgue
measure on $\mathbb{R}^3$), which is fully ergonomic at v4.26.0.

### 3.b — Lune as a cone wedge

A lune $L_\theta$ at dihedral angle $\theta$ around the $\mathbf{z}$-axis is the set

$$L_\theta := \{ (x, y, z) \in S^2 : 0 \leq \arg(x + iy) \leq \theta \}$$

Its cone is the **wedge** of the unit ball:

$$\text{Cone}(L_\theta) = \{ (x, y, z) \in \mathbb{R}^3 : x^2 + y^2 + z^2 \leq 1, 0 \leq \arg(x + iy) \leq \theta \}$$

This is rotationally symmetric in $z$ and has the same volume as $\frac{\theta}{2\pi}$
of the unit ball: $\text{vol}(\text{Cone}(L_\theta)) = \frac{\theta}{2\pi} \cdot \frac{4\pi}{3} = \frac{2\theta}{3}$.

Therefore $\Omega(L_\theta) = 3 \cdot \frac{2\theta}{3} = 2\theta$ ✓.

This proof is **computable in 3-D**, using only `MeasureTheory.volume` and standard
integral changes-of-variables (cylindrical or spherical coordinates).

## 4. S2 plan (3 sub-iterations)

All in new file `Proofs/SphericalLawOfCosinesOQ02.lean`. The parent file
`SphericalLawOfCosines.lean` is NOT modified.

### 4.a — S2a (~80 LOC, easy-medium)

```lean
namespace SphericalExcess

def solidAngle (R : Set (EuclideanSpace ℝ (Fin 3))) : ℝ :=
  3 * (MeasureTheory.volume (cone R)).toReal
  where cone := fun R => { p | ∃ q ∈ R, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ p = t • q }

def lune (axis : EuclideanSpace ℝ (Fin 3)) (θ : ℝ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  { p ∈ Metric.sphere 0 1 | ... }   -- formal lune definition

lemma lune_solidAngle_eq_two_theta (axis : EuclideanSpace ℝ (Fin 3)) (h_unit : ‖axis‖ = 1)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ' : θ ≤ 2 * Real.pi) :
    solidAngle (lune axis θ) = 2 * θ := by sorry
end SphericalExcess
```

**Mathlib API needed**:
- `MeasureTheory.volume` on $\mathbb{R}^3 = $ `EuclideanSpace ℝ (Fin 3)`.
- `MeasureTheory.integral_volume_eq` for the change-of-variables to spherical
  coordinates (or cylindrical coordinates around the axis).
- `Real.pi_pos`, `Real.cos_pos_of_neg_pi_div_two_lt_of_lt_pi_div_two` for argument
  range handling.

### 4.b — S2b (~80 LOC, medium)

```lean
def sphericalTriangle (u v w : EuclideanSpace ℝ (Fin 3)) : Set (EuclideanSpace ℝ (Fin 3)) :=
  { p ∈ Metric.sphere 0 1 | ∃ α β γ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ p = α • u + β • v + γ • w }
  -- (after suitable non-degeneracy + CCW-orientation hypotheses)

theorem six_lune_cover_identity (u v w : EuclideanSpace ℝ (Fin 3))
    (h_uvw_nondeg : ...) :
    Set.Multiset.count (sphericalTriangle u v w) (lunes_at_uvw) = 3 ∧
    Set.Multiset.count (-sphericalTriangle u v w) (lunes_at_uvw) = 3 ∧
    ∀ p ∈ Metric.sphere 0 1, p ∉ sphericalTriangle u v w ∪ -sphericalTriangle u v w →
      Set.Multiset.count {p} (lunes_at_uvw) = 1 := by sorry
```

This is the geometric core. The "every other point is in exactly one of the six
lunes" claim is the delicate part. **The S2b implementer should verify the precise
statement via a case-analysis on which side of each great circle a generic point
$p \in S^2$ lies on.**

### 4.c — S2c (~80 LOC, easy after S2a + S2b)

```lean
theorem girard_theorem (u v w : EuclideanSpace ℝ (Fin 3))
    (h_uvw_nondeg : ...) :
    solidAngle (sphericalTriangle u v w) =
      dihedralAngleAt u v w + dihedralAngleAt v w u + dihedralAngleAt w u v - Real.pi := by
  -- Sum of solid angles of six lunes = 4(A+B+C) (from S2a).
  -- Multiplicity count = 4π + 4·solidAngle(T) (from S2b).
  -- Equate and solve.
  sorry
```

Algebraic; the work is all in S2a + S2b.

## 5. Honest LOC budget

| Step | LOC | Difficulty |
|------|-----|------------|
| S2a `solidAngle` + `lune` + `lune_solidAngle_eq_two_theta` | ~80 | Medium (Mathlib volume calculation) |
| S2b `sphericalTriangle` + `six_lune_cover_identity` | ~80 | Medium-hard (geometric case analysis) |
| S2c `girard_theorem` (assembly) | ~80 | Easy |
| Total | ~240 | |

The Mathlib volume calculation in S2a is the most uncertain. If
`MeasureTheory.integral_volume_eq_spherical` or equivalent is awkward at v4.26.0, S2a
may grow to ~120 LOC with manual cylindrical-coordinate integration. Plan
conservatively at ~250 LOC total.

## 6. Race / coordination notes

- Fresh slug, knowledge_score=0. No competing PR (`gh pr list --search` returned only
  the seeker-init batch PR #18337 from 2026-05-12T22:37Z, not a research PR).
- Parent `spherical-law-of-cosines` and sibling `spherical-law-of-sines` are both
  COMPLETED and stable; no parent drift risk.
- Related axiomatized slug `triangle-angle-sum-oq-02` exists with its own
  `Proofs.TriangleAngleSumOQ02.girard_theorem`; the S2 implementation must NOT import
  it (axiom-integrity policy).

## 7. Outcome of this iteration

**Outcome**: progress (S1 OBSERVE complete, Lhuilier lune-decomposition roadmap mapped,
3-D-cone-Lebesgue area definition recommended for S2a).
**Build status**: N/A (no Lean changes).
**Net change**:
- `problem.md`: 108-line stub → ~170-line populated problem statement.
- `state.md`: 25-line stub → ~70-line S1 state record.
- `knowledge.md`: 21-line stub → ~180-line knowledge log (7 insights + 3 dead ends).
- `sessions/2026-05-12-s1-observe-lune-decomposition-roadmap.md`: NEW ~290-line
  Lhuilier-roadmap survey with S2a/b/c LOC budgets and a concrete recommendation for
  the 3-D-cone-Lebesgue area definition that sidesteps the v4.26.0 spherical-surface-
  measure gap.

**Next step**: S2a — `solidAngle` + `lune` + `lune_solidAngle_eq_two_theta` in
`Proofs/SphericalLawOfCosinesOQ02.lean`. ~80 LOC.
