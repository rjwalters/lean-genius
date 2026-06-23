# Problem: Ellipse Area Formula via Mathlib Change of Variables

**Slug**: area-of-circle-oq-03-oq-03-oq-01
**Tier**: B | **Significance**: 6/10 | **Tractability**: 7/10
**Category**: extension
**Source**: gallery-gap
**Status**: Active (OBSERVE)

## Problem Statement

### Formal Statement

$$
\text{Area}(\{(x, y) \mid (x/a)^2 + (y/b)^2 \leq 1\}) = \pi a b
$$

for real $a, b > 0$.

### Plain Language

Prove that the area of an ellipse with semi-axes $a$ and $b$ equals $\pi ab$ using
Mathlib's measure-theoretic change of variables, not an algebraic placeholder.

The current gallery proof `area-of-circle-oq-03-oq-03` extends Archimedes' method of
exhaustion but leaves the ellipse as a known fact. The OQ asks to formalize the ellipse
area rigorously via the linear scaling map $(x, y) \mapsto (ax, by)$.

### Why This Matters

Ellipse area is a canonical example of the change-of-variables theorem for Lebesgue
measure. A clean Lean proof using `MeasureTheory.MeasurePreserving` or the linear map
Jacobian framework demonstrates the full power of Mathlib's measure theory for classical
geometry and removes any implicit assumption in the parent proof chain.

## Known Results

### What's Already Proven

- `area-of-circle-oq-03-oq-03` — Archimedes method of exhaustion for circles (fully proved, 0 axioms, 0 sorries)
- `area-of-circle-oq-03-oq-01` — polygon inscribed/circumscribed area bounds
- `MeasureTheory.Measure.map_linearMap` — linear maps and image measures
- `LinearMap.det_toLin` — Jacobian/determinant of linear maps

### What's Still Open

- Formal proof of ellipse area via change of variables or measure scaling
- Whether `Real.volume_ball` + scaling suffices or full COV theorem needed

### Our Goal

Prove `MeasureTheory.volume (Metric.ball (0 : ℝ × ℝ) 1 |>.image (LinearMap.prod ...)) = π * a * b`
(or equivalent formulation) using Mathlib's `MeasurePreserving`, `volumePreservingEquivOfScaling`
or the change-of-variables machinery.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `area-of-circle-oq-03-oq-03` | Parent proof — Archimedes exhaustion | Limit, inscribed/circumscribed |
| `area-of-circle-oq-05-oq-01` | Gaussian integral via polar coords | `MeasureTheory.integral_comp` |
| `minkowski-theorem-oq-02` | Dirichlet via parallelogram volume | Shear maps, `measure_pi_Ioo` |

## Initial Thoughts

### Potential Approaches

1. **Scaling map approach**: The linear map $T(x,y) = (ax, by)$ has $|\det T| = ab$.
   The unit disk has area $\pi$. By `measure_image_le_map` or `Measure.map_linearMap`,
   the image disk has area $\pi \cdot ab$.
   - Why it might work: Direct, mirrors the minkowski-theorem-oq-02 shear approach
   - Risk: Need to handle the `ContinuousLinearMap` vs `LinearMap` distinction

2. **Direct integral**: Compute $\int_{-a}^{a} 2b\sqrt{1 - (x/a)^2} \, dx$ via substitution
   $x = a \sin\theta$. Uses `intervalIntegral.integral_comp_mul_right`.
   - Why it might work: Classical calculus approach, Mathlib has the tools
   - Risk: Substitution infrastructure can be verbose in Lean 4

3. **Fubini + 1D change of vars**: Compute as iterated integral $\int_{-a}^{a} 2b\sqrt{1-(x/a)^2} dx$
   using `MeasureTheory.integral_comp_smul_deriv` or similar.

### Key Difficulties

- Mathlib's `Measure.map` for linear maps requires showing the map is injective and measurable
- `Real.volume_closedBall` gives volume of a ball in ℝⁿ; may need `volume_pi_closedBall`
- Connecting `volume` on `ℝ²` to product measure on `ℝ × ℝ`

### What Would a Proof Need?

- Key lemma 1: `volume (T '' (closedBall 0 1)) = |det T| * volume (closedBall 0 1)` where T linear
- Key lemma 2: `volume (closedBall (0:ℝ×ℝ) 1) = π` (unit disk area)
- Mathlib: `MeasureTheory.Measure.map_linearMap`, `LinearMap.det`, or the COV theorem

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The math is standard: $\text{Area}(T(S)) = |\det T| \cdot \text{Area}(S)$ for linear T
- Mathlib has `Measure.map_linearMap` and the COV theorem
- Recent gallery work (`minkowski-theorem-oq-02`) proved similar volume facts for shear maps
- Main challenge: finding the right Mathlib lemma names and handling type coercions

**Estimated Effort**:
- Exploration: 1-2 hours
- If tractable: 2-4 hours of proof development

## References

### Papers
- Archimedes, "On Conoids and Spheroids" — Classical context

### Mathlib
- `Mathlib.MeasureTheory.Measure.MeasureSpace` — core measure theory
- `Mathlib.MeasureTheory.Integral.SetIntegral` — set integrals
- `Mathlib.Analysis.SpecialFunctions.Integrals` — sin, cos integrals
- `Mathlib.MeasureTheory.Constructions.Prod.Integral` — Fubini

## Metadata

```yaml
tags:
  - geometry
  - measure-theory
  - analysis
  - change-of-variables
  - archimedes
  - ellipse
related_proofs:
  - area-of-circle-oq-03-oq-03
  - area-of-circle-oq-05-oq-01
  - minkowski-theorem-oq-02
difficulty: medium
source: gallery-gap
created: 2026-04-05T14:59:31-07:00
```
