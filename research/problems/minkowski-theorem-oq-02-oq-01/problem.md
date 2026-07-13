# Problem: Eliminate Measure-Theoretic Axioms from Dirichlet Approximation via Minkowski

**Slug**: minkowski-theorem-oq-02-oq-01
**Created**: 2026-04-05T04:18:32-07:00
**Status**: Active
**Source**: gallery-gap
**Tier**: B
**Significance**: 8/10
**Tractability**: 7/10

## Problem Statement

### Formal Statement

The proof `MinkowskiTheoremOQ02.lean` formalizes Dirichlet's Approximation Theorem via Minkowski's
Lattice Point Theorem but relies on three axioms:

1. **`dirichletSet_convex`**: The parallelogram $\{(x,y) : |x| < Q+1, |\alpha x - y| < 1/Q\}$ is convex.
2. **`dirichletSet_measurable`**: The parallelogram is Lebesgue measurable.
3. **`dirichletSet_volume`**: Its area equals $4(Q+1)/Q$.

**Goal**: Eliminate all three axioms by proving them from Mathlib's measure theory.

### Plain Language

Dirichlet's Approximation Theorem says: for any real $\alpha$ and positive integer $Q$, there exist
integers $p, q$ with $1 \leq q \leq Q$ such that $|q\alpha - p| < 1/Q$.

The existing Lean proof proceeds via Minkowski's theorem (integer lattice points in convex symmetric
sets with volume $> 4$), but assumes three measure-theoretic facts about the target parallelogram.
The task is to fill these in from Mathlib.

### Why This Matters

- Removes all remaining assumptions, making the proof fully axiom-free
- The three axioms are all provable from standard Mathlib measure theory
- Same pattern as successful `fourier-series-oq-01-oq-02` and `lebesgue-measure-oq-01-oq-02` eliminations
- Connects `MeasureTheory.Measure.map` (shear maps) to Fubini for volume computation

## Known Results

### What's Already Proven

- **Minkowski's theorem** (`MinkowskiProved.minkowski_integer_lattice_proved`): If $S$ is
  convex, symmetric, measurable with volume $> 4$, it contains a non-zero integer lattice point.
- **All logical steps** of Dirichlet's theorem from the three axioms — fully formalized.
- **Fubini's theorem** in Mathlib: `MeasureTheory.integral_prod`
- **Shear map measure preservation**: Linear maps preserve Lebesgue measure up to det factor

### The Three Axioms

```lean
-- (1) Convexity: intersection of halfplanes is convex
axiom dirichletSet_convex (Q : ℕ) (α : ℝ) : Convex ℝ (dirichletSet Q α)

-- (2) Measurability: open set (intersection of open halfplanes) is Borel
axiom dirichletSet_measurable (Q : ℕ) (α : ℝ) : MeasurableSet (dirichletSet Q α)

-- (3) Volume: area = 4(Q+1)/Q via Fubini or shear map T(x,y) = (x, αx-y), det(T) = -1
axiom dirichletSet_volume (Q : ℕ) (α : ℝ) : volume (dirichletSet Q α) = ENNReal.ofReal (4 * (Q + 1) / Q)
```

### What's Still Open

- Which Mathlib lemmas bridge `convex_halfspace_le` to the intersection?
- Does `MeasureTheory.Measure.map_linearMap_eq` apply directly to the shear map?
- Is there a direct Fubini computation for this specific parallelogram shape?

### Our Goal

Prove all three axioms as theorems. The resulting proof would have 0 axioms.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `minkowski-theorem-oq-02` | Parent proof (has the 3 axioms) | Minkowski + lattice points |
| `minkowski-theorem` | Minkowski's fundamental theorem | Measure theory, convex geometry |
| `fourier-series-oq-01-oq-02` | Same pattern: eliminate trigPoly axiom | Mathlib span theorems |
| `lebesgue-measure-oq-01-oq-02` | Same pattern: Bochner integral axiom | Measure theory |

## Initial Thoughts

### Potential Approaches

1. **Convexity via halfspace intersection** (Axiom 1):
   - `Convex.inter` + `convex_halfspace_le` or `convex_Ioo`
   - The set $\{|x| < Q+1\}$ is convex (open interval), and $\{|\alpha x - y| < 1/Q\}$ is a
     halfplane — both convex, intersection is convex.

2. **Measurability via open sets** (Axiom 2):
   - Both halfplane conditions are continuous maps, so the set is open → `isOpen.measurableSet`
   - Risk: Low — Borel measurability of open sets is automatic.

3. **Volume via shear map** (Axiom 3):
   - Shear $T(x,y) = (x, \alpha x - y)$ maps the parallelogram to $(-Q-1, Q+1) \times (-1/Q, 1/Q)$
   - $\det(T) = -1$, so $|\det(T)| = 1$, i.e., $T$ is measure-preserving
   - Rectangle volume: $2(Q+1) \cdot 2/Q = 4(Q+1)/Q$
   - Key Mathlib: `MeasureTheory.Measure.map_linearMap_eq`

### Key Difficulties

- Formalizing the shear map $T$ as a `ContinuousLinearMap` with the right determinant
- Expressing the parallelogram as the preimage of a rectangle under $T$
- ENNReal arithmetic for the volume calculation

### What Would a Proof Need?

- `Convex.inter` and `convex_halfspace_le` for axiom 1
- `isOpen.measurableSet` + continuity for axiom 2
- `MeasureTheory.Measure.map_linearMap_eq` + `MeasureTheory.measure_prod_Ioo` for axiom 3

## Tractability Assessment

**Difficulty**: Low-Medium

**Justification**:
- All three axioms correspond to standard Mathlib capabilities
- The shear map approach is concrete and elementary (det = -1)
- Similar to `lebesgue-measure-oq-01-oq-02` which was successfully completed

## References

### Mathlib
- `MeasureTheory.Measure.map_linearMap_eq` — Linear map measure change
- `Convex.inter` — Intersection of convex sets
- `isOpen.measurableSet` — Open sets are measurable

## Metadata

```yaml
tags:
  - geometry
  - number-theory
  - lattice-theory
  - measure-theory
  - axiom-elimination
  - dirichlet-approximation
  - minkowski-theorem
related_proofs:
  - minkowski-theorem-oq-02
  - minkowski-theorem
  - fourier-series-oq-01-oq-02
  - lebesgue-measure-oq-01-oq-02
difficulty: low-medium
source: gallery-gap
created: 2026-04-05T04:18:32-07:00
```
