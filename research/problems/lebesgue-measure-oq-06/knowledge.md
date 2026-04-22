# Knowledge Base: lebesgue-measure-oq-06

Insights accumulated during research on this problem.

---

## Problem Understanding

The Banach-Tarski paradox (1924) is the statement that the unit ball B³ ⊂ ℝ³ can be
decomposed into finitely many disjoint pieces that reassemble into two unit balls under
rigid motions. The paradox relies on non-measurable sets (hence is not a contradiction
of Lebesgue measure) and the Axiom of Choice.

**Research goal**: Formally state the theorem in Lean 4 and identify exactly what Mathlib
infrastructure is needed. A statement-level formalization (with key lemmas sorry'd) is
achievable; a complete proof would require the Hausdorff paradox.

---

## Key Mathematical Facts

### The Proof Strategy (Hausdorff → Banach-Tarski)

1. **Hausdorff paradox** (1914): The unit sphere S² can be partitioned into four sets
   A, B, C, D where D is countable and {A, B, C} is a "paradoxical triplet":
   - A and B∪C are congruent (under some rotation)
   - B and C are congruent (under some rotation)
   This follows from the free subgroup of SO(3).

2. **Free subgroup of SO(3)**: The rotations
   - φ = rotation by arccos(1/3) around the z-axis
   - ψ = rotation by arccos(1/3) around the x-axis
   generate a free group F₂ inside SO(3). This is the algebraic heart of the paradox.

3. **Paradoxical decomposition of F₂**: The free group on 2 generators {a, b} satisfies:
   F₂ = F₂·a ⊔ F₂·b ⊔ {e} (as sets, via a Cayley graph argument).
   From this one constructs a decomposition of S² into 3 pieces each congruent to the whole.

4. **Extension to B³**: By adding the origin and using a "expanding sphere" argument,
   the S² paradox extends to B³.

### Tarski's Equivalence Theorem
The Banach-Tarski paradox is equivalent (via Tarski's theorem) to the statement:
- B³ is **paradoxically decomposable** with respect to the isometry group of ℝ³
- Equivalently: there is no finitely additive, isometry-invariant measure on all subsets of ℝ³
  that agrees with Lebesgue measure on measurable sets.

---

## Mathlib Status

### What Mathlib Has

- `Matrix.SpecialOrthogonalGroup ℝ (Fin 3)`: The SO(3) group
- `Isometry`, `IsometryEquiv`: Isometries of metric spaces
- `EuclideanSpace ℝ (Fin 3)`: ℝ³ as a Euclidean space
- `MeasureTheory.Measure.Lebesgue.Basic`: Lebesgue measure
- `MeasureTheory.Measure.NullMeasurableSet`: Non-measurable set concept
- `FreeGroup`: Free groups in Mathlib
- `Subgroup.IsFreeGroup`: Free subgroups

### What's Missing / Needs Investigation

- **Free subgroup of SO(3)**: Does Mathlib have the fact that SO(3) contains F₂?
  Check: `Mathlib.GroupTheory.FreeProduct`, free subgroups of Lie groups.
- **Hausdorff paradox**: No known Lean 4 formalization found yet.
- **Paradoxical decomposability**: The `IsParadoxicallyDecomposable` predicate needs
  to be defined (not in Mathlib).
- **Rigid motions = SE(3)**: The semidirect product SO(3) ⋊ ℝ³ may need to be set up.

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]
