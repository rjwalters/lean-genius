# Problem: Complete Pascal's Hexagon Theorem — Sylvester's Law Sorry

**Slug**: pascals-hexagon-incomplete-01
**Created**: 2026-04-21
**Status**: Active
**Source**: gallery-incomplete

## Problem Statement

### Plain Language

`PascalsHexagon.lean` formalizes Pascal's theorem (Wiedijk #77) with one remaining
`sorry`: the Sylvester's law step that connects an arbitrary real conic to the standard
conic via a projective transformation. All other steps are proved. The goal is to
eliminate this sorry by formalizing Sylvester's law of inertia for quadratic forms.

### Formal Statement

The sorry appears in `proof_sketch_conic_implies_pascal` (line 1134):

```lean
obtain ⟨M, hM_det, hM_eq⟩ : ∃ (M : Matrix (Fin 3) (Fin 3) ℝ),
    M.det ≠ 0 ∧
    ∀ (p : ProjPoint), pointOnConic p C ↔
      pointOnConic (projTransform M p) stdConic := by
  sorry -- Sylvester's law: build M from Mathlib's spectral theorem
```

### Why This Matters

This is a concrete Wiedijk-100 gallery completion. Pascal's hexagon theorem (that
opposite sides of a hexagon inscribed in a conic are collinear) is a cornerstone of
projective geometry. Completing it removes the one known sorry in this proof file.

## Known Results

### What's Already Proven

- All individual case steps in the Pascal proof are done
- `projTransform` and `stdConic` are defined
- `ProjPoint` and `Conic` structures are in place
- The reduction to standard conic is identified as the missing piece

### Our Goal

Prove that any non-degenerate real conic (symmetric 3×3 matrix of signature (2,1))
is projectively equivalent to `stdConic = x² + y² - z²` by constructing the
diagonalizing invertible matrix M.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| pascals-hexagon | Source file with the sorry | Projective geometry, quadratic forms |

## Initial Thoughts

### Potential Approaches

1. **Mathlib QuadraticForm path**: Use `QuadraticForm.equivalent` or Sylvester's
   inertia result if it exists in Mathlib's `Analysis.InnerProductSpace` or
   `LinearAlgebra.QuadraticForm`
   - Risk: Mathlib may not have Sylvester inertia in the exact form needed

2. **Spectral theorem + reordering**: Apply `Matrix.IsHermitian.spectral_theorem` to
   diagonalize, then permute eigenvalues by sign to get signature (2,1)
   - Risk: Signature manipulation may require nontrivial intermediate steps

### Key Difficulties

- Connecting `Conic` (defined as a matrix type in PascalsHexagon.lean) to Mathlib's
  abstract `QuadraticForm`
- Ensuring the constructed M is computable / constructive enough for `exact`

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Sylvester's law is classical and should have Mathlib support
- The proof structure is already scaffolded; only one `sorry` remains
- The hardest part is bridging Mathlib's abstract quadratic form API to the
  matrix-based `Conic` definition in the file

## Metadata

```yaml
tags:
  - geometry
  - projective-geometry
  - quadratic-forms
  - wiedijk-100
  - completion
related_proofs:
  - pascals-hexagon
difficulty: medium
source: gallery-incomplete
created: 2026-04-21
```

**Significance**: 7/10
**Tractability**: 6/10
