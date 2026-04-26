# Problem: Napoleon's Theorem: Connection to Discrete Fourier Transform

**Slug**: napoleons-theorem-oq-02
**Created**: 2026-04-22
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

```lean
-- Desired: express Napoleon construction via complex DFT coefficients
theorem napoleon_dft_connection
    (z : Fin 3 → ℂ)
    (ω : ℂ) (hω : IsPrimitiveRoot ω 3) :
    let Z k := Finset.sum Finset.univ (fun j : Fin 3 => z j * ω ^ (j.val * k))
    -- The outer Napoleon centroids are determined by Z 1
    ∃ (center : ℂ), ∀ k : Fin 3,
      napoleon_outer_centroid z k = center + (Z 1 / 3) * ω ^ k.val := by
  sorry
```

### Plain Language

The existing Napoleon's Theorem proof formalizes that erecting equilateral triangles on the
sides of any triangle and connecting their centroids yields an equilateral triangle
("Napoleon's triangle"). This problem asks: can the connection between Napoleon's theorem
and the **Discrete Fourier Transform (DFT)** be made explicit in Lean 4?

The mathematical insight: if the vertices of a triangle are complex numbers z₀, z₁, z₂,
then the 3-point DFT Z_k = Σⱼ zⱼ · ωʲᵏ (ω = e^(2πi/3)) reveals the theorem's structure.
The outer Napoleon triangle is equilateral precisely because the Napoleon construction
symmetrizes the original triangle via 120° rotations — exactly the action of ω.

### Why This Matters

The DFT connection explains *why* Napoleon's theorem holds: the Napoleon construction is
a projection onto the "equilateral component" (frequency 1) in the 3-point DFT of the
vertex sequence. This is a non-obvious bridge between Euclidean geometry and harmonic
analysis, and generalizes via the Napoleon-Douglas-Neumann theorem to n-gons.

## Known Results

### What's Already Proven

- Napoleon's Theorem formalized in `napoleons-theorem` gallery entry (0 sorries)
- `IsPrimitiveRoot` API available in Mathlib
- Complex roots of unity theory in `Mathlib.NumberTheory.CyclotomicPolynomial`

### What's Still Open

- Explicit DFT formulation of Napoleon centroids in Lean
- Proof that equilaterality follows from DFT symmetry (Z₁ coefficient)
- Generalization to Napoleon-Douglas-Neumann (n-gon case)

### Our Goal

Define the Napoleon centroid map using ω = exp(2πi/3), express the 3-point DFT of the
vertices, and prove that the outer Napoleon triangle centroids equal (center) + (Z₁/3)·ωᵏ.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `napoleons-theorem` | Base proof to connect from | Complex arithmetic, rotation |
| `ptolemys-theorem` | Complex number methods in Euclidean geometry | Complex norm, cross-ratio |
| `sqrt2-plus-sqrt3-irrational` | Algebraic number theory (ω is algebraic) | Minimal polynomial |

## Initial Thoughts

### Potential Approaches

1. **Direct centroid computation**: Define napoleon_outer_centroid z k using ω as a
   rotation operator, compute Z₁ explicitly, verify the identity algebraically.
   - Why it might work: straightforward complex arithmetic
   - Risk: connecting to the existing proof's coordinate system may be awkward

2. **DFT symmetry argument**: Show that applying the DFT diagonalizes the Napoleon
   operator, so equilaterality is automatic from Z₀ (centroid), Z₁ (Napoleon triangle),
   Z₂ (complex conjugate component).
   - Why it might work: elegant, generalizes naturally
   - Risk: requires setting up DFT framework cleanly

### Key Difficulties

- The existing Napoleon proof may use real coordinates; need complex number bridge
- Need to define napoleon_outer_centroid formally in complex arithmetic
- IsPrimitiveRoot for ω = Complex.exp (2*π*i/3) requires connecting to Mathlib's API

### What Would a Proof Need?

- Key lemma 1: IsPrimitiveRoot (Complex.exp (2*π*i/3)) 3
- Key lemma 2: napoleon_outer_centroid z k = (z k + z (k+1) + ω*(z (k+1)-z k) + ω⁻¹*(z k-z (k-1)) + ...) / 3 (exact formula depends on orientation)
- Technical requirements: Complex.exp API, Finset.sum for DFT, norm_num for ω³=1

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The mathematical connection is known and explicit
- Mathlib has the necessary components: Complex.exp, IsPrimitiveRoot, Finset.sum
- Main challenge is bridging to the existing Napoleon proof's coordinate system
- Could be proved as a self-contained complex number result without using the gallery proof

**Estimated Effort**:
- Exploration: 1-2 days (understand existing proof, identify complex number bridge)
- If tractable: 3-5 days (set up DFT, prove centroid formula, verify equilaterality)

## References

### Papers
- Napoleon's Theorem via DFT: standard folklore, appears in geometry textbooks
- Douglas, J.: "On the formation of certain plane figures" (Napoleon-Douglas-Neumann generalization)

### Mathlib
- `Mathlib.NumberTheory.CyclotomicPolynomial` — roots of unity, IsPrimitiveRoot
- `Mathlib.Analysis.SpecialFunctions.Complex.Circle` — Complex.exp, arg
- `Mathlib.Algebra.BigOperators.Group.Finset` — Finset.sum for DFT

## Metadata

```yaml
tags:
  - geometry
  - napoleon
  - discrete-fourier-transform
  - complex-analysis
  - harmonic-analysis
  - rotation
  - mathlib
related_proofs:
  - napoleons-theorem
  - ptolemys-theorem
difficulty: medium
source: gallery-gap
created: 2026-04-22
```

**Significance**: 7/10
**Tractability**: 5/10
