# Problem: Dissection of Cubes — Connection to Dehn Invariant Impossibility

**Slug**: dissection-of-cubes-oq-04
**Created**: 2026-04-23T08:50:16+02:00
**Status**: Active
**Source**: gallery-gap
**Parent proof**: dissection-of-cubes-oq-04 (Dehn Invariants for Platonic Solids: Cube Isolation)

## Problem Statement

### Formal Statement

**Primary target** (most tractable):

Using Mathlib's `Module.Flat` infrastructure, prove the remaining axiom in the Platonic solid
Dehn invariant proof:

```lean
-- Currently axiomatized in dissection-of-cubes-oq-04:
axiom tmul_infinite_order_ne_zero :
  ∀ (r : ℝ) (hr : Irrational r) (n : ℤ) (hn : n ≠ 0),
    n • (r ⊗ₜ[ℤ] (1 : ℝ/ℤ)) ≠ 0
```

**Secondary target** (challenging):

Extend the Chebyshev sequence argument (currently proved for arccos(1/3)/π via ℤ[√(5/4)])
to arccos(3/5)/π using ℤ[√5], proving:

```lean
theorem icoAngle_irrational : Irrational (Real.arccos (3/5) / Real.pi)
```

This would yield a fully axiom-free proof that the icosahedron has nonzero Dehn invariant.

### Plain Language

The gallery proof `dissection-of-cubes-oq-04` establishes that the cube is the unique
Platonic solid scissors-congruent to itself (zero Dehn invariant). The proof has two
remaining assumptions:

1. **Flatness axiom**: The tensor product `ℝ ⊗_ℤ (ℝ/ℤ)` is torsion-free. This is a
   consequence of ℝ being a flat ℤ-module, which Mathlib's `Module.Flat` likely supports.

2. **Icosahedron angle irrationality**: The dihedral angle of the icosahedron divided by π
   is irrational. The octahedron case (arccos(1/3)/π) is already proved using a Chebyshev
   sequence in ℤ[√(5/4)] = ℤ[√5]/2. The icosahedron requires ℤ[√5].

### Why This Matters

This connects to three deep areas:
- **Hilbert's Third Problem** (1900): Are all polyhedra of equal volume scissors-congruent?
  Dehn's 1900 solution shows NO — and this gallery proof formalizes the complete Platonic
  solid classification.
- **K-theory**: Dupont and Sah showed `𝒫(ℝ³) ≅ K₃(ℝ)`, linking elementary geometry to
  algebraic K-theory.
- **Niven's method**: The Chebyshev sequence technique provides a general algorithm for
  proving irrationality of arccos(p/q)/π for rational p/q.

Eliminating axioms here improves the gallery's integrity and demonstrates Lean can fully
verify classical impossibility results.

## Known Results

### What's Already Proven (in gallery)

- **dissection-of-cubes**: Cube cannot be dissected into a regular tetrahedron (Dehn 1900)
- **dissection-of-cubes-oq-04**: All 5 Platonic solids classified under scissors congruence;
  cube has Dehn invariant 0, others have nonzero invariants. **2 axioms remain.**
- **Octahedron angle**: `arccos(1/3)/π` irrational via Chebyshev sequence in ℤ[√(5/4)]
- **Dodecahedron, tetrahedron angles**: Already proved irrational in the gallery

### What's Still Open

1. `tmul_infinite_order_ne_zero` — ℝ ⊗_ℤ (ℝ/ℤ) is torsion-free (follows from Module.Flat)
2. `icoAngle_irrational` — arccos(3/5)/π is irrational (needs Chebyshev argument in ℤ[√5])

### Our Goal

Prove one or both of these remaining axioms, reducing the gallery proof from 2 axioms to
0 or 1. Priority: `tmul_infinite_order_ne_zero` first (more likely to follow from Mathlib).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| dissection-of-cubes | Parent — original Dehn impossibility | Dehn invariant, TensorProduct |
| dissection-of-cubes-oq-04 | Immediate parent — Platonic solid classification | Chebyshev sequences, ℤ[√5] |
| dissection-of-cubes-oq-01 | Scissors congruence group structure | Module theory |
| dissection-of-cubes-oq-02 | Rational combinations of arccos values | Niven's theorem |
| dissection-of-cubes-oq-03 | K-theory connection to scissors congruence | Algebraic K-theory |

## Initial Thoughts

### Potential Approaches

1. **Module.Flat approach** (for `tmul_infinite_order_ne_zero`):
   - ℝ is a torsion-free ℤ-module (obvious), but flatness is stronger
   - Mathlib has `Module.Flat` and related API
   - `TensorProduct.torsion_free` or similar lemma may exist
   - Risk: API may not directly expose what we need; may need intermediate steps

2. **Chebyshev in ℤ[√5]** (for `icoAngle_irrational`):
   - The octahedron proof uses the sequence `aₙ = 2^n · cos(n · arccos(1/3))`
   - For icosahedron: `cos(arccos(3/5)) = 3/5`, so `aₙ = 5^n/2^n · 2cos(n·arccos(3/5))`
   - Scaling: define `bₙ = 2·5^n·cos(n·arccos(3/5))` ∈ ℤ[√5] by recurrence
   - Need to show `bₙ` is never divisible by some prime p for n ≥ 1
   - Risk: ℤ[√5] arithmetic in Lean requires `NumberField` or `RingOfIntegers` machinery

3. **Direct tensor torsion** (alternative to Module.Flat):
   - Show directly that if `n · (r ⊗ 1) = 0` in `ℝ ⊗_ℤ (ℝ/ℤ)` then n = 0
   - Use the fact that ℝ is a ℚ-vector space (hence flat over ℤ)
   - Risk: May still require Module.Flat or similar

### Key Difficulties

- Mathlib's `Module.Flat` API may not directly state the result in the needed form
- ℤ[√5] arithmetic for the Chebyshev sequence requires some algebraic number theory setup
- The tensor product `ℝ ⊗_ℤ (ℝ/ℤ)` is somewhat exotic — finding the right Mathlib lemmas

### What Would a Proof Need?

- **For flatness axiom**: `Flat ℤ ℝ` instance + torsion-free tensor consequence
- **For icoAngle**: Define `b : ℕ → ℤ` satisfying `b(n+2) = (6/5)·b(n+1) - b(n)` scaled,
  show `b n ≡ something (mod p)` for appropriate prime p, conclude irrationality

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The flatness approach is likely tractable — ℝ is a ℚ-algebra, hence flat over ℤ; Mathlib
  probably has this
- The Chebyshev extension is more involved but uses the same pattern already proved for the
  octahedron — adaptation rather than new proof
- Both are well-defined mathematical tasks with clear goals
- Main risk: Mathlib API gaps forcing more low-level arguments

**Estimated Effort**:
- Exploration (OBSERVE/ORIENT): 1-2 sessions
- Flatness proof (if Mathlib cooperates): 1 session
- Chebyshev in ℤ[√5]: 2-4 sessions

## References

### Papers
- Dehn, M. (1901). "Über den Rauminhalt." Math. Ann. 55, 465-478.
- Sydler, J.-P. (1965). "Conditions nécessaires et suffisantes..." Comment. Math. Helv. 40.
- Dupont, J. & Sah, C.-H. (1982). "Scissors congruences II." J. Pure Appl. Algebra 25.

### Mathlib
- `Mathlib.LinearAlgebra.TensorProduct.Basic` — TensorProduct construction
- `Mathlib.RingTheory.Flat.Basic` — Module.Flat API
- `Mathlib.NumberTheory.NumberField.Basic` — For ℤ[√5] arithmetic
- `Mathlib.FieldTheory.Adjoin` — Algebraic adjunctions

## Metadata

```yaml
tags:
  - geometry
  - dissection
  - dehn-invariant
  - hilbert-3
  - tensor-product
  - flat-modules
  - algebraic-number-theory
related_proofs:
  - dissection-of-cubes
  - dissection-of-cubes-oq-04
  - dissection-of-cubes-oq-01
  - dissection-of-cubes-oq-02
  - dissection-of-cubes-oq-03
difficulty: medium
source: gallery-gap
created: 2026-04-23T08:50:16+02:00
```

**Significance**: 7/10
**Tractability**: 5/10
