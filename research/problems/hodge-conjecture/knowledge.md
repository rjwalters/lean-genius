# Knowledge Base: Hodge Conjecture

## The Problem

The Hodge Conjecture is a fundamental question about the relationship between algebraic geometry and topology, asking which topological features of complex algebraic varieties come from algebraic subvarieties.

### Core Statement

> On a smooth projective complex variety, every Hodge class is a rational linear combination of classes of algebraic cycles.

In simpler terms: Certain "nice" topological objects (Hodge classes) on complex algebraic varieties should all come from algebraic subvarieties.

### Why It Matters

1. **Algebraic Geometry**: Fundamental question about varieties
2. **Topology-Algebra Bridge**: Connects Betti cohomology to algebraic cycles
3. **Motives**: Central to the theory of motives
4. **Representation Theory**: Connected to Langlands program

## Historical Context

| Year | Mathematician | Contribution |
|------|--------------|--------------|
| 1950 | Hodge | Formulated the conjecture |
| 1961 | Lefschetz | Proved for divisors (codimension 1) |
| 1969 | Deligne | Proved for abelian varieties (certain cases) |
| 1983 | Cattani-Deligne-Kaplan | Some degenerations |
| 2000 | Clay Institute | Named as Millennium Problem |

Unlike some Millennium Problems, the Hodge Conjecture is wide open - no major progress on the general case in decades.

## What This Means

### Hodge Decomposition

For a compact Kähler manifold X, the cohomology splits:

H^k(X, C) = ⊕_{p+q=k} H^{p,q}(X)

where H^{p,q} consists of forms with p "holomorphic" and q "antiholomorphic" directions.

### Hodge Classes

A class α ∈ H^{2p}(X, Q) is a **Hodge class** if it lives in H^{p,p}(X) ∩ H^{2p}(X, Q).

### Algebraic Cycles

A codimension-p algebraic cycle is a formal sum of irreducible subvarieties of codimension p. Each gives a class in H^{2p}(X, Q).

### The Conjecture

Every Hodge class is a Q-linear combination of classes of algebraic cycles.

## What We Know

### Proven Cases

| Case | Status | Prover |
|------|--------|--------|
| Codimension 1 (divisors) | ✅ Proven | Lefschetz (1961) |
| Abelian varieties (certain) | ✅ Proven | Deligne (1969) |
| K3 surfaces | ✅ Proven | Various |
| Fermat varieties (some) | ✅ Proven | Shioda |

### Open Cases

- General smooth projective varieties
- Higher codimension on most varieties
- Variants over other fields

### Known Failures

The **integral** Hodge conjecture (with Z instead of Q coefficients) is FALSE. Counterexamples found by Atiyah-Hirzebruch (1962) and later Totaro.

## What We Could Build

### In Mathlib Now

| Component | Status | Notes |
|-----------|--------|-------|
| Complex manifolds | ⚠️ Partial | Building |
| Algebraic varieties | ⚠️ Partial | Scheme theory exists |
| Cohomology | ⚠️ Partial | Some de Rham |
| Hodge theory | ❌ | Not available |
| Algebraic cycles | ❌ | Not available |

### Tractable Partial Work

1. **Hodge Decomposition**
   - State for Kähler manifolds
   - Prove for complex tori

2. **Divisor Case**
   - Lefschetz (1,1) theorem
   - Line bundles ↔ divisor classes

3. **Abelian Varieties**
   - Define algebraic cycles
   - State Deligne's theorem

4. **K3 Surfaces**
   - Important test case
   - Rich structure theory

## The Mathematical Challenges

### Primary Blocker: Hodge Theory Infrastructure

Formalizing requires:

1. **Complex differential geometry** (~3000 lines)
   - Kähler manifolds
   - Dolbeault cohomology
   - Harmonic forms

2. **Hodge decomposition** (~2000 lines)
   - Laplacian theory
   - Elliptic regularity
   - Representation on cohomology

3. **Algebraic cycles** (~2000 lines)
   - Chow groups
   - Cycle class maps
   - Intersection theory

4. **Scheme theory for varieties** (~1500 lines)
   - Smooth projective schemes
   - Coherent sheaves
   - GAGA principle

### Why This Is Hard

Unlike Navier-Stokes or P vs NP, the Hodge Conjecture:
- Has no known attack strategy
- Involves deep algebraic geometry
- Requires substantial infrastructure just to state

## Related Topics

### Motives

The Hodge Conjecture is part of a larger picture:
- Standard conjectures on algebraic cycles
- Theory of motives
- Motivic cohomology

### Deligne's Conjectures

Related conjectures about:
- Absolute Hodge cycles
- Periods of algebraic varieties
- Special values of L-functions

## Key References

- Hodge, W.V.D. (1950). "The topological invariants of algebraic varieties"
- Deligne, P. (1982). "Hodge cycles on abelian varieties"
- Voisin, C. (2002). "Hodge Theory and Complex Algebraic Geometry"
- Lewis, J. (1999). "A Survey of the Hodge Conjecture"

## Scouting Log

### Assessment: 2026-01-01

**Current Status**: BLOCKED - Heavy algebraic geometry requirements

**Blocker Tracking**:
| Infrastructure | In Mathlib | Last Checked |
|----------------|------------|--------------|
| Algebraic varieties | Basic | 2026-01-01 |
| Sheaf cohomology | Building | 2026-01-01 |
| Hodge theory | No | 2026-01-01 |
| Algebraic cycles | No | 2026-01-01 |

**Path Forward**:
1. State conjecture with axiomatized definitions
2. Formalize Lefschetz (1,1) theorem (divisor case)
3. Build toward K3 surfaces case
4. Long-term: general Hodge theory

**Reality Check**: Even stating the conjecture precisely requires thousands of lines of infrastructure. This is a long-term goal.

**Next Scout**: Monitor Mathlib algebraic geometry development (schemes, cohomology)
