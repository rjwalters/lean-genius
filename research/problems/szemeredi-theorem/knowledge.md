# Knowledge Base: Szemerédi's Theorem

## Progress Summary

**Date**: 2025-12-31
**Phase**: SURVEY (completed)
**Mode**: Feasibility-driven survey

## What We've Built

### Formal Definitions (in Lean)
- `HasAPOfLength S k` - set S contains k-term arithmetic progression
- `hasAPOfLengthFinset S k` - finset version
- `IsAPFree S k` - set has no k-AP
- `SzemerediTheorem` - formal statement of full theorem

### Proven Cases
- `szemeredi_k1` - any nonempty set has 1-AP (trivial)
- `szemeredi_k2` - any set with ≥2 elements has 2-AP

### Axiom Stated
- `szemeredi_theorem` - full Szemerédi theorem as axiom

## Key Finding: What's in Mathlib

| Result | Status | Location |
|--------|--------|----------|
| Roth's Theorem (k=3) | **PROVEN** | `Combinatorics.Additive.Corner.Roth` |
| Corners Theorem | **PROVEN** | same |
| Triangle Removal Lemma | **PROVEN** | `Combinatorics.SimpleGraph.Triangle.Removal` |
| Szemerédi Regularity Lemma | **PROVEN** | `Combinatorics.SimpleGraph.Regularity.Lemma` |
| Hales-Jewett Theorem | **PROVEN** | `Combinatorics.HalesJewett` |
| Van der Waerden (coloring) | **PROVEN** | via Hales-Jewett |
| ThreeAPFree predicate | **DEFINED** | `Combinatorics.Additive.AP.Three.Defs` |
| rothNumberNat | **DEFINED** | same |
| Full Szemerédi (k≥4) | **NOT IN MATHLIB** | - |
| Hypergraph regularity | **NOT IN MATHLIB** | - |

## Critical Insight

**Szemerédi ≠ Van der Waerden**:
- Van der Waerden (in Mathlib): "k-color [1,N] → monochromatic k-AP"
- Szemerédi (NOT in Mathlib): "δN elements in [1,N] → k-AP"

The density version is strictly harder. Van der Waerden follows from Szemerédi,
but not vice versa.

## Why k≥4 is Hard

The proof of Roth (k=3) goes:
```
Roth ← Corners theorem ← Triangle removal ← Graph regularity
```

For k≥4, we need:
```
k-AP ← (k-1)-corners ← Hypergraph removal ← Hypergraph regularity
```

**Hypergraph regularity** is the bottleneck:
- Much more complex than graph regularity
- Definitions alone are non-trivial
- Counting lemmas harder to state/prove
- Not in any proof assistant AFAIK

## What Would Be Needed for Full Proof

### Approach 1: Hypergraph Regularity (Combinatorial)
1. Define k-uniform hypergraphs
2. Define hypergraph regularity
3. Prove hypergraph regularity lemma
4. Prove hypergraph removal lemma
5. Define (k-1)-dimensional corners
6. Prove corners theorem for k-1 dimensions
7. Deduce k-AP density theorem

Estimated effort: Multi-month research project

### Approach 2: Ergodic Theory (Furstenberg)
1. Formalize measure-preserving systems
2. Define ergodic recurrence
3. Prove Furstenberg's correspondence principle
4. Prove multiple recurrence theorem
5. Deduce Szemerédi

Estimated effort: Also multi-month, but more foundational

### Approach 3: Fourier-Analytic (Gowers)
1. Define Gowers uniformity norms
2. Prove inverse theorems
3. Use density increment strategy

Estimated effort: Very technical, needs harmonic analysis

## Value Assessment

This survey was valuable because:
1. ✅ Clarified what's actually in Mathlib (Roth IS there, full Szemerédi is NOT)
2. ✅ Documented the gap precisely
3. ✅ Created formal statement for future work
4. ✅ Proved trivial cases as sanity check
5. ✅ Identified hypergraph regularity as the key missing piece

## Recommendation for Future Work

**Do NOT attempt full proof** - would require:
- Building hypergraph theory from scratch
- Multi-month effort with uncertain payoff

**Better targets**:
- Improve Roth bounds (quantitative Roth)
- Formalize Behrend construction (AP-free sets)
- Work on simpler additive combinatorics

## File Location

`proofs/Proofs/SzemerediTheorem.lean`
