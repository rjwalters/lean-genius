# Problem: Erdős #27 — Almost Covering Systems

**Slug**: erdos-27
**Created**: 2026-04-21
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

An **ε-almost covering system** is a finite set of congruences $a_i \pmod{n_i}$ with distinct moduli $n_1 < \cdots < n_k$ such that the density of integers satisfying none of the congruences is at most $\varepsilon$.

**Erdős #27**: Does there exist $C > 1$ such that for every $\varepsilon > 0$ and $N \geq 1$, there is an $\varepsilon$-almost covering system with all moduli in $[N, CN]$?

**Answer: NO** — disproved by Filaseta-Ford-Konyagin-Pomerance-Yu (FFKPY). Specifically, for $C \leq N^{\alpha(N)}$ where $\alpha(N) = \frac{\log\log\log N}{4\log\log N}$, the uncovered density is at least $(1 - o(1)) \cdot \prod(1 - 1/n_i)$, which cannot be made arbitrarily small.

### Plain Language

Can we cover almost all integers using congruences whose moduli are all close together (within a constant factor $C$)? The answer is no: for any fixed $C$, if moduli are restricted to $[N, CN]$, the "coverage" cannot approach 100%.

### Why This Matters

- Covers the theory of dense covering systems and their limitations
- Connects to sieve theory (Brun, Selberg), density of arithmetic progressions
- The disproof by FFKPY uses the multiplicative structure of intervals and logarithmic density arguments
- The Lean formalization provides a machine-checked account of this negative result

## Known Results

### What's Already Proven (in Lean)

- `Erdos27Problem.lean` (Proofs/Stubs/): Basic definitions — `Congruence`, `CongruenceSystem`, `uncoveredDensity`, `BoundedModuliSystem`, `AlmostCovering`
- Aristotle companion `Erdos27Aristotle.lean` with 5 routine lemma targets for automation
- Gallery entry at `src/data/proofs/erdos-27/` with 12 sorries remaining

### What's Still Open in the Lean File

- 12 sorries in `Erdos27Problem.lean` covering:
  - Density calculation lemmas
  - Product convergence bounds
  - The core FFKPY lower bound argument
  - Final impossibility theorem

### Our Goal

Eliminate or reduce the 12 sorries in `Erdos27Problem.lean`. Priority:
1. **Aristotle targets**: 5 routine lemmas (structural/algebraic) — submit to Aristotle
2. **Density lemmas**: Measure-theoretic density calculations
3. **Product bounds**: $\prod(1 - 1/n)$ convergence/divergence estimates

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `erdos-27` (gallery) | Parent proof with 12 sorries | Congruence systems, density |
| `bertrands-postulate` | Prime distribution bounds | Elementary number theory |
| `chebyshev-bounds` | Log density estimates | Analytic number theory |

## Initial Thoughts

### Potential Approaches

1. **Aristotle-first**: Submit the 5 Aristotle companion lemmas for automated proof search. These are routine structural lemmas that Aristotle can handle.
   - Why it might work: Already identified as Aristotle targets
   - Risk: Some may require non-trivial algebraic manipulation

2. **Mathlib density tools**: Use `MeasureTheory.Measure.addHaar` and `Nat.density` for uncovered density calculations.
   - Why it might work: Mathlib has strong measure theory support
   - Risk: Natural density is non-trivial to formalize; may need Banach density or asymptotic density

3. **Product convergence**: For $\prod(1 - 1/n_i)$ with moduli in $[N, CN]$, use Mathlib's `Finprod` and logarithm estimates.
   - Why it might work: Standard analytic estimates exist in Mathlib
   - Risk: The FFKPY argument requires careful logarithmic bookkeeping

### Key Difficulties

- `uncoveredDensity` requires formalization of natural density (or asymptotic density) — Mathlib may not have a ready-made definition
- The FFKPY lower bound uses multiplicative function estimates — requires `ArithmeticFunction` from Mathlib
- 12 sorries may have interdependencies making partial progress harder

### What Would a Proof Need?

- Key lemma 1: `uncoveredDensity_prod_formula`: $d(\overline{S}) = \prod_i (1 - 1/n_i)$ for pairwise coprime moduli
- Key lemma 2: `log_sum_bounded`: $\sum_{n \in [N, CN]} 1/n$ is bounded — $O(\log C)$
- Key lemma 3: `almost_covering_impossible`: The core impossibility using the product bound
- Technical: Natural density definition compatible with Mathlib's Filter/Measure infrastructure

## Tractability Assessment

**Difficulty**: Medium-High

**Justification**:
- The problem is SOLVED mathematically — no open conjecture to worry about
- The Lean code structure exists with clear sorry targets
- But the density formalization is non-trivial
- Aristotle can handle 5/12 sorries if they are structural
- Core FFKPY sorries (4-5) require analytic number theory machinery

**Priority**: Check Aristotle companion first, then tackle density lemmas.

## References

### Papers
- Filaseta, Ford, Konyagin, Pomerance, Yu (2007) — *Sieving by large integers* — core FFKPY result
- Erdős (1950) — original problem statement

### Mathlib
- `Mathlib.Analysis.Asymptotics.Asymptotics` — asymptotic notation
- `Mathlib.Analysis.SpecialFunctions.Log.Basic` — logarithm estimates
- `Mathlib.Data.Int.ModEq` — congruences
- `Mathlib.MeasureTheory.Measure.Haar.Basic` — Haar measure (density)

## Metadata

```yaml
tags:
  - number-theory
  - covering-systems
  - density
  - erdos-problems
related_proofs:
  - erdos-27
  - bertrands-postulate
  - chebyshev-bounds
difficulty: medium-high
source: gallery-gap
created: 2026-04-21
```

**Significance**: 7/10
**Tractability**: 5/10
