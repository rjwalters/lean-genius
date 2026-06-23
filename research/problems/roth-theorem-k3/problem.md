# Problem: Roth's Theorem (Szemeredi k=3)

**Slug**: roth-theorem-k3
**Created**: 2026-03-21
**Status**: Active
**Source**: marquee-initiative
**Initiative**: Szemeredi Regularity and Applications (Phase 3)

## Problem Statement

### Formal Statement

$$
r_3(N) = \max\{|A| : A \subseteq [N],\ A \text{ contains no 3-term arithmetic progression}\} = o(N).
$$

Equivalently: for every $\delta > 0$, there exists $N_0$ such that for all $N \geq N_0$, every subset $A \subseteq [N]$ with $|A| \geq \delta N$ contains a 3-term arithmetic progression.

### Plain Language

Roth's theorem says that any "dense enough" subset of the integers must contain a 3-term arithmetic progression (three equally spaced numbers like 3, 7, 11). No matter how cleverly you try to avoid creating such patterns, if your set occupies a positive fraction of {1, 2, ..., N}, a 3-term AP will appear once N is large enough. This is the k=3 case of Szemeredi's theorem.

### Why This Matters

Roth's theorem (1953) was the first major result in additive combinatorics showing that density forces arithmetic structure. It introduced Fourier-analytic methods to combinatorics and pioneered the density increment strategy that underpins much of modern additive combinatorics. It is the natural starting point for formalizing the Szemeredi program.

## Dependencies

| Direction | Problem | Relationship |
|-----------|---------|-------------|
| **Depends on** | (none) | Independent, can start immediately |
| **Blocks** | szemeredi-full | Roth is the k=3 base case |

## Known Results

### What's Already in Mathlib

- `Finset` arithmetic operations and cardinality lemmas
- `ZMod` for cyclic group Fourier analysis
- Basic sumset/additive combinatorics in `Mathlib.Combinatorics.Additive`
- Discrete Fourier transform infrastructure via `ZMod.dft`

### What Needs to Be Built

- AP-free set definition and basic properties
- Fourier analysis on Z/NZ with density arguments
- Density increment lemma (key inductive step)
- The r_3(N) = o(N) conclusion

### Our Goal

Formalize Roth's theorem via the density increment argument. The key technical step is showing that if a dense set has no 3-AP, then it has a large Fourier coefficient, which gives a density increment on a long subprogression.

## Initial Thoughts

### Potential Approaches

1. **Fourier analytic (Roth 1953)**
   - Why it might work: Classical, well-documented, cleanest proof
   - Risk: Fourier analysis on Z/NZ requires careful setup in Lean

2. **Density increment (Bourgain style)**
   - Why it might work: Gives better quantitative bounds
   - Risk: More technically demanding, overkill for a first formalization

3. **Energy increment**
   - Why it might work: Parallels the regularity proof strategy
   - Risk: Less standard for k=3 case

### Key Difficulties

- Formalizing discrete Fourier analysis on Z/NZ in Lean
- The density increment argument requires careful bookkeeping of set sizes
- Connecting Fourier coefficients to arithmetic progressions
- Iterating the density increment to get the o(N) bound

## Tractability Assessment

**Difficulty**: Hard
**Tractability**: 6/10
**Significance**: 9/10

**Justification**:
- The Fourier-analytic proof is well-understood but technically nontrivial
- Lean's Mathlib has growing Fourier infrastructure but may need extensions
- The density increment is a clean inductive argument once setup is done
- High payoff as the entry point to the Szemeredi program

**Estimated Effort**:
- Exploration: 2 days
- Implementation: 6-10 days

## References

### Papers
- Roth (1953) - "On certain sets of integers"
- Bourgain (1999) - "On triples in arithmetic progression"
- Bloom & Sisask (2020) - "Breaking the logarithmic barrier in Roth's theorem"

### Mathlib
- `Mathlib.Combinatorics.Additive.FreimanRuzsa`
- `Mathlib.Analysis.InnerProductSpace.Basic`
- `Mathlib.NumberTheory.ZetaFunction` (Fourier tools)

## Metadata

```yaml
tags:
  - szemeredi
  - combinatorics
  - additive-combinatorics
  - arithmetic-progressions
  - marquee-phase-3
related_proofs:
  - prob-method-expectation
  - prob-method-lovasz-local
difficulty: hard
source: marquee-initiative
initiative: szemeredi-regularity-phase-3
created: 2026-03-21
```
