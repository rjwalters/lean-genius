# Feasibility Check: Bounded Prime Gaps (Zhang/Polymath)

**Date**: 2025-12-31
**Time spent**: ~15 minutes

## The Problem

**Bounded Prime Gaps Theorem** (Zhang 2013, optimized by Polymath):
There exists a constant H such that there are infinitely many pairs of primes p, q with |p - q| ≤ H.

- Zhang's original: H ≤ 70,000,000
- Polymath optimization: H ≤ 246
- Assuming Elliott-Halberstam: H ≤ 12

This was a major breakthrough - the first finite bound on prime gaps.

## Step 1: Mathlib Search Results

| Component | In Mathlib? | Notes |
|-----------|-------------|-------|
| von Mangoldt function Λ | **YES** | VonMangoldt.lean |
| L-series infrastructure | **YES** | LSeries/, Dirichlet |
| Dirichlet characters | **YES** | DirichletCharacter |
| Riemann zeta function | **YES** | RiemannZeta.lean |
| Bertrand's postulate | **YES** | Prime in (n, 2n) |
| Prime counting π(x) | **YES** | PrimeCounting.lean |
| Selberg sieve | **NO** | Foundational gap |
| GPY sieve | **NO** | Key to Zhang proof |
| Bombieri-Vinogradov | **NO** | Critical prerequisite |
| Admissible k-tuples | **NO** | Not defined |
| Exponential sums | **NO** | Kloosterman bounds missing |
| Primes in AP | Partial | Basic results only |

## Step 2: The Zhang/Polymath Proof Structure

The proof requires:

### Layer 1: Sieve Theory Foundation
- Selberg sieve (1940s technique)
- Upper/lower bound sieves
- Combinatorial sieve weights

### Layer 2: GPY Sieve (2005-2009)
- Goldston-Pintz-Yıldırım method
- Shows small gaps from EH conjecture
- Modified by Zhang for unconditional result

### Layer 3: Distribution of Primes
- Bombieri-Vinogradov theorem
- Extension to smooth moduli
- Exponential sum estimates

### Layer 4: Zhang's Innovation
- Kloosterman sums
- Deligne's bounds (Weil conjectures!)
- Careful error term analysis

### Layer 5: Polymath Optimization
- Combinatorial improvements
- Better sieve weights
- Admissible tuple optimization

## Step 3: Milestone Tractability

| Milestone | Tractability | Notes |
|-----------|--------------|-------|
| State the theorem | **5/10** | Need to define "bounded gaps" |
| Define Selberg sieve | **2/10** | Major infrastructure |
| Prove basic sieve bounds | **1/10** | Research-level |
| Bombieri-Vinogradov | **1/10** | Major theorem |
| Zhang's main theorem | **0/10** | Years of work |
| Document prerequisites | **8/10** | Survey approach |

## Step 4: Realistic Assessment

### Why This Is Intractable

1. **Sieve methods don't exist**: The entire branch of analytic number theory used for sieve bounds is missing from Mathlib.

2. **Proof is 50+ pages**: Zhang's original paper is extremely technical. The Polymath project involved dozens of mathematicians.

3. **Dependencies are deep**: Requires Weil conjectures (Deligne), which themselves are major formalization targets.

4. **No shortcuts**: Unlike some problems where partial results are meaningful, bounded gaps really needs the full sieve machinery.

### What A Survey Would Produce

If we did a SURVEY:
- Formal statement: "∃ H, ∀ N, ∃ p q, Prime p ∧ Prime q ∧ p < q ∧ q < N ∧ q - p ≤ H"
- Axiom for the theorem
- Documentation of missing infrastructure
- Maybe: definition of admissible tuples

But even this is low value because:
- The statement is trivial to write
- The axiom doesn't teach us anything
- The infrastructure gap is too vast to bridge

## Decision

**Assessment**: SKIP

**Rationale**:
1. **Enormous infrastructure gap**: Sieve theory doesn't exist in Mathlib
2. **Multi-year effort**: Even with infrastructure, proof formalization would take years
3. **No tractable milestones**: Can't prove anything meaningful without sieves
4. **Better alternatives**: Other problems have provable partial results

### Comparison

| Problem | What We Can Prove |
|---------|------------------|
| Twin Primes (structure) | ✓ Form (6k-1, 6k+1) |
| Prime Gaps (Bertrand) | ✓ π(2n) > π(n) |
| Szemerédi | ✓ Trivial cases |
| **Bounded Gaps** | ✗ Nothing meaningful |

## References

- Y. Zhang, "Bounded gaps between primes", Annals of Math. 179 (2014)
- Polymath8 project: https://terrytao.wordpress.com/tag/polymath8/
- J. Maynard, "Small gaps between primes", Annals of Math. 181 (2015)

## Recommendation

Move to next random selection. This problem requires foundational sieve theory infrastructure that would take person-years to develop.
