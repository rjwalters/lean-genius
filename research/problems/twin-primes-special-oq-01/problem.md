# Problem: Twin Prime Conjecture — Infinitely Many Twin Prime Pairs

**Slug**: twin-primes-special-oq-01
**Created**: 2026-04-23T06:12:18+02:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{Are there infinitely many primes } p \text{ such that } p + 2 \text{ is also prime?}
$$

More precisely: is the set $\{p \in \mathbb{P} \mid p + 2 \in \mathbb{P}\}$ infinite?

### Plain Language

A twin prime pair is a pair of primes $(p, p+2)$. The first several: (3,5), (5,7), (11,13), (17,19), (29,31), (41,43). The Twin Prime Conjecture asserts infinitely many such pairs exist. As of 2026, Zhang (2013) proved bounded prime gaps (gap ≤ 246 via Maynard-Tao), but the specific gap-2 case remains open.

### Why This Matters

The Twin Prime Conjecture is one of the oldest unsolved problems in mathematics (Polignac, 1849). It is the canonical test case for sieve theory, the Green-Tao theorem context, and Maynard-Tao bounded gap techniques. Formalization provides a framework for capturing these partial results.

## Known Results

### What's Already Proven

- All twin prime pairs $(p, p+2)$ with $p > 3$ have the form $(6k-1, 6k+1)$ — gallery: `twin-primes-special`
- Zhang (2013): There exist infinitely many prime pairs with gap ≤ 70,000,000
- Maynard-Tao (2013): Gap can be reduced to ≤ 246; infinitely many primes in any admissible 50-tuple
- Hardy-Littlewood conjecture predicts $\pi_2(n) \sim 2C_2 \frac{n}{\log^2 n}$ where $C_2 \approx 0.6601618...$
- Brun proved $\sum_{(p,p+2) \text{ twin}} \frac{1}{p}$ converges (Brun's constant $B_2 \approx 1.9021605...$)

### What's Still Open

- Gap ≤ 2 (the twin prime conjecture itself)
- Whether Maynard-Tao techniques can reach gap = 2

### Our Goal

Formalize the Twin Prime Conjecture as an axiomatized Lean 4 proof capturing: the form constraint ($(6k-1, 6k+1)$ already in gallery), Brun's constant convergence, Hardy-Littlewood density prediction, and the bounded gap result (Zhang/Maynard-Tao). Prove structural consequences under the axiom.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `twin-primes-special` | Parent: form constraint for twin primes | Modular arithmetic |
| `sophie-germain-oq-01` | Analogous problem for (p, 2p+1) | Sieve methods |
| `infinitude-of-primes` | Euclid's infinitude proof | Contradiction |
| `weak-goldbach` | Helfgott's ternary Goldbach proof | Circle method |

## Initial Thoughts

### Potential Approaches

1. **Axiomatize the conjecture + bounded gaps**: State twin prime conjecture as axiom; formally capture Zhang's theorem (infinitely many gaps ≤ 246) as a proven (axiomatized) result.
   - Why it might work: Zhang's theorem is unconditional — can be stated precisely
   - Risk: Formalizing the full Maynard-Tao argument requires advanced analytic number theory

2. **Brun's theorem formalization**: Prove convergence of $\sum 1/p$ over twin primes (requires Brun sieve, which gives an upper bound).
   - Why it might work: Brun's result is classical and well-understood
   - Risk: Brun sieve not in Mathlib

3. **Hardy-Littlewood as structural axiom**: Formalize the Hardy-Littlewood conjecture B as an axiom and derive consequences about prime gaps in arithmetic progressions.
   - Why it might work: Axiom approach used successfully for Goldbach, Riemann
   - Risk: Need to tie it to the form constraint already proven

### Key Difficulties

- Gap = 2 case is genuinely open; no unconditional proof
- Zhang/Maynard-Tao techniques are analytically very heavy
- Brun sieve largely absent from Mathlib

### What Would a Proof Need?

- Key lemma: Form constraint already proven in `twin-primes-special`
- Key axiom: Infinitude of twin prime pairs (the conjecture)
- Supporting: Zhang's 246 bound (unconditional, can be axiomatized with citation)
- Supporting: Hardy-Littlewood density asymptotics

## Tractability Assessment

**Difficulty**: Moonshot (full conjecture) / High (axiomatized formalization with Zhang)

**Justification**:
- Main conjecture is open; direct proof impossible
- Axiomatized approach mirrors `weak-goldbach` pattern
- Zhang's theorem gives an unconditional result to formalize precisely
- Form constraint already in gallery reduces scope

**Estimated Effort**:
- Exploration: 1-2 cycles
- Axiomatized formalization: 2-3 cycles
- Zhang/Maynard-Tao structural formalization: 4-6 cycles

## References

### Papers
- Zhang, Y., "Bounded gaps between primes", Annals of Mathematics, 2014
- Maynard, J., "Small gaps between primes", Annals of Mathematics, 2015
- Hardy, G.H. & Littlewood, J.E., "Some problems of 'Partitio numerorum'", 1923

### Mathlib
- `Mathlib.NumberTheory.PrimesCongruent` — primes in residue classes
- `Mathlib.NumberTheory.ArithmeticFunction` — arithmetic functions for prime counting

## Metadata

```yaml
tags:
  - number-theory
  - prime-gaps
  - twin-primes
  - sieve-methods
  - open-conjecture
related_proofs:
  - twin-primes-special
  - sophie-germain-oq-01
  - infinitude-of-primes
difficulty: moonshot
source: gallery-gap
created: 2026-04-23T06:12:18+02:00
```

**Significance**: 8/10
**Tractability**: 2/10
