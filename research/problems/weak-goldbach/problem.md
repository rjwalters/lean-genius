# Problem: Weak Goldbach Conjecture (Ternary Goldbach)

**Slug**: weak-goldbach
**Created**: 2025-12-31
**Status**: Active
**Source**: candidate-pool (Tier A)
**Significance**: 8/10
**Tractability**: 3/10

## Problem Statement

### Formal Statement

$$
\forall n \in \mathbb{Z}, \quad n > 5 \land n \text{ odd} \implies \exists p_1, p_2, p_3 \text{ prime}: n = p_1 + p_2 + p_3
$$

### Plain Language

Every odd integer greater than 5 can be expressed as the sum of three prime numbers.

Examples:
- 7 = 2 + 2 + 3
- 9 = 3 + 3 + 3
- 11 = 3 + 3 + 5
- 13 = 3 + 3 + 7
- 21 = 3 + 7 + 11 = 5 + 5 + 11 = 7 + 7 + 7

### Why This Matters

1. **Historical significance**: The "weak" version of Goldbach's 1742 conjecture
2. **Recently proved**: Harald Helfgott completed the proof in 2013 - a major 21st century result
3. **Circle method showcase**: Uses Hardy-Littlewood circle method extensively
4. **Not yet formalized**: No Lean/Coq/Isabelle formalization exists
5. **Gateway to strong Goldbach**: Understanding weak case informs the binary case

## Known Results

### What's Already Proven (on paper)

- **Helfgott 2013**: Full proof for all odd n > 5
- **Vinogradov 1937**: Proved for all sufficiently large odd n
- **Computational verification**: Checked up to 10^30

### What's in Mathlib

- `Nat.Prime`: Prime number definition
- `Nat.Prime.add_prime_add_prime`: Unknown if exists
- Basic prime number theory
- Some sieve theory basics

### What's Still Open

- **Strong Goldbach**: Every even n > 2 is sum of two primes (UNSOLVED)
- **Lean formalization**: No formalization of Helfgott's proof

### Our Goal

**Realistic goals (in order of ambition):**

1. **Minimal**: State the theorem formally in Lean, prove for small cases
2. **Partial**: Prove for specific infinite families (e.g., n ≡ 1 mod 6)
3. **Vinogradov-style**: Prove "for all sufficiently large n" (existential bound)
4. **Full**: Complete formalization of Helfgott (extremely ambitious)

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| infinitude-of-primes | Prime basics | Prime existence |
| bertrands-postulate | Prime density | Prime in intervals |
| prime-number-theorem | Asymptotic primes | Analytic number theory |

## Helfgott's Proof Structure

### Major Components

1. **Circle method setup**
   - Decompose into major and minor arcs
   - Exponential sums over primes

2. **Major arc analysis**
   - Contribution from "nice" rationals
   - Uses L-functions and character sums

3. **Minor arc bounds**
   - Bound contribution from "bad" rationals
   - Vinogradov's method

4. **Numerical verification**
   - Check all cases up to threshold
   - Extensive computation

### Key Technical Ingredients

- Exponential sums: $S(α) = \sum_{p \leq N} e(αp)$
- Character sums and L-functions
- Siegel-Walfisz theorem
- Explicit bounds on prime-counting

## Initial Thoughts

### Potential Approaches

1. **Computational verification for small n**
   - Prove: ∀ n ≤ 10000, odd n > 5 → sum of 3 primes
   - Why: Concrete, achievable, builds infrastructure
   - Risk: Not mathematically interesting

2. **Structural approach for special forms**
   - Prove for n = 6k+3 or similar residue classes
   - Why: Might have simpler structure
   - Risk: May not generalize

3. **Formalize Vinogradov's "sufficiently large"**
   - State: ∃ N, ∀ n > N, odd n → sum of 3 primes
   - Why: Avoids explicit bound computation
   - Risk: Still requires heavy analytic machinery

4. **Abstract the key lemmas**
   - Formalize lemmas Helfgott uses
   - Why: Modular progress
   - Risk: Scope creep

### Key Difficulties

1. **Analytic number theory**: Circle method not well-developed in Mathlib
2. **Explicit bounds**: Helfgott's proof requires precise numerical bounds
3. **Computation**: Verification of small cases requires efficient prime checking
4. **Length**: Full proof is 100+ pages of dense mathematics

### What Would a Proof Need?

- **For minimal goal**: `decide` tactic for small cases, prime sum checker
- **For partial goal**: Some structure theory for primes
- **For Vinogradov**: L-functions, character sums, circle method
- **For full Helfgott**: Everything above + months of work

## Tractability Assessment

**Difficulty**: High (bordering on Moonshot for full proof)

**Justification**:
- Full Helfgott proof is 100+ pages
- Circle method barely exists in Mathlib
- BUT: partial results are achievable
- Computational verification is tractable

**Realistic Outcomes**:
1. **Likely**: Formal statement + small case verification
2. **Possible**: Proof for infinite subfamily
3. **Ambitious**: Vinogradov-style existential result
4. **Moonshot**: Full Helfgott formalization

## Partial Progress Milestones

Even without full proof, these are valuable:

- [ ] Formal statement of weak Goldbach in Lean
- [ ] Verification for n ≤ 100
- [ ] Verification for n ≤ 10,000
- [ ] Proof for n = 9 (= 3+3+3, only representation)
- [ ] Proof for n ≡ 3 (mod 6) family
- [ ] Statement of Vinogradov's theorem
- [ ] Any infinite family result

## References

### Papers
- Helfgott, "The ternary Goldbach conjecture is true" (2013) — The proof
- Vinogradov, "Representation of an odd number as sum of three primes" (1937) — Asymptotic version

### Online Resources
- https://arxiv.org/abs/1312.7748 — Helfgott's paper
- https://en.wikipedia.org/wiki/Goldbach%27s_weak_conjecture

### Mathlib
- `Mathlib.NumberTheory.Primorial` — Prime products
- `Mathlib.NumberTheory.SmoothNumbers` — Smooth number theory
- `Mathlib.Analysis.Fourier` — Fourier analysis (for circle method)

## Metadata

```yaml
tags:
  - number-theory
  - additive-combinatorics
  - primes
  - circle-method
  - tier-a
related_proofs:
  - infinitude-of-primes
  - bertrands-postulate
  - prime-number-theorem
difficulty: high
source: candidate-pool
significance: 8
tractability: 3
created: 2025-12-31
```
