# Problem: Strong Goldbach Conjecture — Every Even n > 2 is Sum of Two Primes

**Slug**: weak-goldbach-oq-01
**Created**: 2026-04-23T06:12:18+02:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\forall n \in \mathbb{Z},\; n > 2 \wedge n \text{ even} \implies \exists p, q \in \mathbb{P},\; n = p + q
$$

### Plain Language

The Strong (Binary) Goldbach Conjecture states every even integer greater than 2 is the sum of two primes. For example: 4 = 2+2, 6 = 3+3, 8 = 3+5, 100 = 3+97 = 11+89 = ... This is the open extension of the Weak (Ternary) Goldbach Conjecture, which was proved by Helfgott in 2013 (every odd number > 5 is a sum of three primes, formalized in gallery `weak-goldbach`).

### Why This Matters

Goldbach's conjecture (1742) is one of the oldest open problems in mathematics. Helfgott's 2013 proof of ternary Goldbach made major progress; the binary case remains open. Verified up to $4 \times 10^{18}$ computationally (Oliveira e Silva et al., 2014). It connects prime distribution, the circle method, and additive number theory.

## Known Results

### What's Already Proven

- Weak Goldbach (ternary): Every odd integer > 5 = sum of three primes (Helfgott 2013) — gallery: `weak-goldbach`
- Chen's theorem (1973): Every sufficiently large even number = prime + product of at most two primes (p + P2)
- Binary Goldbach verified computationally for all even n ≤ 4 × 10^18 (Oliveira e Silva et al.)
- Vinogradov's theorem: Every sufficiently large odd integer is sum of three primes
- Hardy-Littlewood circle method gives asymptotic for the number of representations

### What's Still Open

- Binary Goldbach for all even integers (the main conjecture)
- Effective bound in Chen's theorem to handle all even integers (not just "sufficiently large")

### Our Goal

Extend the `weak-goldbach` gallery formalization to capture the Strong Goldbach Conjecture as an axiom, plus Chen's theorem (p + P2) as a key unconditional result. Formalize the computational verification bound and derive structural consequences. The natural open-question sequel to `weak-goldbach`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `weak-goldbach` | Ternary Goldbach (proved); parent proof | Circle method, Vinogradov |
| `twin-primes-special-oq-01` | Analogous prime pairs question | Sieve methods |
| `infinitude-of-primes` | Foundational prime theory | Contradiction |
| `sophie-germain-oq-01` | Analogous open prime conjecture | Sieve methods |

## Initial Thoughts

### Potential Approaches

1. **Axiomatize Binary Goldbach + state Chen's theorem**: State the binary conjecture as an axiom; prove Chen's theorem (p + P2) as a separate supported result requiring axiomatization of sieve bounds.
   - Why it might work: Follows the `weak-goldbach` pattern exactly
   - Risk: Chen's theorem itself is analytically heavy; needs axiomatization

2. **Computational verification formalization**: Formalize the Oliveira e Silva computational verification up to 4×10^18 as a decidable check with axiom for the remainder.
   - Why it might work: Clean separation of computational and theoretical parts
   - Risk: Computational formalization requires decidability framework

3. **Hardy-Littlewood circle method structural results**: Formalize the asymptotic number of Goldbach representations $r(n) \sim \mathfrak{S}(n) \frac{n}{\log^2 n}$ as conditional on GRH.
   - Why it might work: Rich theory to formalize even without proving the conjecture
   - Risk: Requires substantial analytic number theory machinery

### Key Difficulties

- Binary Goldbach is genuinely open; no unconditional proof
- Chen's theorem, while proved, requires complex sieve estimates to formalize
- Connecting to the `weak-goldbach` Lean file requires careful interface design

### What Would a Proof Need?

- Key axiom: Binary Goldbach conjecture
- Key result: Chen's theorem (p + P2 for all large enough even n)
- Supporting: Computational verification bound axiom
- Supporting: Schnirelmann density connection (already in `weak-goldbach`)

## Tractability Assessment

**Difficulty**: Moonshot (full conjecture) / High (axiomatized with Chen + computational bounds)

**Justification**:
- Main conjecture is open; direct proof impossible
- Axiomatized approach mirrors `weak-goldbach` pattern (9 axioms already)
- Chen's theorem is a major unconditional result worth formalizing
- Natural sequel to the existing `weak-goldbach` gallery proof

**Estimated Effort**:
- Exploration: 1-2 cycles
- Axiomatized formalization (conjecture + Chen): 3-4 cycles
- Full circle method structural results: 5-8 cycles

## References

### Papers
- Chen, J.R., "On the representation of a large even integer as the sum of a prime and the product of at most two primes", 1973
- Oliveira e Silva, T. et al., "Empirical verification of the even Goldbach conjecture and computation of prime gaps up to 4×10^18", 2014
- Helfgott, H.A., "The ternary Goldbach conjecture is true", 2013

### Mathlib
- `Mathlib.NumberTheory.PrimesCongruent` — prime structure
- `Mathlib.NumberTheory.ArithmeticFunction` — counting functions

## Metadata

```yaml
tags:
  - number-theory
  - goldbach
  - additive-number-theory
  - circle-method
  - open-conjecture
related_proofs:
  - weak-goldbach
  - twin-primes-special-oq-01
  - infinitude-of-primes
difficulty: moonshot
source: gallery-gap
created: 2026-04-23T06:12:18+02:00
```

**Significance**: 8/10
**Tractability**: 2/10
