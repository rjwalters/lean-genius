# Problem: Carmichael Function at Powers of 2 — λ(2^k) = 2^{k-2} for k ≥ 3

**Slug**: euler-totient-oq-01-oq-02
**Created**: 2026-04-05T16:35:02-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\lambda(2^k) = 2^{k-2} \quad \text{for all } k \geq 3,
$$

where $\lambda(n)$ is the Carmichael function (the exponent of the multiplicative group $(\mathbb{Z}/n\mathbb{Z})^*$).

More precisely, the group $(\mathbb{Z}/2^k\mathbb{Z})^*$ is isomorphic to $\mathbb{Z}/2 \times \mathbb{Z}/2^{k-2}$ for $k \geq 3$, which has exponent $2^{k-2}$.

### Plain Language

The Carmichael function λ(n) gives the smallest positive exponent e such that $a^e \equiv 1 \pmod{n}$ for all integers a coprime to n. For prime powers $p^k$, computing λ is straightforward via the structure of the multiplicative group. The case of $2^k$ is special: for k ≥ 3, the group $(ℤ/2^kℤ)^*$ is NOT cyclic — it decomposes as a direct product of two cyclic groups.

Prove in Lean 4 that $\lambda(2^k) = 2^{k-2}$ for k ≥ 3, using the non-cyclic group structure of $(ℤ/2^kℤ)^*$.

### Why This Matters

- Central to the theory of the Carmichael function and its CRT decomposition.
- The non-cyclic structure of $(ℤ/2^kℤ)^*$ is a key fact distinguishing 2 from odd primes.
- Needed for complete characterization: $\lambda(2^a \prod p_i^{a_i}) = \text{lcm}(\lambda(2^a), \lambda(p_1^{a_1}), \ldots)$.
- Relevant to RSA and discrete logarithm theory.
- The parent proof (`euler-totient-oq-01`) handles $\lambda(p) = p-1$ and $\lambda(2) = 1$ but not the 2-primary case for $k \geq 3$.

## Known Results

### What's Already Proven (in `euler-totient-oq-01`)

- `carmichael_prime`: λ(p) = p - 1 for primes p
- `carmichael_one`: λ(1) = 1
- `carmichael_two`: λ(2) = 1
- `carmichael_dvd_totient`: λ(n) ∣ φ(n)
- `carmichael_minimal`: λ(n) ∣ e iff $a^e \equiv 1$ for all coprime a

### What We Need

- The element 3 ∈ (ℤ/2^kℤ)^* has multiplicative order $2^{k-2}$ for k ≥ 3.
- Therefore $\lambda(2^k) = 2^{k-2}$ for k ≥ 3.

### Our Goal

1. Prove `ord_three_two_pow`: the multiplicative order of 3 mod $2^k$ is $2^{k-2}$ for k ≥ 3.
2. Derive `carmichael_two_pow`: $\lambda(2^k) = 2^{k-2}$ for k ≥ 3.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `euler-totient-oq-01` | Parent — defines carmichael, proves λ(p) = p-1 | ZMod, orderOf |
| `euler-totient` | Base φ function | Nat.totient |

## Initial Thoughts

### Potential Approaches

1. **Order of 3 mod 2^k by induction**: Show ord_{2^k}(3) = 2^{k-2} by induction.
   Key step: $3^{2^{k-2}} \equiv 1 \pmod{2^k}$ but $3^{2^{k-3}} \not\equiv 1 \pmod{2^k}$.
   This follows from the 2-adic valuation of $3^{2^m} - 1$ being exactly $m + 2$.
   - Risk: LTE (lifting-the-exponent) for p=2 has careful hypotheses in Lean.

2. **Direct computation for small k**: Verify λ(8) = 2, λ(16) = 4, λ(32) = 8 by `decide`, then prove inductive step.
   - Risk: `decide` may time out for large moduli; inductive step still needs the key lemma.

3. **ZMod Mathlib search**: Check if Mathlib has `ZMod.orderOf` lemmas for 2-primary case.

### Key Difficulties

- Need: $v_2(3^{2^m} - 1) = m + 2$ for all m ≥ 0 (2-adic valuation).
- Then: ord_{2^k}(3) = 2^{k-2} follows from upper/lower bound on order.
- Lean proof: `multiplicity 2 (3^(2^m) - 1) = m + 2` by induction.

### What Would a Proof Need?

- `ZMod.orderOf_dvd_of_pow_eq_one`
- `orderOf_eq_prime_pow` or manual lower/upper bound argument
- 2-adic valuation induction: `multiplicity` API from `Mathlib.NumberTheory.Multiplicity`
- Key identity: $3^{2^m} = 1 + 2^{m+2} \cdot t_m$ where $t_m$ is odd (by induction)

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Classical result; proof by 2-adic induction is well-understood mathematically.
- Mathlib has `ZMod`, `orderOf`, and `multiplicity` APIs.
- Small cases verifiable by `decide` (k=3,4,5 at least).
- The key valuation lemma is 10-15 lines of Lean.

**Estimated Effort**:
- Exploration: 1 session (Mathlib search for orderOf/ZMod lemmas)
- Formalization: 2-3 sessions

## References

### Books

- Ireland & Rosen. *A Classical Introduction to Modern Number Theory*, Ch. 4.
- Niven, Zuckerman & Montgomery. *An Introduction to the Theory of Numbers*, §2.8.

### Mathlib

- `Mathlib.Data.ZMod.Basic` — ZMod, units, orderOf
- `Mathlib.GroupTheory.OrderOfElement` — orderOf, exponent
- `Mathlib.NumberTheory.Multiplicity` — 2-adic valuation tools

## Metadata

```yaml
tags:
  - number-theory
  - carmichael-function
  - group-theory
  - zmod
  - multiplicative-order
related_proofs:
  - euler-totient-oq-01
  - euler-totient
difficulty: medium
source: gallery-gap
created: 2026-04-05T16:35:02-07:00
```
