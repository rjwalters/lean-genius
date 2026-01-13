# Erdős Problem 69: Irrationality of ∑ω(n)/2^n

## Problem Statement

Is $\sum_{n \geq 2} \frac{\omega(n)}{2^n}$ irrational, where $\omega(n)$ counts the number of distinct prime divisors of $n$?

**Status**: PROVED (Tao-Teräväinen 2025)

## Key Insights

### Tao's Identity
The crucial observation is:
$$\sum_{n \geq 2} \frac{\omega(n)}{2^n} = \sum_{p \text{ prime}} \frac{1}{2^p - 1}$$

This reduces Problem 69 to a special case of Problem 257.

**Proof sketch of identity:**
1. $\omega(n) = \sum_{p | n} 1$ (sum over prime divisors)
2. Swap order of summation: $\sum_n \sum_{p|n} \to \sum_p \sum_{n: p|n}$
3. Inner sum over multiples of $p$: $\sum_{k \geq 1} 1/2^{pk}$
4. Geometric series: $= 1/(2^p - 1)$

### Irrationality (Tao-Teräväinen 2025)
The sum $\sum_p 1/(2^p - 1)$ is proved irrational using deep analytic number theory methods.

## Session 2026-01-13

**Mode**: FRESH (via integration tooling)
**Outcome**: PROGRESS

### What I Did
1. Created formal proof structure in `proofs/Proofs/Erdos69Problem.lean`
2. Defined `omegaSum` and `primeSum` noncomputable functions
3. Proved helper lemma `geometric_sum_over_multiples`: For $p \geq 2$, $\sum_{k \geq 1} 1/2^{pk} = 1/(2^p - 1)$
4. Set up the main theorem structure with `tao_identity` and `primeSum_irrational`

### Sorry Classification
| Sorry | Classification | Reason |
|-------|---------------|--------|
| `tao_identity` | HARD | Known result, requires Fubini-like double sum manipulation |
| `primeSum_irrational` | RESEARCH | Tao-Teräväinen 2025, deep analytic number theory |

### Infrastructure Built
- `two_pow_gt_one`: For $p \geq 2$, $2^p > 1$
- `geometric_sum_over_multiples`: Geometric series for prime multiples
- `omega_eq_card_prime_divisors`: ω equals prime factor count

### Next Steps
1. Submit `tao_identity` to Aristotle for double-sum manipulation
2. The irrationality proof requires research-level analytic number theory beyond our scope

## References
- [TaTe25] T. Tao and J. Teräväinen, "Quantitative correlations and some problems on prime factors of consecutive integers." arXiv:2512.01739 (2025)
- erdosproblems.com/69
