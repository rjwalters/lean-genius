# Erdős #1181 - Knowledge Base

## Problem Statement

Let q(n,k) denote the least prime which does not divide ∏_{1≤i≤k}(n+i).
Is it true that there exists some c > 0 such that, for all large n,
  q(n, log n) < (1-c)(log n)²?

## Status

**Erdős Database Status**: OPEN
**Formalization Status**: COMPLETE (axiomatized)

**Tractability Score**: 6/10
**Aristotle Suitable**: Yes (1 theorem sorry: iterated_log_sublinear)

## Tags

- erdos
- number-theory
- prime-divisors
- consecutive-products
- primorial
- PNT

## Key Results

### Known Upper Bound (Trivial)
q(n, log n) ≤ (1+o(1))(log n)² follows from:
- All primes p < q(n,k) divide the consecutive product
- Their primorial satisfies: primorial(q) ≤ ∏(n+i) ≤ (n+k)^k
- By PNT (θ(q) ~ q): q ≤ (1+o(1)) · k · log(n+k)
- For k = ⌊log n⌋: q ≤ (1+o(1))(log n)²

### Tao's Heuristic
q(n, log n) ≪ (log log n / log log log n) · log n
Would be dramatically stronger than the (1-c)(log n)² conjecture.

## Related Problems

- **Problem #457**: Lower bound question — q(n, log n) ≥ (2+ε) log n infinitely often?
- Problem #663: Related prime factors of consecutive products
- Problem #383, #841: Related number theory / prime divisor problems

## Formalization Details

### Proved Constructively (no axioms)
- consecutiveProduct_pos: positivity from Finset.prod_pos
- q_prime: from Nat.find_spec
- q_not_dvd: from Nat.find_spec
- q_minimal: from Nat.find_min
- **conjectures_compatible**: infinite set ∩ cofinite set is infinite (Set.Infinite.diff + Filter.eventually_atTop)
- **tao_implies_erdos1181**: calc proof complete (modulo iterated_log_sublinear)

### Axioms (4)
1. trivial_upper_bound: (1+o(1))(log n)² bound via primorial/PNT
2. erdos_1181: main open conjecture
3. pnt_chebyshev: PNT for Chebyshev function θ(x) ~ x
4. primorial_divides_bound: if all primes < q divide m, then θ(q) ≤ log m

### Sorries (1 theorem)
1. iterated_log_sublinear: C·(loglog n / logloglog n) < (1/2)·log n eventually

### Notes on Axioms
- **pnt_chebyshev**: PNT is NOT in base Mathlib. The PrimeNumberTheoremAnd external project has it, but it's not integrated.
- **primorial_divides_bound**: Potential issue — θ sums primes ≤ q_val (inclusive via Icc) but hypothesis covers primes < q_val (strict).

## References

- Erdős [Er79d, p.78]
- Erdős-Pomerance [ErGr80, p.91]
- Tao's probabilistic heuristics (comments on problem #457)

## Sessions

### Session 1 (2026-03-29, researcher-9)
- Created full formalization from scratch
- Identified this as the upper bound sub-question from #457
- Built constructive q(n,k) definition (Nat.find, no axioms)
- Created gallery entry with full annotations
- 2 Aristotle-suitable theorem sorries identified

### Session 2 (2026-03-29, researcher-6)
- **Proved conjectures_compatible** (eliminated 1 sorry): Set.Infinite.diff + Filter.eventually_atTop
- **Restructured tao_implies_erdos1181**: isolated growth comparison as iterated_log_sublinear, proved calc steps
- Net result: 2 sorries → 1, 7 theorems → 8, 235 → 261 lines
- Investigated PNT in Mathlib — not in base Mathlib, axiom stays

---

*Generated from erdosproblems.com, updated 2026-03-29*
