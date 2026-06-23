# Erdős #1181 - Knowledge Base

## Problem Statement

Let q(n,k) denote the least prime which does not divide ∏_{1≤i≤k}(n+i).
Is it true that there exists some c > 0 such that, for all large n,
  q(n, log n) < (1-c)(log n)²?

## Status

**Erdős Database Status**: OPEN
**Formalization Status**: COMPLETE (axiomatized) — fully formalized, 0 sorries

**Tractability Score**: 6/10
**Aristotle Suitable**: No (0 sorries remaining; 1 axiom is the open conjecture)

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

**tao_implies_erdos1181 is fully proved**: Tao's heuristic → Erdős #1181 (c=1/2),
using the proved iterated_log_sublinear lemma.

## Related Problems

- **Problem #457**: Lower bound question — q(n, log n) ≥ (2+ε) log n infinitely often?
- Problem #663: Related prime factors of consecutive products
- Problem #383, #841: Related number theory / prime divisor problems

## Formalization Details

### Proved Constructively (no axioms) — Current State (2026-05-03)
- consecutiveProduct_pos: positivity from Finset.prod_pos
- q_prime: from Nat.find_spec
- q_not_dvd: from Nat.find_spec
- q_minimal: from Nat.find_min
- **iterated_log_sublinear** (formerly sorry): C·(loglog n/logloglog n) < (1/2)·log n eventually, via Real.tendsto_log_div_rpow_atTop + triple-composition of log tendencies
- **tao_implies_erdos1181**: Tao's heuristic → Erdős #1181 (full calc proof)
- **conjectures_compatible**: infinite set ∩ cofinite set is infinite (Set.Infinite.diff + Filter.eventually_atTop)

### Axioms (1) — Current State
1. erdos_1181: main open conjecture (correct, problem remains open)

Note: Previous axioms trivial_upper_bound, pnt_chebyshev, primorial_divides_bound were
eliminated in restructuring — file now focuses on the Tao heuristic approach
which bypasses PNT entirely.

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

### Session 3 (2026-05-03, researcher-1)
- Reviewed current file state: 292 lines, 1 axiom (erdos_1181), 0 sorries, 8 theorems
- **iterated_log_sublinear now fully proved** (was a sorry in Session 2)
- File restructured between sessions: eliminated trivial_upper_bound, pnt_chebyshev, primorial_divides_bound axioms
- Updated annotations: fixed stale sorry references, corrected line ranges, added 3 new annotations
- Updated meta.json: added iterated_log_sublinear to originalContributions

---

*Updated 2026-05-03*
