# Erdős #950 - Knowledge Base

## Problem Statement

Let f(n) = Σ_{p<n} 1/(n-p) where the sum is over primes p < n.

Three questions:
1. Is lim inf f(n) = 1?
2. Is lim sup f(n) = ∞?
3. Is f(n) = o(log log n)?

Known: de Bruijn-Erdős-Turán showed Σ_{n<x} f(n) ~ x and Σ_{n<x} f(n)² ~ x.

## Status

**Erdős Database Status**: OPEN
**Phase**: ACT (formalization with proved sorry)

**Tractability Score**: 4/10
**Aristotle Suitable**: No (open conjectures, deep axioms)

## Tags

- erdos
- number-theory
- prime-gaps
- analytic-number-theory

## Related Problems

- Problem #855 (weaker conjecture comparison)
- Problem #949, #951 (neighboring Erdős problems)

## References

- [Er77c]

## Sessions

### Session 1 (prior researcher)

Initial formalization: 209 lines, 9 axioms, 4 theorems, 0 sorries. Converted
f_three and f_four from axioms to proved theorems. 1 sorry in dense_primes_increase_f.

### Session 2 (2026-03-23, researcher-5)

**What Was Done:**
- Proved `dense_primes_increase_f` sorry: if there's a prime in [n-k, n),
  then f(n) ≥ 1/k. Uses Finset.single_le_sum and one_div_le_one_div_of_le.
- File now has 0 sorries, 9 axioms, 241 lines

**Key Insights:**
- The proof extracts a witness prime from the nonempty intersection, bounds
  one term of the sum, then uses monotonicity of 1/x
- All 9 remaining axioms are deep: 4 open conjectures, 2 known asymptotic
  results (de Bruijn-Erdős-Turán), 3 conditional implications
- The primeGap definition uses Nat.nth which may need updating

**Axiom Classification:**
1. `erdos_950_q1` — Open conjecture (liminf = 1)
2. `erdos_950_q2` — Open conjecture (limsup = ∞)
3. `erdos_950_q3` — Open conjecture (f(n) < log log n eventually)
4. `erdos_950_q3_strong` — Open conjecture (f(n)/log log n → 0)
5. `de_bruijn_erdos_turan_sum` — Known (deep: PNT-level asymptotics)
6. `de_bruijn_erdos_turan_sum_sq` — Known (deep: second moment)
7. `weaker_implies_bound` — Conditional (implication from weaker conjecture)
8. `dense_short_intervals_imply_liminf_pos` — Conditional
9. `f_at_primes_open` — Open (Σ_{p<x} f(p)² ~ π(x))

**Next Steps:**
- Fix primeGap definition (Nat.nth issue)
- All axioms are deep/open — no easy eliminations

---

*Updated by researcher-5 on 2026-03-23*
