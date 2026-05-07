# Research State: basel-problem-oq-01-oq-01-oq-02-oq-03

## Current State
**Phase**: ACT (structural infrastructure being added; full proof requires Mathlib upstream)
**Path**: full
**Since**: 2026-05-07
**Last Updated**: 2026-05-07
**Iteration**: 2

## Current Focus
Iteration 2 (2026-05-07): added foundational structural lemmas required
by every subsequent proof attempt:
- `lcmRange_succ`: lcm(1,...,n+1) = Nat.lcm (lcmRange n) (n+1) — the
  recursive structure inducting along `n` will use.
- `lcmRange_dvd_lcmRange_of_le`: divisibility monotonicity.
- `lcmRange_monotone`: numerical monotonicity (with `n=0` boundary).

Iteration 1 (bootstrap, completed 2026-05-07):
- Provable elementary bounds: lcmRange n ≤ n!, lcmRange n ≤ n^n.
- Numerical verification of Hanson's bound for n ∈ {1..10, 12, 15, 20}.
- Axiom statement of the general claim with documentation of proof
  strategy and Mathlib gaps.

## Active Approach

**Approach (canonical, blocked on Mathlib infrastructure)**:
Hanson's 1972 Beta-integral approach. Use
`∫₀¹ x^k(1-x)^(n-k) dx = 1/((n+1)·C(n,k))` and
`lcmRange(n+1) · Beta(k, n-k) ∈ ℤ` to derive `3^n` via a
careful summing argument over k ∈ {0,...,n}.

Currently blocked on:
- Mathlib lacks Beta-integral identities in usable form for ℚ-valued
  bounds.
- Mathlib lacks the `primorial → lcm` bridge needed for the easier
  `4^n` intermediate.

## Attempt Count
- Total attempts: 2.
- Current approach attempts: 0 (Approach 1 not started; awaits Mathlib).
- Approaches tried: bootstrap with elementary bounds + axiom (iter 1);
  structural-lemma layer for inductive proofs (iter 2).

## Blockers
- **Mathlib Beta-integral over ℚ**: not in usable form.
- **Mathlib primorial → lcm bridge**: missing.
- **Mathlib LCM-specific bounds**: none exist.

## Next Action

**Two follow-up paths:**

1. **Intermediate `lcm(1..n) ≤ 4^n`** (easier). Develop the bridge
   `primorial(n) ≤ lcm(1..n) ≤ n · primorial(n)` and combine with
   Mathlib's `primorial_le_4_pow`. Estimated 1-2 weeks of focused work.

2. **Full Hanson `3^n`** (harder). Requires Beta-integral machinery.
   Estimated months.

Either result discharges (or strengthens) the parent file's
`lcm_hanson_bound` axiom.

## References

- `proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean` — bootstrap file.
- `proofs/Proofs/BaselProblemOQ01OQ01OQ02.lean:410` — parent's
  `axiom lcm_hanson_bound` that this OQ targets.
- `src/data/proofs/basel-problem-oq-01-oq-01-oq-02-oq-03/meta.json` — gallery.
- `research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03/problem.md` — full
  problem statement with three approaches and Mathlib gap analysis.
