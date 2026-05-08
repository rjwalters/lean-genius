# Research State: basel-problem-oq-01-oq-01-oq-02-oq-03

## Current State
**Phase**: ACT (structural infrastructure being added; full proof requires Mathlib upstream)
**Path**: full
**Since**: 2026-05-07
**Last Updated**: 2026-05-08 (Iteration 5, researcher-1)
**Iteration**: 5

## Current Focus
Iteration 5 (2026-05-08, this PR): added the prime-power
specialization on top of Iteration 3's `pow_dvd_lcmRange`:

- `prime_pow_dvd_lcmRange : ∀ {p n : ℕ}, p.Prime → 1 ≤ n →
   p ^ Nat.log p n ∣ lcmRange n`

The proof is a one-line specialization of `pow_dvd_lcmRange`, using
`Nat.pow_log_le_self p hn'` to discharge `p ^ Nat.log p n ≤ n`. New
imports: `Mathlib.Data.Nat.Log`, `Mathlib.Data.Nat.Prime.Basic`. This
is the maximal-prime-power half of Chebyshev's decomposition
`lcm(1,...,n) = ∏_{p prime ≤ n} p ^ ⌊log_p n⌋`.

Iteration 3 (#16772 merged): added `pow_dvd_lcmRange : 0 < b → b^k ≤ n
→ b^k ∣ lcmRange n` — the generic power-divisibility lemma whose prime
specialization Iteration 5 just discharged.

Iteration 2 (#16704 merged): added foundational structural lemmas:
- `lcmRange_succ`: lcm(1,...,n+1) = Nat.lcm (lcmRange n) (n+1).
- `lcmRange_dvd_lcmRange_of_le`: divisibility monotonicity.
- `lcmRange_monotone`: numerical monotonicity.

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
- Total attempts: 5.
- Current approach attempts: 0 (Approach 1 not started; awaits Mathlib).
- Approaches tried: bootstrap with elementary bounds + axiom (iter 1);
  structural-lemma layer for inductive proofs (iter 2); generic
  power-divisibility lemma `pow_dvd_lcmRange` (iter 3); empirical
  evidence extension n ∈ {25, 30, 50} (iter 4, in flight as #16880);
  prime-power specialization `prime_pow_dvd_lcmRange` (iter 5, this PR).

## Blockers
- **Mathlib Beta-integral over ℚ**: not in usable form.
- **Mathlib primorial → lcm bridge**: missing.
- **Mathlib LCM-specific bounds**: none exist.

## Next Action

**Iteration 6 candidate**: prove `lcmRange_eq_prod_prime_powers`,
the Chebyshev decomposition

  `lcmRange n = ∏ p ∈ Finset.filter Nat.Prime (Finset.range (n+1)),
                p ^ Nat.log p n`.

Forward direction (RHS ∣ LHS): use `prime_pow_dvd_lcmRange` (this PR)
together with pairwise-coprimality of distinct primes — distinct prime
powers are coprime, so a finite-product divisibility argument gives
the result. The relevant Mathlib facts are
`Nat.Coprime.prime_pow_pow` and `Finset.prod_dvd_of_dvd_of_pairwiseDisjoint`.

Reverse direction (LHS ∣ RHS): for each `k ∈ {1,...,n}` use unique
factorization (`Nat.factorization`) to express `k = ∏_p p^(k.factorization p)`
and bound each exponent by `Nat.log p n`.

After this, the Chebyshev product gives an explicit numerator-denominator
form for `lcmRange n` as a product over primes ≤ n, and the bound
`lcmRange n ≤ ∏_{p ≤ n} n = n^{π(n)}` follows immediately
(strictly weaker than 3^n but a non-trivial published-bound milestone).

**Long-term paths still open:**

1. **Intermediate `lcm(1..n) ≤ 4^n`** via primorial bridge: blocked on
   the Mathlib bridge `lcm(1..n) ≤ n · primorial(n)`. Note (Iteration 3
   insight): the literal `≤ n · primorial(n)` form is FALSE
   (counterexample n=9: 2520 > 1890). Correct route is via Chebyshev's
   prime-power formula above.

2. **Full Hanson `3^n`** (Beta-integral + Chebyshev): months.

Either result discharges the parent file's `lcm_hanson_bound` axiom.

## References

- `proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean` — bootstrap file.
- `proofs/Proofs/BaselProblemOQ01OQ01OQ02.lean:410` — parent's
  `axiom lcm_hanson_bound` that this OQ targets.
- `src/data/proofs/basel-problem-oq-01-oq-01-oq-02-oq-03/meta.json` — gallery.
- `research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03/problem.md` — full
  problem statement with three approaches and Mathlib gap analysis.
