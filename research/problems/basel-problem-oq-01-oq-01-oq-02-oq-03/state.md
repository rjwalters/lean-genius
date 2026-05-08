# Research State: basel-problem-oq-01-oq-01-oq-02-oq-03

## Current State
**Phase**: ACT (structural infrastructure being added; full proof requires Mathlib upstream)
**Path**: full
**Since**: 2026-05-07
**Last Updated**: 2026-05-08 (Iteration 8, researcher-9)
**Iteration**: 8

## Current Focus
Iteration 8 (2026-05-08, this PR): closes the **reverse direction of
Chebyshev's decomposition**, complementing Iter 7's forward direction:

- `lcmRange_dvd_prod_prime_powers (n : ℕ) :
   lcmRange n ∣ ∏ p ∈ (Finset.range (n+1)).filter Nat.Prime, p ^ Nat.log p n`

The proof routes through `Nat.factorization`:

1. By `Finset.lcm_dvd_iff` it suffices to show every `m ∈ {1,…,n}`
   divides the product `N`.
2. Rewrite `m = ∏_{p ∈ m.primeFactors} p^(m.factorization p)` via
   `Nat.factorization_prod_pow_eq_self`.
3. Extend the index set from `m.primeFactors` to
   `(Finset.range (n+1)).filter Nat.Prime` via `Finset.prod_subset`
   (the extra factors contribute `p^0 = 1`).
4. Pointwise divisibility on the resulting two products: each
   `m.factorization p ≤ Nat.log p n` since
   `p^(m.factorization p) ∣ m ≤ n` and `Nat.le_log_of_pow_le` lifts
   the `p^k ≤ n` inequality into the exponent bound (using
   `hp_prime.one_lt`).

Combining Iter 7 and Iter 8 via `Nat.dvd_antisymm` gives the exact
Chebyshev identity (Iter 9 candidate).

Iteration 7 (#17166 merged): closes the **easy direction of
Chebyshev's decomposition**, the major structural milestone of the
last six iterations:

- `prod_prime_powers_dvd_lcmRange (n : ℕ) :
   (∏ p ∈ (Finset.range (n+1)).filter Nat.Prime, p ^ Nat.log p n)
     ∣ lcmRange n`

The proof has two parts:
1. **Helper lemma** `prod_dvd_of_pairwise_coprime` (private; ~22 lines):
   for any Finset ℕ S and function f : ℕ → ℕ, if every f p (for p ∈ S)
   divides N and the f p are pairwise coprime, then ∏ f p ∣ N.
   Standard Finset.induction; combines `Nat.Coprime.prod_right` (lift
   pairwise to coprime-with-product) with `Nat.Coprime.mul_dvd_of_dvd_of_dvd`.
   Direct parallel of `Erdos1057Problem.prod_primes_dvd_of_each_dvd`,
   abstracted over f to support prime-power factors.
2. **Main theorem** (8 lines on top of helper): n=0 case dispatches via
   `Nat.not_prime_zero` (range 1 = {0}, 0 ∉ Prime ⇒ filter = ∅);
   n ≥ 1 case applies the helper with f = (· ^ Nat.log · n), feeding
   `prime_pow_dvd_lcmRange` (each-factor-divides) and
   `coprime_prime_pow_pow_of_ne` (pairwise-coprime).

Iteration 6 (#17128 merged): added `coprime_prime_pow_pow_of_ne :
∀ {p q}, p.Prime → q.Prime → p ≠ q → ∀ a b, Coprime (p^a) (q^b)`.

Iteration 5 (#17021 merged): added the prime-power
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
- Total attempts: 8.
- Current approach attempts: 0 (Approach 1 not started; awaits Mathlib).
- Approaches tried: bootstrap with elementary bounds + axiom (iter 1);
  structural-lemma layer for inductive proofs (iter 2); generic
  power-divisibility lemma `pow_dvd_lcmRange` (iter 3); empirical
  evidence extension n ∈ {25, 30, 50} (iter 4, in flight as #16880);
  prime-power specialization `prime_pow_dvd_lcmRange` (iter 5, #17021);
  coprime distinct prime powers `coprime_prime_pow_pow_of_ne` (iter 6,
  #17128); easy direction of Chebyshev's decomposition
  `prod_prime_powers_dvd_lcmRange` (iter 7, #17166); reverse
  direction `lcmRange_dvd_prod_prime_powers` via `Nat.factorization`
  (iter 8, this PR).

## Blockers
- **Mathlib Beta-integral over ℚ**: not in usable form.
- **Mathlib primorial → lcm bridge**: missing.
- **Mathlib LCM-specific bounds**: none exist.

## Next Action

**Iteration 9 candidate**: the **antisymmetric closure** —
combining Iter 7 and Iter 8 to produce the exact Chebyshev identity:

  `lcmRange_eq_prod_prime_powers : lcmRange n =
     ∏ p ∈ filter Prime (range (n+1)), p ^ Nat.log p n`

This is a one-line `Nat.dvd_antisymm` proof from
`prod_prime_powers_dvd_lcmRange` (Iter 7) and
`lcmRange_dvd_prod_prime_powers` (Iter 8).

After this, the Chebyshev product gives an explicit prime-power
form for `lcmRange n`, and the bound
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
