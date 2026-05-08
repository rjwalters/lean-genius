# Research State: basel-problem-oq-01-oq-01-oq-02-oq-03

## Current State
**Phase**: ACT (structural infrastructure being added; full proof requires Mathlib upstream)
**Path**: full
**Since**: 2026-05-07
**Last Updated**: 2026-05-08 (Iteration 10, researcher-4)
**Iteration**: 10

## Current Focus
Iteration 10 (2026-05-08, this PR): converts Iter 9's Chebyshev
decomposition equality into the **first non-trivial prime-counting bound**:

- `lcmRange_le_pow_card_primes {n : ℕ} (hn : 1 ≤ n) :
   lcmRange n ≤ n ^ ((Finset.range (n + 1)).filter Nat.Prime).card`

The proof is three lines: rewrite via `lcmRange_eq_prod_prime_powers`
(Iter 9), use `Finset.prod_const` to express `n^π(n)` as a constant
Finset product, then apply `Finset.prod_le_prod` with the per-factor
bound `p^⌊log_p n⌋ ≤ n` from `Nat.pow_log_le_self`.

The bound is strictly stronger than `lcmRange_le_self_pow` (`lcmRange n
≤ n^n`) for n ≥ 3, since `π(n) < n`. Asymptotically `n^π(n) ~ e^n` by
PNT (since π(n)·log n ~ n); for moderate n the bound exceeds Hanson's
3^n (numerical crossover near n=18: π(18)=7 gives 18^7 ≈ 6.1e8 vs
3^18 ≈ 3.9e8). This is therefore a **structural milestone** rather
than a route to Hanson — but it is the first bound with no
LCM-specific content remaining, exposing the prime-counting reduction
launched in Iters 5–9.

Iteration 9 (#17333 merged): added `lcmRange_eq_prod_prime_powers` —
the antisymmetric closure of Iters 7 and 8, giving the exact Chebyshev
identity `lcmRange n = ∏ p prime ≤ n, p^⌊log_p n⌋`.

Iteration 8 (#17312 merged): closes the **reverse direction of
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
- Total attempts: 10.
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
  (iter 8, #17312); antisymmetric closure `lcmRange_eq_prod_prime_powers`
  (iter 9, #17333); first prime-counting bound
  `lcmRange_le_pow_card_primes : lcmRange n ≤ n^π(n)` (iter 10,
  this PR).

## Blockers
- **Mathlib Beta-integral over ℚ**: not in usable form.
- **Mathlib primorial → lcm bridge**: missing.
- **Mathlib LCM-specific bounds**: none exist.

## Next Action

**Iteration 11 candidate**: **tighten the Iter 10 bound** by exploiting
that not every prime contributes a full factor of `n`. Two natural
sub-targets:

1. **Split-at-√n refinement**. For p > √n we have `⌊log_p n⌋ = 1`, so
   the prime-counting product factors as
   `(∏_{p ≤ √n} p^⌊log_p n⌋) · (∏_{√n < p ≤ n} p)`.
   - Big-prime block ≤ `primorial(n) / primorial(√n)`. Bounded by
     `4^n / 1 = 4^n` via `Nat.primorial_le_4_pow` (loose; refined
     bound exploits the denominator).
   - Small-prime block ≤ `√n^π(√n) ≤ √n^√n`, sub-exponential in n.
   - Combined: `lcmRange n ≤ √n^√n · 4^n`, asymptotically dominated
     by `4^n`.
2. **Erdős/Nair central-binomial route**. `lcm(1,…,n) ∣ n · C(2n, n)`
   (Erdős 1932) combined with `Nat.centralBinom_lt_pow_of_le_pow_of_pos`
   gives `4^n` directly. Mathlib has `Nat.centralBinom_lt_pow_of_le_pow_of_pos`
   (v4.26); the `lcm ∣ n · C(2n, n)` divisibility itself is missing
   and would need its own iteration to formalize.

After Iter 11, the Hanson 3^n target requires a sharper Chebyshev
prime-counting estimate (split at log n, or use Nair's polynomial
identity); each of those is a longer project.

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
