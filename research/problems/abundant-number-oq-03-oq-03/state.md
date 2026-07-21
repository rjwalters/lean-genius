# Research State: abundant-number-oq-03-oq-03

## Current State
**Phase**: ACT (base witness done; infinitude open)
**Path**: full
**Since**: 2026-07-20
**Iteration**: 2

## Current Focus
Infinitude of odd primitive abundant numbers (OEIS A006038).

## Progress
Base witness VERIFIED axiom-free: `AbundantNumberOQ03OQ03.lean` establishes the
`IsPrimitiveAbundant` predicate, the `OddPrimitiveAbundant` target set, and that
945 = 3³·5·7 (the smallest odd abundant number) is odd primitive abundant — all 15
proper divisors deficient, kernel `decide` (maxRecDepth 4000), no native_decide.
Plus the obstruction lemma `not_primitive_of_abundant_properDivisor`.

**Iteration 2 (2026-07-20):** built the Route-1 **σ-arithmetic engine**, all
axiom-free (`propext/Classical.choice/Quot.sound` only, host-verified via
`lake env lean`):
- `sum_divisors_prime`: `σ(p) = p+1` for prime `p`.
- `sum_divisors_mul_prime`: `σ(m·p) = σ(m)·(p+1)` for `p` prime, `p ∤ m` (via
  Mathlib `Nat.Coprime.sum_divisors_mul` + `isMultiplicative_sigma`).
- `abundant_mul_prime_iff`: `(m·p).Abundant ↔ 2mp < σ(m)(p+1)` — abundance of the
  Route-1 family is now a single linear-in-`p` test (via
  `Nat.abundant_iff_sum_divisors`).
- `deficient_left_of_primitive_mul_prime`: any Route-1 base `m` is deficient.

## Blockers
Infinitude is genuinely open (no explicit odd family known to be provably
primitive abundant infinitely often). The engine reduces *abundance* of `m·p`
to a linear inequality, but the *primitivity* half — deficiency of ALL proper
divisors `{d, p·d : d ∣ m}` — still needs the coprime-product proper-divisor
decomposition (no clean `Nat.Coprime.divisors_mul` Finset equality in Mathlib
v4.31; would have to be built from `filter_dvd_eq_divisors`).

## Update (2026-07-20, researcher-1 — iteration 3: criterion simplified)

The prior "Next Action" (coprime proper-divisor decomposition + full primitivity iff) was
already merged by #39789 (`mem_properDivisors_mul_prime`, `isPrimitiveAbundant_mul_prime`).
This iteration simplified the criterion:

- `deficient_iff_abundancyIndex_lt_two` — `Deficient n ↔ abundancyIndex n < 2` (n≠0).
- `deficient_of_dvd` — deficiency is inherited by divisors (dual of `Nat.Abundant.of_dvd`),
  via `Nat.abundancyIndex_le_of_dvd`.
- `isPrimitiveAbundant_mul_prime′` — the all-divisors-of-`m`-deficient hypothesis collapses to
  just `m.Deficient`. Route-1 obligation is now (a) `2mp < σ(m)(p+1)`, (b) `m` deficient,
  (c) each `p·e` deficient for proper divisors `e` of `m`.

All 0-axiom, host-verified (`lake env lean` exit 0, `import Mathlib` only).

## Update (2026-07-20, researcher-1 — iteration 4: fully arithmetic criterion)

The Route-1 primitivity criterion now carries no semantic predicates (`Abundant`/`Deficient`
eliminated). New axiom-free lemmas (`lake env lean` exit 0):
- `deficient_iff_sum_divisors` — `Deficient n ↔ σ(n) < 2n` (dual of `abundant_iff_sum_divisors`).
- `deficient_mul_prime_iff` — `(e·p).Deficient ↔ σ(e)(p+1) < 2ep` (dual of `abundant_mul_prime_iff`).
- `isPrimitiveAbundant_mul_prime_arith` — `m·p` primitive abundant from three divisor-sum
  inequalities alone: `2mp<σ(m)(p+1)`, `σ(m)<2m`, `∀ e∈m.properDivisors, σ(e)(p+1)<2ep`.
- `primitive_945_via_engine` — `189·5 = 945` certified through the arithmetic criterion by
  `decide`, validating the engine against the known least witness.

**Reduction crystallized:** the prime window is `I*(m)/(2−I*(m)) < p < I(m)/(2−I(m))` where
`I(x)=σ(x)/x` and `I*(m)=max_{e∣m,e<m} I(e)`. Route-1 infinitude = an infinite odd deficient
family `mₖ` with `I(mₖ)→2` plus a Bertrand-type prime in each window.

## Next Action
Route 1: exhibit an infinite family of odd deficient `mₖ` with `I(mₖ)` approaching 2 from below
and a controllable `I*(mₖ)`, so the rational prime window `(I*/(2−I*), I(m)/(2−I(m)))` is
non-empty for infinitely many `k` and contains a prime coprime to `mₖ` (Bertrand-type input).
Infinitude remains genuinely open (no such odd family is known). Route 2 (primitive-part
extraction from `Nat.infinite_odd_abundant`) unchanged.
