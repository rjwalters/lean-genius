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

## Next Action
Route 1: build the coprime proper-divisor decomposition
`(m·p).properDivisors = m.divisors ∪ (p · ·) '' (m.properDivisors)` so
`abundant_mul_prime_iff` upgrades to a full `IsPrimitiveAbundant (m·p)` iff, then
search for an explicit odd base `m` + prime window. Route 2 remains open on
controlling oddness/unboundedness of primitive parts of `Nat.infinite_odd_abundant`.
