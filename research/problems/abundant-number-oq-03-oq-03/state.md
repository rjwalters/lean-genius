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

## Update (2026-07-21, Loom Auditor / researcher-1 — Route 2 DISPROVEN; vein SATURATED)

Route 2 ("every abundant `n` has a primitive-abundant divisor", the extraction path to
infinitude) is now proven **FALSE** under the file's strict `IsPrimitiveAbundant` (abundant
with ALL proper divisors deficient, OEIS A071395) — landed on main (commit af5389a8f5):
- `not_isPrimitiveAbundant_12` — `12` (the smallest abundant) is not strict-primitive: its
  proper divisor `6` is perfect (not deficient).
- `no_isPrimitiveAbundant_dvd_12` — no divisor of `12` is `IsPrimitiveAbundant` (the smallest
  strict primitive abundant is `20 > 12`). A direct Route-2 counterexample: extraction holds
  only for the weaker A091191 notion (no abundant proper divisor), not the strict A071395.

**Vein status: SATURATED at the elementary layer.** Both infinitude routes are exhausted for
session-sized work:
- **Route 1** is deep-open MATHEMATICS, not a Lean gap: it needs an infinite family of odd
  deficient `mₖ` with `I(mₖ) → 2⁻` and controlled `I*(mₖ)` so the rational prime window
  `(I*/(2−I*), I(m)/(2−I(m)))` is non-empty infinitely often and holds a coprime prime
  (Bertrand-type input). No such odd family is known in the literature. This cannot be
  manufactured in Lean — it is the genuine open problem.
- **Route 2** is disproven (above).

The Route-1 σ-arithmetic engine (`abundant_mul_prime_iff`, `deficient_mul_prime_iff`,
`isPrimitiveAbundant_mul_prime_arith`, the `945` and `189·5` validations) is complete and
axiom-free; there is no remaining elementary reduction to formalize. Adding further witnesses
or restatements would be enumeration theater. **Do not re-serve for depth-first RICH work**
until a genuinely new mechanism for the odd-family construction (Route 1) is available.

## Next Action
BLOCKED (see structured blocker in the tracker). Reopen only with a materially new mechanism
for the Route-1 odd-family construction — an explicit infinite family of odd deficient `mₖ`
with `I(mₖ) → 2⁻` and a prime in each window. Route 2 is permanently closed (disproven).

## Status (researcher-2, 2026-07-24) — **TARGET PROVED: OddPrimitiveAbundant.Infinite**

The SATURATED verdict is superseded by a third mechanism neither recorded route
covered: first-crossing products of consecutive primes (grow the base through
the abundance boundary; ∑ 1/p divergence forces the crossing, first-crossing
minimality + mod-4 σ≠2n exclusion give primitivity, distinct least primes give
injectivity). `oddPrimitiveAbundant_infinite` in AbundantNumberOQ03OQ03.lean,
0 sorries / 0 axioms, docker green. Problem COMPLETED. See knowledge.md
session 2026-07-24 and the adversarial checklist in problem.md.

## Next Action
None — target theorem proved. Follow-up directions recorded in knowledge.md
(fixed-least-prime infinitude; ω ≥ 3 for odd abundants; Dickson finiteness).
