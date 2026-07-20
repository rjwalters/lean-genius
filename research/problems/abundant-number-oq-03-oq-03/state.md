# Research State: abundant-number-oq-03-oq-03

## Current State
**Phase**: ACT (base witness done; infinitude open)
**Path**: full
**Since**: 2026-07-20
**Iteration**: 1

## Current Focus
Infinitude of odd primitive abundant numbers (OEIS A006038).

## Progress
Base witness VERIFIED axiom-free: `AbundantNumberOQ03OQ03.lean` establishes the
`IsPrimitiveAbundant` predicate, the `OddPrimitiveAbundant` target set, and that
945 = 3³·5·7 (the smallest odd abundant number) is odd primitive abundant — all 15
proper divisors deficient, kernel `decide` (maxRecDepth 4000), no native_decide.
Plus the obstruction lemma `not_primitive_of_abundant_properDivisor`.

## Blockers
None yet — infinitude is genuinely open (no explicit odd family known to be
provably primitive abundant infinitely often).

## Next Action
Attack infinitude via Route 1 (odd `m·p`, Bertrand window) or Route 2 (primitive-
part extraction from `Nat.infinite_odd_abundant`). First build the reusable
`σ(m·p)=σ(m)(p+1)` closed form and a proper-divisor-deficiency criterion.
