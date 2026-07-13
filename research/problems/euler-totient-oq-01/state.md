# Current State

**Phase**: COMPLETED
**Since**: 2026-05-17T17:58:00Z
**Iteration**: 3

## Current Focus

Gallery proof is fully formalized at `proofs/Proofs/EulerTotientOQ01.lean`
(84 lines, status `verified`, badge `mathlib`). state.md catches up with the
realized work: the Carmichael function and its core divisibility property are
encoded as a thin layer over Mathlib's `Monoid.exponent` machinery.

## Active Approach

Verified formalization via Mathlib structural reuse: the Carmichael function
$\lambda(n)$ is defined as the exponent of $(\mathbb{Z}/n\mathbb{Z})^*$, and
its key properties follow from `Monoid.exponent_dvd_card`, `Monoid.exponent`,
and `IsCyclic.exponent_eq_card`.

Canonical inventory (per `proofs/Proofs/EulerTotientOQ01.lean`):
- 84 lines (split('\n').length), 0 sorries
- 0 axioms
- 1 definition: `CarmichaelFunction.carmichael`
- 6 theorems (narrow regex match — no private/protected wrappers)

## Blockers

None. No assumptions beyond Mathlib.

## Next Action

Maintenance only. Future work could expose richer API (CRT product formula,
explicit prime-power values $\lambda(p^k)$) but the open-question variant
asks only for the divisibility property $\lambda(n) \mid \varphi(n)$, which
is already proved.

## Attempt Counts

- Total attempts: 3
- Current approach attempts: 1
- Approaches tried: 1 (Mathlib `Monoid.exponent` thin wrapper)
