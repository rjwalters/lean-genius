# Current State

**Phase**: ACT — {2,3} case fully solved + density-zero + coprime-empty proved; 1 deep axiom remains
**Since**: 2026-05-29T19:14:09.134Z
**Iteration**: 4
**Last Updated**: 2026-06-28 (researcher-3, S5 ACT)

## S5 ACT (researcher-3, 2026-06-28) — Yu-Chen coprime {2,3} = ∅, 0-axiom

Gave the first content to the previously-unused `CoprimeNonRepresentable` definition
by settling the {2,3} case of the Yu-Chen *coprime* non-representables, unconditionally
(0-axiom):
- `coprimeNonRepresentable_two_three_eq_empty : CoprimeNonRepresentable 2 3 = ∅`
  and the `3 2` companion. Reason: `NonRepresentable 2 3 = {0}` and `0` is not coprime
  to `2·3 = 6` (`Nat.coprime_zero_left`: `Coprime 0 6 ↔ 6 = 1`, false), so the filter
  empties the singleton. This *sharpens* Yu-Chen's "{2,3}-excluded" infinitude
  statement: for {2,3} there are not merely finitely many coprime non-representables —
  there are zero.
- `hasDensity_empty : HasDensity ∅ 0` ⟹ `coprimeNonRepresentable_two_three_density_zero`
  / `_three_two_density_zero`.

Host-verified (`lake env lean`, EXIT 0); `#print axioms` = propext/Choice/Quot only
(independent of `erdos_lewin_infinite`). 28→33 thm, 696→788 lines, axiom count
UNCHANGED at 1. The deep axiom `erdos_lewin_infinite` (Erdős–Lewin 1996 infinitude,
not in Mathlib) remains — not session-sized.

## S4 ACT (researcher-1, 2026-06-28) — Yu-Chen density-zero for {2,3}, 0-axiom

Gave content to the previously def-only `HasDensity` scaffolding by proving the
{2,3} case of the Yu-Chen density-zero phenomenon, unconditionally (0-axiom):
- `hasDensity_singleton_zero : HasDensity {0} 0` (count = 1, ratio 1/n → 0).
- `nonRepresentable_two_three_density_zero : HasDensity (NonRepresentable 2 3) 0`
  and the `3 2` companion — reduce to the singleton helper via the existing
  `nonRepresentable_two_three`/`_three_two` (= {0}). The sharpest possible Yu-Chen
  instance (density exactly 0, set = {0}).

Host-verified (`lake env lean`, EXIT 0); `#print axioms` = propext/Choice/Quot only.
The file's single deep axiom `erdos_lewin_infinite` (hard direction, {p,q}≠{2,3} ⇒
infinite, not in Mathlib) is UNCHANGED — genuinely deep (Erdős–Lewin 1996), not the
target this session.

## Current Focus

Reduce/eliminate the last deep axiom `erdos_lewin_infinite` (or a concrete special case).

## Active Approach

The {2,3} elementary side is exhausted (representability + non-rep set + density all
proved 0-axiom). Remaining work is the deep infinitude direction.

## Blockers

`erdos_lewin_infinite` is a deep 1996 result absent from Mathlib 4.26.

## Next Action

Attempt a concrete special case of the infinitude direction, or clean up the
remaining unused `minSummandBound`/`CoprimeNonRepresentable` scaffolding.

## Attempt Counts

- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0
