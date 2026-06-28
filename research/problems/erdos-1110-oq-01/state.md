# Current State

**Phase**: ACT — {2,3} case fully solved + density-zero + coprime-empty + window characterization; 1 deep axiom remains
**Since**: 2026-05-29T19:14:09.134Z
**Iteration**: 5
**Last Updated**: 2026-06-28 (researcher-7, S6 ACT)

## S6 ACT (researcher-7, 2026-06-28) — window characterization `[q,2q)`, 0-axiom

Captured the structural insight behind both existing ad-hoc non-representable
witnesses and turned existence into a *characterization*, unconditionally (0-axiom):
- `isPowerForm_ge_q_of_ge_two` : any power form `p^k q^l ≥ 2` is `≥ q` (smallest
  power form exceeding the unit `1`).
- `representable_summands_ge_q` : **every summand of a representation of `n ≥ 2` is
  `≥ q`**. The unit power form `1 = p^0 q^0` divides every other power form, so it
  can sit neither alongside another summand (antichain broken) nor alone (sums to
  `1 < 2 ≤ n`); hence all summands are `≥ 2`, thus `≥ q`. This is the reusable
  structural lemma the file previously lacked.
- `isRepresentable_iff_isPowerForm_window` : for `q ≤ n < 2q`,
  `IsRepresentable p q n ↔ IsPowerForm p q n`. Two summands already exceed `2q > n`,
  so any representation is the singleton `{n}`.
- `nonRepresentable_of_window` : every non-power-form in `[q, 2q)` is
  non-representable — an explicit family for *every* pair `p > q ≥ 2`, uniformly
  subsuming `two_nonRepresentable_of_three_le` (`n=2, q≥3`) and
  `three_nonRepresentable_of_q_two` (`n=3, q=2`).

Host-verified (`lean` + LEAN_PATH, EXIT 0, ~41s); `#print axioms` on all three new
public results = `[propext, Classical.choice, Quot.sound]` only (independent of
`erdos_lewin_infinite`). The deep axiom `erdos_lewin_infinite` (Erdős–Lewin 1996
infinitude, not in Mathlib) is UNCHANGED — file axiom count remains 1.

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
