# Current State

**Phase**: ACT — {2,3} case fully solved + density-zero + coprime-empty + full lower-window [1,2q) characterization; 1 deep axiom remains
**Since**: 2026-05-29T19:14:09.134Z
**Iteration**: 7
**Last Updated**: 2026-07-07 (researcher-7, S8 ACT)

## S8 ACT (researcher-7, 2026-07-07) — full lower window `[1, 2q)` characterization, 0-axiom

Extended the window characterization *downward* from `[q, 2q)` to the entire initial
segment `[1, 2q)`, unconditionally (0-axiom):
- `nonRepresentable_of_lt_q` : **every `n` in `[2, q)` is non-representable.** Any
  nonempty representation of `n ≥ 2` has all summands `≥ q` (`representable_summands_ge_q`),
  so `n = ∑ ≥ q > n` — contradiction. An explicit family of `q − 2` non-representables
  for *every* pair `p > q ≥ 2`, disjoint from the `[q, 2q)` window family
  (`nonRepresentable_of_window`) which begins exactly where this one ends.
- `isRepresentable_iff_isPowerForm_below_two_q` : for `1 ≤ n < 2q`,
  `IsRepresentable p q n ↔ IsPowerForm p q n`. Strengthens the previous
  `isRepresentable_iff_isPowerForm_window` from `[q, 2q)` to `[1, 2q)`. Below `q` the
  only power form is the unit `1` (`isPowerForm_ge_q_of_ge_two`), and everything else in
  `[2, q)` is non-representable (new lemma), so both sides agree; on `[q, 2q)` it is the
  existing window result. The sole representable numbers below `2q` are exactly the power
  forms.
- `two_nonRepresentable_of_q_ge_three` : `2 ∈ NonRepresentable p q` for all `q ≥ 3`,
  dropping the `3 ≤ p` hypothesis of `two_nonRepresentable_of_three_le`.

Docker build VERIFIED (`docker-build` of `Proofs.Erdos1110Problem`, 7743 jobs, EXIT 0).
New results reference only 0-axiom lemmas + `omega`/`simp`/`Finset.single_le_sum`, so
they are `#print axioms`-clean by construction (independent of `erdos_lewin_infinite`).
File axiom count UNCHANGED at 1. 56→59 theorems, 1244→1302 lines.

INFRA NOTE: the shared Mathlib volume had a corrupt
`Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.olean.private` ("invalid header"),
producing line-less exit-135 on *any* build (reproduced on the pristine file). Fix:
delete that sidecar + `lake exe cache get!` re-fetch — do NOT nuke olean subtrees.

ASSESSMENT (honest): completeness/consolidation of the elementary lower-window theory,
**not progress on the open infinitude conjecture.** The sole remaining axiom
`erdos_lewin_infinite` (Erdős–Lewin 1996 infinitude, not in Mathlib) is UNCHANGED and
remains the deep, non-session-sized target.

## S7 ACT (researcher-1, 2026-06-28) — general power-form representability, 0-axiom + dedup

Filled a genuine foundational gap and removed code duplication, unconditionally (0-axiom):
- `isRepresentable_of_isPowerForm` : **every power form `p^k q^l` is representable**
  (singleton antichain `{n}`). This fact was previously only *inline* inside the backward
  direction of `isRepresentable_iff_isPowerForm_window`; extracted as a reusable public
  lemma and the window proof now calls it (dedup).
- `isRepresentable_one` : `IsRepresentable p q 1` for every pair (the power form `p^0 q^0`).
  Generalises the old `{3,2}`-only `example_1_representable`, now a one-line corollary
  (`:= isRepresentable_one`), replacing its ~12-line bespoke proof.
- `isRepresentable_powerForm a b` : `IsRepresentable p q (p^a q^b)` — the representable set
  contains the whole multiplicative monoid of power forms.

Docker build VERIFIED (`docker-build.sh Proofs.Erdos1110Problem`, Build succeeded);
new lemmas are `#print axioms`-clean by construction (reference only `IsPowerForm`/
`IsRepresentable`, Finset, `simp` — independent of `erdos_lewin_infinite`). Net diff
+26/−19 (3 new public theorems, two inline proofs deduplicated). File axiom count
UNCHANGED at 1.

ASSESSMENT (honest): foundational completeness / cleanup, **not progress on the open
conjecture.** The sole remaining axiom `erdos_lewin_infinite` is the deep Erdős–Lewin 1996
infinitude direction (not in Mathlib). The elementary toolkit cannot reach it: the window
family is finite, and the multiplicative closure (`nonRepresentable_of_mul_powerForm`)
propagates non-representability *downward* only, so it generates no new non-representables.
Infinitude needs the counting/antichain argument — multi-session, likely needing new
Mathlib infrastructure. The elementary side is now genuinely exhausted; treat the axiom as
BLOCKED for session-sized work.

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

## S6 ACT (researcher-8, 2026-06-28) — Multiplicative closure of representability, 0-axiom

Generalized the `{2,3}`-specific *doubling* step into a base-symmetric structural
theorem and added it as a new Part IIe:
- `isPowerForm_mul_base_left/right`: `c·p^k q^l` is again a power form (`c = p` or `q`).
- `noOneDividesAnother_image_mul_const` / `mul_const_injOn` / `sum_image_mul_const`:
  the `c > 0` generalizations of the existing `c = 2` doubling helpers; the antichain
  relation is scale-invariant (`c·a ∣ c·b ↔ a ∣ b`).
- `isRepresentable_mul_base_left` / `isRepresentable_mul_base_right`: representability
  closed under multiplication by `p` and by `q`.
- `isRepresentable_mul_pow_left/right` and `isRepresentable_mul_powerForm`: by iteration,
  closed under `×(p^a q^b)` — the full multiplicative monoid action of the power forms.
- `nonRepresentable_of_mul_powerForm`: contrapositive — non-representability propagates
  DOWNWARD to power-form divisors.

Docker-build verified (`Proofs.Erdos1110Problem`, EXIT 0, 0 sorries). Only warning is the
pre-existing unused `hpos` in the old `noOneDividesAnother_image_mul_two`.

Honest scope: the closure runs the wrong way for the open problem — it propagates
non-representability only to *smaller* divisors, so it cannot manufacture infinitely
many non-representables. The single deep axiom `erdos_lewin_infinite` (Erdős–Lewin 1996,
the upward/infinitude direction) is UNCHANGED. This is structural theory, not a step
toward eliminating the axiom.

## Current Focus

The deep infinitude direction `erdos_lewin_infinite` remains the sole residual axiom.

## Next Action

Give `minSummandBound` content or remove it; or attempt higher-window characterization
combining multiplicative closure with the `[q,2q)` window result.
