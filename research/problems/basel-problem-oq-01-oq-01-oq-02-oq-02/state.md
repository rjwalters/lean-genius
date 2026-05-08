# Current State

**Phase**: ACT
**Since**: 2026-05-08
**Iteration**: 7

## Session 7 (this session, build pending)

Added two algebraic identities for the m=3 case as Part 7 of
`BaselProblemOQ01OQ01OQ02OQ02.lean`:

1. `three_mul_choose_three_eq` (n ≥ 3): `3 · C(n, 3) = n · C(n - 1, 2)`.
   Direct one-line corollary of `mul_choose_eq_mul_choose_pred`.
2. `two_mul_three_mul_choose_three_eq` (n ≥ 3):
   `2 · (3 · C(n, 3)) = n · (n - 1) · (n - 2)`. Combines (1) with the
   m=2 absorption step `2 · C(n - 1, 2) = (n - 1) · (n - 2)`.

These reduce the m=3 divisibility question
`3 · C(n, 3) ∣ lcmRange n` to whether `n(n-1)(n-2)/2 ∣ lcmRange n`
(the `/2` being the substantive obstacle that needs Kummer's theorem
or a careful coprimality argument). Either route — Kummer or double
induction — can use these identities as the entry point.

**Axiom delta**: 0 (algebraic identities, no divisibility yet).

## Current Focus

Discharging base cases of the binomial-denominator divisibility
  `mul_choose_dvd_lcmRange : 0 < m → m ≤ n → m · C(n, m) ∣ lcmRange n`,
which is needed for the alternating-bilinear half of the van der
Poorten denominator analysis (route F).

Session 6 (this session) proved the m=1 and m=2 cases:
  `mul_choose_dvd_lcmRange_one`, `mul_choose_dvd_lcmRange_two`.
The general theorem (m ≥ 3) requires either Kummer's theorem on
`v_p(C(n, m))` or a double `(n, m)` induction (~100-200 lines).

Earlier sessions:
- Session 5: added `mul_choose_eq_mul_choose_pred` (binomial absorption)
  + `dvd_mul_choose` (n divides m·C(n,m)) + `lcmRange_pos` + numerical
  witnesses 6, 7. Identified that the full
  `mul_choose_dvd_lcmRange` is harder than the Session 5 next-action
  implied (absorption only proves divisibility by `n`, not by
  `lcmRange n`).
- Session 4: discharged the H_n^{(3)} half of vdP (`harmonicCubed_lcm_clear`).
- Sessions 1-3: route selection + infrastructure.

## Active Approach

**Route (F)**: van der Poorten closed form for `aperyA n`.

Two halves of the denominator analysis:
- **H_n^{(3)} half** (this OQ-02-OQ-02): DONE Session 4.
- **Alternating-bilinear half**: m=1, 2 base cases of the
  `m · C(n, m) ∣ lcmRange n` divisibility DONE in Session 6;
  general case (m ≥ 3) remains.

## Blockers

For `mul_choose_dvd_lcmRange` (m ≥ 3):
- The absorption identity `m·C(n,m) = n·C(n-1,m-1)` only proves
  divisibility by `n`, not by `lcmRange n`.
- Closing the m ≥ 3 case requires either:
  - (a) Kummer's theorem on `v_p(C(n,m)) = c_p(m, n-m)` per prime p,
    ~150 lines of p-adic analysis;
  - (b) double `(n, m)` induction via Pascal
    `C(n,m) = C(n-1,m) + C(n-1,m-1)` plus the absorption identity to
    flip indices, ~100-200 lines.
- For m=3 specifically, `3 · C(n, 3) = n(n-1)(n-2)/2` introduces a
  `/2` that cannot be discharged by the coprime argument used at m=2.

For the full `denominator_control`:
- The alternating bilinear summand
  `∑_{m=1}^{k} (-1)^{m-1}/(2 m^3 C(n,m) C(n+m,m))`
  needs `mul_choose_dvd_lcmRange` (general m) as input.
- `aperyA_explicit_formula` must be stated and validated numerically.

## Next Action

Session 7: prove the m=3 case
  `mul_choose_dvd_lcmRange_three : 3 ≤ n → 3 · C(n, 3) ∣ lcmRange n`
via Kummer's theorem on `v_2(C(n, 3))`. Concretely: rewrite
`3 · C(n, 3) = n · C(n - 1, 2)` via `mul_choose_eq_mul_choose_pred`,
then compute `v_2(C(n-1, 2))` via `Nat.Prime.multiplicity_choose` and
the carry-count of `2 + (n - 3)` in base 2.

Alternative if Kummer is too heavy: pursue the double `(n, m)`
induction starting from the proved m=1, m=2 base cases.

## Attempt Counts

- Total attempts: 6
- Current approach attempts: 3 (route F, sessions 4-6 each made
  forward progress)
- Approaches tried: 2 (recurrence-induction ruled out in session 1;
  van der Poorten closed form being executed in sessions 2-6+)
