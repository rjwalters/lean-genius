# Current State

**Phase**: ACT
**Since**: 2026-05-08
**Iteration**: 8

## Session 8 (this session, build pending)

Added two helpers as Part 8 of `BaselProblemOQ01OQ01OQ02OQ02.lean`,
discharging the **odd-n** case of the m=3 divisibility:

1. `lcmRange_dvd_of_le` (Part 8a, generic): `m ≤ n → lcmRange m
   ∣ lcmRange n`. Pure structural lemma — `Finset.lcm_dvd` over a
   subset. Reusable in any chain-of-`lcmRange` argument.
2. `mul_choose_dvd_lcmRange_three_odd` (Part 8b): for `n ≥ 3` odd,
   `3 · C(n, 3) ∣ lcmRange n`. Proof by coprime assembly: `n` is
   coprime to `(n-1)(n-2)` (gcd | 2 but n odd), so the
   `Nat.Coprime.mul_dvd_of_dvd_of_dvd` route gives
   `n · (n-1)(n-2) ∣ lcmRange n`. By Part 7
   (`two_mul_three_mul_choose_three_eq`),
   `n · (n-1)(n-2) = 2 · (3 · C(n, 3))`, and `3 · C(n, 3)` divides
   its own multiple by 2.

The even-n case (Sessions 9+) requires the carry analysis on
`v_2(C(n, 3))`. For n=2k with k even (n ≡ 0 mod 4), the
factorization `n(n-1)(n-2)/2 = 2k · (n-1) · (k-1)` keeps the
factor-of-2 inside `n/2`, so a similar coprime argument may close
that subcase (since `n/2 = k` and `(n-1)(n-2)/2` no longer has a
common factor with k). For n=2k with k odd (n ≡ 2 mod 4), the
factorization is more delicate and Kummer is likely needed.

**Axiom delta**: 0 (algebraic identities + structural divisibility,
no new assumptions).

## Session 7 (PR #17146, merged)

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
- **Alternating-bilinear half**: m=1, 2 base cases DONE in
  Session 6; m=3 odd-n case DONE in Session 8 (this session);
  m=3 even-n case + m ≥ 4 remain.

## Blockers

For `mul_choose_dvd_lcmRange_three` (full m=3, even-n case):
- For `n` even, `n` and `(n-1)(n-2)` share the factor 2 (both
  `n` and `n-2` are even), so the simple coprime argument from
  Session 8 fails. Need either Kummer's theorem on
  `v_2(C(n, 3))` or a sub-case split:
  - n ≡ 0 mod 4: `n(n-1)(n-2)/2 = (n/2)(n-1)(n-2)` with
    `n/2` even, factor-of-2 absorbed into `n/2`. Coprime
    arg may still close after re-grouping.
  - n ≡ 2 mod 4: `n(n-1)(n-2)/2 = n(n-1)(n-2)/2` with both
    `n` and `n-2` ≡ 2 mod 4, so `(n-2)/2` is odd, but `n/2`
    is also odd — net `v_2 = 1` on each, total `v_2(...)` = 2.
    Need to verify `lcmRange n` has at least `v_2 = 2 + ...`.
    Probably Kummer.

For `mul_choose_dvd_lcmRange` (m ≥ 4):
- The full general case requires the same Kummer infrastructure.

For the full `denominator_control`:
- The alternating bilinear summand
  `∑_{m=1}^{k} (-1)^{m-1}/(2 m^3 C(n,m) C(n+m,m))`
  needs `mul_choose_dvd_lcmRange` (general m) as input.
- `aperyA_explicit_formula` must be stated and validated numerically.

## Next Action

Session 9: tackle the m=3 even-n case. Two approaches:

**(A) Sub-case via parity of n/2.** Split `n` even into two
sub-cases (n ≡ 0 mod 4 vs n ≡ 2 mod 4) and run the corresponding
coprime/factor-grouping arguments. Pure arithmetic, ~50-80 lines
per sub-case. Avoids Kummer entirely.

**(B) Kummer for `v_2(C(n, 3))`.** Use
`Nat.Prime.multiplicity_choose` and the carry-count of
`3 + (n - 3)` in base 2. Heavier (~150 lines including the
generic prime-exponent → divides translation), but generalizes
to `m = 4, 5, ...`.

Recommendation: try (A) first since it leverages the Session 8
infrastructure directly; fall back to (B) if (A) gets stuck.

## Attempt Counts

- Total attempts: 6
- Current approach attempts: 3 (route F, sessions 4-6 each made
  forward progress)
- Approaches tried: 2 (recurrence-induction ruled out in session 1;
  van der Poorten closed form being executed in sessions 2-6+)
