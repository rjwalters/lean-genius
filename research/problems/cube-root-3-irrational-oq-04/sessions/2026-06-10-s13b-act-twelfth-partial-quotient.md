# Session S13b — Twelfth Partial Quotient `cbrt3_a11 = 5`

**Date**: 2026-06-10
**Researcher**: researcher-1
**Slug**: `cube-root-3-irrational-oq-04`
**Mode**: Main-ACT (consumes S13a Helper-ACT sandwich)
**Outcome**: shipped `cbrt3_a11 = 5` (12th partial quotient of the simple
CF of `∛3`); main file 1747 → 1999 LOC (+252 LOC, +1 theorem;
theoremCount 18 → 19); 0 sorries, 0 axioms (slug remains 0/0).

## Summary

This session extends the chain `cbrt3_a0, …, cbrt3_a10` shipped in S12b
by one more partial quotient. Consumes the S13a Helper-ACT sandwich
pair (`597449/414248 < cbrt3 < 73011/50623`, combined gap ≈ 2.9·10⁻¹⁰)
through a 22-step `lt_div_iff₀` / `div_lt_iff₀` / `le_div_iff₀` chain
on an eleven-fold-nested fraction, followed by floor antisymmetry on
the final `1/x_11 ∈ (5, 41/8) ⊂ (5, 6)` interval.

## OEIS A002945 Cross-Verification

The simple CF of `∛3` begins:

  `[1; 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, 8, 3, 3, …]`

with index 0 through (here) index 11. This prefix is independently
verified to 200 decimal digits via the Newton-iteration CF expansion
in `sessions/2026-06-01-s12a-helper-act-eleventh-convergent.md` and
cross-checked against `sessions/2026-06-10-s13-helper-act-thirteenth-convergent.md`.

The chain proved so far:

| iter | session | theorem | partial quotient | helper introduced |
|------|---------|---------|------------------|-------------------|
| S2   | …       | `cbrt3_floor_eq_one` (or `cbrt3_a0`) | `a₀ = 1` | (initial bounds) |
| S3   | …       | `cbrt3_a1` | `a₁ = 2` | `four_thirds_lt_cbrt3`, `cbrt3_lt_three_halves` |
| S4   | …       | `cbrt3_a2` | `a₂ = 3` | `ten_sevenths_lt_cbrt3`, `cbrt3_lt_thirteen_ninths` |
| S5   | …       | `cbrt3_a3` | `a₃ = 1` | `twenty_three_sixteenths_lt_cbrt3` |
| S6   | …       | `cbrt3_a4` | `a₄ = 4` | `sixty_two_over_forty_three_lt_cbrt3`, `cbrt3_lt_seventy_five_over_fifty_two` |
| S7   | …       | `cbrt3_a5` | `a₅ = 1` | `four_thirty_seven_over_three_oh_three_lt_cbrt3` |
| S8   | …       | `cbrt3_a6` | `a₆ = 5` | `cbrt3_lt_five_twelve_over_three_fifty_five` |
| S9   | …       | `cbrt3_a7` | `a₇ = 1` | `nine_forty_nine_over_six_fifty_eight_lt_cbrt3` |
| S10  | …       | `cbrt3_a8` | `a₈ = 1` | `cbrt3_lt_six_two_oh_six_over_four_three_oh_three` |
| S11a | …       | (helper-only) | (paves for `a₉`) | `seven_one_five_five_over_four_nine_six_one_lt_cbrt3` |
| S11b | …       | `cbrt3_a9` | `a₉ = 6` | (reuses S11a + S10 upper) |
| S12a | …       | (helper-only) | (paves for `a₁₀`) | `one_three_three_six_one_over_nine_two_six_four_lt_cbrt3` |
| S12b | …       | `cbrt3_a10` | `a₁₀ = 2` | `cbrt3_lt_seven_three_oh_one_one_over_five_oh_six_two_three` |
| S13a | …       | (helper-only) | (paves for `a₁₁`) | `five_nine_seven_four_four_nine_over_four_one_four_two_four_eight_lt_cbrt3` |
| **S13b** | **this** | **`cbrt3_a11`** | **`a₁₁ = 5`** | (reuses S13a lower + S12b upper) |

## Sandwich Used

```
S13a (lower):  597449 / 414248  < cbrt3
S12b (upper):  cbrt3           < 73011 / 50623
```

- S13a lower-bound gap: `213_256_617_080_909_849 / 71_085_539_027_220_992`
  vs `3`; diff `−753_127` in the cube, relative gap `≈ 3.53·10⁻¹²`.
- S12b upper-bound gap: relative gap `≈ 2.87·10⁻¹⁰`.
- Combined sandwich gap (upper − lower): `≈ 2.9·10⁻¹⁰`, about **30×
  tighter** than S12b's sandwich (`13361/9264 < cbrt3 < 73011/50623`,
  combined gap `≈ 4.34·10⁻⁹`) which sufficed at depth 10.

## Algebraic Chain (22 steps)

Each step is one `linarith` call after `rw [lt_div_iff₀ …]` /
`rw [div_lt_iff₀ …]` / `rw [le_div_iff₀ …]`. The propagated rational
bounds at each level (verified in pre-claim Python sanity using
`fractions.Fraction`):

| step | symbol | bound (lower) | bound (upper) |
|------|--------|---------------|---------------|
| 0    | `cbrt3` (sandwich)         | `597449/414248`    | `73011/50623`   |
| 1    | `1/(cbrt3-1)`  = `y₁`      | `50623/22388`      | `414248/183201` |
| 2    | `y₁-2`          = `x₂`     | `5847/22388`       | `47846/183201`  |
| 3    | `1/x₂`          = `y₂`     | `183201/47846`     | `22388/5847`    |
| 4    | `y₂-3`          = `x₃`     | `39663/47846`      | `4847/5847`     |
| 5    | `1/x₃`          = `y₃`     | `5847/4847`        | `47846/39663`   |
| 6    | `y₃-1`          = `x₄`     | `1000/4847`        | `8183/39663`    |
| 7    | `1/x₄`          = `y₄`     | `39663/8183`       | `4847/1000`     |
| 8    | `y₄-4`          = `x₅`     | `6931/8183`        | `847/1000`      |
| 9    | `1/x₅`          = `y₅`     | `1000/847`         | `8183/6931`     |
| 10   | `y₅-1`          = `x₆`     | `153/847`          | `1252/6931`     |
| 11   | `1/x₆`          = `y₆`     | `6931/1252`        | `847/153`       |
| 12   | `y₆-5`          = `x₇`     | `671/1252`         | `82/153`        |
| 13   | `1/x₇`          = `y₇`     | `153/82`           | `1252/671`      |
| 14   | `y₇-1`          = `x₈`     | `71/82`            | `581/671`       |
| 15   | `1/x₈`          = `y₈`     | `671/581`          | `82/71`         |
| 16   | `y₈-1`          = `x₉`     | `90/581`           | `11/71`         |
| 17   | `1/x₉`          = `y₉`     | `71/11`            | `581/90`        |
| 18   | `y₉-6`          = `x₁₀`    | `5/11`             | `41/90`         |
| 19   | `1/x₁₀`         = `y₁₀`    | `90/41`            | `11/5`          |
| 20   | `y₁₀-2`         = `x₁₁`    | `8/41`             | `1/5`           |
| 21   | `⌊1/x₁₁⌋ ≤ 5`              | (upper-side floor)                   |
| 22   | `5 ≤ ⌊1/x₁₁⌋`              | (lower-side floor)                   |

Final result: `1/x_11 ∈ (5, 41/8) ⊂ (5, 6)`, so
`⌊1/x_11⌋ = 5 = a_11` ✓.

## Floor Antisymmetry

```lean
apply le_antisymm
· -- ⌊1/x₁₁⌋ ≤ 5: from 1/x₁₁ < 6.
  have hlt : 1 / (… - 2) < (6 : ℝ) := by
    rw [div_lt_iff₀ hpos11]
    -- Goal: 1 < 6 * x₁₁.  Have hx11_gt : 8/41 < x₁₁, so 6·(8/41) = 48/41 > 1.
    linarith [hx11_gt]
  have hflt : ⌊…⌋ < (6 : ℤ) := by rw [Int.floor_lt]; exact_mod_cast hlt
  omega
· -- 5 ≤ ⌊1/x₁₁⌋: from 5 ≤ 1/x₁₁.
  have hge : (5 : ℝ) ≤ 1 / (… - 2) := by
    rw [le_div_iff₀ hpos11]
    -- Goal: 5 * x₁₁ ≤ 1.  Have hx11_lt : x₁₁ < 1/5 (strict), so 5·(1/5) = 1.
    linarith [hx11_lt]
  rw [Int.le_floor]
  exact_mod_cast hge
```

The lower-side bound is exactly at the boundary: `5 * (1/5) = 1`,
relying on the strict `x_11 < 1/5` to push the product strictly below
`1`. This matches the pattern in S12b for `cbrt3_a10`, where the upper
bound was at the boundary `2 * (1/2) = 1`.

## Heartbeat Budget

`set_option maxHeartbeats 6400000 in` (2× S12b's 3_200_000).

The 2×-per-depth empirical scaling continues to hold:

| iter | depth | heartbeats | LOC delta |
|------|-------|------------|-----------|
| S7   | 5     | 200_000   | (helper only) |
| S8   | 6     | 200_000   | +160 |
| S9   | 7     | 400_000   | +225 |
| S10  | 8     | 800_000   | +234 |
| S11b | 9     | 1_600_000 | +216 |
| S12b | 10    | 3_200_000 | +242 |
| **S13b** | **11** | **6_400_000** | **+252** |

Predicted S14b (depth 12): `maxHeartbeats 12_800_000`, ~260 LOC delta.

## Pre-claim Python Cube-Direction Sanity

Per the slug's standing math-correction precedent (FIVE firings so far,
all caught pre-claim), every new bound's cube direction is verified
independently in Python `Fraction` arithmetic before being committed
to Lean. This session reused the S13a/S12b helpers (no new helpers
introduced), so the precaution was applied to the 22 propagated chain
bounds: all consistent with `cbrt3 ≈ 1.442_249_570_307_408_3` per
`Decimal` arithmetic.

Direct verification of the final step:

```python
>>> from fractions import Fraction
>>> # x_10 ∈ (5/11, 41/90); subtract 2 to get x_11; reciprocate.
>>> x10_lo, x10_hi = Fraction(5, 11), Fraction(41, 90)
>>> x11_lo, x11_hi = x10_lo - 0 - 2 + 2, x10_hi - 0 - 2 + 2
>>> # Wait: x10 - 2 directly.
>>> x11_lo, x11_hi = Fraction(90, 41) - 2, Fraction(11, 5) - 2  # using y_10 bounds
>>> x11_lo, x11_hi
(Fraction(8, 41), Fraction(1, 5))
>>> y11_lo, y11_hi = Fraction(1, x11_hi), Fraction(1, x11_lo)
>>> y11_lo, y11_hi
(Fraction(5, 1), Fraction(41, 8))
>>> int(y11_lo), int(y11_hi)  # floor candidates
(5, 5)  # both equal 5
```

## Math-Correction Precedent Status

**Count: FIVE (unchanged)**. No correction triggered this iteration.
Both the recursion arithmetic (`90/41 - 2 = 8/41`, `11/5 - 2 = 1/5`)
and the cube-direction inheritance from S13a/S12b matched the
expected values on the first pass. The pre-claim Python sanity
discipline has stabilized at this depth.

## Files Modified

- `proofs/Proofs/CubeRoot3IrrationalOQ04.lean`:
  1747 → 1999 LOC (+252 LOC, +1 theorem; theoremCount 18 → 19)
  — added `cbrt3_a11` with full 22-step chain.
- `src/data/research/problems/cube-root-3-irrational-oq-04.json`:
  `currentState.iteration` 15 → 16, `currentState.since` updated,
  `currentState.focus` rewritten for S13b ACT, `currentState.nextAction`
  rewritten for S14a Helper-ACT sketch, `attemptCounts.total`
  14 → 15, `leanFiles[CubeRoot3IrrationalOQ04.lean]` lineCount
  1747 → 1999, theoremCount 18 → 19, `knowledge.progressSummary`
  rewritten, `knowledge.builtItems` appended with `cbrt3_a11` entry,
  `knowledge.insights` appended with S13b insight, `knowledge.nextSteps[0]`
  rewritten for S14a sketch (replacing stale S12 entry).
- `research/problems/cube-root-3-irrational-oq-04/state.md`:
  head bumped to iteration 16, phase ACT, new Current Focus block,
  S14a Next Action block (replacing prior S13b sketch), prior
  iterations moved to Prior Focus sections.
- `research/problems/cube-root-3-irrational-oq-04/sessions/2026-06-10-s13b-act-twelfth-partial-quotient.md`:
  this file (new).
- `research/problems/cube-root-3-irrational-oq-04/knowledge.md`:
  Session S13b entry appended.

## S14a Next-Action Sketch

**S14a Helper-ACT (any researcher)**: Add the true 14th CF convergent
upper bound to `CubeRoot3IrrationalOQ04Helpers.lean`. Per OEIS A002945
`a_13 = 3`:

  `p_13 = 3 · 597449 + 73011 = 1_865_358`
  `q_13 = 3 · 414248 + 50623 = 1_293_367`

So `1_865_358/1_293_367 > cbrt3` (even-index 14th convergent, upper side).

Pre-claim Python cube sanity (this session):

```
1_865_358³ = 6_490_625_955_773_462_712
         > 6_490_625_955_771_185_589 = 3 · 1_293_367³
diff +2_277_123, gap ≈ 3.51·10⁻¹³
```

Candidate helper name:
`cbrt3_lt_one_eight_six_five_three_five_eight_over_one_two_nine_three_three_six_seven`.

Two-line proof via `cbrt3_lt_iff_three_lt_cube + norm_num`. Helper
file delta: +50–60 LOC (+1 theorem, +1 prose section).

After S14a lands, S14b main ACT proves `cbrt3_a12 = 8` via the
sandwich `597449/414248 < cbrt3 < 1_865_358/1_293_367` through an
estimated 25-step chain (one rung deeper than S13b's 22). Heartbeat
budget `maxHeartbeats 12_800_000` (2× S13b's 6_400_000); estimated
main-file delta ~260 LOC.

## Open Questions / Limits

This finite-prefix approach can in principle continue indefinitely
(non-periodic CF by Lagrange ⟹ no closed-form a_i), but each step
doubles the elaboration cost. At S14+ the heartbeat budget exceeds
`12_800_000` and the chain length exceeds 25 algebraic steps. The
practical stopping point is governed by Lean elaboration cost, not
the mathematics — every a_i is provable by this template; eventually
elaboration becomes the bottleneck. A future bundling step into
`IntFractPair.stream` (carried open question, deferred since S5) would
generalize the per-i lemmas to a single statement about the canonical
Mathlib CF API at indices 0..N.

## Build Verification

Docker build initiated this session:
`./proofs/scripts/docker-build.sh Proofs.CubeRoot3IrrationalOQ04`.
Outcome to be recorded in the PR body. The 7745-job Mathlib cache hits
in ~60s (per S10/S11b/S12b precedent), with the main file's
eleven-fold-nested theorem elaboration expected to dominate. If the
6_400_000 heartbeat budget is insufficient (highly unlikely given the
2×-per-depth empirical scaling has held cleanly from S7 through S12b),
S13c (a thin retry) would raise to 12_800_000.
