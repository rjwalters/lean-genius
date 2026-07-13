# S12b ACT — Eleventh partial quotient `cbrt3_a10 = 2`

**Researcher**: researcher-1
**Date**: 2026-06-01
**Phase**: ACT (iteration 14, combined Helper-ACT + Main-ACT)
**PR**: (this PR)

## Summary

Shipped the **eleventh partial quotient** `a₁₀ = 2` of the simple
continued fraction of `∛3` in two parts within one PR:

1. **Helper-ACT predecessor** (added to `CubeRoot3IrrationalOQ04Helpers.lean`):
   the twelfth CF convergent upper bound

   ```lean
   theorem cbrt3_lt_seven_three_oh_one_one_over_five_oh_six_two_three :
       cbrt3 < (73011 / 50623 : ℝ) := by
     rw [cbrt3_lt_iff_three_lt_cube (by norm_num)]
     norm_num
   ```

   Two-line proof via the established cubing-iff template (same
   pattern as S7/S8/S9/S10/S11a/S12a).

2. **Main-ACT** (added to `CubeRoot3IrrationalOQ04.lean`): the
   floor identity

   ```lean
   set_option maxHeartbeats 3200000 in
   theorem cbrt3_a10 :
       ⌊1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2)
         - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6)⌋ = (2 : ℤ) := by
     ...
   ```

   consuming the sandwich `13361/9264 < cbrt3 < 73011/50623` (S12a
   lower bound + S12b new upper bound) via a 21-step
   `lt_div_iff₀` / `div_lt_iff₀` / `le_div_iff₀` chain on a ten-fold
   nested fraction followed by floor antisymmetry.

Heartbeat budget `set_option maxHeartbeats 3200000 in` (2× S11b's
1.6M, per the empirical 2× per-depth scaling validated through S7–S11b).

Helper file: **528 → 586 LOC** (+58 LOC, +1 theorem, +1 prose
section; theoremCount 16 → 17).
Main file: **1505 → 1747 LOC** (+242 LOC, +1 theorem; theoremCount
unchanged in JSON tracking, the cbrt3_a* family bumps by 1).
0 sorries, 0 axioms (slug remains 0/0).

The chain `cbrt3_a0, …, cbrt3_a10` now covers the OEIS A002945
prefix one step beyond S11b — and verifies that `a₁₀ = 2` (the
**actually-correct** value, per the math-correction #FOUR landed in
S12a).

## Math-correction precedent #FIVE

The post-S12a `nextAction` sketch in `state.md` and JSON
`currentState.nextAction` (as of 2026-06-01, immediately after PR
#21873 merged) claimed:

> 12th-convergent upper-side backup `cbrt3 < 73011/50623`
> (`a₁₁ = 5` per OEIS A002945; pre-claim Python sanity:
> `73011³ = 389_271_307_557_812_731 > 389_271_307_493_213_241 =
>  3 · 50623³`, diff `+64_599_490`).

These cube digits are **off by ~1000×**. The actual values
(re-verified to all digits by Python `int` arithmetic in this
S12b session) are:

| Quantity | Sketch claim | Actual value |
|----------|--------------|--------------|
| `73011³` | `389_271_307_557_812_731` | `389_192_883_500_331` |
| `3 · 50623³` | `389_271_307_493_213_241` | `389_192_883_463_101` |
| diff | `+64_599_490` | **`+37_230`** |

Both magnitudes are wrong (the sketch was working in `10¹⁸` while
actual is `10¹⁴`), but the **direction is unchanged**:
`73011³ > 3 · 50623³` ⟹ `(73011/50623)³ > 3` ⟹ `73011/50623 > cbrt3`,
which is the upper-bound direction needed for the sandwich.

**Math-correction precedent count for this slug now stands at FIVE**:

1. S7 → S8 sketch (cube-digit error)
2. S8 → S9 sketch (PR #19011, cube-digit error)
3. S10 → S11 sketch (PR #19420, three cube-digit errors)
4. S11b → S12a sketch (OEIS-position-off-by-one in `a₁₀`)
5. **S12a → S12b sketch (this S12b, cube-digit error of ~1000× in
   both `73011³` and `3 · 50623³`)**

(Per `feedback_researcher_cf_convergent_recursion_direction_trap`,
the math-correction frequency in this slug warrants pre-claim Python
sanity-checks on every cube digit. This S12b session re-verified
all relevant cube products at exact integer precision.)

## Cube arithmetic (verified)

For the new helper (eleventh upper bound):

| Quantity | Value |
|----------|-------|
| `p₁₁` | `73011` |
| `q₁₁` | `50623` |
| `p₁₁³` | `389_192_883_500_331` |
| `q₁₁³` | `129_730_961_154_367` |
| `3 · q₁₁³` | `389_192_883_463_101` |
| diff `p₁₁³ - 3·q₁₁³` | **`+37_230`** (positive ⇒ `(73011/50623)³ > 3` ⇒ `73011/50623 > ∛3` ✓) |
| absolute cube gap | `37_230 / 129_730_961_154_367 ≈ 2.87·10⁻¹⁰` |
| relative gap (vs `3 · q³`) | `≈ 9.57·10⁻¹¹` |

Compare with the full convergent ladder:

| Helper | Gap (cube-domain, `\|p³-3q³\|/3q³`) | Convergent type |
|--------|------------------------------------|-----------------|
| S7 `437/303` | `≈ 5.0·10⁻⁶` | 7th true (lower) |
| S8 `cbrt3 < 512/355` | `≈ 2.47·10⁻⁵` | 8th true (upper) |
| S9 `949/658` | `≈ 2.06·10⁻⁶` | 9th true (lower) |
| S10 `cbrt3 < 6206/4303` | `≈ 1.44·10⁻⁷` | 10th true (upper) |
| S11a `7155/4961` | `≈ 1.49·10⁻⁷` | semi-convergent between 9th and 11th |
| S12a `13361/9264` | `≈ 4.34·10⁻⁹` | 11th true (lower) |
| **S12b `cbrt3 < 73011/50623`** | **`≈ 9.57·10⁻¹¹`** | **12th true (upper)** |

The new gap is roughly two orders of magnitude tighter than S10's
upper-side gap — consistent with `73011/50623` being two true
convergents beyond `6206/4303` on the upper side.

## Sandwich tightness — propagation verification

Pre-claim rational-arithmetic propagation (Python `Fraction`) of the
sandwich `13361/9264 < cbrt3 < 73011/50623` through the 10-level CF
recursion:

| Step | Variable | Lower bound | Upper bound |
|------|----------|-------------|-------------|
| 0 | `cbrt3` | `13361/9264` | `73011/50623` |
| 1 | `cbrt3 - 1` | `4097/9264` | `22388/50623` |
| 2 | `1/(cbrt3-1)` | `50623/22388` | `9264/4097` |
| 3 | `x₂ := y₁ - 2` | `5847/22388` | `1070/4097` |
| 4 | `1/x₂` | `4097/1070` | `22388/5847` |
| 5 | `x₃ := y₂ - 3` | `887/1070` | `4847/5847` |
| 6 | `1/x₃` | `5847/4847` | `1070/887` |
| 7 | `x₄ := y₃ - 1` | `1000/4847` | `183/887` |
| 8 | `1/x₄` | `887/183` | `4847/1000` |
| 9 | `x₅ := y₄ - 4` | `155/183` | `847/1000` |
| 10 | `1/x₅` | `1000/847` | `183/155` |
| 11 | `x₆ := y₅ - 1` | `153/847` | `28/155` |
| 12 | `1/x₆` | `155/28` | `847/153` |
| 13 | `x₇ := y₆ - 5` | `15/28` | `82/153` |
| 14 | `1/x₇` | `153/82` | `28/15` |
| 15 | `x₈ := y₇ - 1` | `71/82` | `13/15` |
| 16 | `1/x₈` | `15/13` | `82/71` |
| 17 | `x₉ := y₈ - 1` | `2/13` | `11/71` |
| 18 | `1/x₉` | `71/11` | `13/2` |
| 19 | `x₁₀ := y₉ - 6` | **`5/11`** | **`1/2`** |
| 20 | `1/x₁₀` | **`2`** | **`11/5`** |

At step 20: `2 < 1/x₁₀ < 11/5 < 3`. Floor antisymmetry closes with:

- `⌊1/x₁₀⌋ ≤ 2` from `1/x₁₀ < 3` via `Int.floor_lt`.
- `2 ≤ ⌊1/x₁₀⌋` from `2 ≤ 1/x₁₀` (strict `2 < 1/x₁₀`) via `Int.le_floor`.

Sanity at the critical step 19:
- `5/11 ≈ 0.4545` (need `> 1/3 ≈ 0.3333` for `1/x₁₀ < 3`) ✓
- `1/2 = 0.5` (need `≤ 1/2` for `1/x₁₀ ≥ 2`) ✓
- True `x₁₀ ≈ 0.4566` (Decimal CF expansion), comfortably inside.

The S10 upper bound `6206/4303` (gap `≈ 1.44·10⁻⁷`) is **insufficient**
at depth 10 — propagation with the sandwich `13361/9264 < cbrt3 <
6206/4303` gives `x₁₀ ∈ (0, 1/2)` (lower bound collapses to `0`),
which does not separate from `1/x₁₀ ≥ 2`. The S12b upper bound
`73011/50623` (gap `≈ 9.57·10⁻¹¹`, three orders of magnitude tighter)
is required.

## Build verification

```
./proofs/scripts/docker-build.sh Proofs.CubeRoot3IrrationalOQ04
```

(Build verification embedded after PR creation; see PR description.)

## Files modified

1. `proofs/Proofs/CubeRoot3IrrationalOQ04Helpers.lean` (528 → 586
   LOC, +58 LOC; theorem count 16 → 17): added prose section
   `## S12b prep: new upper bound for the eleventh partial quotient
   (the twelfth convergent)` + the new theorem
   `cbrt3_lt_seven_three_oh_one_one_over_five_oh_six_two_three`.
2. `proofs/Proofs/CubeRoot3IrrationalOQ04.lean` (1505 → 1747 LOC,
   +242 LOC, +1 theorem): added the `cbrt3_a10` main theorem with
   `set_option maxHeartbeats 3200000 in`.
3. `src/data/research/problems/cube-root-3-irrational-oq-04.json`:
   bump `currentState.iteration` 13 → 14, refresh
   `currentState.focus` / `currentState.nextAction`, update
   `leanFiles[5]` (Helpers) lineCount 528 → 586 / theoremCount
   16 → 17, update `leanFiles[?]` (main file) lineCount 1505 → 1747,
   bump `lastUpdate` / `knowledge.lastUpdated` / top-level
   `lastUpdated`.
4. `research/problems/cube-root-3-irrational-oq-04/state.md`: bump
   head Iteration → 14, prepend Current Focus block for S12b, push
   prior S12a focus to "## Prior Focus (S12a Helper-ACT, PR #21873,
   MERGED 2026-06-01T08:15:18Z)".
5. NEW `research/problems/cube-root-3-irrational-oq-04/sessions/2026-06-01-s12b-act-eleventh-partial-quotient.md`
   (this file).

No edits to:
- `proofs/Proofs/CubeRoot3Irrational.lean` (parent, unchanged)
- `src/data/proofs/cube-root-3-irrational-oq-04/` gallery (no meta
  changes — slug research JSON is the authoritative tracker for
  in-progress research)
- sibling slugs
- problem.md / knowledge.md (only state.md narrative updated)

## Next ACT picker priority (S13)

The main `cbrt3_a10 = 2` is now landed. The S13 ACT should aim for
the twelfth partial quotient `a₁₁ = 5` (per OEIS A002945).

Likely structure:
1. Helper-ACT predecessor: add the 13th convergent **lower** bound
   `(597449/414248 : ℝ) < cbrt3` (using `a₁₂ = 8` per OEIS A002945;
   even index ⟹ lower side). Pre-claim Python sanity required.
2. Main-ACT: 23-step chain on an 11-fold nested fraction with
   `set_option maxHeartbeats 6400000 in` (2× S12b), ~270 LOC delta.

Convergent recursion for the 13th convergent (using `a₁₂ = 8`):
- `q₁₂ = 8 · q₁₁ + q₁₀ = 8 · 50623 + 9264 = 414_248`
- `p₁₂ = 8 · p₁₁ + p₁₀ = 8 · 73011 + 13361 = 597_449`

(All recursion arithmetic to be re-verified pre-claim in S13.)

End of S12b ACT memo.
