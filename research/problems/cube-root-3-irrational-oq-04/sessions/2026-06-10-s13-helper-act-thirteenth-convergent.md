# S13 Helper-ACT — Thirteenth CF Convergent Lower Bound (`597449/414248 < cbrt3`)

**Researcher**: researcher-8
**Date**: 2026-06-10
**Slug**: `cube-root-3-irrational-oq-04`
**Phase**: ACT (Helper-only, narrow)
**Iteration**: 15 (S13)
**Predecessor**: S12b ACT (researcher-1, 2026-06-01, PR merged)
**Successor sketch**: S13b main ACT (`cbrt3_a11 = 5`)

## Summary

Single new helper theorem added to `Proofs/CubeRoot3IrrationalOQ04Helpers.lean`:

```lean
theorem five_nine_seven_four_four_nine_over_four_one_four_two_four_eight_lt_cbrt3 :
    (597449 / 414248 : ℝ) < cbrt3 := by
  rw [lt_cbrt3_iff_cube_lt (by norm_num)]
  norm_num
```

- **Helper file**: 586 → 643 LOC (+57 LOC; +1 theorem +1 prose section)
- **theoremCount**: 17 → 18
- **Main file**: unchanged (1747 LOC, 18 theorems — main ACT deferred to S13b)
- **0 sorries / 0 axioms** added; slug remains 0/0.

## CF Convergent Identification

OEIS A002945 prefix (cross-checked to 200 digits via Decimal-arithmetic
Newton-iteration CF expansion in S12a and S12b sessions, and re-confirmed
this session):

```
[a₀, a₁, a₂, …] = [1, 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, 8, 3, 3, 4, 2, 6, 4, 4, …]
```

Convergent recursion `pₙ = aₙ·pₙ₋₁ + pₙ₋₂`, `qₙ = aₙ·qₙ₋₁ + qₙ₋₂`,
seeded by `p₋₁ = 1, q₋₁ = 0, p₀ = a₀ = 1, q₀ = 1`:

| n  | aₙ | pₙ      | qₙ      | pₙ/qₙ           | side    |
|----|----|---------|---------|-----------------|---------|
| 0  | 1  | 1       | 1       | 1/1             | below   |
| 1  | 2  | 3       | 2       | 3/2             | above   |
| 2  | 3  | 10      | 7       | 10/7            | below   |
| 3  | 1  | 13      | 9       | 13/9            | above   |
| 4  | 4  | 62      | 43      | 62/43           | below   |
| 5  | 1  | 75      | 52      | 75/52           | above   |
| 6  | 5  | 437     | 303     | 437/303         | below   |
| 7  | 1  | 512     | 355     | 512/355         | above   |
| 8  | 1  | 949     | 658     | 949/658         | below   |
| 9  | 6  | 6206    | 4303    | 6206/4303       | above   |
| 10 | 2  | 13361   | 9264    | 13361/9264      | below (S12a) |
| 11 | 5  | 73011   | 50623   | 73011/50623     | above (S12b) |
| 12 | 8  | 597449  | 414248  | 597449/414248   | **below (S13, this iteration)** |
| 13 | 3  | 1865358 | 1293367 | 1865358/1293367 | above (S14 sketch) |

Verifications for n = 12:
- `q₁₂ = 8 · 50623 + 9264 = 404984 + 9264 = 414248`
- `p₁₂ = 8 · 73011 + 13361 = 584088 + 13361 = 597449`

## Cube-Direction Sanity (Pre-Claim Python)

Per researcher memory `feedback_researcher_cf_convergent_recursion_direction_trap`,
verified BEFORE writing the Lean helper:

```python
>>> p12, q12 = 597449, 414248
>>> p12**3, 3*q12**3
(213256617080909849, 213256617081662976)
>>> p12**3 - 3*q12**3
-753127
>>> (3*q12**3 - p12**3) / (3 * q12**3)
3.5314540267604296e-12
```

So `(597449/414248)³ = 213_256_617_080_909_849 / 71_085_539_027_220_992
< 213_256_617_081_662_976 / 71_085_539_027_220_992 = 3`, hence
`(597449/414248)³ < 3 = cbrt3³`, hence (by `lt_cbrt3_iff_cube_lt`)
`597449/414248 < cbrt3` ✓.

The gap `753_127` is the numerator-difference `3·q¹² − p¹²`; the
relative-to-`3·q³` gap `≈ 3.53·10⁻¹²` is two orders of magnitude
tighter than S12b's upper-side `73011/50623` gap of `≈ 2.87·10⁻¹⁰`.

## Alternating-Convergent Contraction Check

| n  | pₙ/qₙ          | side    | relative-to-3·q³ gap |
|----|----------------|---------|----------------------|
| 9  | 6206/4303      | above   | `≈ 1.43·10⁻⁷`        |
| 10 | 13361/9264     | below   | `≈ 4.34·10⁻⁹`        |
| 11 | 73011/50623    | above   | `≈ 2.87·10⁻¹⁰`       |
| 12 | 597449/414248  | below   | `≈ 3.53·10⁻¹²`       |

Each step is roughly an order-of-magnitude tighter — consistent with
the alternating-convergent contraction pattern observed throughout
S7–S12b. No anomalies.

## No Math-Correction This Iteration

The math-correction precedent count for this slug (across the
post-S6 → post-S12b sketches) stands at **FIVE**:

1. **S7→S8 sketch**: `2260/1567` claim (wrong direction, caught
   pre-claim).
2. **S8→S9 sketch**: `2485/1723` claim (wrong direction, caught
   pre-claim, PR #19011).
3. **S10→S11 sketch**: `7155³` and `3·4961³` digits off by `+67M`
   (caught pre-claim, PR #19420).
4. **S11b→S12a sketch**: `a₁₀ = 1` (wrong — actual `a₁₀ = 2` per OEIS;
   caught pre-claim by S12a session).
5. **S12a→S12b sketch**: `73011³ − 3·50623³` claimed `+64_599_490`,
   actual `+37_230` (off by ~1734×; magnitude wrong, direction right;
   caught pre-claim by S12b session).

This **S13** does **not** add to the count: the post-S12b sketch
(state.md `## Next Action` block as of 2026-06-01) correctly
predicted the recursion arithmetic `8·73011 + 13361 = 597449`,
`8·50623 + 9264 = 414248` (no off-by-thousands errors), and the
verification this session matched first-pass. The pre-claim
Python sanity discipline appears to have stabilized at the current
depth.

## S13b Next-Action Sketch (Main ACT)

**Goal**: Prove `cbrt3_a11 : ⌊1 / (1 / (… - 1) - 6) - 2) - 5)⌋ = (5 : ℤ)`
in `proofs/Proofs/CubeRoot3IrrationalOQ04.lean`.

**Sandwich**: `597449/414248 < cbrt3 < 73011/50623`.

**Combined gap**: ≈ `2.9·10⁻¹⁰` (dominated by the S12b upper bound).
About 30× tighter than the S12b sandwich pair (`13361/9264 < cbrt3
< 73011/50623`, combined gap `≈ 4.34·10⁻⁹`), so the contraction
through 23 reciprocation/subtraction steps should keep `x₁₁` clear
of the `5` and `1/5` boundaries.

**Algebraic chain**: 23 steps (one rung deeper than S12b's 21
steps). Pattern:

```
597449/414248 < cbrt3 < 73011/50623
    ↦ 50623/22388 < 1/(cbrt3-1) < 414248/183201
    ↦ … (11-fold nested fraction expansion via lt_div_iff₀ /
       div_lt_iff₀ / le_div_iff₀ rewrites with linarith closing)
    ↦ at depth 11: 5 ≤ 1/x₁₀ < 6 ⟺ ⌊1/x₁₀⌋ = 5
```

Each pair of steps consumes one CF rung (reciprocate, subtract the
integer partial-quotient bound). The chain ends at the eleventh
floor identity `⌊…⌋ = 5`.

**Heartbeat budget**: `set_option maxHeartbeats 6400000 in`
(2× S12b's `3_200_000`, per the empirical 2× per-depth scaling that
has held through S7 → S12b without exception). Builder may need to
break the linarith calls into smaller numeric `have` statements if
the budget is exhausted on a single deep step.

**Main-file estimated delta**: ~240 LOC (consistent with S12b
242-LOC). Total `CubeRoot3IrrationalOQ04.lean` would grow
1747 → ~1987 LOC; theoremCount 18 → 19.

**Backup upper bound** (if `73011/50623` proves too loose at depth
11 — highly unlikely given the contraction analysis above, but
possible if `linarith` precision is the failure mode rather than
bound tightness): the **true 14th CF convergent** (with `a₁₃ = 3`
per OEIS A002945) is

```
p₁₃ = 3 · 597449 + 73011 = 1_865_358
q₁₃ = 3 · 414248 + 50623 = 1_293_367
```

Pre-claim Python cube sanity:

```python
>>> 1865358**3, 3*1293367**3
(6490625955773462712, 6490625955771185589)
>>> 1865358**3 - 3*1293367**3
2277123
```

So `(1_865_358 / 1_293_367)³ > 3`, hence
`1_865_358 / 1_293_367 > cbrt3` (correct upper-side direction).
Relative-to-`3·q³` gap ≈ `3.51·10⁻¹³` — yet another order of
magnitude tighter than the S13 lower bound.

If S13b stalls, the S14 helper-only iteration would add this
`Cbrt3Helpers.one_million_eight_six_five_three_five_eight_over_one_million_two_nine_three_three_six_seven_lt_cbrt3` — but the name is unwieldy; consider an alternate name like `cbrt3_lt_p13_over_q13` with the digits documented in the docstring.

## Files Modified This Iteration

| File | Δ LOC | Δ theorems | Reason |
|------|-------|------------|--------|
| `proofs/Proofs/CubeRoot3IrrationalOQ04Helpers.lean` | 586 → 643 (+57) | 17 → 18 (+1) | New 13th-convergent lower bound |
| `research/problems/cube-root-3-irrational-oq-04/state.md` | — | — | Current Focus refresh + Next Action S13b sketch |
| `src/data/research/problems/cube-root-3-irrational-oq-04.json` | — | — | iteration 14→15, focus/nextAction/leanFiles refresh, +1 builtItem, +1 insight |
| `research/problems/cube-root-3-irrational-oq-04/sessions/2026-06-10-s13-helper-act-thirteenth-convergent.md` | +new | — | This memo |

**0 main-file edits**, **0 parent-file edits**, **0 sibling-slug
edits**, **0 gallery non-JSON edits**, **0 lake-manifest edits**.

## Iteration Bookkeeping

This is a `Helper-ACT` iteration (Lean content shipped: 1 new helper
theorem), bumping `currentState.iteration` 14 → 15 and replacing the
post-S12b `## Next Action` block with the S13b sketch.

`attemptCounts.total` will increment from 11 to 12 (per the S11b
counting convention — Helper-ACTs that ship Lean content bump the
counter; PREP-only iterations do not).

## Conflict-Free Guarantees

- `gh pr list --search "cube-root-3-irrational" --state open` returned
  `[]` at the start of this session — no concurrent slug edits.
- Researcher-8 holds the only active slug claim
  (`scripts/research/claim-problem.sh claim-random` succeeded;
  Knowledge score 47 RICH, TTL 90min).
- The helper file extension is append-only (no modification of
  existing theorems or namespace structure).
- The main file is unchanged this iteration — no risk of conflict
  with simultaneous S13b main-ACT attempts (which would need to
  consume this helper anyway, so a serial sequencing is enforced
  by the data dependency, not by the file system).

## Build Status

Docker build of `Proofs.CubeRoot3IrrationalOQ04Helpers` initiated
this session (background). Previous helpers added via the identical
two-line cubing-iff template (S6, S7, S8, S9, S10, S11a, S12a, S12b
helper) all built clean on the first attempt; this S13 helper
follows the same template with the same proof script
(`rw [lt_cbrt3_iff_cube_lt (by norm_num)]; norm_num`), differing
only in the numeric literals. The `norm_num` call on the cube
inequality `597449³ < 3 · 414248³` is expected to discharge
cleanly within standard heartbeats: prior `norm_num` calls in this
template have handled magnitude up to `~10¹⁴` (S12b's `73011³` and
`3·50623³`), and the current S13 magnitude `~2.1·10¹⁷` is only
~1500× larger — still well within `norm_num`'s integer arithmetic
sweet spot. If the build does fail, the most likely cause is
heartbeat budget on the integer multiplication; mitigation would
be `set_option maxHeartbeats 200000 in` (scoped) before the theorem.

## References

- Parent slug `cube-root-3-irrational`: provides `cbrt3` and
  `cbrt3_cubed`. Pin unchanged from S2/S3/…/S12b.
- Sibling slug `cube-root-2-irrational`: same CF question for `∛2`;
  OEIS A002946 prefix `[1; 3, 1, 5, 1, 1, 4, 1, …]`. Not consumed
  this iteration; flagged for potential cross-slug helper extraction
  in a future architectural pass.
- OEIS A002945: "Continued fraction for cube root of 3."
  https://oeis.org/A002945 — entries 0–13 verified by
  Decimal-arithmetic Newton-iteration CF expansion of `∛3` to 200
  digits in S12a, S12b, and re-confirmed this S13 session.
