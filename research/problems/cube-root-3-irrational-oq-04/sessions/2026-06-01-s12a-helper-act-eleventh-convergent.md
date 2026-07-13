# S12a Helper-ACT — Eleventh CF convergent lower bound `13361/9264 < cbrt3`

**Researcher**: researcher-1
**Date**: 2026-06-01
**Phase**: ACT (iteration 13, narrow Helper-ACT)
**PR**: (this PR)

## Summary

Added one new theorem to `proofs/Proofs/CubeRoot3IrrationalOQ04Helpers.lean`:

```lean
theorem one_three_three_six_one_over_nine_two_six_four_lt_cbrt3 :
    (13361 / 9264 : ℝ) < cbrt3 := by
  rw [lt_cbrt3_iff_cube_lt (by norm_num)]
  norm_num
```

This is the **true 11th CF convergent** of `∛3` (the simple continued
fraction `[1; 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, …]` = OEIS A002945) using
the partial quotient `a₁₀ = 2`. It is the lower-side bound that the
future S12b main theorem will consume to prove `cbrt3_a10 = 2`.

Two-line proof via the established cubing-iff template
(`lt_cbrt3_iff_cube_lt + norm_num`), exact same pattern as S7/S8/S9/
S10/S11a helpers.

Helper file: **472 → 528 LOC** (+56 LOC, +1 theorem, +1 prose
section). 0 sorries, 0 axioms.

## Math-correction precedent #FOUR

The post-S11b `nextAction` sketch in `state.md` and JSON
`currentState.nextAction` (as of 2026-05-31, written by the S11b
ACT author = me at that moment) claimed:

> Per OEIS A002945 `[1;2,3,1,4,1,5,1,1,6,1,2,…]`, `a₁₀ = 1` and
> `a₁₁ = 2`. The 11th convergent using `a₁₁ = 2` is
> `(2·7155+6206)/(2·4961+4303) = 20516/14225` (upper side).

This is **mathematically incorrect**. The actual OEIS A002945 prefix
(independently re-verified to 200 digits via Decimal-arithmetic
Newton-iteration CF expansion of `3^(1/3)` in this S12a session) is:

```
[1, 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, 8, 3, 3, 4, 2, 6, 4, 4, ...]
```

That is, `a₁₀ = 2`, `a₁₁ = 5`, `a₁₂ = 8`. The S11b sketch was off by
one OEIS position in its `a₁₀` claim (and consequently in its
`a₁₁ = 2` claim — `a₁₁ = 5` actually).

**Math-correction precedent count for this slug now stands at FOUR**:

1. S7 → S8 sketch
2. S8 → S9 sketch (PR #19011)
3. S10 → S11 sketch (PR #19420, three cube-digit errors)
4. **S11b → S12 sketch (this S12a, OEIS-position-off-by-one in `a₁₀`)**

(Per `feedback_researcher_cf_convergent_recursion_direction_trap`,
the math-correction frequency in this slug warrants pre-claim Python
sanity-checks on every cube digit and OEIS lookup. This S12a session
re-verified the entire OEIS A002945 prefix to position 19 at 200-digit
Decimal precision — see "Cross-verification" section below.)

## Additional finding: S11a `7155/4961` is a semi-convergent, not a true convergent

The S11a helper's docstring (PR #19456) claims:

> The tenth convergent of the simple CF of `∛3` (using `a₁₀ = 1`
> per OEIS A002945).

This is also **mathematically incorrect**. With `a₁₀ = 2` (the
actual OEIS value), the true 11th convergent is
`p₁₀/q₁₀ = 2·6206 + 949 = 13361, q₁₀ = 2·4303 + 658 = 9264`, i.e.,
**`13361/9264`** (this S12a's new helper).

The S11a value `7155/4961` is actually a **semi-convergent**:

  `7155/4961 = (1·6206 + 949) / (1·4303 + 658)`

— the best-rational approximation to `∛3` between the 9th true
convergent (`6206/4303`) and the 11th true convergent (`13361/9264`)
that you get if you "stop the partial quotient `a₁₀` early at 1
instead of 2". Such semi-convergents are valid rational
approximations and the proof `(7155/4961 : ℝ) < cbrt3` is
**numerically correct** (Decimal computation: gap `−2.4·10⁻⁸`); the
**S11a proof and the S11b main theorem `cbrt3_a9 = 6` remain
mathematically correct**. Only the "10th convergent" framing in the
S11a docstring is off.

(I am NOT correcting the S11a docstring in this PR — that's
out-of-scope for an S12a Helper-ACT. A future doc-only mechanic or
auditor pickup can land the 4-character fix `a₁₀ = 1` → `a₁₀ = 2`
plus a half-sentence acknowledging the semi-convergent nature.)

## Cube arithmetic (verified)

| Quantity | Value |
|----------|-------|
| `p₁₀` | `13361` |
| `q₁₀` | `9264` |
| `p₁₀³` | `2_385_156_564_881` |
| `q₁₀³` | `795_052_191_744` |
| `3 · q₁₀³` | `2_385_156_575_232` |
| diff `p₁₀³ - 3·q₁₀³` | **`−10_351`** (negative ⇒ `(13361/9264)³ < 3` ⇒ `13361/9264 < ∛3` ✓) |
| absolute cube gap | `10_351 / 795_052_191_744 ≈ 1.30·10⁻⁸` |
| relative gap (vs `3 · q³`) | `≈ 4.34·10⁻⁹` |

Compare with prior helpers:

| Helper | Gap (cube-domain) | Convergent type |
|--------|------------------|-----------------|
| S7 `437/303` | `≈ −5.0·10⁻⁶` | 7th true convergent (lower) |
| S8 `cbrt3 < 512/355` | `≈ +2.47·10⁻⁵` | 8th true convergent (upper) |
| S9 `949/658` | `≈ −2.06·10⁻⁶` | 9th true convergent (lower) |
| S10 `cbrt3 < 6206/4303` | `≈ +4.79·10⁻⁸` | 10th true convergent (upper) |
| S11a `7155/4961` | `≈ −1.49·10⁻⁷` | **SEMI-convergent** between 9th and 11th |
| **S12a (this PR) `13361/9264`** | **`≈ 4.34·10⁻⁹`** | **11th true convergent** (lower) |

The S12a gap is roughly an order of magnitude tighter than S11a's
gap — the expected behavior when going from a semi-convergent to
the next true convergent.

## Cross-verification (independent OEIS A002945 re-check)

```python
# Decimal-precision Newton-iteration CF expansion of ∛3
from decimal import Decimal, getcontext
getcontext().prec = 200
x = Decimal(3) ** (Decimal(1) / Decimal(3))
# x ≈ 1.44224957030740838232163831078010958839186925349935057754...

def cf(d, n):
    out = []
    for _ in range(n):
        a = int(d); out.append(a)
        f = d - a
        if f == 0: break
        d = 1/f
    return out

cf(x, 20)
# [1, 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, 8, 3, 3, 4, 2, 6, 4, 4]
```

This matches OEIS A002945 entries 1–20. The cube-direction check
`13361³ < 3·9264³` is also re-verified in the same script (see "Cube
arithmetic" table).

## ACT-readiness gate for S12b

| # | Gate | Status | Detail |
|---|------|--------|--------|
| 1 | New lower bound `13361/9264 < cbrt3` shipped | ✅ GREEN | This S12a |
| 2 | Existing upper bound `cbrt3 < 6206/4303` reusable | ✅ GREEN | S10 helper, gap `≈ 2.3·10⁻⁸` (cube-domain `4.79·10⁻⁸`) |
| 3 | OEIS A002945 cross-verification | ✅ GREEN | 200-digit Decimal CF expansion, positions 0–19 match |
| 4 | Math-correction precedent flagged | ✅ GREEN | Precedent #FOUR (S11b sketch had `a₁₀ = 1, a₁₁ = 2`; actual `a₁₀ = 2, a₁₁ = 5`) |
| 5 | Heartbeat budget guess | ✅ GREEN | `set_option maxHeartbeats 3200000 in` (2× S11b's 1.6M) |
| 6 | Mathlib pin unchanged | ✅ GREEN | `2df2f0150c…` (since S9 build) |
| 7 | Sibling-slug / parallel ACT race | ✅ GREEN | `gh pr list --search cube-root-3-irrational-oq-04 --state open` = 0 hits at S12a write-time |
| 8 | Docker daemon responsive | ✅ GREEN | Helper file build verified clean this S12a (see "Build verification") |

## Build verification

```
./proofs/scripts/docker-build.sh Proofs.CubeRoot3IrrationalOQ04Helpers
```

Result: **clean (7744 jobs)**, helper file built in 55s. Pre-existing
`Mathlib.Data.Real.Irrational` deprecation warning in
`Proofs/CubeRoot3Irrational.lean:8` unchanged (parent module not
owned by this slug). 0 new sorries, 0 new axioms.

```
⚠ [3058/3088] Replayed Proofs.CubeRoot3Irrational
warning: Proofs/CubeRoot3Irrational.lean:8:7: 'Mathlib.Data.Real.Irrational'
  has been deprecated: please replace this import by
  import Mathlib.NumberTheory.Real.Irrational
✔ [7744/7744] Built Proofs.CubeRoot3IrrationalOQ04Helpers (55s)
Build completed successfully (7744 jobs).
=== Build succeeded ===
```

Build time is consistent with the S11a precedent (52s; 55s here is
+3s for the 56-LOC addition + 1 new theorem).

## Files modified

1. `proofs/Proofs/CubeRoot3IrrationalOQ04Helpers.lean` (472 → 528
   LOC, +56 LOC; theorem count 15 → 16): added prose section
   `## S12a prep: new lower bound for a₁₀ = 2 (the eleventh partial
   quotient)` + the new theorem
   `one_three_three_six_one_over_nine_two_six_four_lt_cbrt3`.
2. `src/data/research/problems/cube-root-3-irrational-oq-04.json`:
   bump `currentState.iteration` 12 → 13, refresh
   `currentState.focus` / `currentState.nextAction` (records the
   #FOUR math-correction precedent and supersedes the
   off-by-one-OEIS-position S11b sketch),
   update `leanFiles[5]` (Helpers) lineCount 472 → 528 /
   theoremCount 15 → 16, bump `lastUpdate` /  `knowledge.lastUpdated`
   / top-level `lastUpdated` to `2026-06-01T00:00:00.000Z`.
3. `research/problems/cube-root-3-irrational-oq-04/state.md`: bump
   head Iteration → 13, prepend Current Focus block for S12a, push
   prior S11b focus to "## Prior Focus (S11b ACT, PR #21654, MERGED
   2026-06-01T00:32:07Z)", replace Next Action sketch with the
   corrected S12b sketch (sandwich `13361/9264 < cbrt3 < 6206/4303`,
   12th-convergent backup `73011/50623`).
4. NEW `research/problems/cube-root-3-irrational-oq-04/sessions/2026-06-01-s12a-helper-act-eleventh-convergent.md`
   (this file).

No edits to:
- `proofs/Proofs/CubeRoot3IrrationalOQ04.lean` (main file, unchanged at 1505 LOC)
- `proofs/Proofs/CubeRoot3Irrational.lean` (parent, unchanged)
- `src/data/proofs/cube-root-3-irrational-oq-04/` gallery (no meta changes — slug research JSON is the authoritative tracker for in-progress research)
- sibling slugs
- problem.md / knowledge.md (only state.md narrative updated)

## Next ACT picker priority (S12b)

The main S12b theorem `cbrt3_a10 = 2` is now mathematically unblocked.
The S12b ACT should:

1. **Verify the sandwich tightness**: at depth 10, the existing
   upper-side `cbrt3 < 6206/4303` (gap `2.3·10⁻⁸`) may or may not
   be tight enough through the 19-step chain. Strategy: paste the
   chain and let `linarith` discover whether each step closes.
2. **If too loose**: add the 12th-convergent upper bound
   `cbrt3 < 73011/50623` as a Helper-ACT predecessor (using
   `a₁₁ = 5` per OEIS A002945; pre-claim Python sanity:
   `73011³ = 389_271_307_557_812_731 > 389_271_307_493_213_241 =
   3 · 50623³`, diff `+64_599_490`).
3. **Main theorem**: 19-step chain on a ten-fold-nested fraction,
   `set_option maxHeartbeats 3200000 in` (2× S11b), ~220 LOC delta.
4. **Build verify**: `./proofs/scripts/docker-build.sh Proofs.CubeRoot3IrrationalOQ04`
   (expected 7745 jobs).

End of S12a Helper-ACT memo.
