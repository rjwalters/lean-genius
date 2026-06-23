# S11a ACT — `7155/4961 < cbrt3` helper (narrow ACT, conflict-free vs open PREP #19420)

**Researcher**: researcher-6
**Date**: 2026-05-15
**PR**: (this PR)
**Phase**: ACT (helper-only; main theorem `cbrt3_a9` deferred to S11b)
**Lake SHA**: `2df2f0150c` (main HEAD `a3451198830`)
**Predecessor**: PR #19395 (S10 ACT, `cbrt3_a8 = 1` via 6206/4303, merged 2026-05-16T03:52Z); PR #19420 (S11 PREP MATH-CORRECTION, doc-only, OPEN at claim time)
**Build**: clean (7744/7744 jobs, helper file 52s, log
`researcher-6-cbrt3-oq04-s11a-build.log`)

## Summary

Adds the S11 lower-bound helper
`seven_one_five_five_over_four_nine_six_one_lt_cbrt3 : (7155/4961 : ℝ) < cbrt3`
to `proofs/Proofs/CubeRoot3IrrationalOQ04Helpers.lean`. The
helper is the tenth-convergent (even-index) lower bound consumed
by the future S11b ACT theorem `cbrt3_a9 = 6`. Conflict-free vs
open PR #19420 (doc-only PREP): orthogonal file (PR #19420 touches
state.md / JSON / sessions only, no Lean), zero overlap.

## Why narrow

- Open peer PREP #19420 is doc-only (paste-ready S11 ACT Lean) but
  state.md / JSON edits live on its branch. Shipping the main
  theorem `cbrt3_a9` here would require duplicating those edits
  (creating a merge conflict) or skipping them (creating drift).
- Helper-only ACT keeps Lean diff isolated to one file
  (`CubeRoot3IrrationalOQ04Helpers.lean`) and 0 doc edits. After
  PR #19420 merges, the next picker can ship S11b (the main
  `cbrt3_a9` theorem) with the helper already in place.
- The helper is a 2-line `rw + norm_num` proof — atomic and cheap
  to verify in one Docker iteration.

## Cube-direction pre-claim sanity (per `feedback_researcher_cf_convergent_recursion_direction_trap`)

Python verification (`p, q = 7155, 4961`):

```
p^3            = 366_293_248_875
q^3            = 122_097_755_681
3 * q^3        = 366_293_267_043
3 * q^3 - p^3  = 18_168   (> 0, so p^3 < 3 * q^3, so (p/q)^3 < 3, so p/q < cbrt3)
p / q          ≈ 1.4422495465
cbrt3          ≈ 1.4422495703
gap            ≈ 1.488 × 10^-7
```

Recursion check (using `a₁₀ = 1` per OEIS A002945):

```
p₁₀ = 1 · p₉ + p₈ = 1 · 6206 + 949 = 7155   ✓
q₁₀ = 1 · q₉ + q₈ = 1 · 4303 + 658 = 4961   ✓
```

Alternation: tenth convergent is even-index → lower side of cbrt3 ✓.
Contraction: gap `1.488 × 10⁻⁷` is barely tighter than S10's
upper-side gap `1.43 × 10⁻⁷`, consistent with alternating-convergent
theory. (PR #19420 caught and corrected three magnitude errors in
the post-S10 next-action sketch — cube digits had been off by ~67M
each; my paste used the corrected values.)

## Paste-ready Lean (now in `proofs/Proofs/CubeRoot3IrrationalOQ04Helpers.lean`)

```lean
/-- `7155/4961 < ∛3`. Cube target: `(7155/4961)³ =
366_293_248_875 / 122_097_755_681 < 366_293_267_043 / 122_097_755_681
= 3` (strict: `7155³ = 366_293_248_875 < 366_293_267_043 = 3 · 4961³`,
gap `18_168`). The tenth convergent of the simple CF of `∛3` (using
`a₁₀ = 1` per OEIS A002945). -/
theorem seven_one_five_five_over_four_nine_six_one_lt_cbrt3 :
    (7155 / 4961 : ℝ) < cbrt3 := by
  rw [lt_cbrt3_iff_cube_lt (by norm_num)]
  norm_num
```

Plus a `/-! ## S11 prep ... -/` prose block above it (recursion +
cube targets + math-correction note), matching the
existing-section style for `cbrt3_lt_six_two_oh_six_over_four_three_oh_three`
(S10 helper).

## Build evidence

`./proofs/scripts/docker-build.sh Proofs.CubeRoot3IrrationalOQ04Helpers`:

- 7744/7744 jobs (matches S10 baseline)
- `Proofs.CubeRoot3IrrationalOQ04Helpers (52s)` — single elaboration
  pass, no retries
- Pre-existing deprecation warning at
  `Proofs/CubeRoot3Irrational.lean:8` (`Mathlib.Data.Real.Irrational`)
  unchanged from prior S10 build — not owned by this slug
- No other warnings or errors

## Forward-pointer for S11b ACT

The main theorem `cbrt3_a9 : ⌊…⌋ = (6 : ℤ)` should now be
appendable to `proofs/Proofs/CubeRoot3IrrationalOQ04.lean` once
PR #19420 (PREP MATH-CORRECTION) merges. Skeleton + heartbeat
guess (`maxHeartbeats 1600000`) per PR #19420's
`2026-05-15-s11-prep-math-correction.md` §"Paste-ready Lean for
S11 ACT" — 17-step `lt_div_iff₀ / div_lt_iff₀ / le_div_iff₀` chain
on a nine-fold-nested fraction; the new lower bound
`seven_one_five_five_over_four_nine_six_one_lt_cbrt3` and the
existing upper bound `cbrt3_lt_six_two_oh_six_over_four_three_oh_three`
sandwich `cbrt3` across the tenth/ninth convergent pair to fix
`⌊1/x₉⌋ = 6`.

Expected delta to main file: ~230-260 LOC (one rung deeper than
S10's 234-LOC delta).

## Files touched (1 Lean, 1 docs)

- EDIT `proofs/Proofs/CubeRoot3IrrationalOQ04Helpers.lean`
  (+57 LOC: 1 new theorem `seven_one_five_five_over_four_nine_six_one_lt_cbrt3`
  with a `/-! ## S11 prep ... -/` prose block; matches the S9/S10 pattern)
- NEW `research/problems/cube-root-3-irrational-oq-04/sessions/2026-05-15-s11a-helper-act-7155-4961-lower-bound.md` (this file)

## Conflict-free guarantees (vs open PR #19420)

- 0 state.md edits (owned by PR #19420)
- 0 JSON edits (owned by PR #19420)
- 0 problem.md / knowledge.md edits
- 0 meta.json / gallery edits (helper is in proofs/Proofs/, not gallery surface)
- 0 parent-file edits (`Proofs/CubeRoot3IrrationalOQ04.lean` untouched)
- Lean file delta is strictly additive: new theorem appended above
  `end Cbrt3Helpers`; no rename / no deletion / no signature change to
  pre-existing helpers

## Iteration bookkeeping

- Phase: ACT (unchanged)
- Iteration: stays 10 in main (S11 numbering will be applied to JSON
  by the future STATE-SYNC that absorbs both this S11a and PR #19420)
- Sorries / axioms count: unchanged (no new sorries; no new axioms)
- Theorem count: +1 in `CubeRoot3IrrationalOQ04Helpers.lean`
  (`seven_one_five_five_over_four_nine_six_one_lt_cbrt3`)

## Notes / risks

- If PR #19420 merges before this PR: clean merge (orthogonal files).
- If this PR merges before #19420: still clean — PR #19420 is doc-only.
- If both merge: no STATE-SYNC needed for Lean state, but a future
  STATE-SYNC should absorb this S11a + PREP #19420 + retire the
  "paste-ready helper Lean" line in the PREP's nextAction text.
- The future S11b ACT picker should `git pull` first and confirm
  `seven_one_five_five_over_four_nine_six_one_lt_cbrt3` is present
  (`grep -n "seven_one_five_five_over_four_nine_six_one_lt_cbrt3" proofs/Proofs/CubeRoot3IrrationalOQ04Helpers.lean`)
  before pasting the main theorem.

**Cycle**: ~25 min (orient + sanity + paste + Docker build + memo).
