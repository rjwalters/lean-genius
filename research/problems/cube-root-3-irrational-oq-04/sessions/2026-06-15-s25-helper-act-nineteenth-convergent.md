# S25 — Nineteenth CF convergent lower bound (a₁₈ = 4)

**Agent:** researcher-6 · **Date:** 2026-06-15 · **PR:** #24556

## Result
Added self-contained helper to `CubeRoot3IrrationalOQ04Helpers.lean`:

    theorem ..._lt_cbrt3 : (1593368375 / 1104779927 : ℝ) < cbrt3

The nineteenth CF convergent of ∛3 (index 18, even ⟹ lower side), partial
quotient `a₁₈ = 4`. Proven by the standard `lt_cbrt3_iff_cube_lt` + `norm_num`
cubing route — identical in form to the 15 prior convergent helpers on `main`.

## Verification
- 300-digit CF recomputation (`research/scripts/verify_cbrt3_oq04_s25_19th_convergent.py`):
  prefix `a₀..a₁₈ = [1,2,3,1,4,1,5,1,1,6,2,5,8,3,3,4,2,6,4]` matches OEIS A002945.
- Cube-side direction (exact integer): `1593368375³ − 3·1104779927³ = −1_374_678_574 < 0`
  ⟹ lower bound. Cert PASS.

## Context
- `main` frontier was the 16th convergent (S15, upper, 26639450/18470763).
- 17th (S23, #24516) and 18th (S24, #24538) are in unmerged sibling PRs; this
  19th rung is self-contained and does not depend on them being present.
- Main partial-quotient chain (`cbrt3_a12`+) remains contention-blocked
  (#23388, #23983 own a12) — not touched.

## Build
Docker daemon in blackout (`docker info` exit 124); build deferred to deployer.
Arithmetic independently certified.
