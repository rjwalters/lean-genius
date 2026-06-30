# S8 ACT — non-degeneracy meaning + uniqueness capstone (PART 4j)

**Agent:** researcher-2 · **Date:** 2026-06-27 · **Phase:** ACT · **Status:** VERIFIED

## Summary

Added **PART 4j** to `PascalsHexagonOQ03.lean`. Two complementary increments,
both 0-sorry / 0-new-axiom, `docker-build Proofs.PascalsHexagonOQ03` succeeded
(3070 jobs):

1. **`pascalProjLine_unique`** — uniqueness *capstone*. Combines PART 4h
   (incidence: the three Pascal points lie on `pascalProjLine`) with PART 4i
   (uniqueness: two points determine their line). Any projective line `l`
   carrying all three opposite-side intersections `P, Q, R` is
   `sameProjLine l (pascalProjLine hex)`. One-line corollary of
   `sameProjLine_pascalProjLine_of_pointOnLine hex hl.1 hl.2.1`.

2. **Geometric meaning of the non-degeneracy hypothesis `hnd`.** Every
   well-definedness theorem of PART 4g–5b carries
   `hnd : ∀ k, pascalProjLine (permuteHexagon hex k) ≠ 0`. Since
   `pascalProjLine hex = crossProduct (pascalP hex) (pascalQ hex)`, this is
   purely a statement about the two spanning Pascal points. PART 4j unpacks it:
   - `crossProduct_eq_zero_iff` — for `u, v : ℝ³`, `u ×₃ v = 0` iff all three
     `2×2` minors vanish (`u1 v2 = u2 v1 ∧ u2 v0 = u0 v2 ∧ u0 v1 = u1 v0`).
     This is exactly linear dependence / projective coincidence of `u, v`.
     Forward: `congrFun` on each component + `linarith`; backward: `funext` +
     `fin_cases` + `linarith`.
   - `pascalProjLine_eq_zero_iff` — specialisation to `P = AB ∩ DE`,
     `Q = BC ∩ EF`: `pascalProjLine hex = 0` iff those three minors vanish, i.e.
     `P` and `Q` are projectively the same point. So `hnd` says **exactly** "for
     every relabeling the two opposite-side intersection points spanning the
     line are projectively distinct" — no more, no less.
   - `pascalProjLine_ne_zero_of_minor` — checkable *sufficient* condition: one
     nonvanishing `2×2` minor of `P, Q` already gives `pascalProjLine hex ≠ 0`.
     This is the practical handle for discharging the per-relabeling side of
     `hnd` without abstract projective-distinctness reasoning.

## Significance (honest)

The OQ-03-OQ-02 well-definedness backbone was already complete in prior sessions
(PART 4c–5b: generator action, sameProjLine PER, quotient descent, incidence,
uniqueness). This session does **not** discharge `hnd` (that needs the conic /
general-position theory, a large effort) and does **not** touch the genuinely
open Steiner-20 / Kirkman-60 counts (out of scope, 2 remaining sorries). What it
adds is a precise *reading* of the non-degeneracy hypothesis the whole descent
rides on — turning the opaque `∀ k, pascalProjLine … ≠ 0` into the concrete,
checkable "the two spanning Pascal points are distinct" — plus the uniqueness
capstone that names `pascalProjLine` as *the* Pascal line. Routine coordinate
algebra; modest but genuine clarification of the file's standing assumption.

## Next steps

- Discharge `hnd` under `C.nondegenerate` + distinct vertices: needs that
  `AB ∩ DE` and `BC ∩ EF` are distinct projective points for six points in
  general position on a non-degenerate conic. `pascalProjLine_ne_zero_of_minor`
  is the target lemma to feed.
- Steiner-20 / Kirkman-60 remain genuinely OPEN (Conway–Ryba combinatorics).
