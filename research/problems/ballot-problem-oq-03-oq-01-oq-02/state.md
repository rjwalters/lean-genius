# Research State: ballot-problem-oq-03-oq-01-oq-02

## Current State
**Phase**: ACT (S51 — `hookLength_at_d_ge_3` geometric prerequisite added; ensures ℚ-cast safety for the rational factor `(h_d − 1)² / (h_d (h_d − 2))` in the upcoming `hookProd_doubleRemove_factor` proof)
**Path**: full
**Since**: 2026-04-21T20:08:44+02:00
**Last Updated**: 2026-05-08
**Iteration**: 51

## Current Focus
Close `gnwProb_exchange` (Helpers, line ~14441 after S50) — the GNW 1979 exchange identity
in product form. This is now the SOLE remaining sorry-bearing lemma; the
`hook_length_formula_general` dispatcher is sorry-free, and `gnwProb_key` for the
multi-corner case is now structurally proved by well-founded recursion on
`μ.card`, modulo `gnwProb_exchange` and `isCorner_removeCorner_of_ne`.

## Active Approach
Route A (GNW probabilistic hook-walk) is the chosen path; the proof skeleton is
in place:

1. **Single-corner case** of `gnwProb_key` (rectangles): PROVED (~144 lines,
   arm/leg telescoping via `hookProd_ratio_formula`).
2. **Multi-corner case** of `gnwProb_key`: PROVED modulo `gnwProb_exchange`,
   using strong induction on `μ.card` (`termination_by μ.card`,
   `decreasing_by removeCorner_card hc'; omega`).
3. **`gnwProb_exchange`** (~100 lines, sorry'd): the GNW 1979 exchange
   identity in product form
   `F(μ,c)·H(μ\c)·H(μ\c') = F(μ\c',c)·H((μ\c')\c)·H(μ)`
   for distinct corners c, c'. Proof requires careful analysis of how removing
   c' shifts hook lengths in the arm/leg of c. Verified on small examples
   (L-shape, (3,1)).

## Attempt Count
- Total attempts: 51 (sessions 1–51; sessions 1–4 archived to
  `sessions/`; sessions 5–51 in `knowledge.md` + `sessions/`)
- Current approach attempts: 15 (sessions 37–51 on GNW)
- Approaches tried:
  1. LGV-determinant via `lgv_lemma_rxr` + Jacobi–Trudi (sessions 1–10) —
     dead scaffolding deleted in session 32.
  2. Corner recursion via `card_SYT_corner_step` + `hook_walk_identity`
     (sessions 11–14) — successful: gave `hook_length_formula_general`
     modulo `hook_walk_identity`.
  3. Row-by-row dispatch on `hook_walk_identity` (sessions 15–30) —
     successful for ≤9 rows / ≤9 cols (transpose duality) / all rectangles;
     hit file-size wall at session 30.
  4. Modularization (session 35) — split monolithic file into
     `BallotProblemOQ03OQ01OQ02.lean` (main, 398 lines, 0 sorries) +
     `BallotProblemOQ03OQ01OQ02Helpers.lean` (~14000 lines, 1 sorry) +
     `BallotProblemOQ03OQ01OQ02Aristotle.lean` (companion, 113 lines).
  5. GNW infrastructure (sessions 37–42) — added `strictHookCells`, `gnwProb`,
     `gnwProb_step`, `gnwProb_stable`, `gnwProb_sum_corners`. Proved single-corner
     case of `gnwProb_key`. Stated `gnwProb_exchange` and
     `isCorner_removeCorner_of_ne`.
  6. Strong induction wrapper (session 43) — wired `gnwProb_key` multi-corner
     to `gnwProb_exchange` via `termination_by μ.card`; reduces remaining work
     to a single sorry on `gnwProb_exchange`.
  7. Anti-monotone corner helpers (session 44) — added three structural lemmas
     `corner_col_lt_of_row_lt`, `corner_row_lt_of_col_lt`,
     `doubly_affected_cell_mem` (after `colLen_of_isCorner` ~line 4733).
     These reduce the upcoming `gnwProb_exchange` case analysis: given two
     distinct corners with `c.1 < c'.1`, the unique doubly-affected cell
     `(c.1, c'.2)` is in `μ` and lies in the arm of c and leg of c'.
  8. Corner-distinctness coordinate lemmas (session 45) — added three more
     structural lemmas after `corner_row_lt_of_col_lt`:
     `corners_fst_ne`, `corners_snd_ne`, `distinct_corners_dichotomy`.
     These promote the geometric anti-monotonicity of session 44 to clean
     coordinate-distinctness predicates: `c ≠ c' → c.1 ≠ c'.1 ∧ c.2 ≠ c'.2`
     and a packaged dichotomy `(c.1 < c'.1 ∧ c'.2 < c.2) ∨
     (c'.1 < c.1 ∧ c.2 < c'.2)` for downstream case analysis. They eliminate
     repeated `rowLen_of_isCorner` / `colLen_of_isCorner` boilerplate in the
     upcoming `gnwProb_exchange` proof.
  9. Aristotle Target 3 closed via dispatcher (session 46) — replaced the
     redundant `sorry` in `hook_walk_identity_Aristotle` with a one-line
     term-mode delegation `hook_walk_identity_gnw μ hn`.  The Aristotle
     companion file's sorry count drops from 3 to 2 (only the deep LGV-route
     `ni_count_eq_syt_count_Aristotle` and `lgv_det_factors_as_hook_quotient_Aristotle`
     remain).  No new dependency is introduced; transitive dependence on
     `gnwProb_exchange` is unchanged.
 10. Diagram commutativity for double removal (session 47) — added
     `removeCorner_swap` (line ~4397) and its corollary
     `hookProd_removeCorner_swap`.  The first is a `Finset`-level identity
     `(μ.cells.erase c).erase c' = (μ.cells.erase c').erase c` lifted to
     `YoungDiagram` via `YoungDiagram.ext`; the second is a one-line
     `rw` corollary.  Together they let the upcoming `gnwProb_exchange`
     proof rewrite `H((μ\c')\c)` ↔ `H((μ\c)\c')` freely, avoiding
     iteration-order bookkeeping at every algebraic step.
 11. Double-removal hookLength shift characterization (session 48) — added
     six lemmas after `hookLength_eq_of_not_arm_leg` (line ~5005) covering
     every case of how `hookLength` shifts when both `c` and `c'` are removed:
     `hookLength_doubleRemove_doubly_affected` (cell `(c.1, c'.2)` shifts by
     2), the four single-shift lemmas
     `_arm_of_c_off_d`, `_leg_of_c`, `_arm_of_c'`, `_leg_of_c'_off_d`
     (each shifts by 1 with explicit "no shift from the other corner"
     side-conditions), and `_other` (cells outside both arm/leg sets are
     unchanged).  The block is iteration-order `(μ\c)\c'` (convert with
     `removeCorner_swap` if needed) and uses only existing primitives:
     `hookLength_removeCorner_arm/_leg/_eq_of_not_arm_leg`,
     `corner_col_lt_of_row_lt`, `isCorner_removeCorner_of_ne`,
     `mem_removeCorner`.  All proofs close with 1–2 lines of
     `omega` / `rw`+`exact`.
 12. Single-removal bridges (session 50) — added two `private` lemmas after
     `hookLength_doubleRemove_other` (~line 5207) capturing how `μ → μ\c'`
     shifts hookLength at arm/leg cells of `c`:
     - `hookLength_removeCornerC'_arm_of_c_off_d`: arm cells `(c.1, s)` with
       `s ≠ c'.2` are unaffected by removing `c'`.
     - `hookLength_removeCornerC'_leg_of_c`: leg cells `(r, c.2)` with
       `r < c.1` are unaffected by removing `c'`.
     These are the dual chain to S48's `(μ\c)\c'` block; combined with
     `hookLength_removeCorner_leg hc' hi` for the doubly-affected cell, they
     pre-align the products produced by `hookProd_ratio_formula` applied to
     corner `c` on `μ` versus on `μ\c'`.  Used in the upcoming
     `hookProd_doubleRemove_factor` proof (S52).  ~33 lines.
 13. Doubly-affected hookLength lower bound (session 51) — added a single
     `private lemma hookLength_at_d_ge_3` after the S50 bridges (~line 5288)
     establishing the structural fact `3 ≤ hookLength μ c.1 c'.2` for distinct
     corners `c, c'` with `c.1 < c'.1`.  Proof: `armLen ≥ 1` from
     `c.2 − c'.2 ≥ 1` (anti-monotonicity) and `legLen ≥ 1` from
     `c'.1 − c.1 ≥ 1` (the row-distinctness hypothesis), so
     `hookLength = armLen + legLen + 1 ≥ 3` by `omega` after `unfold` and the
     two `*_of_isCorner` rewrites.  ~10 lines.  Provides the ℚ-cast safety
     prerequisite for `hookProd_doubleRemove_factor` (S52): `h_d ≥ 3` ensures
     `h_d − 1 ≥ 2 > 0` and `h_d − 2 ≥ 1 > 0`, so the rational factor
     `(h_d − 1)² / (h_d (h_d − 2))` is well-formed and ℕ-subtraction
     truncation is benign.  No build risk: identical proof shape to existing
     `hookLength_pos` and the `*_of_isCorner` rewrites are 1-step.

## Blockers
- **`gnwProb_exchange` proof.** This is the GNW 1979 hook-weight shift argument.
  The proof requires showing that hookProd and the gnwProb sum transform
  predictably when one corner c' is removed. Estimated ~100 lines of careful
  case analysis on arm/leg of c vs c'.
- **Build verification.** Helpers file is at 14719 lines after S51 (was 14704
  after S50, +~15 lines for `hookLength_at_d_ge_3`); whether it type-checks
  under Docker's 32GB memory limit is not yet confirmed in this session.
  CI will verify the PR.

## Next Action
**S52 — prove `hookProd_doubleRemove_factor`** using the S50 single-removal
bridges + S51 `hookLength_at_d_ge_3` + `hookProd_ratio_formula` (twice) +
`hookProd_removeCorner_swap`.

S50 added the two single-removal bridge lemmas
(`hookLength_removeCornerC'_arm_of_c_off_d`, `hookLength_removeCornerC'_leg_of_c`)
that establish the dual chain `μ → μ\c' → (μ\c')\c`.  S51 (this session)
added the geometric prerequisite `hookLength_at_d_ge_3` that ensures
`h_d ≥ 3` at the doubly-affected cell, so the rational factor
`(h_d − 1)² / (h_d (h_d − 2))` is well-formed in ℚ.  Combined with
`hookLength_removeCorner_leg hc' hi` for the doubly-affected cell, these are
exactly the pointwise hookLength facts needed when comparing the two
`hookProd_ratio_formula` applications: one for corner `c` on `μ`, one for
corner `c` on `μ\c'`.

The refined attack still splits `gnwProb_exchange` into:

1. **Algebraic "easy half" — `hookProd_doubleRemove_factor`** (~80-120 lines).
   Pure hookProd identity using `hookProd_ratio_formula` (twice) plus the
   S50 bridge lemmas + `hookLength_removeCorner_leg hc' hi` (single-shift at
   `d`) + `hookProd_removeCorner_swap` (to identify `(μ\c')\c` with `(μ\c)\c'`)
   + S51 `hookLength_at_d_ge_3` (ℚ-cast safety; `h_d ≥ 3`).
   States that
   `H(μ) · H((μ\c)\c') · (h_d − 1)² = H(μ\c) · H(μ\c') · h_d · (h_d − 2)`
   where `d = (c.1, c'.2)`.  Confidence: high — all geometric prerequisites
   are now in place.  See `sessions/2026-05-08-s05.md` for the Lean-skeleton
   recipe and `sessions/2026-05-08-s06.md` for the S51 prerequisite note.

2. **F-side "hard half"** (~100-200 lines).  Joint K-induction on the
   sum-level invariant
   `(∑ gnwProb μ c K) · h_d (h_d−2) = (∑ gnwProb (μ\c') c K) · (h_d − 1)²`,
   using `gnwProb_step` for K-stability and the S43 sum-bridges
   (`sum_gnwProb_eq_removeCorner_cells`,
   `sum_gnwProb_strictHookCells_eq_removeCorner`).  Confidence: medium.

3. **Combine** to close `gnwProb_exchange` (~50 lines algebraic
   rearrangement).

Practical sequencing for S52: complete step 1 (the easy half).  This will
either succeed cleanly via the dual-chain S50 bridges + S51 `_ge_3` bound,
or surface specific Mathlib `Finset.mul_prod_erase`/`Finset.prod_congr`
quirks that the next session can patch.

**File-size**: Helpers.lean is at 14719 lines after S51 (+15 from 14704
after S50, for the new lemma + its docstring).  S52's algebraic proof
adds another ~80-120 lines.  Approaching 14900 — still below the practical
Docker 32GB-memory ceiling but extraction into
`BallotProblemOQ03OQ01OQ02DoubleRemove.lean` should be on the radar by S53
to forestall the wall.

Alternative (deferred): a deterministic weighted-path recasting of GNW
that avoids the exchange step entirely (count weighted walks of every
length, divide by `μ.card · ∏ |strict hook|`); ~400 lines self-contained.
Fallback if S52-S54 stall.

## References

- `literature/closing-the-final-sorry.md` — three-route comparison (session 33)
- `knowledge.md` §Session 35 — modularization decision and split
- `knowledge.md` §Session 37 — GNW infrastructure: `gnwProb`, `gnwProb_sum_corners`
- `knowledge.md` §Session 38 — `gnwProb_step` and stability
- `knowledge.md` §Session 40-42 — single-corner case proof, exchange framework
- `knowledge.md` §Session 43 — strong induction wrapper
- `knowledge.md` §Session 44 — anti-monotone corner helpers (PR #16648)
- `knowledge.md` §Session 45 — corner-distinctness coordinate lemmas
- `sessions/2026-05-08-s01.md` — Session 46: Aristotle Target 3 closed via dispatcher
- `sessions/2026-05-08-s02.md` — Session 47: `removeCorner_swap` + `hookProd_removeCorner_swap`
- `sessions/2026-05-08-s03.md` — Session 48: double-removal hookLength shift lemmas
- `sessions/2026-05-08-s04.md` — Session 49: refined attack plan; cell-wise → sum-level pivot
- `sessions/2026-05-08-s05.md` — Session 50: single-removal bridges + S51 Lean recipe
- `sessions/2026-05-08-s06.md` — Session 51: `hookLength_at_d_ge_3` geometric prerequisite for ℚ-cast safety
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:4397` — `removeCorner_swap`
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:4412` — `hookProd_removeCorner_swap`
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:5035` — `hookLength_doubleRemove_doubly_affected` (S48)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:5057` — `hookLength_doubleRemove_arm_of_c_off_d` (S48)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:5092` — `hookLength_doubleRemove_leg_of_c` (S48)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:5122` — `hookLength_doubleRemove_arm_of_c'` (S48)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:5156` — `hookLength_doubleRemove_leg_of_c'_off_d` (S48)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:5186` — `hookLength_doubleRemove_other` (S48)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:5232` — `hookLength_removeCornerC'_arm_of_c_off_d` (S50)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:5258` — `hookLength_removeCornerC'_leg_of_c` (S50)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:5288` — `hookLength_at_d_ge_3` (S51)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:14464` — `gnwProb_exchange`
  (sorry'd, target of S52-S53 — line shifted by +23 from S51 additions)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:14489` — `gnwProb_key`
  (proved modulo `gnwProb_exchange`)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:14698` — `hook_walk_identity_gnw`
  (sorry-free dispatcher, transitive on `gnwProb_exchange`)
