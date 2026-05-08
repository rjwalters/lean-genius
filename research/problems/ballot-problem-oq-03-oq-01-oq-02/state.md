# Research State: ballot-problem-oq-03-oq-01-oq-02

## Current State
**Phase**: ORIENT/PLAN (S49 — refined attack plan for `gnwProb_exchange`: cell-wise gnwProb invariance shown to fail; pivot to sum-level joint-K induction strategy)
**Path**: full
**Since**: 2026-04-21T20:08:44+02:00
**Last Updated**: 2026-05-08
**Iteration**: 49

## Current Focus
Close `gnwProb_exchange` (Helpers, line 14143) — the GNW 1979 exchange identity
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
- Total attempts: 49 (sessions 1–49; sessions 1–4 archived to
  `sessions/`; sessions 5–49 in `knowledge.md` + `sessions/`)
- Current approach attempts: 13 (sessions 37–49 on GNW)
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

## Blockers
- **`gnwProb_exchange` proof.** This is the GNW 1979 hook-weight shift argument.
  The proof requires showing that hookProd and the gnwProb sum transform
  predictably when one corner c' is removed. Estimated ~100 lines of careful
  case analysis on arm/leg of c vs c'.
- **Build verification.** Helpers file is at 14428 lines (was 14398); whether
  it type-checks under Docker's 32GB memory limit (post-modularization) is
  not yet confirmed in this session. CI will verify the PR.

## Next Action
**S50 — extract `BallotProblemOQ03OQ01OQ02DoubleRemove.lean` + prove
`hookProd_doubleRemove_factor`** (the algebraic "easy half" of
`gnwProb_exchange`).

S49 (this session) re-examined S48's outlined cell-by-cell pairing and
identified a subtle obstacle: cell-wise gnwProb invariance for cells
"far from c'" does NOT hold, because the gnwProb random walk
recursively descends into arm/leg of c' even when starting at cells
disjoint from arm/leg of c'.  See `sessions/2026-05-08-s04.md` for the
counterexample sketch (e.g., `x = (c'.1 - 1, 0)` reaches `(c'.1, 0)` in
one walk step, and `(c'.1, 0)` is in the arm of c').

The refined attack splits `gnwProb_exchange` into two sub-lemmas:

1. **Algebraic "easy half" — `hookProd_doubleRemove_factor`** (~80 lines).
   Pure hookProd identity using `hookProd_ratio_formula` (twice) plus
   the six S48 shift lemmas.  States that
   `H(μ) · H((μ\c)\c') · (h_d − 1)² = H(μ\c) · H(μ\c') · h_d · (h_d − 2)`
   where `d = (c.1, c'.2)`.  Confidence: high.

2. **F-side "hard half"** (~100-200 lines).  Joint K-induction on the
   sum-level invariant
   `(∑ gnwProb μ c K) · h_d (h_d−2) = (∑ gnwProb (μ\c') c K) · (h_d − 1)²`,
   using `gnwProb_step` for K-stability and the S43 sum-bridges
   (`sum_gnwProb_eq_removeCorner_cells`,
   `sum_gnwProb_strictHookCells_eq_removeCorner`).  Confidence: medium.

3. **Combine** to close `gnwProb_exchange` (~50 lines algebraic
   rearrangement).

Practical sequencing for S50: do step 1 first (purely algebraic, low risk,
buildable in isolation).  Step 2 involves K-bookkeeping and may need
multiple sub-sessions.

**File-size mitigation.** Helpers.lean is at 14629 lines after S48; the
new bridge lemmas add ~150-300 lines.  Before S50 starts coding, extract
S43-S48 + new bridges into `BallotProblemOQ03OQ01OQ02DoubleRemove.lean`
to stay below the 32GB Docker build ceiling.  This file would import
the existing primitives and re-export the bridges to Helpers.

Alternative (deferred): a deterministic weighted-path recasting of GNW
that avoids the exchange step entirely (count weighted walks of every
length, divide by `μ.card · ∏ |strict hook|`); ~400 lines self-contained.
Fallback if S50-S52 stall.

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
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:4397` — `removeCorner_swap`
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:4412` — `hookProd_removeCorner_swap`
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:5035` — `hookLength_doubleRemove_doubly_affected` (S48)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:5057` — `hookLength_doubleRemove_arm_of_c_off_d` (S48)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:5092` — `hookLength_doubleRemove_leg_of_c` (S48)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:5122` — `hookLength_doubleRemove_arm_of_c'` (S48)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:5156` — `hookLength_doubleRemove_leg_of_c'_off_d` (S48)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:5186` — `hookLength_doubleRemove_other` (S48)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:14374` — `gnwProb_exchange`
  (sorry'd, target of next session — line shifted by +201 from session 48 additions)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:14399` — `gnwProb_key`
  (proved modulo `gnwProb_exchange`)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:14608` — `hook_walk_identity_gnw`
  (sorry-free dispatcher, transitive on `gnwProb_exchange`)
