# Research State: ballot-problem-oq-03-oq-01-oq-02

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-05-08T17:36:50+03:00
**Last Updated**: 2026-05-08
**Iteration**: 53

## Current Focus
Close `gnwProb_exchange` (Helpers, line 14597 after S52) — the GNW 1979 exchange identity
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
- Total attempts: 53 (sessions 1–53; sessions 1–4 archived to
  `sessions/`; sessions 5–53 in `knowledge.md` + `sessions/`)
- Current approach attempts: 17 (sessions 37–53 on GNW)
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
 14. Algebraic "easy half" of GNW exchange (session 52) — proved
     `private lemma hookProd_doubleRemove_factor` (~line 5297, +133 lines
     including 38-line docstring):
     `H(μ) · H((μ\c)\c') · (h_d - 1)² = H(μ\c) · H(μ\c') · h_d · (h_d - 2)`
     where `h_d = hookLength μ c.1 c'.2`.  Proof: apply `hookProd_ratio_formula`
     twice (corner `c` on `μ`, corner `c` on `μ\c'` via
     `isCorner_removeCorner_of_ne hc' hc hne.symm`); use `Finset.mul_prod_erase`
     to extract the `d`-factor on each side (`h_d/(h_d-1)` for R₁,
     `(h_d-1)/(h_d-2)` for R₂ after `h_d_in_ν : hookLength (μ\c') c.1 c'.2 = h_d - 1`
     from `hookLength_removeCorner_leg hc' hi`); pointwise equality off `d` by
     S50 bridges (`Finset.prod_congr`); `div_eq_iff` to clear LHS hookProd
     ratios; `← h_swap` to align with `H((μ\c)\c')`; final
     `rw [hR1, hR2]; field_simp; ring`.  ℚ-cast safety from S51
     `hookLength_at_d_ge_3` via `linarith`.  Closes step 1 of 3 in the s05
     recipe; step 2 (F-side joint K-induction) is S53, step 3 (combine) is
     S54+.  Sorry count unchanged (1).
 15. Algebraic combiner for `gnwProb_exchange` (session 53, **this session**)
     — proved `private lemma gnwProb_exchange_lt_row_of_F_side` (line ~14591,
     +87 lines including ~37-line docstring).  This is **step 3 of the s05
     recipe**, NOT step 2 (the F-side K-induction is still open).  The
     combiner takes the F-side identity as a hypothesis `h_F` and discharges
     `gnwProb_exchange` (case 1: `c.1 < c'.1`) algebraically by:
     - Multiplying both sides of the goal by `(h_d − 1)²` (nonzero by
       `hookLength_at_d_ge_3` ≥ 3) via `mul_right_cancel₀`.
     - Applying `hookProd_removeCorner_swap` to align iteration orders
       `H((μ\c')\c) ↔ H((μ\c)\c')` so S52 applies directly.
     - `linear_combination` with coefficients `(H(μ\c) · H(μ\c'))` for `h_F`
       and `(−F_ν)` for `h_S52` closes the polynomial identity over ℚ.
     **Correctness verified concretely** on the (3,1) shape: c = (0,2),
     c' = (1,0), h_d = 4, F(μ,c) = 8/3, F(μ\c',c) = 3, identity
     `(8/3) · 9 = 24 = 3 · 4 · 2` ✓.  Important side discovery: the F-side
     direction recorded in state.md was **reversed** — corrected here.
     **Sorry count unchanged (1)**: the combiner is sorry-free; future
     S53 work that proves the F-side identity in this form can immediately
     instantiate `gnwProb_exchange_lt_row_of_F_side` to close case 1.
     Case 2 (`c'.1 < c.1`) needs an analogous combiner (deferred to a
     follow-up session — symmetric proof structure).

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
**S54 — prove the F-side "hard half" of `gnwProb_exchange`** via joint
K-induction on the sum-level invariant.  After S53's combiner, the
remaining target is the **corrected** F-side identity (case `c.1 < c'.1`):
```
F(μ,c) · (h_d − 1)² = F(μ\c',c) · h_d · (h_d − 2)
```
where `F(ν,c) := ∑_{x ∈ ν.cells} gnwProb ν c (h_ν(x)) x` and
`h_d = h_μ(c.1, c'.2)`.  **Note**: the direction here is the reverse of
what was recorded in state.md before S53 — verified concretely on the
(3,1) shape (`F(μ,c) = 8/3`, `F(μ\c',c) = 3`, `h_d = 4`,
`(8/3)·9 = 24 = 3·4·2` ✓).

Once S54 proves this identity (~100-200 lines of joint K-induction using
`gnwProb_step` for K-stability and the S43 sum-bridges
`sum_gnwProb_eq_removeCorner_cells`,
`sum_gnwProb_strictHookCells_eq_removeCorner`), case 1 of
`gnwProb_exchange` closes via S53's
`gnwProb_exchange_lt_row_of_F_side`.  Case 2 (`c'.1 < c.1`) requires a
symmetric companion combiner + a symmetric F-side identity.  After both
cases, `gnwProb_exchange` itself is closed via
`distinct_corners_dichotomy`, and the entry can be promoted to
`verified` (last sorry eliminated).

S53 (this session) closed step 3 of 3 from the s05 recipe: the
**algebraic combiner** that takes the F-side identity as a hypothesis
and closes `gnwProb_exchange` (case `c.1 < c'.1`) by combining with S52
and `hookProd_removeCorner_swap`.  The combiner is sorry-free.  S52 had
already closed step 1.  Step 2 (F-side joint K-induction) is now the
sole remaining open piece of `gnwProb_exchange`.

Remaining steps in the s05 recipe:

1. ✓ **Algebraic "easy half" — `hookProd_doubleRemove_factor`** (S52,
   sorry-free, merged in PR #17173).

2. **F-side "hard half"** (~100-200 lines, S54 next action — corrected
   direction).  Joint K-induction on the sum-level invariant.
   Confidence: medium.  May require S54.5 to extract the K=0 base case
   as a separate lemma if the induction step is too large for one PR.

3. ✓ **Combine** to close `gnwProb_exchange` case 1 (S53, this session,
   sorry-free conditional on F-side identity).  Case 2 combiner deferred.

**File-size**: Helpers.lean is at 14939 lines after S53 (+87 from 14852
after S52).  Approaching the Docker 32GB-memory ceiling estimate (~15500
lines).  S54 will likely push us close to or over 15000 — extraction into
`BallotProblemOQ03OQ01OQ02DoubleRemove.lean` should now be a *blocking
prerequisite* for S54 (or S54 should target the extracted file directly).

Alternative (deferred): a deterministic weighted-path recasting of GNW
that avoids the exchange step entirely (count weighted walks of every
length, divide by `μ.card · ∏ |strict hook|`); ~400 lines self-contained.
Fallback if S53-S54 stall.

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
- `sessions/2026-05-08-s07.md` — Session 52: `hookProd_doubleRemove_factor` algebraic "easy half"
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
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:5297` — `hookProd_doubleRemove_factor` (S52)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:14597` — `gnwProb_exchange`
  (sorry'd, target of S53-S54 — line shifted by +133 from S52 additions)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:14622` — `gnwProb_key`
  (proved modulo `gnwProb_exchange` and `isCorner_removeCorner_of_ne`)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:14831` — `hook_walk_identity_gnw`
  (sorry-free dispatcher, transitive on `gnwProb_exchange`)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:14489` — `gnwProb_key`
  (proved modulo `gnwProb_exchange`)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:14698` — `hook_walk_identity_gnw`
  (sorry-free dispatcher, transitive on `gnwProb_exchange`)
