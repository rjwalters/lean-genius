# Research State: ballot-problem-oq-03-oq-01-oq-02

## Current State
**Phase**: ACT (S57.6 prep 1/2/3 done — partition + vanishing-class IH discharge + non-vanishing-class K-shift facts in place; **S65's planned naive pointwise S57.7 refuted by Session 66 (3,2)-shape counter-example**, replanned to sum-level δ_arm-correction identity)
**Path**: full
**Since**: 2026-05-08T17:36:50+03:00
**Last Updated**: 2026-05-12 (Session 66 / S57.7 plan refutation researcher-8)
**Iteration**: 66

## Session 66 — S57.7 plan refutation: pointwise equality fails (researcher-8, 2026-05-12)

**Mode.** ANALYSIS-ONLY (no `.lean` edits).

**Outcome.** Concrete `(3,2)`-shape counter-example refuting S65's
"Next step (S57.7)" plan that proposed proving
`gnwProb μ c K y = gnwProb (μ\c') c K y` pointwise on the
non-vanishing crossing cells (case-1 arm-class
`y = (x.1, c'.2)`, case-2 leg-class `y = (c'.1, x.2)`).  The
divisor mismatch `|H*(y)| = |H*'(y)| + 1` (since `c' ∈ H*(y)`,
`c' ∉ H*'(y)`) genuinely breaks pointwise equality even though IH
on the strict-hook cells holds.  Realigns S57.7's "Next Action"
with state.md's earlier `δ_arm` correction-term plan
(line 537–539, line 558–563).

**Counter-example summary.** `μ = (3,2)`, `c = (0,2)`, `c' = (1,1)`
(case 1: `0 < 1`).  Off-spine `x = (0,0)`, non-vanishing arm-class
`y = (0,1)`.  Direct computation from the `gnwProb` def (line
14384):

```
gnwProb μ      c K (0,1) = 1/2  (K ≥ 2)
gnwProb (μ\c') c K (0,1) = 1    (K ≥ 2)
```

The `μ`-side strict hook `H*(y) = {(0,2), (1,1)}` includes
`c' = (1,1)`; the `(μ\c')`-side `H*'(y) = {(0,2)}` does not.
At K+1: `(1/2)(1 + 0) = 1/2` vs `(1/1)(1) = 1`.  Hook-length shift
`hookLength_at_arm_class_case1` does not bridge the missing-mass
gap; mass redistributes globally, not locally.

**Sum-level identity verified.** `F_side_identity_aligned`
sum at the same `(3,2)` data: LHS sum of
`gnwProb μ c (h_μ x) x` over `(μ\c').cells` weighted by
`(h_d - 1)² = 4` equals 8; RHS sum of
`gnwProb (μ\c') c (h_{μ\c'} x) x` weighted by
`h_d · (h_d - 2) = 3` also equals 8.  The aligned identity holds
**globally** despite per-cell pointwise inequality at three of
four `(μ\c')` cells.  See `sessions/2026-05-12-s05.md` for the
full table and arithmetic.

**Implication.**  Any K-induction targeting *per-cell* equality on
non-vanishing crossing cells is structurally doomed.  S57.7 must
operate at the **summed** level with a sum-level reweighting
(equivalently, a per-cell `δ_arm` correction term) that
redistributes the missing `c'`-step mass across the arm/leg cells
of the doubly-affected `d`-row/column.  The discrepancy
`(h_d - 1)² - h_d · (h_d - 2) = +1` is the geometric content of
this reweighting.

**Files modified.**
* `research/problems/ballot-problem-oq-03-oq-01-oq-02/state.md` — this entry, Session 65 acknowledgment, "Next Action" rewritten.
* `research/problems/ballot-problem-oq-03-oq-01-oq-02/sessions/2026-05-12-s05.md` — counter-example, structural diagnosis, suggested S57.7 reformulation.
* `src/data/research/problems/ballot-problem-oq-03-oq-01-oq-02.json` — iteration 64 → 66.

**Build status.** No `.lean` changes; no build attempted.  Parent
`BallotProblemOQ03OQ02.lean` remains broken on `origin/main`.

## Session 65 — S57.6 prep 3 non-vanishing crossing K-shifts (researcher-4, 2026-05-12)

PR #17865 added two sorry-free single-removal hook-length shift
lemmas in `BallotProblemOQ03OQ01OQ02Helpers.lean`:

* `hookLength_at_arm_class_case1` (line ~5005) — for off-row cell
  `(r, c'.2) ∈ μ` with `r ≠ c'.1`,
  `hookLength (μ\c') r c'.2 + 1 = hookLength μ r c'.2`.

* `hookLength_at_leg_class_case2` — mirror for off-column cell
  `(c'.1, s) ∈ μ` with `s ≠ c'.2`.

Pre-positioned for S57.7 K-bookkeeping at the non-vanishing
crossing cells.  Helpers.lean: 15920 → 15995 lines (after S57.6
prep 2 + prep 3 both merged).

**S65's "Next step (S57.7)" plan refuted by Session 66** — see above.
The shift lemmas remain valid as algebraic facts; only the proposed
*use* of them in a naive pointwise K-induction is invalid.  They
will instead serve as ingredients in the sum-level `δ_arm`
correction once S57.7's correct formulation crystallizes.

## Session 64 — S57.6 prep 2 crossing-class IH discharge (researcher-4, 2026-05-12)

**Deliverable.** Two sorry-free private lemmas in
`BallotProblemOQ03OQ01OQ02Helpers.lean`, immediately after S57.6
prep's `strictHookCells_off_spine_class_at_c'` (line 15243):

* `gnwProb_eq_on_leg_class_case1` (line 15295) — for `y` with
  `y.1 = c'.1` and `c.1 < c'.1`, `gnwProb μ c K y =
  gnwProb (μ\c') c K y` (both sides 0 via S57.3a
  `gnwProb_zero_of_row_eq_c'_case1` applied to both `μ`s).

* `gnwProb_eq_on_arm_class_case2` (line 15333) — mirror for case 2:
  for `y` with `y.2 = c'.2` and `c.2 < c'.2`, both sides 0 via
  S57.3a `gnwProb_zero_of_col_eq_c'_case2`.

**Why these prepare S57.6 proper.**  The S57.4 K-step recurrence
`gnwProb_succ_eq_off_spine_of_c'` requires the K-step IH equality on
`strictHookCells μ x.1 x.2`.  S57.6 prep's 3-way partition splits
those cells into fully-off-spine / arm-on-c'-col / leg-on-c'-row
classes.  This PR's lemmas close the K-step IH on the two *vanishing*
crossing classes (case-1 leg-on-c'-row, case-2 arm-on-c'-col).  The
fully-off-spine class is handled recursively by the K-induction; the
*non-vanishing* crossing diagonal (case-1 arm-class single cell,
case-2 leg-class single cell) is the only open piece, deferred to
S57.7+ pointwise comparison.

**Net change.**  Helpers.lean: 15868 → 15943 lines (+75, two new
private lemmas with comprehensive docstrings).  sorries: 1 → 1
(unchanged — `F_side_identity_aligned` remains).  No new imports.

**Build status.**  Build pending — `BallotProblemOQ03OQ02.lean`
remains broken on `origin/main` (LGV-route parent, ~24 errors lines
1911–2386), blocking build verification of all `ballot-OQ03-OQ01-*`
descendants.  Matches `(build pending — parent OQ03OQ02 break)`
precedent of PRs #17747 (S57.6 prep), #17734 (S57.5), #17719 (S57.3
rebase), #17652 (S57.4), #17650 (S58), #17611 (S57.3a), #17568
(S57.2), #17537 (S57.1).

**File-size watch.**  Helpers.lean now at 15943 lines, ~443 over the
~15500-line Docker 32GB-memory ceiling estimate (was ~293 after
S57.6 prep).  S57.0 Option E3 extraction into a new
`BallotProblemOQ03OQ01OQ02DoubleRemove.lean` sub-file is now an
imminent prerequisite for S57.6 proper landing its ~80–150-line bulk.

## Session 63 — S57.6 prep: off-spine strict-hook 3-way partition (researcher-9, 2026-05-12)

Added `strictHookCells_off_spine_class_at_c'` (line 15243, +77
Helpers lines), classifying every strict-hook cell of an off-spine
`x` into fully-off-spine / arm-on-c'-col / leg-on-c'-row.  PR #17747.

## Session 62 — S57.5 arm/leg residual reductions (researcher-10, 2026-05-12)

## Session 62 — S57.5 arm/leg residual reductions (researcher-10, 2026-05-12)

**Deliverable.** Two sorry-free private lemmas in
`BallotProblemOQ03OQ01OQ02Helpers.lean` (after S57.4's
`gnwProb_succ_eq_off_spine_of_c'`, line ~14998):

* `sum_gnwProb_leg_of_c'_reduce_case1` — case 1 (`c.1 < c'.1`):
  `∑ r ∈ range c'.1, gnwProb μ c K (r, c'.2) = ∑ r ∈ range (c.1+1), …`.
  High-row block `Ico (c.1+1) c'.1` vanishes pointwise via
  `gnwProb_unreachable_zero`'s `Or.inl` disjunct.

* `sum_gnwProb_arm_of_c'_reduce_case2` — case 2 (`c.2 < c'.2`):
  `∑ s ∈ range c'.2, gnwProb μ c K (c'.1, s) = ∑ s ∈ range (c.2+1), …`.
  Mirror of the case-1 lemma; high-column block vanishes via
  `Or.inr` disjunct.

**Why these complete the geometry.**  S57.3 (PR #17719) handles the
*trivial vanishing* sub-branches (case-1 arm-of-c', case-2 leg-of-c').
S57.5 handles the *non-trivial residual* sub-branches.  Together the
four lemmas tightly bound each sub-branch:

|        | Arm-of-c'                                | Leg-of-c'                                |
|--------|-------------------------------------------|------------------------------------------|
| Case 1 | **Vanishes** (S57.3, PR #17719)           | **Reduces** to `range (c.1+1)` (S57.5)   |
| Case 2 | **Reduces** to `range (c.2+1)` (S57.5)    | **Vanishes** (S57.3, PR #17719)          |

**Tightness.**  For the case-1 leg-of-c' residual `r ∈ range (c.1+1)`,
cells `(r, c'.2)` have `r ≤ c.1` (so `Or.inl` fails) and `x.2 = c'.2
< c.2` in case 1 (so `Or.inr` also fails).  The cells are
*reachable* from `c`, so the residual is genuinely nonzero; at
`r = c.1` it contains the **doubly-affected cell** `d = (c.1, c'.2)`.
Mirror tightness for case-2 arm-of-c': residual contains `d =
(c'.1, c.2)` at `s = c.2`.

**Net change.**  Helpers.lean: 15600 → 15716 lines (+116, two new
private lemmas with comprehensive docstrings).  sorries: 1 → 1
(unchanged — `F_side_identity_aligned` remains).  No new imports.

**Build status.**  Build pending — `BallotProblemOQ03OQ02.lean`
remains broken on `origin/main` (LGV-route parent, ~24 errors lines
1911–2386), blocking build verification of all `ballot-OQ03-OQ01-*`
descendants.  Matches `(build pending — parent OQ03OQ02 break)`
precedent of PRs #17719 (S57.3), #17652 (S57.4), #17650 (S58),
#17611 (S57.3a), #17568 (S57.2), #17537 (S57.1).

**File-size watch.**  Helpers.lean now at 15716 lines, crossing the
~15500-line Docker 32GB-memory ceiling estimate by ~216 lines.  CI
will confirm; if build memory pressure manifests post-parent-fix,
the next S57.6+ commit should trigger the S57.0 Option E3 extraction
into a new `BallotProblemOQ03OQ01OQ02DoubleRemove.lean` sub-file.

## Earlier sessions (preserved)

**Session 58 + S57.4** added transpose-equivariance infrastructure
(`strictHookCells_transpose`, `gnwProb_transpose`) and the off-spine
inductive step (`isCorner_invariant_off_spine_of_c'`,
`gnwProb_succ_eq_off_spine_of_c'`).

## Current Focus
Close `F_side_identity_aligned` (Helpers, line ~15275 post-S57.5) —
the **common-domain parametric F-side hook-shift identity** that is
the sole remaining sorry-bearing lemma on the GNW route after S56.

**Session 62 / S57.5 (researcher-10, this session)** added two
sorry-free residual-reduction lemmas as the complement of S57.3
(PR #17605/#17719):
* `sum_gnwProb_leg_of_c'_reduce_case1` — case 1 leg-of-c' sum reduces
  to `range (c.1 + 1)` (high-row block vanishes via
  `gnwProb_unreachable_zero`'s `Or.inl` disjunct).
* `sum_gnwProb_arm_of_c'_reduce_case2` — case 2 arm-of-c' sum reduces
  to `range (c.2 + 1)` (high-column block vanishes via `Or.inr`).

After S57.5 the Finset-level cell-partition geometry is closed: all
four sub-branches (case 1 / case 2, arm-of-c' / leg-of-c') are
tightly bounded — two vanish (S57.3, PR #17719) and two reduce to a
small residual (S57.5).  Each residual contains the doubly-affected
cell `d` (`min c.1 c'.1, min c.2 c'.2`) plus a few "below-`c`" cells
where genuine pointwise comparison is required.

**Session 58 (researcher-5)** added two sorry-free transpose-equivariance
lemmas as S57.4 reduction infrastructure:
* `strictHookCells_transpose` (Helpers, line ~14788) —
  `strictHookCells μᵀ i j = (strictHookCells μ j i).image Prod.swap`.
* `gnwProb_transpose` (Helpers, line ~14837) —
  `gnwProb μᵀ c K x = gnwProb μ c.swap K x.swap` for every K, c, x.
The S57.0 K-induction plan partitions cells by case 1 (`c.1 < c'.1`)
vs. case 2 (`c.2 < c'.2`).  PR #17605 (S57.3) discharges the
"vanishing" sub-branches in each case (case-1 arm-of-c', case-2
leg-of-c'); the residual "live" sub-branches (case-1 leg-of-c',
case-2 arm-of-c') are exact transpose-duals of each other under the
swap `(c, c', x) ↦ (c.swap, c'.swap, x.swap)`.  After S58, an S57.4
proof of the case-1 leg-of-c' branch automatically yields the case-2
arm-of-c' branch via `gnwProb_transpose`, halving the remaining
pointwise-comparison work.

Earlier S57 layers (preserved):
* S57.1 added three foundational **off-spine structural invariances**
  under c'-removal: `c'_notMem_strictHookCells_of_off_spine`,
  `hookLength_invariant_off_spine_of_c'`, and
  `strictHookCells_invariant_off_spine_of_c'`.
* S57.2 added `gnwProb_unreachable_zero` (the trivial-vanishing
  cornerstone for S57.3/S57.3a).
* S57.3a (PR #17611, merged) added per-cell `gnwProb_zero_of_row_eq_c'_case1`
  and `gnwProb_zero_of_col_eq_c'_case2`.
* S57.3 (PR #17605, open) packages the two summand-form vanishings.

`F_side_identity` (S55a) is sorry-free.  `gnwProb_exchange` (S55a)
is sorry-free.  Only `F_side_identity_aligned` blocks `verified`
status.

## Session 58 — Transpose-equivariance helpers (researcher-5, 2026-05-09)

**Goal.** Add transpose-equivariance of `gnwProb` so that S57.4's
case-1-vs-case-2 symmetry can be exploited mechanically.

**Deliverables.** Two sorry-free private lemmas in
`BallotProblemOQ03OQ01OQ02Helpers.lean`, inserted right after the
S57.3a per-cell vanishings (line 14747) and before
`sum_gnwProb_strictHookCells_eq_removeCorner` (the S43 bridge):

1. `strictHookCells_transpose` (≈12 lines + 18 docstring) —
   the geometric duality that arms/legs swap under transpose.
   Proof: unfold, rewrite `rowLen_transpose`/`colLen_transpose`,
   push `image Prod.swap` through `image_union` and
   `image_image`, identify the function compositions
   `Prod.swap ∘ Prod.mk j = (·, j)` and
   `Prod.swap ∘ (·, i) = Prod.mk i` by `funext; rfl`, close by
   `Finset.union_comm`.

2. `gnwProb_transpose` (≈50 lines + 30 docstring) —
   `gnwProb μᵀ c K x = gnwProb μ c.swap K x.swap`.  Proof:
   induction on `K`; base case definitional.  Successor case
   unfolds via the `K + 1` defining equation (`:= rfl`, matching
   the pattern used by S57.2's `gnwProb_unreachable_zero`).  At a
   corner, `isCorner_transpose_iff` transports the `if` condition
   and `Prod.swap_injective` discharges the `if x = c` indicator
   match.  Off a corner, `strictHookCells_transpose` rewrites the
   recursive sum's domain, `Finset.card_image_of_injective` keeps
   the cardinality factor, `Finset.sum_image` reindexes the sum,
   and the inductive hypothesis applied to `y.swap` (with
   `Prod.swap_swap` collapsing the double swap) gives the
   pointwise integrand equality.

**File-size**.  Helpers.lean: 15349 → 15487 lines (+138 lines incl.
docstrings).  Approaches the Docker 32GB-memory ceiling (~15500);
S57.4 work (the live pointwise comparison) likely needs the
file-extraction split discussed in S57.0 / s06 (Option E2/E3 to
`BallotProblemOQ03OQ01OQ02DoubleRemove.lean`).

**Build status**: pending (parent `BallotProblemOQ03OQ02.lean` LGV
infrastructure has ~24 errors on origin/main lines 1911–2386 per
memory note `feedback_researcher_ballot_oq03oq02_parent_break.md`,
blocking build verification of all OQ03-OQ01-* descendants).
Matches S57.1/S57.2/S57.3a/S57.3 "(build pending)" precedent;
proof verified by reading Mathlib API (`Finset.image_union`,
`Finset.image_image`, `Finset.sum_image`,
`Finset.card_image_of_injective`, `Prod.swap_injective`,
`Prod.swap_swap`, `YoungDiagram.rowLen_transpose`,
`YoungDiagram.colLen_transpose`).

**Coordination with PR #17605 (S57.3 summand form, open)**.  The
S58 lemmas are inserted at lines 14770–14885; PR #17605 inserts
its summand-form lemmas before `sum_gnwProb_strictHookCells_eq_removeCorner`
in roughly the same region.  Whichever lands first will trigger a
small textual rebase for the other; no semantic conflict
(disjoint lemma names, both sorry-free).

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
 16. Algebraic combiner (case 2) for `gnwProb_exchange` (session 54,
     **this session**) — proved
     `private lemma gnwProb_exchange_lt_col_of_F_side` (line ~14723,
     +88 lines including ~46-line docstring).  Symmetric companion to
     S53's `gnwProb_exchange_lt_row_of_F_side`, completing Case 2 of the
     `distinct_corners_dichotomy` branch (`c'.1 < c.1`).  Conditional on
     the symmetric F-side identity
     `F(μ,c) · (h_d' − 1)² = F(μ\c',c) · h_d' · (h_d' − 2)` with
     `h_d' = h_μ(c'.1, c.2)`.  Proof structure identical to S53 but
     **without** the iteration-order swap step:
     `hookProd_doubleRemove_factor hc' hc hne.symm hi` produces
     `H((μ\c')\c)` directly — already matching the gnwProb_exchange RHS
     iteration order — so no `hookProd_removeCorner_swap` invocation is
     needed.  `linear_combination` coefficients identical to S53's
     `(α=H(μ\c)·H(μ\c'), β=−F(μ\c',c))`; only the doubly-affected cell
     coordinates `(c.1, c'.2) → (c'.1, c.2)` differ.  **Sorry count
     unchanged (1)**: combiner is sorry-free.  After S54, both branches
     of `distinct_corners_dichotomy` have closed combiners: dispatching
     `gnwProb_exchange` itself is now a two-line case-split modulo the
     two F-side identities (one per case).
 17. Parametric F-side identity + sorry-free `gnwProb_exchange` dispatcher
     (session 55a, **this session**) — added
     `private lemma F_side_identity` (line ~14795, sorry-bearing, ~40
     lines including 25-line docstring) stating the F-side hook-shift
     identity in `(min c.1 c'.1, min c.2 c'.2)` parametric form, and
     replaced `gnwProb_exchange`'s `sorry` with a 14-line dispatcher:
     `rcases distinct_corners_dichotomy` → `min_eq_left/right` rewrites
     → `exact` to S53 (`gnwProb_exchange_lt_row_of_F_side`) or S54
     (`gnwProb_exchange_lt_col_of_F_side`) combiner.  Both
     `min c.1 c'.1` and `min c.2 c'.2` collapse to the
     case-specific doubly-affected cell coordinates
     (`(c.1, c'.2)` for case 1, `(c'.1, c.2)` for case 2) by
     `corner_col_lt_of_row_lt`/`corner_row_lt_of_col_lt`.  **Sorry count
     unchanged (1)**: the abstract `gnwProb_exchange` sorry has been
     *relocated* to the more concrete `F_side_identity` sorry — no net
     regression, but a structural sharpening.  Two stale comments
     cleaned up: S53 docstring's "deferred to a follow-up session" now
     points to S54; `gnwProb_key`'s "two sorry'd steps" comment is
     reduced to one (step (a) `termination_by` was already resolved
     since S43).  +63 Helpers.lean lines.
 18. Common-domain sharpening of `F_side_identity` (session 56,
     **this session**) — added `private lemma F_side_identity_aligned`
     (line ~14811, sorry-bearing, +46 lines including 38-line
     docstring) running both sums over `(removeCorner μ c' hc').cells`
     (the same finite-cell domain).  Replaced `F_side_identity`'s
     `sorry` with a 2-line proof:
     `rw [sum_gnwProb_eq_removeCorner_cells hc' hne]`
     `exact F_side_identity_aligned hc hc' hne`,
     deriving the original `μ.cells`-domain statement from the aligned
     form via the existing S43 bridge (which uses
     `gnwProb_at_other_corner` to deduce `gnwProb μ c K c' = 0`, so the
     `c'` term vanishes when erasing the LHS sum domain).
     **Sorry count unchanged (1)**: the abstract `F_side_identity`
     sorry has been *relocated* to the more concrete same-domain
     `F_side_identity_aligned` sorry — no net regression, but a
     structural sharpening that removes the cell-wise `c'` excision
     step from the K-induction's burden (S57+ now compares integrands
     pointwise on a single common domain).
 19. Off-spine structural invariances under c'-removal (session 57.1,
     researcher-1) — three sorry-free private lemmas after
     `strictHookCells_removeCorner_eq_of_not_mem` (~line 14534):
     `c'_notMem_strictHookCells_of_off_spine` (~14562),
     `hookLength_invariant_off_spine_of_c'` (~14588),
     `strictHookCells_invariant_off_spine_of_c'` (~14616).  These
     pin down the *base step* (K = 0 / x off-spine) of the joint
     K-induction in `F_side_identity_aligned`, eliminating two of the
     three "moving pieces" in S57.0's analysis.  +89 Helpers lines.
     PR #17537 (merged 2026-05-08 23:55Z, build pending).
 21. **Off-spine `isCorner` invariance + integrand recurrence step
     (session 57.4, this session, researcher-10)** — two sorry-free
     private lemmas after S57.3a's `gnwProb_zero_of_col_eq_c'_case2`
     (line ~14747):
     - `isCorner_invariant_off_spine_of_c'` (line ~14775, +22 lines):
       the fourth structural invariance under `c'`-removal at
       off-spine cells: `isCorner (μ\c') x ↔ isCorner μ x` whenever
       `x.1 ≠ c'.1 ∧ x.2 ≠ c'.2`.  Proof: unfold `isCorner`'s three
       conjuncts; the right and below neighbours of `x` cannot equal
       `c'` since they would force `x.1 = c'.1` or `x.2 = c'.2` (each
       contradicting one off-spine hypothesis).
     - `gnwProb_succ_eq_off_spine_of_c'` (line ~14830, +30 lines):
       the K-step recurrence at off-spine cells: assuming
       `∀ y ∈ strictHookCells μ x.1 x.2, gnwProb μ c K y =
       gnwProb (μ\c') c K y` (the K-step IH on the strict hook of
       `x`), derive
       `gnwProb μ c (K+1) x = gnwProb (μ\c') c (K+1) x`.  Proof:
       unfold both `gnwProb _ c (K+1) x` to the recursive
       `if isCorner _ x then indicator else (1/|H*|) · ∑` form;
       rewrite the `(μ\c')`-side `isCorner` and `strictHookCells` via
       the four off-spine invariances (S57.1's three + this PR's
       `isCorner_invariant_off_spine_of_c'`) to align both sides;
       `by_cases isCorner μ x` discharges corners trivially and
       non-corners via `Finset.sum_congr` against the IH.
     **Why useful for S57.5+**: provides the inductive step of the
     joint K-induction on the off-spine branch (S1) of S57.0's plan.
     Pairs with the trivial K = 0 base case (both sides are 0 by
     definition) to give pointwise off-spine integrand identity at
     every K, modulo IH on cells "below" `x` in the strict-hook
     recursion.  Caveat: the strict hook of an off-spine cell can
     contain on-spine cells (where `y.1 = c'.1` or `y.2 = c'.2`),
     so unconditional off-spine pointwise identity must be derived
     at the **sum level** (integrating spine contributions via
     S57.3/S57.3a's trivial branches and the S43 bridge); S57.5
     is therefore not just a wrapper around S57.4.
     **Sorry count unchanged (1)** — `F_side_identity_aligned`
     remains the sole open sorry.  +109 Helpers.lean lines.
     File at 15458 lines (was 15349; ~42 under Docker ceiling — file
     extraction is now required before S57.5+ lands further bulk).
 20. **Walk-unreachability lemma for arm/leg-of-c' (session 57.2,
     this session)** — added `private lemma gnwProb_unreachable_zero`
     (line ~14656, +68 lines including 32-line docstring): for any
     cell `x` with `c.1 < x.1 ∨ c.2 < x.2`, `gnwProb μ c K x = 0` for
     every `K`.  **Proof**: induction on `K` (~15 lines).  Base `K=0`
     is `rfl`.  Step `K+1`: unfold; if `x` is a corner the indicator
     is `0` (since `x ≠ c` from the unreachability disjunction); if
     not a corner, the recursive sum over `y ∈ strictHookCells μ x`
     vanishes pointwise by IH (each `y` has `y.1 ≥ x.1` and
     `y.2 ≥ x.2`, so the unreachability disjunct propagates from `x`
     to `y`).  **Why useful for S57+**: in case 1 (`c.1 < c'.1`),
     the arm-of-c' cells `x = (c'.1, s)` with `s < c'.2` satisfy
     `x.1 = c'.1 > c.1`, so both LHS and RHS of (S2)
     `gnwProb_aligned_on_arm_of_c'` are `0` — the `δ_arm`
     correction-term design problem **dissolves entirely** in this
     branch.  Case 2 leg-of-c' cells dissolve similarly via the
     `c.2 < x.2` disjunct.  This is the cleanest factoring: rather
     than inventing a `δ_arm` and proving an algebraic identity
     `(α-1)² + δ_arm`, we observe that gnwProb is identically 0 on
     the arm-of-c' branch in case 1 (and leg-of-c' in case 2),
     collapsing (S2)/(S3) for those branches to triviality.
     **Sorry count unchanged (1)** — `F_side_identity_aligned`
     remains the sole open sorry; this lemma is sorry-free
     infrastructure that simplifies the upcoming S57.3+ K-induction.
     File at 15293 lines (was 15225 after S57.1, +68).

## Blockers
- **`F_side_identity_aligned` proof.** The common-domain parametric
  F-side hook-shift identity (S56) is now the sole open sorry on the
  GNW route.  Both summation domains run over `(μ\c').cells`; the
  remaining obligation compares **integrands pointwise**:
  `gnwProb μ c (h_μ x) x` (LHS) versus
  `gnwProb (μ\c') c (h_{μ\c'} x) x` (RHS).  Estimated ~100-300 lines
  via joint K-induction on the sum-level invariant (see
  `sessions/2026-05-08-s05.md` recipe).
- **Build verification.** Helpers file is at 15136 lines after S56
  (was 15090 after S55a, +46 lines for `F_side_identity_aligned`
  + sorry-free `F_side_identity`); ~360 lines under the Docker 32GB-
  memory ceiling estimate (~15500).  CI will verify the PR.

## Next Action

**S57.7 — sum-level F-side aligned residual identity for non-vanishing
crossings** (replaces S65's refuted naive pointwise plan; see Session 66
above + `sessions/2026-05-12-s05.md`).

The S57.6 prep 1/2/3 chain (PRs #17747 / #17817 / #17865) reduces
`F_side_identity_aligned` modulo two remaining contributions: the
non-vanishing arm-class summands (case 1, `y = (x.1, c'.2)`) and the
non-vanishing leg-class summands (case 2, `y = (c'.1, x.2)`).
*Per-cell* equality `gnwProb μ c K y = gnwProb (μ\c') c K y` is
**false** on these cells (Session 66 counter-example), because
`c' ∈ H*(y) \ H*'(y)` causes the K+1 step's divisor and summands to
mismatch by mass that is not recoverable from the IH.

The correct target is at the **summed** level:

```
∑ x ∈ (μ\c').cells.filter (off-spine of c'),
    [ gnwProb μ      c (hookLength μ      x.1 x.2) x · (h_d - 1)²
    − gnwProb (μ\c') c (hookLength (μ\c') x.1 x.2) x · h_d · (h_d - 2) ]
= 0
```

with the discrepancy `(h_d − 1)² − h_d · (h_d − 2) = +1` absorbing the
missing `c'`-step mass uniformly across the off-spine arm/leg cells.
Equivalently, S57.7 introduces a `δ_arm`-style per-cell correction
term that integrates to zero against the off-spine sum.

**Approach.**

1. **Sub-lemma S57.7a — partial sums on the case-1 arm class.**  For
   the non-vanishing arm-class strict-hook contributions of off-spine
   cells `x = (r, c) ∈ (μ\c').cells` with `r ≠ c'.1`, write the
   K-step residual `gnwProb μ c (K+1) x − gnwProb (μ\c') c (K+1) x`
   as `(1/(K+1)) · gnwProb μ c K c'` plus a divisor-mismatch term
   that recombines as a *fraction* of `gnwProb (μ\c') c K x` with
   coefficient `+1/(|H*'(x)| · (|H*'(x)| + 1))`.
   (S65's `hookLength_at_arm_class_case1` gives `|H*(x)| = |H*'(x)| + 1`.)

2. **Sub-lemma S57.7b — case-2 leg-class mirror.**  Reduce to S57.7a
   via S58 (PR #17650, transpose-equivariance of `strictHookCells`
   and `gnwProb`).

3. **Sub-lemma S57.7c — `δ_arm` integration to zero.**  Sum the
   per-cell `δ_arm` correction over the off-spine arm/leg sub-domain
   and show it cancels the `+1` discrepancy weighted by the
   off-spine cell count.

   Tools: S57.5's `sum_gnwProb_arm_of_c'_reduce_*` /
   `sum_gnwProb_leg_of_c'_reduce_*` (PR #17734) for the sum reductions;
   `sum_gnwProb_strictHookCells_eq_removeCorner` (line 15405) for the
   strict-hook domain bridge.

**Estimated.**  150–250 lines (sub-lemmas) + 40–80 lines for the
final `F_side_identity_aligned` assembly.  Total likely exceeds the
~15500-line Helpers.lean ceiling, forcing the Option E3 extraction
into `BallotProblemOQ03OQ01OQ02DoubleRemove.lean` to land first.

**Risk.**  Medium-high.  S57.7a's algebraic restatement is the
crux; the `+1` discrepancy must factor cleanly through the
divisor-mismatch.  Recommend an **analysis-only S57.7 spec session**
next (Session 67) to derive S57.7a's exact algebraic form on the
`(3,2)` and `(3,2,1)` test diagrams before any `.lean` edit.

## Historical Next Action (S57.6, replanned by Session 66)

The pre-S65 plan called for S57.6 to be a single ~80–150-line
well-founded-recursion lemma deriving the unconditional pointwise
off-spine integrand identity.  The S57.6 prep 1/2/3 chain (PRs
#17747 / #17817 / #17865) decomposed S57.6 into bookkeeping
sub-lemmas; Session 66 then refuted the implicit assumption that
the non-vanishing crossing classes admit pointwise equality.
S57.6 *proper* (the well-founded recursion) is now subsumed by
S57.7's sum-level identity above.

## Historical Next Action (S57.3, now superseded by S57.5)
**S57.3 — apply `gnwProb_unreachable_zero` to discharge (S2) and (S3)
in the trivial branches** *[completed; both per-cell variants merged
as #17611 and sum-form variants in flight as PR #17719; complement
non-trivial residuals reduced by S57.5 — this session]*, completing
the case-1 arm-of-c' and case-2 leg-of-c' summands of the K-induction.
After S57.2's lemma, the
remaining work for `F_side_identity_aligned` reduces materially:
* **(S2) case 1** (`c.1 < c'.1`, arm-of-c'): `gnwProb_unreachable_zero`
  immediately gives `gnwProb μ c (h_μ x) x = 0` and
  `gnwProb (μ\c') c (h_{μ\c'} x) x = 0` for all such `x`, so the
  pointwise identity is `0 · α² = 0 · ((α−1)² + 0)`.  Trivial; needs
  a wrapper lemma showing `gnwProb_zero_on_arm_of_c'_case1`
  (~10 lines), then the (S4) summand follows by `Finset.sum_eq_zero`
  (~10 lines).
* **(S3) case 2** (`c'.1 < c.1`, leg-of-c'): analogous, via the
  `c.2 < x.2` disjunct of `gnwProb_unreachable_zero`.
* **(S2) case 2** (arm-of-c' with `c'.1 < c.1`): NOT covered.
  Cells `x = (c'.1, s)` with `s < c'.2` and `c'.1 < c.1` give
  `x.1 = c'.1 < c.1`, no unreachability.  These cells need genuine
  pointwise comparison — the `δ_arm` story still applies for this
  sub-branch.  But (S2) case 2 falls under (S3) case 1 by
  transpose-mirror argument; needs investigation.

The plan partitions the open lemma `F_side_identity_aligned` into
seven sublemmas (S1)–(S7), keyed to the four cell categories A/B/C/D
of `(μ\c').cells` (off-spine, off-arm-of-c, arm-of-c', leg-of-c').

S57.0's blueprint (sublemma family — see `2026-05-09-s02.md` for full
discussion):
* (S1) `gnwProb_invariant_off_strictHook_of_c'` — pointwise off-spine
  invariance.  ~30-50 lines, **high** confidence.  ← **S57.1 target**.
* (S2) `gnwProb_aligned_on_arm_of_c'` — arm-cell pointwise reduction
  with `δ_arm` correction term.  ~80-150 lines, medium confidence.
  Hardest piece.  ← S57.2.
* (S3) `gnwProb_aligned_on_leg_of_c'` — leg-cell mirror via PART XXIV
  transpose duality.  ~30-60 lines, high.  ← S57.3.
* (S4)/(S5) arm/leg summands.  ~30-50 each.  ← S57.4/S57.5.
* (S6) off-spine summand.  ~40-80 lines.  ← S57.6.
* (S7) assembly.  ~40-80 lines.  ← S57.7.

**Total estimated**: 280-520 lines.  This *will* exceed the 15500-line
Helpers.lean ceiling, so an extraction is forced before assembly
lands; S57.0's plan recommends **Option E3** (defer the split until
empirically needed; only move the F-side proof apparatus into a fresh
`BallotProblemOQ03OQ01OQ02FsideKind.lean` if the S57.1+ commits push
past the ceiling).

**Open statement** (target of S57.1+):
```
[∑ x ∈ (μ\c').cells, gnwProb μ c (h_μ x) x] · (h_d − 1)²
  = [∑ x ∈ (μ\c').cells, gnwProb (μ\c') c (h_{μ\c'} x) x]
    · h_d · (h_d − 2)
where  h_d = hookLength μ (min c.1 c'.1) (min c.2 c'.2)
```
```
[∑ x ∈ (μ\c').cells, gnwProb μ c (h_μ x) x] · (h_d − 1)²
  = [∑ x ∈ (μ\c').cells, gnwProb (μ\c') c (h_{μ\c'} x) x]
    · h_d · (h_d − 2)
where  h_d = hookLength μ (min c.1 c'.1) (min c.2 c'.2)
```
On both branches of `distinct_corners_dichotomy`, `(min c.1 c'.1, min c.2 c'.2)`
collapses to the doubly-affected cell `d`:
* Case 1 (`c.1 < c'.1`): `d = (c.1, c'.2)` (verified concretely on (3,1)
  shape during S53: `F(μ,c) = 8/3`, `F(μ\c',c) = 3`, `h_d = 4`,
  `(8/3) · 9 = 24 = 3 · 4 · 2` ✓).
* Case 2 (`c'.1 < c.1`): `d = (c'.1, c.2)` (mirror of case 1).

Approach: joint K-induction using `gnwProb_step` for K-stability and the
S43 sum-bridges (`sum_gnwProb_eq_removeCorner_cells`,
`sum_gnwProb_strictHookCells_eq_removeCorner`).  Crucially, both sums
in `F_side_identity_aligned` are now over the **same** finite-cell
domain `(μ\c').cells`, so the K-induction can attack the integrands
pointwise; the cell-wise `c'` excision step (LHS sum split) is no
longer needed, having been absorbed by the bridge in `F_side_identity`.
A single parametric proof discharges both cases simultaneously
(~100-300 lines).  Once `F_side_identity_aligned` is sorry-free, the
entry promotes to `verified` (last sorry eliminated).

S53–S54 (sessions completed) closed step 3 of 3 from the s05 recipe for
**both** branches of `distinct_corners_dichotomy`: the algebraic
combiners that take the F-side identity as a hypothesis and close
`gnwProb_exchange` for each case.  Both combiners are sorry-free.  S52
had already closed step 1.  Step 2 (F-side joint K-induction) is now the
sole remaining open piece of `gnwProb_exchange`.

Remaining steps in the s05 recipe:

1. ✓ **Algebraic "easy half" — `hookProd_doubleRemove_factor`** (S52,
   sorry-free, merged in PR #17173).

2. **F-side "hard half"** (~150-250 lines if proved parametrically for
   both cases, or ~100-200 each).  Joint K-induction on the sum-level
   invariant.  Confidence: medium.  S56 (this session) sharpened the
   obligation to a common-domain form `F_side_identity_aligned`; the
   K-induction now compares integrands pointwise on `(μ\c').cells`.
   May still require S57.5 to extract the K=0 base case as a separate
   lemma if the induction step is too large for one PR.

3. ✓ **Combine** to close `gnwProb_exchange`:
   - Case 1 (`c.1 < c'.1`): S53 (`gnwProb_exchange_lt_row_of_F_side`),
     merged in PR #17320, sorry-free conditional on F-side identity.
   - Case 2 (`c'.1 < c.1`): S54 (`gnwProb_exchange_lt_col_of_F_side`),
     sorry-free conditional on F-side identity.
   - Final dispatcher: ✓ S55a — wired `gnwProb_exchange` through
     `distinct_corners_dichotomy` + S53/S54 + parametric
     `F_side_identity` (sorry-bearing).  `gnwProb_exchange` is now
     sorry-free.
   - Common-domain sharpening: ✓ S56 (**this session**) — added
     `F_side_identity_aligned` (sorry-bearing, both sums over
     `(μ\c').cells`); `F_side_identity` is now sorry-free, deriving
     from `F_side_identity_aligned` via the S43 bridge.

Step 2 reduces to a single sorry'd lemma `F_side_identity_aligned`
(parametric in `min`-coordinates, both sums on `(μ\c').cells`), which
is the sole remaining open piece of the GNW route.

**File-size**: Helpers.lean is at 15225 lines after S57.1 (+89 from
15136 after S56).  ~275 lines under the Docker 32GB-memory ceiling
estimate (~15500 lines).  S57.2+ (the bulk of the joint K-induction
in `F_side_identity_aligned`) is likely to push beyond 15500;
extraction into `BallotProblemOQ03OQ01OQ02DoubleRemove.lean` is a
deferred prerequisite for S57.2+ (per S57.0 Option E3).  The natural
extraction boundary is the entire double-removal infrastructure
(S48-S57.1: lines ~5035–5500 for geometric+S52, plus ~14535–14860
for the S57.1 off-spine block, S43 bridges, S53/S54/S55a-dispatcher,
and the S55a/S56 F-side block).

Alternative (deferred): a deterministic weighted-path recasting of GNW
that avoids the exchange step entirely (count weighted walks of every
length, divide by `μ.card · ∏ |strict hook|`); ~400 lines self-contained.
Fallback if S55+ stalls.

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
- `sessions/2026-05-08-s08.md` — Session 53: `gnwProb_exchange_lt_row_of_F_side` algebraic combiner (case 1)
- `sessions/2026-05-08-s09.md` — Session 54: `gnwProb_exchange_lt_col_of_F_side` algebraic combiner (case 2)
- `sessions/2026-05-08-s10.md` — Session 55a: parametric `F_side_identity` + sorry-free `gnwProb_exchange` dispatcher
- `sessions/2026-05-09-s01.md` — Session 56: common-domain `F_side_identity_aligned` + sorry-free `F_side_identity`
- `sessions/2026-05-09-s02.md` — Session 57.0: K-induction strategy + cell-partition + (S1)-(S7) sublemma plan
- `sessions/2026-05-09-s03.md` — Session 57.1: off-spine structural invariances under c'-removal (3 lemmas, sorry-free)
- `sessions/2026-05-09-s04.md` — Session 57.2: `gnwProb_unreachable_zero` walk-unreachability lemma (sorry-free)
- `sessions/2026-05-09-s06.md` — Session 57.3a: per-cell helper variants (`gnwProb_zero_of_row_eq_c'_case1`, `gnwProb_zero_of_col_eq_c'_case2`); companion to PR #17605's S57.3 summand lemmas (sorry-free)
- `sessions/2026-05-09-s07.md` — Session 57.4: off-spine `isCorner` invariance + integrand recurrence step (`isCorner_invariant_off_spine_of_c'`, `gnwProb_succ_eq_off_spine_of_c'`; both sorry-free); the inductive step for the (S1) off-spine branch of `F_side_identity_aligned`'s K-induction
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
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:14562` — `c'_notMem_strictHookCells_of_off_spine` (S57.1)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:14588` — `hookLength_invariant_off_spine_of_c'` (S57.1)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:14616` — `strictHookCells_invariant_off_spine_of_c'` (S57.1)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:14656` — `gnwProb_unreachable_zero` (S57.2; sorry-free; closes (S2)/(S3) on the unreachable branches via case-1 arm-of-c' / case-2 leg-of-c')
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:14722` — `gnwProb_zero_of_row_eq_c'_case1` (S57.3a, sorry-free; per-cell vanishing for arbitrary `x` with `x.1 = c'.1` — companion to PR #17605's `sum_gnwProb_arm_of_c'_eq_zero_case1`)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:14742` — `gnwProb_zero_of_col_eq_c'_case2` (S57.3a, sorry-free; per-cell vanishing for arbitrary `x` with `x.2 = c'.2` — companion to PR #17605's `sum_gnwProb_leg_of_c'_eq_zero_case2`)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:14775` — `isCorner_invariant_off_spine_of_c'` (S57.4, sorry-free; the fourth off-spine structural invariance: `isCorner (μ\c') x ↔ isCorner μ x` for `x.1 ≠ c'.1 ∧ x.2 ≠ c'.2`)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:14830` — `gnwProb_succ_eq_off_spine_of_c'` (S57.4, sorry-free; off-spine integrand recurrence step: assuming K-step IH on `x`'s strict hook, derive (K+1)-step at `x`)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:14719` — `gnwProb_exchange_lt_row_of_F_side`
  (S53 combiner, sorry-free conditional on F-side identity, case `c.1 < c'.1`)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:14814` — `gnwProb_exchange_lt_col_of_F_side`
  (S54 combiner, sorry-free conditional on F-side identity, case `c'.1 < c.1`)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:14900` — `F_side_identity_aligned`
  (S56, sorry-bearing, both sums on `(μ\c').cells` — sole open sorry on the GNW route)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:14929` — `F_side_identity`
  (S55a; sorry-free as of S56, derives from `F_side_identity_aligned` via `sum_gnwProb_eq_removeCorner_cells`)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:14955` — `gnwProb_exchange`
  (S55a, sorry-free, dispatches via `distinct_corners_dichotomy` to S53/S54 combiners, transitive on `F_side_identity_aligned`)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:14993` — `gnwProb_key`
  (proved modulo `gnwProb_exchange` and `isCorner_removeCorner_of_ne`; `gnwProb_exchange` itself is sorry-free as of S55a)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:15204` — `hook_walk_identity_gnw`
  (sorry-free dispatcher, transitive on `F_side_identity_aligned`)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:15243` — `strictHookCells_off_spine_class_at_c'`
  (S57.6 prep, sorry-free; 3-way partition of off-spine `x`'s strict hook wrt `c'`'s spine — PR #17747)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:15295` — `gnwProb_eq_on_leg_class_case1`
  (S57.6 prep 2, sorry-free; K-step IH equality on the case-1 vanishing crossing class — this PR)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:15333` — `gnwProb_eq_on_arm_class_case2`
  (S57.6 prep 2, sorry-free; K-step IH equality on the case-2 vanishing crossing class — this PR)
