# Research State: ballot-problem-oq-03-oq-01-oq-02

## Current State
**Phase**: ACT (GNW exchange-step framework wired up)
**Path**: full
**Since**: 2026-04-21T20:08:44+02:00
**Last Updated**: 2026-05-07
**Iteration**: 43

## Current Focus
Close `gnwProb_exchange` (Helpers, line 13871) — the GNW 1979 exchange identity
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
- Total attempts: 43 (sessions 1–43; sessions 1–4 archived to
  `sessions/`; sessions 5–43 in `knowledge.md`)
- Current approach attempts: 7 (sessions 37–43 on GNW)
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

## Blockers
- **`gnwProb_exchange` proof.** This is the GNW 1979 hook-weight shift argument.
  The proof requires showing that hookProd and the gnwProb sum transform
  predictably when one corner c' is removed. Estimated ~100 lines of careful
  case analysis on arm/leg of c vs c'.
- **Build verification.** Helpers file is at 14126 lines; whether it
  type-checks under Docker's 32GB memory limit (post-modularization) is
  not yet confirmed in this session. CI will verify the PR.

## Next Action
**ACT — prove `gnwProb_exchange`.**

1. Decompose `μ.cells = (removeCorner μ c').cells ∪ {c'}` and split the LHS sum
   into the c' contribution + the rest.
2. For x ≠ c', relate `gnwProb μ c (h(x)) x` to `gnwProb (μ\c') c (h(x)) x`
   by analyzing how `strictHookCells x` changes when c' is removed
   (changes only when x is in the arm/leg of c').
3. The hook lengths satisfy:
   - `h_{μ\c'}(r,c'.2) = h_μ(r,c'.2) - 1` for r < c'.1 (leg of c')
   - `h_{μ\c'}(c'.1,s) = h_μ(c'.1,s) - 1` for s < c'.2 (arm of c')
   - `h_{μ\c'}(x) = h_μ(x)` elsewhere
4. The product
   `H(μ)·H((μ\c')\c) = H(μ\c)·H(μ\c')` follows from a careful tally of the
   doubly-affected cell `(c'.1,c.2)` (or similar boundary cells if c, c'
   are adjacent in the appropriate sense).

Alternative: a deterministic weighted-path recasting of GNW that avoids the
exchange step entirely (count weighted walks of every length, divide by
`μ.card · ∏ |strict hook|`); ~400 lines self-contained.

## References

- `literature/closing-the-final-sorry.md` — three-route comparison (session 33)
- `knowledge.md` §Session 35 — modularization decision and split
- `knowledge.md` §Session 37 — GNW infrastructure: `gnwProb`, `gnwProb_sum_corners`
- `knowledge.md` §Session 38 — `gnwProb_step` and stability
- `knowledge.md` §Session 40-42 — single-corner case proof, exchange framework
- `knowledge.md` §Session 43 — strong induction wrapper (this session)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:13871` — `gnwProb_exchange`
  (sorry'd, target of next session)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:13884` — `gnwProb_key`
  (proved modulo `gnwProb_exchange`)
