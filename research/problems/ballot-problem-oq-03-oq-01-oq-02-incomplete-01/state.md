# Current State

**Phase**: ACT
**Since**: 2026-05-04T00:00:00Z
**Iteration**: 5

## Current Focus

Proving `gnwProb_key` (GNW 1979 KEY theorem) — sole remaining sorry in
`BallotProblemOQ03OQ01OQ02Helpers.lean`. One sorry remains after session 40.

## Session 40 Progress (2026-05-04)

Proved `h_ratio_card` (117 lines) in PR `fix/ballot-gnw-key` (#15599).

### Single-Corner Case: FULLY PROVED (pending Docker build verification)
- **gnwProb = 1 everywhere**: PROVED (session 39)
- **Hook ratio = μ.card**: PROVED via 117-line `h_ratio_card` proof

#### h_ratio_card proof strategy:
1. `rowLen(0) = c.2+1`: Corner at bottom of last column = c → rowLen(0)-1 = c.2
2. `colLen(0) = c.1+1`: Corner at end of last row = c → colLen(0)-1 = c.1
3. Uniform rowLen/colLen: anti-monotone squeezing gives rowLen(r) = c.2+1 for r ≤ c.1,
   colLen(s) = c.1+1 for s ≤ c.2. (colLen_anti proved inline via contradiction.)
4. hookLength formulas: h(c.1, s) = c.2-s+1 (for s < c.2), h(r, c.2) = c.1-r+1 (for r < c.1)
5. Products telescope via `prod_div_telescope`: arm=c.2+1, leg=c.1+1
6. Rectangle card: `μ.cells = range(c.1+1) ×ˢ range(c.2+1)`, so μ.card = (c.1+1)*(c.2+1)
7. Assembly: `hookProd_ratio_formula hc` + arm/leg prods + push_cast + ring

### Multi-Corner Case: SORRY (line 14024)
- Requires GNW 1979 exchange argument (~150-200 lines)
- The pointwise exchange F_x(mu,c) = F_x(mu\c',c) is FALSE (L-shape counterexample)
- Need the TOTAL sum exchange using hookProd ratio invariance

## State of PR `fix/ballot-gnw-key` (#15599, 2026-05-04)

Commits: e36e8a7b8a, 344e1d5f8d, 414a62ae67

**File**: BallotProblemOQ03OQ01OQ02Helpers.lean, ~14,035 lines

## Blockers

**Sorry 1** (multi-corner GNW exchange, line 14024):
- GNW 1979 exchange argument: ~150-200 lines
- Strategy: pick c' ∈ corners(mu)\{c}. By induction: F(mu\c', c) = hookProd(mu\c')/hookProd(mu\{c,c'})
  Show F(mu,c) = F(mu\c',c) using hookProd ratio invariance (already proved as hookProd_ratio_invariance?)
- Need to check if `hookProd_ratio_invariance` lemma exists in Helpers

## Potential Build Issues in h_ratio_card

- `push_cast [show s ≤ c.2 from by omega]` — must handle Nat.cast_sub correctly
- `field_simp` after `prod_div_telescope` — may need explicit `div_one`
- `simp only [Prod.fst, Prod.snd]` alignment with `hookProd_ratio_formula hc` output

## Next Action

1. **Verify Docker build** of PR #15599 — fix any type errors in h_ratio_card
2. **Multi-corner case**: check if hookProd_ratio_invariance exists, then write exchange argument
3. **Consider Aristotle submission** for multi-corner case (HARD sorry, known GNW 1979 proof)

## Attempt Counts

- Total attempts: 5
- Current approach attempts: 5
- Approaches tried: 5 (GNW sketch, direct exchange FALSE, partial proof, case split, rectangle proof)
