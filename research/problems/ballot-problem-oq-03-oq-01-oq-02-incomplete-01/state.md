# Current State

**Phase**: ACT
**Since**: 2026-05-04T00:00:00Z
**Iteration**: 4

## Current Focus

Proving `gnwProb_key` (GNW 1979 KEY theorem) — sole remaining sorry in
`BallotProblemOQ03OQ01OQ02Helpers.lean`. Two sorrys remain after this session's work.

## Session 39 Progress (2026-05-04)

Partial proof written in PR `fix/ballot-gnw-key`. Split gnwProb_key into two cases:

### Single-Corner Case (rectangle): PARTIALLY PROVED
- **gnwProb = 1 everywhere**: PROVED via gnwProb_sum_corners
  - corners(mu) = {c} → Finset.sum_eq_single_of_mem + Subtype.ext gives gnwProb = 1
  - Sum = mu.card: proved via sum_congr + sum_const_one
- **Hook ratio = mu.card**: SORRY with detailed sketch
  - By hookProd_ratio_formula: ratio = arm_prod * leg_prod
  - Single-corner implies rowLen(r) = c.2+1 (r ≤ c.1) and colLen(s) = c.1+1 (s ≤ c.2)
  - Proof sketch: strict decrease in rowLen before c.1 → second corner (contradiction)
  - Then hookLength(c.1, s) = c.2-s+1, hookLength(r, c.2) = c.1-r+1
  - prod_div_telescope gives arm_prod = c.2+1, leg_prod = c.1+1
  - (c.2+1)*(c.1+1) = mu.card (counting rectangle cells)
  - Estimated: ~70 Lean lines

### Multi-Corner Case: SORRY
- Requires GNW 1979 exchange argument
- Key insight: H(mu)/H(mu\c) = H(mu\c')/H(mu\{c,c'}) for any corner c'≠c
  (proved above as hookProd ratio invariance)
- Exchange implies F(mu,c) relates to F(mu\c',c) via induction
- Estimated: ~150-200 Lean lines

## State of origin/main (as of 2026-05-04, commit e5282f6792c)

All supporting lemmas proved (previous sessions):
- strictHookCells, gnwProb, gnwProb_sum_corners, gnwProb_step, gnwProb_stable: **PROVED**
- hook_walk_identity_gnw: **PROVED modulo gnwProb_key**

**File**: BallotProblemOQ03OQ01OQ02Helpers.lean, 13,935 lines (after this session)

## Blockers

**Sorry 1** (h_ratio_card, single-corner case):
- Need: single-corner → rowLen/colLen const → hookLength formula → telescoping product
- Available tools: rowLen_anti, colLen_anti (from YoungDiagram), prod_div_telescope
- Obstacle: rectangle lemmas (arm_prod_rectYD etc.) are private in main file, not accessible
- Solution: prove rectangle characterization from scratch in Helpers (~70 lines)

**Sorry 2** (multi-corner case):
- GNW 1979 exchange argument: ~150-200 lines
- Key step: relate F(mu,c) to F(mu\c',c) via hook weight changes
- The pointwise exchange F_x(mu,c) = F_x(mu\c',c) is FALSE (verified by counterexample)
- Need the TOTAL sum exchange, which uses the hookProd ratio invariance

## Next Action

1. **h_ratio_card proof** (~70 lines): prove single-corner → rectangle structure + telescoping
   - Lemma: no strict decrease in rowLen/colLen before c.1/c.2 in single-corner mu
   - Use prod_div_telescope (available in Helpers) to telescope the arm/leg products
   - Counting argument for mu.card = (c.1+1)*(c.2+1)

2. **Multi-corner case** (~150-200 lines): GNW 1979 exchange
   - Consider submitting to Aristotle (HARD sorry, known proof)
   - Or prove directly using the hookProd ratio invariance as a lemma

## Attempt Counts

- Total attempts: 4
- Current approach attempts: 4
- Approaches tried: 4 (GNW sketch, direct exchange FALSE, partial proof structure, current)
