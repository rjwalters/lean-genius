# Current State

**Phase**: ACT
**Since**: 2026-05-04T00:00:00Z
**Iteration**: 7

## Current Focus

Proving `gnwProb_key` (GNW 1979 KEY theorem) — sole remaining sorry in
`BallotProblemOQ03OQ01OQ02Helpers.lean`. Single-corner case proved (PR #15599, merged).
Multi-corner case structure complete: two named sorries remain.

## Session 42 Progress (2026-05-04)

**Infrastructure added** (PR #15685):

1. `isCorner_removeCorner_of_ne` (PROVED, ~11 lines): distinct corners of μ survive
   removing the other corner. Enables the IH step in GNW induction.

2. `gnwProb_exchange` (NAMED SORRY): the GNW 1979 exchange identity in product form:
   `F(μ,c)·H(μ\c)·H(μ\c') = F(μ\c',c)·H((μ\c')\c)·H(μ)`
   where `F(ν,d) = Σ_{x∈ν} gnwProb(ν,d,h(x),x)` and `H = hookProd`.
   This is the core GNW 1979 step; avoids division. Verified on L-shape and (3,1).

3. **Multi-corner proof structure** (COMPLETE MODULO SORRIES): the algebraic chain
   from gnwProb_exchange + IH to gnwProb_key is fully written out and correct.
   Steps: pick c'≠c, IH on μ\c', rw h_IH_prod into h_exch, cancel H(μ\c'),
   conclude via mul_right_cancel₀.

## Two Remaining Sorries

### Sorry 1: `gnwProb_exchange` (~100 lines)

The GNW 1979 hook-weight shift argument. Key structure:
- For corners c and c' of μ (c.1 > c'.1 since YD corners are anti-ordered):
  c' is in the arm of leg-cell (c.1, c'.2) of c.
- hookLen_μ(c.1, c'.2) = hookLen_{μ\c'}(c.1, c'.2) + 1 (removing c' decreases this arm-cell's hook by 1)
- All other arm/leg cells of c: hook lengths unchanged
- Need: F(μ,c)/F(μ\c',c) = [h_μ(c.1,c'.2) · (h_μ(c.1,c'.2)-2)] / (h_μ(c.1,c'.2)-1)²
  (ratio from the single affected arm cell)
- This requires inducting on the walk recursion to propagate the hook-change

### Sorry 2: Strong induction wrapper (~30 lines)

The `h_IH` sorry in the multi-corner case needs access to an IH.
Current `gnwProb_key` is not set up with induction. Need either:
(a) Restructure gnwProb_key to use `Nat.strong_rec_on` on μ.card, or
(b) Add a separate `gnwProb_key_ind` helper that wraps in strong induction

This is ~30 lines of boilerplate.

## State of PR `feat/ballot-gnw-exchange` (#15685, 2026-05-04)

Commits: 6590609fa8 (plus 4 prior merged in #15599)

### Proved
- gnwProb = 1 everywhere for single-corner (session 39)
- h_ratio_card: single-corner hook ratio = μ.card (session 40, 117 lines)
- isCorner_removeCorner_of_ne (session 42, ~11 lines)

### Remaining Sorries
- gnwProb_exchange: exchange identity (~100 lines)
- IH wrapper for multi-corner: strong induction setup (~30 lines)

## Next Action

1. **Strong induction wrapper** (easier, ~30 lines): restructure gnwProb_key to use
   Nat.strongRecOn, or extract gnwProb_key_ind helper. Should be tractable.
2. **gnwProb_exchange** (harder, ~100 lines): prove hook-weight shift for the single
   affected arm-cell. Key lemma: hookLength_removeCorner_arm already exists at line 4821!
   Check if it gives hookLen_μ(c.1,c'.2) = hookLen_{μ\c'}(c.1,c'.2) + 1.
3. Check `hookLength_removeCorner_arm` (line 4821) and `hookLength_removeCorner_leg` 
   (line 4835) for usability in proving gnwProb_exchange.

## Attempt Counts

- Total attempts: 7
- Current approach attempts: 3 (direct exchange, cross product identity, exchange+IH)
- Approaches tried: 6 + new structured exchange approach
