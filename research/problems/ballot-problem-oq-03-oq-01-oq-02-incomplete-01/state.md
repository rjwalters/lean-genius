# Current State

**Phase**: ACT
**Since**: 2026-05-03T20:13:11+02:00
**Iteration**: 3

## Current Focus

Proving `gnwProb_key` (GNW 1979 KEY theorem) — the SOLE remaining sorry in
`BallotProblemOQ03OQ01OQ02Helpers.lean` (line 13872). This sorry blocks
`hook_walk_identity_gnw`, which is needed for the ≥10×10 non-rectangular case of the
Hook-Length Formula.

## State of origin/main (as of 2026-05-03, commit c538eb09968)

All supporting lemmas now proved (PR #15288, merged):
- `strictHookCells` definition (Finset.Ico + image)
- `strictHookCells_mem`, `strictHookCells_card`, `strictHookCells_nonempty`, `strictHookCells_hookLen_lt`
- `gnwProb`: noncomputable definition
- `gnwProb_sum_corners`: Sigma_c gnwProb(c,K,x) = 1 for x in mu, K >= hookLen(x) **PROVED**
- `hookLength_isCorner_one`: corners have hookLength = 1 **PROVED**
- `gnwProb_step`: gnwProb(K+1,x) = gnwProb(K,x) for K >= hookLen(x) **PROVED**
- `gnwProb_stable`: gnwProb(K,x) = gnwProb(hookLen(x),x) for K >= hookLen(x) **PROVED**
- `hook_walk_identity_gnw`: complete (calls gnwProb_key) **PROVED modulo gnwProb_key**

**File**: BallotProblemOQ03OQ01OQ02Helpers.lean, 13,898 lines

## Mathematical Analysis of gnwProb_key

Statement: `Sigma_{x in mu} gnwProb mu c (hookLength x) x = hookProd(mu) / hookProd(mu\c)`

### Base Case (|mu|=1): hookLen(c)=1, gnwProb=1, ratio=1. TRIVIAL.

### Rectangle Case (single corner c):
- gnwProb_sum_corners with corners(mu)={c} gives gnwProb(mu,c,K,x) = 1 for all x
- Sum = |mu|
- hookProd(mu)/hookProd(mu\c) = |mu| by hook_walk_identity_rectYD

### Non-Rectangle Case (multiple corners, |mu|>=3):
Non-rectangular Young diagrams have >=2 corners.
Requires the GNW 1979 exchange argument.

**Key observation**: The naive exchange identity is FALSE:
gnwProb_mu(c,K,x) ≠ gnwProb_{mu\c'}(c,K,x) in general.
Counterexample: mu={(0,0),(0,1),(1,0)}, c=(1,0), c'=(0,1), x=(0,0):
  - mu: gnwProb = 1/2 (H*(0,0)={(0,1),(1,0)}, uniform)
  - mu\c': gnwProb = 1 (H*(0,0)={(1,0)}, forced)

The actual GNW 1979 proof is more subtle. Required infrastructure:
1. preHook(c) = arm-row + leg-col cells of c in mu
2. hookProd ratio = Pi_{y in preHook(c)} hookLen(y)/(hookLen(y)-1)
3. Induction on |mu| with exchange argument (~200-300 Lean lines)

## Blockers

- GNW 1979 exchange argument: requires reading the paper carefully
- No shortcut: hook_walk_identity cannot be proved independently (it IS the HLF)
- Estimated effort: 200-300 lines of non-trivial Lean formalization

## Next Action

1. Read GNW 1979 paper to understand the exchange argument
2. Consider Aristotle submission (HARD sorry with known proof)
3. Alternatively: prove rectangle case via gnwProb_sum_corners + hook_walk_identity_rectYD
   as a partial contribution before tackling non-rectangle case

## Attempt Counts

- Total attempts: 2
- Current approach attempts: 2
- Approaches tried: 2 (GNW induction sketch, direct exchange identity -- FALSE)
