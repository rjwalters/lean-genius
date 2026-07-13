# Current State

**Phase**: ACT
**Since**: 2026-05-04T00:00:00Z
**Iteration**: 6

## Current Focus

Proving `gnwProb_key` (GNW 1979 KEY theorem) — sole remaining sorry in
`BallotProblemOQ03OQ01OQ02Helpers.lean`. Single-corner case proved (PR #15599).
Multi-corner case blocked pending cross-product identity proof.

## Session 41 Progress (2026-05-04)

**Mathematical structure fully analyzed**. Key findings:

### Equivalence Triangle

gnwProb_key (multi-corner) ⟺ HWI (hook walk identity) ⟺ HLF (hook-length formula).

All three are equivalent given:
- `card_SYT_corner_step` (SYT corner recursion, proved)
- `hook_length_formula_Q` uses well-founded recursion requiring HWI for same size μ
- HWI = Σ_c H(μ)/H(μ\c) = |μ| follows from gnwProb_key for all corners

The GNW walk probabilities are the ONLY non-circular bridge.

### Cross Product Identity (key to multi-corner case)

For corners c₁, c₂ of μ:
F(μ,c₁) * F(μ\c₁,c₂) = F(μ,c₂) * F(μ\c₂,c₁)

where F(μ,c) = Σ_{x∈μ} gnwProb(μ,c,h(x),x).

**Verified**: L-shape (3/2)*(2) = (3/2)*(2) = 3 ✓, shape(3,1) (8/3)*(3/2) = (4/3)*(3) = 4 ✓.

**Consequence**: From cross product identity + IH (gnwProb_key for smaller diagrams):
- F(μ,c₁)/F(μ,c₂) = H(μ\c₂)/H(μ\c₁) [ratio is inverse hookProd ratio]
- F(μ,c) = α/H(μ\c) for constant α = |μ|!/|SYT(μ)|
- To get α = H(μ): need |SYT(μ)| = |μ|!/H(μ) = HLF for μ (CIRCULAR)

### Why Induction Fails Directly

1. **Pointwise exchange FALSE**: gnwProb(μ,c,h_μ(x),x) ≠ gnwProb(μ\c',c,h_{μ\c'}(x),x).
   L-shape counterexample: μ={(0,0),(0,1),(1,0)}, c=(1,0), c'=(0,1), x=(0,0): 1/2 ≠ 1.

2. **Hook ratio NOT invariant**: H(μ)/H(μ\c) ≠ H(μ\c')/H(μ\{c,c'}).
   L-shape: 3/2 ≠ 2.

3. **Corner count not monotone**: removing corner c' can create new corners.
   Shape (3,2): removing c'=(1,1) creates new corner (1,0). The topmost corner
   (r₁,s₁) with r₁>0 always creates new corner (r₁-1,s₁) since rowLen(r₁-1)=s₁+1.

### What the GNW Proof Needs

The cross product identity + a non-circular determination of α = H(μ).

One path: prove the cross product identity by induction on |μ| using the walk recursion
(expanding F via gnwProb_step/stable), and simultaneously prove α = H(μ) via a mutual
induction with hook_length_formula_Q. But the mutual induction structure needs care.

## State of PR `fix/ballot-gnw-key` (#15599, 2026-05-04)

Commits: e36e8a7b8a, 344e1d5f8d, 414a62ae67, c7a1fd9569

**File**: BallotProblemOQ03OQ01OQ02Helpers.lean, ~14,050 lines

### Single-Corner Case: FULLY PROVED (pending Docker build)
- **gnwProb = 1 everywhere**: PROVED (session 39)
- **Hook ratio = μ.card**: PROVED (117-line h_ratio_card, session 40)

### Multi-Corner Case: SORRY (line 14024)
- Requires cross product identity + alpha determination

## Blockers

**Sorry 1** (multi-corner GNW exchange, line 14024):
- Cross product identity: ~50-80 lines
- Alpha determination / closing: ~50-100 lines
- Total: ~150-200 lines
- Strategy: induction on |μ| using walk recursion, cross product as bridge
- Aristotle submission blocked by `/-!` docstrings in 14050-line file

## Next Action

1. **Verify Docker build** of PR #15599 (single-corner case)
2. **Prove cross product identity** F(μ,c₁)*F(μ\c₁,c₂) = F(μ,c₂)*F(μ\c₂,c₁) by
   induction on |μ| — this is the pure mathematical heart of GNW 1979
3. **Alpha determination** using cross product + HLF for μ (if mutual induction succeeds)
4. **Aristotle**: Create companion file with just gnwProb_key after fixing docstring issue

## Attempt Counts

- Total attempts: 6
- Current approach attempts: 2 (direct exchange, cross product identity)
- Approaches tried: 6 (GNW sketch, direct exchange FALSE, partial proof, case split, rectangle proof, equivalence analysis)
