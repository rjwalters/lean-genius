# Research State: erdos-98-wip-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-21
**Iteration**: (see knowledge.md session log)

## Current Focus
Lower bound `h 5 ≥ 3` ⟺ no general-position `PointConfig 5` is a two-distance set.
Reduction + degree structure proved; now excluding short-degree-3 vertices sub-case by
sub-case (needs the geometric fifth point).

## Active Approach
Short-distance-graph structure: degree bounds (1–3) + handshake parity ⟹ some vertex has
exactly 2 short neighbours. Pushing toward full 2-regularity by ruling out degree 3.
Degree-3 exclusion splits by `k = #{a-edges among the 3 neighbour pairs}`:
- k=3 DONE (`no_four_equidistant_indices`), k=0 DONE (`degree_three_equilateral_impossible`).
- k=1, k=2 OPEN (same Gram-system inner-product method; both force `b=a√3`, then 5th point
  `w` has no consistent position).
Then 2-regular ⟹ C₅ ⟹ regular pentagon ⟹ concyclic ⟹ contradiction with NoFourConcyclic.

## Attempt Count
- See knowledge.md session log.

## Blockers
Full 2-regularity requires ruling out short-degree 3 in all sub-cases (k=1, k=2 remain);
pure graph theory does not force C₅ — each sub-case needs the geometric fifth point.

## Next Action
Prove the k=2 sub-case: a degree-3 vertex `v` whose neighbours `x,y,z` have exactly one
`a`-pair-... (two `a`-edges, one `b`-edge) — a 60°-rhombus `{v,x,y,z}` forcing `b=a√3` — is
impossible once the fifth point `w` (at `dist b` from `v`) is present. Mirror
`degree_three_equilateral_impossible`: linear-dependence of `uₓ,u_y,u_z` in ℝ² pins the
Gram relations, then contradiction on the forced inner products of `u_w`. Then k=1.
