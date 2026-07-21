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
- k=3 DONE (`no_four_equidistant_indices`), k=0 DONE (`degree_three_equilateral_impossible`),
  k=2 DONE (`degree_three_rhombus_impossible`).
- k=1 OPEN (same Gram-system inner-product method; forces `b=a√3`, then 5th point `w` has no
  consistent position).
Then 2-regular ⟹ C₅ ⟹ regular pentagon ⟹ concyclic ⟹ contradiction with NoFourConcyclic.

## Attempt Count
- See knowledge.md session log.

## Blockers
Full 2-regularity requires ruling out short-degree 3 in all sub-cases (only k=1 remains);
pure graph theory does not force C₅ — each sub-case needs the geometric fifth point.

## Next Action
Prove the k=1 sub-case: a degree-3 vertex `v` whose neighbours `x,y,z` have exactly one
`a`-edge among them (say `dist x y = a`, `dist x z = dist y z = b`) — so `{v,x,y}` is
equilateral of side `a` and `z` sits off it.  Mirror `degree_three_rhombus_impossible`, BUT
NOTE the Gram system here is DIFFERENT: `⟪uₓ,u_y⟫=a²/2`, `⟪uₓ,u_z⟫=⟪u_y,u_z⟫=a²−b²/2`, and
`det Gram = 0` gives `(a²−b²/2)² = ¾a⁴`, i.e. **`b² = (2±√3)a²`** (verified numerically —
both signs realizable), NOT `b²=3a²`.  So the k=1 obstruction is a genuine two-branch case:
extract the explicit linear relation among `uₓ,u_y,u_z` (its coefficients now depend on which
√3 branch), then contradict on the forced inner products of `u_w` in each branch.  Harder than
k=0/k=2 because `b²` is a quadratic irrational in `a²`; may need `nlinarith` with the
`(a²−b²/2)²=¾a⁴` relation rather than a clean `b²=3a²` substitution.  After k=1: short-degree
∈ {1,2}, and by the `a↔b` symmetry the same family excludes b-degree 3, giving full
2-regularity ⟹ C₅.
