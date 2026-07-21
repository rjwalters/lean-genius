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
  k=2 DONE (`degree_three_rhombus_impossible`), **k=1 DONE (`degree_three_isosceles_impossible`,
  this session)**. ALL FOUR SUB-CASES NOW PROVED axiom-free (docker-verified).
Then 2-regular ⟹ C₅ ⟹ regular pentagon ⟹ concyclic ⟹ contradiction with NoFourConcyclic.

## Attempt Count
- See knowledge.md session log.

## Blockers
Full 2-regularity now requires only the ASSEMBLY of the four sub-case lemmas (all proved) into
"no short-degree-3 vertex" + the `a↔b` symmetry; then the C₅ endgame. Pure graph theory does
not force C₅ — each sub-case needed (and now has) the geometric fifth point.

## Next Action
1. **Assemble degree-3 exclusion.** Prove "no short-degree-3 vertex" by combining the four
   sub-case lemmas (`degree_three_{equilateral,isosceles,rhombus}_impossible` for k=0,1,2 and
   `no_four_equidistant_indices` for k=3). The three neighbour pairs `{xy,xz,yz}` each carry an
   `a`- or `b`-edge; `k = #{a-edges} ∈ {0,1,2,3}` is exhaustive. For each `k`, permute
   `x,y,z` so the odd-one-out pair matches the lemma's hypotheses (k=1: the single a-edge is
   `xy`; k=2: the single b-edge is `yz`), and the 5th point `w` (the non-neighbour of `v`, at
   `dist b`) feeds `hwx/hwy/hwz`. Careful: need to also identify which vertex is `w` (the one
   of the 5 not in `{v,x,y,z}`) and that its distances to `x,y,z` lie in `{a,b}` (two-distance
   set). Output: a lemma `¬ (∃ vertex of a-degree 3)`.
2. **`a↔b` symmetry.** b-degree = 4 − a-degree (each vertex has 4 others, `card_fiber_dist_le_three`
   bounds both). The SAME four lemmas with `a,b` swapped exclude b-degree 3, so a-degree 1 (⟺
   b-degree 3) is also excluded ⟹ every a-degree = 2 ⟹ short-graph is 2-regular.
3. **C₅ endgame.** 2-regular on 5 vertices ⟹ single 5-cycle ⟹ metric realization forces a
   regular pentagon ⟹ its 5 vertices concyclic ⟹ contradicts `NoFourConcyclic`. Closes `h 5 ≥ 3`.
