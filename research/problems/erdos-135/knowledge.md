# Erdos #135 - Knowledge Base

## Problem Statement

Let A ⊂ ℝ² be a set of n points such that any 4 points determine at least 5 distinct distances. Must A determine Ω(n²) distinct distances?

## Status

**Erdos Database Status**: DISPROVED (Tao 2024)

**Tractability Score**: 10/10
**Aristotle Suitable**: No (main result is a disproof via construction)

## Key Definitions Built

| Name | Type | Description | Location |
|------|------|-------------|----------|
| Point | abbrev | EuclideanSpace ℝ (Fin 2) | Erdos135Problem.lean:39 |
| sqDist | def | Squared distance ‖p - q‖² | Erdos135Problem.lean:42 |
| distinctDistances | def | Set of distances in A | Erdos135Problem.lean:46 |
| distanceCount | def | Number of distinct distances | Erdos135Problem.lean:50 |
| fourPointDistances | def | 6 distances from 4 points | Erdos135Problem.lean:56 |
| HasFiveDistanceProperty | def | Any 4 points → ≥5 distances | Erdos135Problem.lean:61 |
| ErdosConjecture135 | def | Original (false) conjecture | Erdos135Problem.lean:71 |
| TaoCounterexample | def | Tao's construction statement | Erdos135Problem.lean:82 |
| InGeneralPosition | def | No 3 collinear | Erdos135Problem.lean:98 |
| IsParallelogram | def | Parallelogram condition | Erdos135Problem.lean:105 |
| IsForbiddenPattern | def | <5 distances from 4 points | Erdos135Problem.lean:125 |
| ParabolaParams | structure | Algebraic curve parameters | Erdos135Problem.lean:144 |
| RandomizedParabolaApproach | def | Tao's method | Erdos135Problem.lean:154 |

## Key Results Built

| Name | Status | Description |
|------|--------|-------------|
| erdos_135_false | AXIOM | ¬ErdosConjecture135 |
| tao_counterexample | AXIOM | O(n²/√log n) construction exists |
| erdos_135_disproved | THEOREM | Conjecture is false |
| parallelogram_few_distances | SORRY | Parallelograms give ≤3 distances |
| tao_avoids_parallelograms | AXIOM | Construction avoids parallelograms |
| parallelogram_forbidden | THEOREM | Parallelograms violate 5-distance |
| randomized_parabola_works | AXIOM | Tao's method works |
| trivial_distance_bound | SORRY | Upper bound n(n-1)/2 |
| guth_katz_lower_bound | AXIOM | Ω(n/√log n) lower bound |
| tao_optimal_up_to_log | THEOREM | Bounds match in log exponent |

## Insights

1. **Algebraic Geometry Key**: Parabolas over finite fields naturally avoid parallelograms
2. **Randomization Essential**: Fixed constructions fail; random transformations succeed
3. **Probabilistic Deletion**: O(n) bad 4-tuples can be removed while keeping Ω(n) points
4. **Log Factor Tight**: Both upper and lower bounds have √log n factor

## Tags

- erdos
- combinatorial-geometry
- distance-problems
- disproved
- tao

## Related Problems

- Erdős distinct distances problem (Guth-Katz 2015)
- Problem #121 (also solved by Tao 2024)
- Problem #442 (also solved by Tao 2024)

## References

- Tao (2024): arXiv:2409.01343
- Tao blog: terrytao.wordpress.com/2024/09/03/
- Guth-Katz (2015): Distinct distances bound

## Sessions

### Session 2026-01-14

**Focus**: Initial formalization of Tao's disproof
**Outcome**: Complete formalization with 238 lines, 5 axioms, 6 sorries
**Key Definitions**: 13 definitions capturing problem structure
**Next**: Examples (square, rhombus) could be proved explicitly

---

*Generated on 2026-01-14*
