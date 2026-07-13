# Multi-Candidate Ballot Problem - Research Knowledge

## Problem
Given m ≥ 2 candidates where candidate 0 receives `a` votes and all opponents
receive a combined `b` votes (a > b), prove that the probability candidate 0
leads all opponents combined throughout the counting is (a-b)/(a+b).

## Key Insight
The "leads all combined" property depends ONLY on the ±1 projection (leader → +1,
opponent → -1), not on how opponent votes are distributed. This reduces the
multi-candidate problem to the classical 2-candidate ballot theorem.

## Proof Architecture (9 parts)

1. **Projection** (proved): `project leader s` maps multi-candidate → ±1
2. **Prefix Sums** (proved): `prefixSum`, `leadsAllThroughout`, `project_sum_eq`
3. **Invariance** (proved): `leadsAllThroughout_of_same_projection` — KEY theorem
4. **Fin Candidates** (proved): Concrete instantiation with `Fin m`
5. **Mathlib Connection** (3 sorries): `project_mem_countedSequence` via count lemmas
6. **Ballot Bounds** (proved): Formula ∈ [0, 1]
7. **Fiber Uniformity** (1 sorry): Each fiber has multinomial size b!/(a₁!...aₘ₋₁!)
8. **Classical Reference** (proved): `#check Ballot.ballot_problem`
9. **Examples** (proved): Concrete numerical verifications

## Remaining Sorries (3)

| Sorry | Type | Difficulty |
|-------|------|-----------|
| `project_count_one` | List counting | Easy (API friction with List.count/BEq) |
| `project_count_neg_one` | List counting | Easy (follows from above) |
| `fiber_same_leader_positions` | getElem reasoning | Medium (getElem bounds transport) |

## Mathlib API Notes

- `Ballot.ballot_problem` uses `ProbabilityTheory.uniformOn`, NOT `condCount`
- `List.count_map` doesn't exist — must use manual induction
- `List.count_cons` uses `decide`-based `BEq`, resistant to omega/simp
- `getElem` bounds don't transport through `congrArg` when lists change — use `getElem?`

## Related Files
- `proofs/Proofs/BallotProblem.lean` — Classical ballot (Wiedijk #30, complete)
- `proofs/Proofs/BallotProblemOQ01.lean` — k-fold ballot generalization
- `proofs/Proofs/BallotProblemOQ03.lean` — LGV lemma (lattice paths)
