# Erdos #140 - Knowledge Base

## Problem Statement

Let r_3(N) be the size of the largest subset of {1,...,N} which does not contain a non-trivial 3-term arithmetic progression. Prove that r_3(N) << N/(log N)^C for every C > 0.

## Status

**Erdos Database Status**: SOLVED (Kelley-Meka 2023)

**Tractability Score**: 10/10
**Aristotle Suitable**: No (main theorem axiomatized as deep proof)

## Key Definitions Built

| Name | Type | Description | Location |
|------|------|-------------|----------|
| IsAP3 | def | 3-term AP: 2b = a + c, a < b < c | Erdos140Problem.lean:36 |
| Is3APFree | def | Set has no 3-APs | Erdos140Problem.lean:39 |
| Finset3APFree | def | Finset has no 3-APs | Erdos140Problem.lean:43 |
| r3 | def | Roth number r_3(N) | Erdos140Problem.lean:50 |
| RothBound | def | Roth's o(N) bound | Erdos140Problem.lean:63 |
| KelleyMekaTheorem | def | Main theorem statement | Erdos140Problem.lean:98 |
| greedyAP3Free | def | Greedy 3-AP-free sequence | Erdos140Problem.lean:167 |
| rk | def | k-term AP Roth number | Erdos140Problem.lean:178 |
| ErdosAPConjecture | def | General k-AP conjecture | Erdos140Problem.lean:182 |

## Key Results Built

| Name | Status | Description |
|------|--------|-------------|
| roth_theorem | AXIOM | r_3(N) = o(N) |
| roth_explicit_bound | AXIOM | r_3(N) <= C*N/log(log N) |
| bourgain_bound | AXIOM | r_3(N) = O(N/sqrt(log log N)) |
| sanders_bound | AXIOM | r_3(N) = O(N(log log N)^5/log N) |
| bloom_sisask_bound | AXIOM | r_3(N) = O(N/(log N)^{1+c}) |
| kelley_meka | AXIOM | r_3(N) = O(N/(log N)^C) for all C |
| erdos_140_solved | THEOREM | Main theorem proof |
| r3_superlogarithmic | SORRY | Corollary: o(N/(log N)^C) |
| r3_density_vanishes | SORRY | Density tends to 0 |
| behrend_lower_bound | AXIOM | r_3(N) >= N*exp(-c*sqrt(log N)) |
| greedy_is_3APFree | AXIOM | Greedy sequence is 3-AP-free |
| erdos_ap_conjecture_k3 | SORRY | k=3 case of general conjecture |

## Insights

1. **Historical Progress**: 70 years from Roth (1953) to Kelley-Meka (2023)
2. **Breakthrough Method**: New density increment arguments
3. **Gap Remains**: Upper bound O(N/(log N)^C) vs Lower bound N*exp(-c*sqrt(log N))
4. **Open for k>=4**: The conjecture for longer APs remains open

## Tags

- erdos
- additive-combinatorics
- arithmetic-progressions
- density
- roth-theorem

## Related Problems

- Problem #228 (4-term APs)
- Problem #261 (k-term AP density)

## References

- Roth, K.F. (1953): "On certain sets of integers"
- Kelley, Z., Meka, R. (2023): "Strong bounds for 3-progressions"
- Bloom, T., Sisask, O. (2020): "Breaking the logarithmic barrier"
- Behrend, F.A. (1946): Lower bound construction

## Sessions

### Session 2026-01-14

**Focus**: Initial formalization of Kelley-Meka theorem
**Outcome**: Complete formalization with 217 lines, 9 axioms, 7 sorries
**Key Definitions**: IsAP3, r3, KelleyMekaTheorem, historical bounds
**Next**: Examples and corollaries could use proof search

---

*Generated on 2026-01-14*
