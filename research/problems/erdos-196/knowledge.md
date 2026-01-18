# Erdos #196 - Knowledge Base

## Problem Statement

Must every permutation of the natural numbers contain a monotone 4-term arithmetic progression?

## Status

**Erdos Database Status**: OPEN

**Tractability Score**: 5/10
**Aristotle Suitable**: No (OPEN problem)

## Key Definitions Built

| Name | Type | Description | Location |
|------|------|-------------|----------|
| Permutation | def | Bijection N -> N | Erdos196Problem.lean:33 |
| IsAP3 | def | 3-term AP predicate | Erdos196Problem.lean:70 |
| IsAP4 | def | 4-term AP predicate | Erdos196Problem.lean:50 |
| IsAP5 | def | 5-term AP predicate | Erdos196Problem.lean:74 |
| HasMonotone3AP | def | Permutation has monotone 3-AP | Erdos196Problem.lean:86 |
| HasMonotone4AP | def | Permutation has monotone 4-AP | Erdos196Problem.lean:92 |
| HasMonotone5AP | def | Permutation has monotone 5-AP | Erdos196Problem.lean:98 |
| Erdos196Conjecture | def | Main conjecture statement | Erdos196Problem.lean:106 |

## Key Results Built

| Name | Status | Description |
|------|--------|-------------|
| ap4_iff_ap4' | PROVED | Two AP4 definitions equivalent |
| conjecture_implies_3ap | PROVED | 4-AP conjecture implies 3-AP theorem |
| no_4ap_implies_nonextendable | PROVED | Avoiding 4-AP means all 3-APs non-extendable |
| forbidden_value_constraint | PROVED | Each 3-AP forbids specific values at later indices |
| degs_3ap_theorem | AXIOM | DEGS 1977: every perm has monotone 3-AP |
| degs_5ap_counterexample | AXIOM | DEGS 1977: exists perm avoiding monotone 5-AP |
| finite_3ap_threshold | AXIOM | Finite version threshold N <= 9 |
| erdos_szekeres_theorem | AXIOM | Related monotone subsequence theorem |
| finite_threshold_implies_conjecture | SORRY | If finite threshold exists, conjecture follows |

## Key Definitions Added (Session 2026-01-18)

| Name | Type | Description | Location |
|------|------|-------------|----------|
| CanExtendForward | def | 3-AP can extend to 4-AP forward | Erdos196Problem.lean:207 |
| CanExtendBackward | def | 3-AP can extend to 4-AP backward | Erdos196Problem.lean:213 |
| IsNonExtendable3AP | def | 3-AP cannot be extended either way | Erdos196Problem.lean:218 |
| ForbiddenForwardValue | def | Value forbidden at later indices | Erdos196Problem.lean:247 |
| ForbiddenBackwardValue | def | Value forbidden at earlier indices | Erdos196Problem.lean:250 |
| count3APs | def | Count 3-APs in finite permutation | Erdos196Problem.lean:282 |
| DensityConjecture | def | Density argument conjecture | Erdos196Problem.lean:289 |
| Finite4APThreshold | def | Finite threshold conjecture | Erdos196Problem.lean:301 |

## Insights

1. **Boundary Case**: k=4 is the critical threshold - k=3 proved, k=5 disproved
2. **Implication Structure**: 4-AP conjecture would imply 3-AP theorem as corollary
3. **DEGS Construction**: Counterexample for k=5 uses interleaving increasing/decreasing segments
4. **Erdos-Szekeres Connection**: Guarantees long monotone subsequences but not AP structure
5. **Non-Extendability (NEW)**: If a permutation avoids 4-APs, every 3-AP must be non-extendable
6. **Forbidden Values (NEW)**: Each 3-AP (a, a+d, a+2d) forbids value a+3d at later indices
7. **Density Approach (NEW)**: Conjecture that forbidden value constraints accumulate to force 4-AP
8. **Compactness (NEW)**: If finite threshold exists for permutations of [1,n], infinite case follows

## Tags

- erdos
- combinatorics
- permutations
- arithmetic-progressions

## Related Problems

- Problem #194
- Problem #195

## References

- Davis, Entringer, Graham, Simmons (1977): "Monotone subsequences and arithmetic progressions"

## Sessions

### Session 2026-01-14

**Focus**: Initial formalization
**Outcome**: Complete formalization with 230+ lines, 4 axioms for known results, 2 proved theorems
**Next**: Consider explicit DEGS counterexample construction

### Session 2026-01-18

**Mode**: FRESH research iteration
**Focus**: Creative mathematical work on this OPEN problem

**What I Did**:
- Researched DEGS 1977 paper and current state of problem
- Confirmed k=4 is genuinely OPEN (not just unformalised)
- Developed "non-extendability" framework for analyzing 4-AP avoiding permutations
- Proved two new lemmas: `no_4ap_implies_nonextendable`, `forbidden_value_constraint`
- Added 8 new definitions to support density argument approach
- Formulated `Finite4APThreshold` and `DensityConjecture` as potential paths forward

**Key Mathematical Insight**:
If π avoids all monotone 4-APs, then every 3-AP (a, a+d, a+2d) with increasing indices
(i < j < k) forbids the value a+3d from appearing at ANY index > k. This constraint
grows with the number of 3-APs. Potential proof strategy:
1. Show number of 3-APs grows as Θ(n²) or faster in any long permutation
2. Each 3-AP creates a distinct forbidden value constraint
3. Eventually constraints exceed available "slots", forcing contradiction

**Files Modified**:
- proofs/Proofs/Erdos196Problem.lean (expanded from 227 to 340+ lines)
- research/problems/erdos-196/knowledge.md (this file)

**Outcome**: PROGRESS - substantial new infrastructure for attacking this OPEN problem

**Next Steps**:
1. Prove lower bound on number of 3-APs in permutations of [1,n]
2. Formalize the density counting argument
3. Investigate computational search for finite threshold
4. Consider alternative: try to construct 4-AP avoiding permutation

**References Consulted**:
- Davis et al. (1977) - Original DEGS paper
- arXiv:1803.06334 - "Forbidden arithmetic progressions in permutations"
- arXiv:2012.12339 - Recent improvements on k=5,6 case
- Discrete Mathematics 2024 - "Avoiding monotone APs in permutations of integers"

---

*Last updated: 2026-01-18*
