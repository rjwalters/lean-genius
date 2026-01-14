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
| degs_3ap_theorem | AXIOM | DEGS 1977: every perm has monotone 3-AP |
| degs_5ap_counterexample | AXIOM | DEGS 1977: exists perm avoiding monotone 5-AP |
| finite_3ap_threshold | AXIOM | Finite version threshold N <= 9 |
| erdos_szekeres_theorem | AXIOM | Related monotone subsequence theorem |

## Insights

1. **Boundary Case**: k=4 is the critical threshold - k=3 proved, k=5 disproved
2. **Implication Structure**: 4-AP conjecture would imply 3-AP theorem as corollary
3. **DEGS Construction**: Counterexample for k=5 uses interleaving increasing/decreasing segments
4. **Erdos-Szekeres Connection**: Guarantees long monotone subsequences but not AP structure

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

---

*Generated on 2026-01-14*
