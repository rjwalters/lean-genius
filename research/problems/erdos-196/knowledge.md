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

## Key Definitions Added (Sessions 2026-01-18)

| Name | Type | Description | Location |
|------|------|-------------|----------|
| CanExtendForward | def | 3-AP can extend to 4-AP forward | Erdos196Problem.lean:207 |
| CanExtendBackward | def | 3-AP can extend to 4-AP backward | Erdos196Problem.lean:213 |
| IsNonExtendable3AP | def | 3-AP cannot be extended either way | Erdos196Problem.lean:218 |
| ForbiddenForwardValue | def | Value forbidden at later indices | Erdos196Problem.lean:247 |
| ForbiddenBackwardValue | def | Value forbidden at earlier indices | Erdos196Problem.lean:250 |
| count3APs | def | Count 3-APs in finite permutation | Erdos196Problem.lean:282 |
| DensityConjecture | def | Density argument conjecture | Erdos196Problem.lean:289 |
| Finite4APThreshold | def | Finite threshold conjecture | Erdos196Problem.lean:465 |
| IsAP3WithOddCD | def | 3-AP with odd common difference | Erdos196Problem.lean:305 |
| IsAP3WithEvenCD | def | 3-AP with even common difference | Erdos196Problem.lean:309 |
| IsAP4WithOddCD | def | 4-AP with odd common difference | Erdos196Problem.lean:313 |
| IsAP4WithEvenCD | def | 4-AP with even common difference | Erdos196Problem.lean:317 |
| HasMonotone3APOddCD | def | Perm has monotone 3-AP odd CD | Erdos196Problem.lean:321 |
| HasMonotone4APOddCD | def | Perm has monotone 4-AP odd CD | Erdos196Problem.lean:326 |
| HasMonotone4APEvenCD | def | Perm has monotone 4-AP even CD | Erdos196Problem.lean:331 |
| HasMonotone3APEvenCD | def | Perm has monotone 3-AP even CD | Erdos196Problem.lean:406 |

## Key Results Added (Session 2026-01-18 continued)

| Name | Status | Description |
|------|--------|-------------|
| every_perm_has_3ap_odd_cd | AXIOM | LeSaulnier-Vijay: every perm has odd-CD 3-AP |
| exists_perm_avoiding_4ap_odd_cd | AXIOM | LeSaulnier-Vijay: can avoid odd-CD 4-APs |
| ap4_odd_cd_iff_ap3_odd_cd | PROVED | 4-AP has odd CD iff its 3-AP prefix has odd CD |
| conjecture_equiv_even_cd_forced | PROVED | Conjecture ⟺ avoiding odd-CD 4-APs forces even-CD 4-APs |
| forbidden_even_cd_extension | PROVED | Even-CD 3-APs forbid specific forward extensions |
| forbidden_even_cd_backward | PROVED | Even-CD 3-APs forbid specific backward extensions |
| ap4_parity_dichotomy | PROVED | Every 4-AP has either odd or even common difference |

## Insights

1. **Boundary Case**: k=4 is the critical threshold - k=3 proved, k=5 disproved
2. **Implication Structure**: 4-AP conjecture would imply 3-AP theorem as corollary
3. **DEGS Construction**: Counterexample for k=5 uses interleaving increasing/decreasing segments
4. **Erdos-Szekeres Connection**: Guarantees long monotone subsequences but not AP structure
5. **Non-Extendability**: If a permutation avoids 4-APs, every 3-AP must be non-extendable
6. **Forbidden Values**: Each 3-AP (a, a+d, a+2d) forbids value a+3d at later indices
7. **Density Approach**: Conjecture that forbidden value constraints accumulate to force 4-AP
8. **Compactness**: If finite threshold exists for permutations of [1,n], infinite case follows
9. **Common Difference Parity (NEW)**: The conjecture reduces to even-CD case - LeSaulnier-Vijay showed odd-CD 4-APs CAN be avoided
10. **Critical Reformulation (NEW)**: Conjecture ⟺ "avoiding odd-CD 4-APs forces even-CD 4-APs"

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

### Session 2026-01-18 (continued)

**Mode**: REVISIT research iteration
**Focus**: Common difference parity structure

**What I Did**:
- Researched LeSaulnier-Vijay (2011) results on common difference parity
- Added full infrastructure for odd/even common difference analysis
- Proved key theorem: conjecture is equivalent to "avoiding odd-CD 4-APs forces even-CD 4-APs"
- Added 10 new definitions for parity-based analysis
- Proved 5 new theorems including constraint propagation lemmas

**Key Mathematical Insight**:
LeSaulnier-Vijay (2011) showed:
1. Every permutation of ℕ MUST contain a 3-term AP with ODD common difference
2. There EXIST permutations of ℕ avoiding ALL 4-term APs with ODD common difference

This means odd-CD 4-APs can be avoided! The conjecture thus reduces to:
**"Can even-CD 4-APs also be avoided?"**

Proved `conjecture_equiv_even_cd_forced`:
```
Erdős196Conjecture ⟺ ∀ x, ¬HasMonotone4APOddCD x → HasMonotone4APEvenCD x
```

**Files Modified**:
- proofs/Proofs/Erdos196Problem.lean (expanded to 505+ lines)
- research/problems/erdos-196/knowledge.md (this file)

**Outcome**: PROGRESS - identified that even-CD case is the critical remaining question

**Next Steps**:
1. Investigate whether even-CD 4-APs can be avoided (potential counterexample)
2. Explore interaction between odd-CD 3-APs and even-CD 4-APs
3. Consider whether LeSaulnier-Vijay construction creates even-CD 4-APs
4. Try to prove constraint accumulation argument for even-CD case

**References Consulted**:
- LeSaulnier-Vijay (2011) - "On permutations avoiding arithmetic progressions"
- arXiv:1004.1740 - Related constructions
- Discrete Mathematics 2024 (Adenwalla) - Recent improvements

---

*Last updated: 2026-01-18*
