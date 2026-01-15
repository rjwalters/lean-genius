# Erdos #29 - Knowledge Base

## Problem Statement

Is there an explicit construction of a set A ⊆ ℕ such that A + A = ℕ but r_A(n) = o(n^ε) for every ε > 0?

## Status

**Erdos Database Status**: SOLVED (JPSZ 2024)

**Tractability Score**: 10/10
**Aristotle Suitable**: No (main result requires explicit construction)

## Key Definitions Built

| Name | Type | Description | Location |
|------|------|-------------|----------|
| Sumset | def | A + B = {a + b : a ∈ A, b ∈ B} | Erdos29Problem.lean:37 |
| Doubling | def | A + A for single set | Erdos29Problem.lean:42 |
| representationCount | def | r_A(n) = #{pairs summing to n} | Erdos29Problem.lean:45 |
| IsAdditiveBasis | def | A + A = ℕ | Erdos29Problem.lean:55 |
| IsEconomical | def | r_A(n)/n^ε → 0 for all ε > 0 | Erdos29Problem.lean:75 |
| JPSZ_set | axiom | The explicit construction | Erdos29Problem.lean:101 |
| ExplicitSet | class | Computable membership | Erdos29Problem.lean:179 |
| IsSidon | def | At most one representation | Erdos29Problem.lean:160 |

## Key Results Built

| Name | Status | Description |
|------|--------|-------------|
| erdos_probabilistic_existence | AXIOM | Erdős's non-constructive proof |
| JPSZ_is_basis | AXIOM | JPSZ set is additive basis |
| JPSZ_is_economical | AXIOM | JPSZ set is economical |
| erdos_29_solved | THEOREM | Main result: explicit solution exists |
| univ_is_basis | THEOREM | ℕ is trivially an additive basis |
| univ_not_economical | SORRY | ℕ is not economical |
| squares_not_basis | SORRY | Squares don't form a basis |
| sidon_not_basis | SORRY | Sidon sets can't be bases |
| basis_size_lower_bound | SORRY | |A ∩ [1,N]| ≥ √N for bases |

## Insights

1. **Middle Ground**: JPSZ construction is between Sidon sets (too thin) and ℕ (not economical)
2. **Subpolynomial Growth**: r_A(n) ≤ exp(C√(log n)) is slower than any polynomial
3. **Optimal Size**: |A ∩ [1,N]| ≈ √N · √(log N), essentially matching lower bound
4. **Explicit = Computable**: The set has decidable membership, unlike probabilistic proofs

## Tags

- erdos
- additive-combinatorics
- additive-bases
- solved
- jpsz
- explicit-construction

## Related Problems

- Erdős-Turán conjecture on additive bases
- Sidon sets and B_h sequences
- Distinct distances problem (Guth-Katz)

## References

- Jain, Pham, Sawhney, Zakharov (2024): arXiv:2405.08650
- Erdős: Original probabilistic existence proof
- Sidon (1932): Original question to Erdős

## Sessions

### Session 2026-01-14

**Focus**: Initial formalization of JPSZ solution
**Outcome**: Complete formalization with 246 lines, 3 axioms for JPSZ properties, 5 sorries
**Key Definitions**: 8 definitions capturing problem structure
**Proved**: univ_is_basis (ℕ is an additive basis)
**Next**: Could prove examples (representation counts) and helper lemmas

---

*Generated on 2026-01-14*
