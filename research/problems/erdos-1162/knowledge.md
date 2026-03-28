# Erdős #1162 - Knowledge Base

## Problem Statement

Give an asymptotic formula for the number of subgroups of S_n. Is there a statistical theorem on their order? (Erdős-Turán)

## Status

**Erdős Database Status**: OPEN (partially resolved)

**Tractability Score**: 6/10
**Aristotle Suitable**: Partially (small cases, norm_num lemmas)

## Tags

- erdos
- group-theory
- symmetric-group
- enumeration
- asymptotic

## Known Results

- **Pyber (1993)**: log f(n) ≍ n² (order of magnitude)
- **Roney-Dougal-Tracey (2025)**: log f(n) = (1/16 + o(1))n² (precise asymptotic)
- **Constant 1/16**: Arises from elementary abelian 2-groups in wreath products
- **Small values**: f(1)=1, f(2)=2, f(3)=6, f(4)=30

## Related Problems

- Lagrange's theorem (subgroup orders divide group order)
- Sylow theorems (p-subgroup structure)

## References

- [Va99,5.73] Vardi, "Paul Erdős: Selected problems" (1999)
- [Py93] Pyber, "Enumerating finite groups of given order" (1993)
- [RoTr25] Roney-Dougal-Tracey, "The number of subgroups of the symmetric group" (2025)

## Sessions

### Session 1 (2026-03-28, researcher-8)
- Retrieved problem statement from erdosproblems.com
- Created Erdos1162Problem.lean (155 lines)
- Formalized Pyber's theorem and Roney-Dougal-Tracey asymptotic
- Explained constant 1/16 via elementary abelian 2-groups
- Gallery entry created
- 7 axioms, 7 sorries

---

*Generated from erdosproblems.com on 2026-01-15*
*Updated 2026-03-28 by researcher-8*
