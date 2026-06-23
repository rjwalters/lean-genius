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

## Session 2026-03-28 (Session 4, researcher-2) - Axiom Elimination

**Mode**: REVISIT (AXIOM HUNT)
**Outcome**: AXIOM ELIMINATION — 10 axioms → 7 axioms

### What I Did
- Converted `numSubgroups` from axiom to noncomputable def: `Fintype.card (Subgroup (Equiv.Perm (Fin n)))`
- Proved `instFiniteSubgroupPerm`: Finite instance for Subgroup type via injection into Finset G
- Proved `numSubgroups_pos`: uses `Fintype.card_pos` (⊥ : Subgroup G always exists)
- Proved `trivial_upper`: injection Subgroup → Finset → card_finset gives 2^|G| = 2^(n!)
- Added imports: GroupTheory.Subgroup.Finite, Data.Fintype.Card, Data.Finset.Powerset

### Key Findings
- Subgroup G is Finite for finite G: each subgroup maps injectively to `Finset.univ.filter (· ∈ H)`
- `Fintype.card_finset` gives `|Finset G| = 2^|G|` and `Fintype.card_perm` gives `|Perm (Fin n)| = n!`
- Making numSubgroups a proper definition enables proving downstream facts from the Fintype API
- Docker was not available; build not verified

### Files Modified
- `proofs/Proofs/Erdos1162Problem.lean` (187 → 223 lines, 10 → 7 axioms, 4 → 6 theorems)
- `src/data/proofs/erdos-1162/meta.json` (updated counts)
- `src/data/research/problems/erdos-1162.json` (updated knowledge)

### Remaining Axioms (7)
1. `roney_dougal_tracey` — Deep 2025 published result (KEEP)
2. `numSubgroupsElem2` — Opaque enumeration function (KEEP)
3. `elem2_subgroup_count_asymptotic` — Deep Gaussian binomial result (KEEP)
4. `f1 : numSubgroups 1 = 1` — Small case, possibly provable with native_decide
5. `f2 : numSubgroups 2 = 2` — Small case
6. `f3 : numSubgroups 3 = 6` — Computationally expensive
7. `f4 : numSubgroups 4 = 30` — Computationally expensive
