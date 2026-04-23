# Selection Report: erdos-73

**Date**: 2026-04-23
**Mode**: SELECT
**Pool Status**: 84 available, 1257 in-progress, 589 completed

## Selected Problem

- **ID**: erdos-73
- **Name**: Erdős Problem #73: Almost Bipartite Graphs (Reed's Theorem Extensions)
- **Tier**: B
- **Significance**: 7/10
- **Tractability**: 6/10
- **Knowledge Score**: 0 (EMPTY)
- **Composite Score**: 67
- **Status**: available

## Selection Rationale

1. **EMPTY knowledge score** (highest priority tier): no research workspace yet
2. **Graph theory domain** is fresh — no recent selections from this area
3. **Clear extension path**: gallery proof is axiomatized with 3 known axioms; OQ-A (growth rate of f(k)) is well-defined
4. **Non-trivial but bounded**: partial progress (weak bounds, literature survey) is achievable even without full axiom removal
5. **Diversity**: spans combinatorics/structural graph theory, complementing recent algebra/analysis selections

## Rejection Summary

- **Candidates considered**: 18 uninitialized available problems
- **Candidates rejected**: 15 (geometry domain penalty, lower tractability, or near-duplicates)
- **Confidence**: medium (3 tied candidates at score=67; graph theory domain chosen for diversity)

## Related Gallery Proofs

- `erdos-73`: Direct parent (axiomatized Reed's theorem, 3 axioms)
- `erdos-476`: Related Erdős graph coloring problem

## Suggested First Steps

1. **OBSERVE**: Read `proofs/Proofs/Erdos73Problem.lean` — identify the 3 axioms and what they encode
2. **ORIENT**: Scout for Reed 1999 "Mangoes and Blueberries" and known bounds on f(k)
3. **DECIDE**: Choose between (a) literature survey documenting f(k) bounds, or (b) attempt to prove a weak bound like f(k) ≤ 2k² that could replace `reed_bound`

## Caution

The 3 axioms encode Reed's probabilistic argument (Lovász Local Lemma-style). Full axiom
removal is a research-months task. The realistic goal is:
- Document the state of art for f(k) growth
- Prove a weak combinatorial bound if possible
- Explore if OQ-C (polynomial algorithm) can be formalized

## Initialized

- [x] Research workspace created
- [x] problem.md populated
- [ ] Ready for /researcher
