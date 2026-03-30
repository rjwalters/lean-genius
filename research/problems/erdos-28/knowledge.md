# Erdős #28 - Knowledge Base

## Problem Statement

If $A\subseteq \mathbb{N}$ is such that $A+A$ contains all but finitely many integers then $\limsup 1_A\ast 1_A(n)=\infty$. Conjectured by Erdős and Turán. They also suggest the stronger conjecture that $\limsup 1_A\ast 1_A(n)/\log n>0$. Another stronger conjecture would be that the hypothesis $\lvert A\cap [1,N]\rvert \gg N^{1/2}$ for all large $N$ suffices. Erdős and Sárközy conjectured the stronger version that if $A=\{a_1[40]. This is discussed in problem C9 of Guy's collection [Gu04]. View the LaTeX source This page was last edited 18 November 2025.

## Status

**Erdős Database Status**: OPEN
**Prize**: $500
**Tractability Score**: 4/10
**Aristotle Suitable**: No

## Tags

- erdos

## Related Problems

- Problem #337
- Problem #2000
- Problem #2
- Problem #40
- Problem #27
- Problem #29
- Problem #39
- Problem #1

## References

- ErTu41
- Er56
- Er57
- Er59
- Er61
- Er65
- Er65b
- Er69
- Er70c
- Er73
- Er77c
- ErGr80
- Er81
- Er85c
- Er89d
- Er90
- Er94b
- Er95
- Er97c
- Er97f
- Gu04

## Sessions

### Session 2026-03-29 (researcher-2) — Axiom Elimination in Erdos28Problem.lean

**Mode**: REVISIT (AXIOM HUNT)
**Outcome**: AXIOM ELIMINATION — 6 axioms → 5 in Erdos28Problem.lean

#### What Was Done
- Proved `basis_counting_lower` as a theorem (was axiom)
- Fixed incorrect statement: original said `∀ N ≥ 1`, which fails when A has no elements below threshold
- Corrected to `∃ N₁, ∀ N ≥ N₁, 4 * (countingFn A N + 1) ^ 2 ≥ N`
- Proof: standard counting argument (sums from A∩[0,N] cover [T+1,N], count pairs ≤ |A∩[0,N]|²)
- Unified threshold extraction via `Set.Finite.toFinset.sup id` (handles empty/nonempty complement)

#### Key Findings
- `basis_counting_lower` was unused by any other theorem — safe to change signature
- Original `∀ N ≥ 1` form is incorrect: A = {0} ∪ {n≥100} is a basis but countingFn A 1 = 0
- `average_rep_unbounded` axiom is likely incorrectly stated (average for thin basis ≈ O(1), not → ∞)
- Remaining 5 axioms in Problem file: 3 are OPEN conjectures ($500), 2 are deep published theorems

#### Files Modified
- `proofs/Proofs/Erdos28Problem.lean` (117 → 180 lines, 6 → 5 axioms, 2 → 3 theorems)

---

*Generated from erdosproblems.com on 2026-01-12*
