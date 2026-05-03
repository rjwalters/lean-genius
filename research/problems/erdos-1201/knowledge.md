# Erdős #1201 - Knowledge Base

## Problem Statement

Is it true that for every $\epsilon,\eta>0$ there exists a $k$ such that the density of $n$ for which\[P(n(n+1)\cdots(n+k))>n^{1-\epsilon}\]is at least $1-\eta$ (where $P(m)$ is the greatest prime divisor of $m$)? Erdős wrote he could prove this for $\epsilon=1/2$.## Status

**Erdős Database Status**: OPEN

**Tractability Score**: 5/10
**Aristotle Suitable**: No

## Tags

- erdos

## Related Problems

- Problem #337
- Problem #2000
- Problem #62
- Problem #2
- Problem #1200
- Problem #1202
- Problem #39
- Problem #1

## References

- (None available)

## Sessions

## Session 2026-05-03 (Session 1) — Gallery Entry Completed

**Mode**: FRESH
**Outcome**: completed

### What I Did
- Discovered that `Erdos1201Problem.lean` was already on `origin/main` (added in PR #15109)
- Gallery entry `src/data/proofs/erdos-1201/meta.json` existed but was missing `annotations.json` and `index.ts`
- Created `annotations.json` with 9 annotations covering all 6 proof sections
- Created `index.ts` with gallery exports
- Updated research JSON to status: completed, phase: COMPLETED
- Committed and pushed to `feature/researcher-11` (bundled with PR #14961)

### Key Findings
- Lean formalization: 266 lines, 14 structural theorems, 1 axiom (`erdos_1201_half_case`), 0 sorries
- `ErdosProblem1201` (full conjecture) is a `def`, not axiomatized — correct, it's the open question
- `gpfConsecutive_large_of_prime_dvd` is the key structural lemma: a prime p > n^(1-ε) in the window witnesses the density condition
- The ε=1/2 axiom is justified: Erdős proved it using Dickman function arguments, but those are not in Mathlib
- The main open gap: smooth number theory (Dickman ρ function) missing from Mathlib prevents proving ε=1/2 from scratch

### Files Modified
- `src/data/proofs/erdos-1201/annotations.json` — new (9 annotations)
- `src/data/proofs/erdos-1201/index.ts` — new
- `src/data/research/problems/erdos-1201.json` — status/phase updated to COMPLETED

### Next Steps
None — gallery entry is complete. Future sessions could:
1. Prove the ε=1/2 result (requires Dickman ρ function formalization, ~500+ lines)
2. Add Sylvester-Schur lower bound as a structural theorem: gpfConsecutive n k ≥ k+1 for n ≥ k+1

---

*Generated from erdosproblems.com on 2026-04-16*
