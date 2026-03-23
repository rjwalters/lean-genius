# Erdős #1055 - Knowledge Base

## Problem Statement

Forum
Favourites
Tags
More
 Go
 Go
Dual View
Random Solved
Random Open

A prime $p$ is in class $1$ if the only prime divisors of $p+1$ are $2$ or $3$. In general, a prime $p$ is in class $r$ if every prime factor of $p+1$ is in some class $\leq r-1$, with equality for at least one prime factor.

Are there infinitely many primes in each class? If $p_r$ is the least prime in class $r$, then how does $p_r^{1/r}$ behave?



A classification due to Erd\H{o}s and Selfridge. It is easy to prove that the number of primes $\leq n$ in class $r$ is at most $n^{o(1)}$.

The sequence $p_r$ begins $2,13,37,73,1021$ (A005113 in the OEIS). Erd\H{o}s thought $p_r^{1/r}\to \infty$, while Selfridge thought it quite likely to be bounded.

A similar question can be asked replacing $p+1$ with $p-1$.

This is problem A18 in Guy's collection \cite{Gu04}.




References


[Gu04] Guy, Richard K., Unsolved problems in number theory. (2004), xviii+437.


Back to the problem

## Status

**Erdős Database Status**: OPEN

**Tractability Score**: 4/10
**Aristotle Suitable**: No

## Tags

- erdos

## Related Problems

- Problem #2000
- Problem #83
- Problem #888
- Problem #1998
- Problem #1054
- Problem #1056
- Problem #2
- Problem #39
- Problem #1

## References

- Er77
- Gu04

## Sessions

### Session 2026-03-23 (Session 1) - WF Migration: 0 Sorries

**Mode**: FRESH (revisit of existing formalization)
**Outcome**: completed

#### What I Did
- Fixed the sorry in `primeClassWF_ge_succ_factor` (key lower bound theorem)
  - Root cause: dite/ite mismatch between WF definition and helper theorems
  - Solution: `congr` tactic bridges definitional equality; `simp only []` unfolds lets without normalizing filter predicates; `simp_all` + `rename_i` closes isEmpty contradictions
- Migrated `primeClass` from fuel-based `primeClassAux 30` to well-founded `primeClassWF`
- Proved `class_of_factor_lt` (was sorry due to fuel convergence)
- Rewrote `class_one_iff_smooth` and `primeClass_pos_of_prime` for WF definition
- Removed dependency on `primeClassAux` (kept definition but unused)

#### Key Findings
- The dite/ite gap (WF needs `dite` for termination proof, helpers use `ite`) is bridged by `congr` which treats them as definitionally equal
- `simp only []` (empty simp set) effectively unfolds `let` bindings without normalizing `!=` to `decide (¬·)`, preserving filter predicate matching
- Fuel-based definitions fundamentally cannot prove convergence in general

#### Files Modified
- `proofs/Proofs/Erdos1055Problem.lean` — 0 sorries, 4 axioms, 36 theorems, 305 lines
- `src/data/proofs/erdos-1055/meta.json` — Updated line count, theorem count, sections
- `src/data/research/problems/erdos-1055.json` — Updated knowledge, phase

#### Next Steps
- Consider proving `class_density_subpolynomial` (Erdős stated it as "easy to prove")
- Remove `primeClassAux` entirely (now unused after migration)

---

*Generated from erdosproblems.com on 2026-01-15*
