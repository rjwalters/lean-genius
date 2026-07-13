# Erdős #456 - Knowledge Base

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

Let $p_n$ be the smallest prime $\equiv 1\pmod{n}$ and let $m_n$ be the smallest integer such that $n\mid \phi(m_n)$.

Is it true that $m_n<p_n$ for almost all $n$? Does $p_n/m_n\to \infty$ for almost all $n$? Are there infinitely many primes $p$ such that $p-1$ is the only $n$ for which $m_n=p$?



Linnik's theorem implies that $p_n\leq n^{O(1)}$. It is trivial that $m_n\leq p_n$ always.

If $n=q-1$ for some prime $q$ then $m_n=p_n$. Erd\H{o}s \cite{Er79e} writes it is 'easy to show' that for infinitely many $n$ we have $m_n <p_n$, and that $m_n/n\to \infty$ for almost all $n$.

van Doorn in the comments has noted that if $n=2^{2k+1}$ then $m_n\leq 2n$ and $p_n\geq 2n+1$.




References


[Er79e] Erd\H{o}s, Paul, Some unconventional problems in number theory. Ast\'{e}risque (1979), 73-82.


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
- Problem #455
- Problem #457
- Problem #2
- Problem #39
- Problem #1

## References

- Er79e

## Sessions

### Session 1 (2026-04-27) — Mathlib API Drift Confirmed (Build Blocked)

**Mode**: REVISIT (claimed RICH, score 29)
**Outcome**: BLOCKED — file does not build on `origin/main` due to a removed Mathlib module

#### Build Verification
Ran `LEAN_MEMORY_LIMIT=6144 ./proofs/scripts/docker-build.sh Proofs.Erdos456Problem`. The build fails before any Lean code in this repo is checked:

```
error: no such file or directory (error code: 2)
  file: .lake/packages/mathlib/Mathlib/Data/Rat/Order.lean
error: Proofs/Erdos456Problem.lean: bad import 'Mathlib.Data.Rat.Order'
```

`Mathlib.Data.Rat.Order` no longer exists in Mathlib (likely merged into `Mathlib.Data.Rat.Basic` or similar in the same 2026-04-26 upgrade cohort that broke `Erdos1151OQ04` and `AngleTrisectionOQ02OQ01OQ02Incomplete01`).

Both files have the broken import:
- `proofs/Proofs/Erdos456Problem.lean:38`
- `proofs/Proofs/Erdos456Aristotle.lean:16`

#### State of the Lean Code (when import is restored)
A grep audit of both files shows **0 axiom declarations and 0 sorry instances** (excluding occurrences in comments/docstrings):

- `Erdos456Problem.lean`: 272 lines, 15 theorems, 6 defs, 0 axioms, 0 sorries
- `Erdos456Aristotle.lean`: 83 lines, 3 theorems, 2 defs, 0 axioms, 0 sorries

Both `meta.json` and the `leanFiles` block in the problem JSON are roughly accurate on `axiomCount` and `sorries`, but the `progressSummary` says "2 deep axioms (linnik_bound, m_over_n_diverges)" — this is **stale**. Those axioms were eliminated in earlier sessions; the progressSummary needs updating to reflect that the file is fully verified except for the open conjectures (which are stated as `def Prop`, not as `axiom`).

#### Why I Did Not Fix
Per project memory `project_mathlib_api_drift_2026_04`, removing or renaming a Mathlib import is part of the same upgrade-cohort drift that researchers should not fix in research sessions. The right owner is the Mechanic agent. I have, however, refreshed the JSON metadata where it was clearly stale (separate from the import drift).

#### Files Modified
- `research/problems/erdos-456/knowledge.md` — this entry
- `src/data/research/problems/erdos-456.json` — `progressSummary`, `currentState.blockers`, Session 1 insight

#### Next Steps
1. Mechanic should remove the `Mathlib.Data.Rat.Order` import (and verify nothing in the file depended uniquely on it; ℚ comparisons used in `AlmostAll` may need a replacement import like `Mathlib.Data.Rat.Defs` or the order content reaches via `Mathlib.NumberTheory.LSeries.PrimesInAP`)
2. After build is green: SOLVED-style follow-up — generate strong open questions (e.g., unconditional `mₙ < pₙ` infinitely often via van Doorn for `n = 2^{2k+1}, k ≥ 1` using `3 ∣ 2^{2k+1}+1`, sharpening `part1_implies_infinitely_many` to drop the conjecture hypothesis)
3. Refresh `progressSummary` to drop the stale "2 deep axioms" claim

---

*Generated from erdosproblems.com on 2026-01-13*
