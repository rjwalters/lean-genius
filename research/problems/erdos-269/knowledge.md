# Erdős #269 - Knowledge Base

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

Let $P$ be a finite set of primes with $\lvert P\rvert \geq 2$ and let $\{a_1<a_2<\cdots\}=\{ n\in \mathbb{N} : \textrm{if }p\mid n\textrm{ then }p\in P\}$. Is the sum\[\sum_{n=1}^\infty \frac{1}{[a_1,\ldots,a_n]},\]where $[a_1,\ldots,a_n]$ is the lowest common multiple of $a_1,\ldots,a_n$, irrational?



If $P$ is infinite this sum is always irrational (in \cite{Er88c} Erd\H{o}s says this is a 'simple exercise').

This problem was asked by Erd\H{o}s in a letter to the editor written January 1st 1973 in issue 12 of the Fibonacci Quarterly, 1974, p. 335. In that letter he says that he can prove the sum is irrational if duplicate summands are removed.




References


[Er88c] Erd\"{o}s, P., On the irrationality of certain series: problems and results. New advances in transcendence theory (Durham, 1986) (1988), 102-109.


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
- Problem #268
- Problem #270
- Problem #2
- Problem #39
- Problem #1

## References

- Er88c

## Sessions

### 2026-06-06 (researcher-1) — Session 7: Mathlib v4.26 build repair

**Mode**: VERIFY/REPAIR
**Outcome**: Docker build clean (7743/7743 jobs); 1 build-breaking error + 1 deprecation + 4 unused-variable warnings resolved.

#### Context

Per state.md, Erdos269Problem.lean is graduated (completed 2026-03-24). After previous-session work (PR #13317 added `pow_isPSmooth`), Mathlib v4.26 introduced an API drift that broke the file. The error was a build failure, not just warnings — so this is repair, not just hygiene.

#### Build-breaking error fixed

Line 84: `Unknown constant Nat.pos_pow_of_pos`. The lemma was renamed/removed in Mathlib v4.26. Replaced `Nat.pos_pow_of_pos k hp.pos` with `pow_pos hp.pos k` — `pow_pos : 0 < a → 0 < a^n` is the modern equivalent and works for any `n : ℕ` (the original signature required `1 ≤ k` but `pow_pos` does not).

Side effect: the `hk : 1 ≤ k` hypothesis in `pow_isPSmooth` is now unused. Kept for backwards compatibility (callers may pass it) but underscored to `_hk` to silence the lint.

#### Other warnings fixed

- `not_le_of_lt hp.one_lt` → `not_le_of_gt hp.one_lt` (line 55, deprecation).
- Unused-variable warnings silenced via underscore prefix (`_p` on line 54, `_hP` on line 109, `_hPrime` and `_hCard` on line 190). These preserve the theorem signatures while silencing the Lean 4.26 `linter.unusedVariables` linter.

#### File status (S7 end)

- 303 lines (unchanged), 15 theorems, 9 defs, 3 axioms (the open conjecture + 2 variants), 0 sorries.
- Status `axiomatized` (correct per axiom-integrity policy).
- All Mathlib v4.26 warnings eliminated.

#### Honest assessment

Build-repair work, not mathematical progress. The Erdős 269 conjecture (P-smooth LCM series irrationality) remains OPEN. Lasting value: the file builds cleanly on Mathlib v4.26 and the graduation status is preserved.

---

*Generated from erdosproblems.com on 2026-01-12*
