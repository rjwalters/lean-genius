# Erdős #929 - Knowledge Base

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

Let $k\geq 2$ be large and let $S(k)$ be the minimal $x$ such that there is a positive density set of $n$ where\[n+1,n+2,\ldots,n+k\]are all divisible by primes $\leq x$.

Estimate $S(k)$ - in particular, is it true that $S(k)\geq k^{1-o(1)}$?



It follows from Rosser's sieve that $S(k)> k^{1/2-o(1)}$.

It is trivial that $S(k)\leq k+1$ since, for example, one can take $n\equiv 1\pmod{(k+1)!}$. The best bound on large gaps between primes due to Ford, Green, Konyagin, Maynard, and Tao \cite{FGKMT18} (see [4]) implies\[S(k) \ll k \frac{\log\log\log k}{\log\log k\log\log\log\log k}.\]




References


[FGKMT18] Ford, Kevin and Green, Ben and Konyagin, Sergei and Maynard, James and Tao, Terence, Long gaps between primes. J. Amer. Math. Soc. (2018), 65-105.


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
- Problem #2
- Problem #4
- Problem #928
- Problem #930
- Problem #39
- Problem #1

## References

- Er76d
- FGKMT18

## Current State

- **File**: `proofs/Proofs/Erdos929Problem.lean` (387 lines)
- **Sorries**: 0
- **Axioms**: 2 (rosser_lower, fgkmt_upper — deep published results)
- **Theorems**: ~22

## Session 2026-03-25 (Session 1) - Prove sorry + eliminate axiom

**Mode**: REVISIT (RICH knowledge, score 19)
**Outcome**: completed (1S+3A → 0S+2A)

### What I Did
- Proved `smoothBlockSet_pos_density` (sorry → theorem): the AP {M*t+1} ⊆ smoothBlockSet gives density ≥ 1/(2M) > 0
  - Created `ap_count_bound`: AP elements inject into the filter, giving card ≥ t+1
  - Used `le_csInf` on the limsup defining set with by_contra argument
  - Key arithmetic: 1/(2M) ≤ (N₀+1)/(M*(N₀+1)+1) via `div_le_div_of_nonneg_left`
- Proved `smooth_threshold_2` (axiom → theorem): S(2) = 3 via Nat.find_eq_iff
  - Created `smoothBlockSet_two_empty_of_le_one`: sets empty for x ≤ 1 (minFac bounds)
  - Created `smoothBlockSet_two_two_sub_zero`: set ⊆ {0} for x = 2 (odd consecutive argument)
  - Created `upperDensity_singleton_zero`: {0} has density 0 via limsup_le_of_le + 1/(N+1) → 0

### Key Findings
- `le_csInf` (not `le_limsup_of_le`) is the way to bound limsup from below: provide nonemptiness + lower bound for the defining set
- `Filter.eventually_map.mp` converts `∀ᶠ in f.map u` to `∀ᶠ in f` (not `rw [Filter.eventually_map]`)
- omega needs `dsimp` first for beta-reduction of function application terms
- `mul_left_cancel₀` + explicit `Nat.factorial_ne_zero` for AP injectivity
- `div_le_div_iff` and `div_le_iff` NOT available in Lean 4.26.0/Mathlib — use `div_le_div_of_nonneg_left` + `field_simp` instead
- `le_antisymm h1 hprime.two_le` closes minFac = 2 contradiction cleanly
- `exact_mod_cast Nat.factorial_pos _` converts `0 < M` (Nat) to `1 ≤ ↑M` (ℝ)

### Files Modified
- `proofs/Proofs/Erdos929Problem.lean` (224→387 lines, -1 sorry, -1 axiom, +8 theorems)
- `src/data/proofs/erdos-929/meta.json` (axiomCount 3→2, lineCount 224→387)
- `src/data/research/problems/erdos-929.json` (knowledge updated)

### Next Steps
- Problem complete — 0 sorries, 2 deep axioms (Rosser sieve + FGKMT)
- No further work possible without sieve theory infrastructure in Mathlib

---

*Generated from erdosproblems.com on 2026-01-15*
