# Erdős #460 - Knowledge Base

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

Let $a_0=n$ and $a_1=1$, and in general $a_k$ is the least integer $>a_{k-1}$ for which $(n-a_k,n-a_i)=1$ for all $1\leq i<k$. Does\[\sum_{i}\frac{1}{a_i}\to \infty\]as $n\to \infty$? What about if we restrict the sum to those $i$ such that $n-a_j$ is divisible by some prime $\leq a_j$, or the complement of such $i$?



This question arose in work of Eggleton, Erd\H{o}s, and Selfridge, who could prove that $a_k <k^{2+o(1)}$ for $k$ large enough depending on $n$, but conjectured that in fact $a_k\ll k\log k$ is true.


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
- Problem #459
- Problem #461
- Problem #2
- Problem #39
- Problem #1

## References

- Er77c
- ErGr80

## Sessions

(No research sessions yet)

---

*Generated from erdosproblems.com on 2026-01-13*

## Session 2026-07-01 (Session 1) — Repair + Structural Backbone

**Mode**: FRESH (claimed erdos-460-incomplete-01, status blocked)
**Outcome**: progress (file repaired + 6 verified theorems added; main question still OPEN)

### What I Did
- Found the committed `Erdos460Problem.lean` did **not compile** against Mathlib v4.26.0 (13 errors) — the real reason it was `blocked`. Repaired all API-drift breakages:
  - `Nat.minFac_prime` now takes `p ≠ 1` (was given `2 ≤ p`).
  - `Finset.min'_le` takes `(s a h)` explicitly (was given the nonempty proof).
  - Well-founded base cases no longer reduce by `rfl` → `sieve_at_zero`/`sieve_at_one` use `simp [greedyCoprimeSieve]`.
  - `∃`-guarded `Finset.filter`/`if` need a classical `Decidable` instance → `sieveCount`, `smallPrimeDivisibleSum` wrapped `by classical; exact`.
  - `dsimp only []` is now a no-progress error → replaced by an explicit `show` (zeta-inline the `let a`).
- Added Section IX: 6 verified (0-axiom, 0-sorry) structural theorems.

### Key Findings
- `sieve_ge_index` (a_k ≥ k) is the *wrong* direction for divergence (upper-bounds the sum by the harmonic series). Divergence needs an **upper** bound on a_k. Known `a_k < k^{2+o(1)}` ⇒ Σ 1/k^{2+ε} **converges** ⇒ insufficient. Conjectured `a_k ≪ k log k` ⇒ Σ 1/(k log k) diverges. This is the sharp obstruction — #460 is genuinely open.
- The shifted values n − a_i are pairwise coprime (`sieve_pairwise_coprime`), confirming the construction's design.

### Files Modified
- `proofs/Proofs/Erdos460Problem.lean` (327 → 462 lines; +6 theorems; repaired)
- `src/data/proofs/erdos-460/meta.json` (counts, Section IX, contributions)
- `src/data/research/problems/erdos-460.json` (knowledge)

### Verification
- `lake env lean` against full Mathlib v4.26.0: **0 errors**, 1 pre-existing sorry.
- `#print axioms` on all 6 new theorems: only `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no `eggleton_erdos_selfridge`.

### Next Steps
- Formalize the conditional reduction `SieveConjecturedBound → ErdosProblem460` (the real content), needing a Mathlib lemma on divergence of Σ 1/(n log n).
- Use the structural bounds to control `sieveCount n`.
