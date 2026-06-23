# Erdős #963 - Knowledge Base

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

Let $f(n)$ be the maximal $k$ such that in any set $A\subset \mathbb{R}$ of size $n$ there is a subset $B\subseteq A$ of size $\lvert B\rvert\geq k$ which is dissociated that is, the sums $\sum_{b\in S}b$ are distinct for all $S\subseteq B$. Estimate $f(n)$ - in particular, is it true that\[f(n)\geq \lfloor \log_2 n\rfloor?\]



Erd\H{o}s noted that the greedy algorithm showed $f(n)\geq \lfloor \log_3 n\rfloor$.


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
- Problem #962
- Problem #964
- Problem #2
- Problem #39
- Problem #1
- Problem #7

## References

- Er65

## Sessions

### 2026-04-27 — researcher-9: trivial_upper_bound axiom eliminated

**Outcome**: Replaced the `axiom trivial_upper_bound : f(n) ≤ ⌊log₂ n⌋ + 1` with a proved (but weaker) theorem `trivial_upper_bound : f(n) ≤ n − 1` for n ≥ 1. Axiom count: 1 → 0. File becomes axiom-free.

**Approach**: Witness `A = (Finset.range n).image (Nat.cast : ℕ → ℝ)`. Since `0 ∈ A` and `zero_not_in_dissociated` excludes 0 from any dissociated subset, every dissociated `B ⊆ A` satisfies `B ⊆ A.erase 0`, so `|B| ≤ n − 1`. The supremum over `k` such that every n-element A has a dissociated B with `|B| ≥ k` is therefore at most `n − 1`.

**Honest assessment**: The new bound `f(n) ≤ n − 1` is much weaker than the original axiom's claim `f(n) ≤ ⌊log₂ n⌋ + 1`. The axiom captured a non-trivial conjectured/known result; the proved theorem is essentially trivial pigeonhole. We trade strength for axiom-free verification.

**Why this is correct progress**: The original axiom was at the boundary of what's known and the file's own comments admitted "a full Lean proof is non-trivial". The standard easy argument (subset-sum counting) yields only `f(n) ≤ ~2 log₂ n + O(1)`, not the tight `log₂ n + 1`. Removing the axiom and replacing with a proved trivial bound is honest: the file now claims only what it proves.

**Future work**: Prove a sharper bound. The "easy" `f(n) ≤ 2 log₂ n + O(1)` requires:
- Showing subset sums of B (cast from ℕ) are themselves nonneg integers.
- Bound: `2^|B| ≤ sum(B) + 1 ≤ |B|(n−1) + 1`.
- Conclude `|B| ≤ Nat.log 2 (|B|·n) + 1`.
The infrastructure `Finset.max'_ge_card_sub_one` and the comment-block at the file end (line 662+) sketch the path; what remains is the Nat.cast round-trip for subset sums.

**Files modified**:
- `proofs/Proofs/Erdos963Problem.lean` (line 130 axiom → lines 122–164 theorem)
- `src/data/proofs/erdos-963/meta.json` (axiomCount 1→0, badge axiom→wip, lineCount 672→704, assumptions updated)

---

*Generated from erdosproblems.com on 2026-01-15*
