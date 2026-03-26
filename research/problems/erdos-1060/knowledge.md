# Erdős #1060 - Knowledge Base

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

Let $f(n)$ count the number of solutions to $k\sigma(k)=n$, where $\sigma(k)$ is the sum of divisors of $k$. Is it true that $f(n)\leq n^{o(\frac{1}{\log\log n})}$? Perhaps even $\leq (\log n)^{O(1)}$?



This is discussed in problem B11 of Guy's collection \cite{Gu04}.




References


[Gu04] Guy, Richard K., Unsolved problems in number theory. (2004), xviii+437.


Back to the problem

## Status

**Erdős Database Status**: OPEN

**Tractability Score**: 5/10
**Aristotle Suitable**: No

## Tags

- erdos

## Related Problems

- Problem #2000
- Problem #83
- Problem #888
- Problem #1998
- Problem #1059
- Problem #1061
- Problem #2
- Problem #39
- Problem #1

## References

- Gu04

## Sessions

### Session 2026-03-24 (Session 1) - Eliminate All Sorries

**Mode**: FRESH
**Outcome**: progress (3 sorries → 0 sorries)

#### What I Did
- Proved `sigma_mul_coprime`: σ is multiplicative on coprime arguments. Bridge to Mathlib's `ArithmeticFunction.isMultiplicative_sigma` via showing our local `sigma k = (ArithmeticFunction.sigma 1) k`.
- Proved `f_eq_f'`: Bridge between `Set.ncard` and `Finset.card` characterizations of f(n). Key: showed `solutionSet n = ↑((Icc 1 n).filter (fun k => g k = n))` then used `Set.ncard_coe_finset`.
- Proved `mem_A327153_iff`: Characterized OEIS A327153 membership for n > 0. Added hypothesis `n > 0` (original statement was unprovable for n=0). Uses `f_eq_f'` bridge and `Finset.card_pos`.
- Fixed pre-existing `sigma_prime` proof that relied on `simp` which couldn't close `∑ x ∈ {1, p}, x = p + 1`. Used explicit `Finset.sum_insert` + `Finset.sum_singleton` + `omega`.

#### Key Findings
- `Nat.Coprime.divisors_mul` was removed/renamed in Mathlib v4.26.0 - need to use ArithmeticFunction bridge instead
- `sigma_isMultiplicative` → now `ArithmeticFunction.isMultiplicative_sigma`
- `Set.ncard_coe_Finset` → deprecated, use `Set.ncard_coe_finset`
- `Set.Finite` is now `Finite` on the subtype in recent Mathlib

#### Files Modified
- `proofs/Proofs/Erdos1060Problem.lean` (3 sorries → 0, also fixed sigma_prime)

#### Next Steps
- 2 axioms remain (OPEN conjectures - cannot be proved)
- File is now in good shape: 0 sorries, well-structured
- Consider adding more supporting lemmas (e.g., bounds on f for specific n)

### Session 2026-03-26 (Session 2) - Trivial Upper Bound and Properties

**Mode**: REVISIT
**Outcome**: progress (3 new theorems)

#### What I Did
- Proved `f_le_n`: **trivial upper bound f(n) ≤ n** for n > 0. Uses f_eq_f' bridge, Finset.card_filter_le, and Nat.card_Icc. This establishes the baseline that the open conjectures dramatically improve upon.
- Proved `g_pos`: g(k) > 0 for k > 0. Direct from Nat.mul_pos and sigma_pos.
- Proved `g_gt_k`: g(k) > k for k ≥ 2. Key step: σ(k) ≥ k+1 because {1,k} ⊆ divisors(k) with 1 ≠ k. Uses Finset.sum_le_sum_of_subset_of_nonneg (same pattern as sigma1_ge_succ in Erdos413Problem.lean).
- Renumbered Part sections (V-VIII) for consistency.

#### Key Findings
- The pattern `sum_le_sum_of_subset_of_nonneg` + `sum_pair` is well-established in the codebase (cf. Erdos413Problem.lean:445-460)
- The `card_filter_le` + `Nat.card_Icc; omega` pattern matches Erdos1000Problem.lean:62-64 exactly
- Problem is now essentially complete: 0 sorries, 2 OPEN conjecture axioms, 15 theorems

#### Files Modified
- `proofs/Proofs/Erdos1060Problem.lean` (3 new theorems: f_le_n, g_pos, g_gt_k)

#### Next Steps
- Problem is complete — 2 axioms are the open conjectures themselves
- No further work needed unless the conjectures are resolved

---

*Generated from erdosproblems.com on 2026-01-15*
