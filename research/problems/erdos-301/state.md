# Current State

**Phase**: SCOPED — open conjecture, lower-bound proved, upper-bound trivially weak
**Since**: 2026-04-27T17:35:00Z
**Iteration**: 2

## Current Focus

The Lean file `proofs/Proofs/Erdos301Problem.lean` (158 lines, 0 sorries, 0 `axiom`
declarations) formalizes **Erdős #301**: maximum size of `A ⊆ {1,…,N}` with no Egyptian
fraction decomposition `1/a = 1/b₁ + … + 1/bₖ` over `A`. The conjecture
`f(N) = (½ + o(1)) · N` is encoded as `def ErdosProblem301 : Prop` (correctly
`axiomatized` per project convention for open conjectures, even with no axioms).

## What is proved in the file

| Theorem | Status | Notes |
|---|---|---|
| `halfInterval_egyptFree` | **Proved** | (N/2, N] is decomposition-free. Splits singleton (forces b=a) vs |B| ≥ 2 (sum ≥ 2/N > 1/a). |
| `maxEgyptFree_lower` | **Proved** | f(N) ≥ N/2 via the half-interval witness. |
| `maxEgyptFree_le` | **Proved** | f(N) ≤ N (trivial cardinality bound). |
| `vanDoorn_upper` | **Misleadingly weak** | States f(N) ≤ (25/28 + 1) · N. The proof is just `≤ N ≤ (25/28 + 1) · N` — Van Doorn's actual 25/28 argument is NOT formalized. |
| `egyptFractionFree_empty/_singleton/_subset` | **Proved** | Basic closure properties. |

The `ErdosProblem301` Prop itself is open and unproved (correctly).

## Issues identified

1. **`vanDoorn_upper` is misleadingly named.** The theorem statement
   `f(N) ≤ (25/28 + 1) · N = (53/28) · N` is trivially true since `f(N) ≤ N` and
   `1 ≤ 53/28`. It does NOT formalize Van Doorn's actual upper bound of
   `(25/28 + o(1)) · N`. A future contribution could either:
   - Rename it (e.g., `trivial_upper_53_28`) to remove the false implication,
   - Strengthen the statement (e.g., `f(N) ≤ (25/28) · N + cN` for some o(N) error),
   - Replace with a genuine attempt at Van Doorn's argument (significant effort).

2. **Closure under deletion is proved (`egyptFractionFree_subset`)** but not used
   downstream. It would naturally support an inductive maximization argument.

## Active Approach

**Direction: tighten or correctly label the upper bound.**

Plausible incremental improvements:

1. **Honest renaming**: rename `vanDoorn_upper` → `trivial_upper_const` and add a
   `--TODO` comment documenting that Van Doorn's actual bound is much stronger.
   Smallest possible change; immediately removes the misleading attribution.

2. **Slight strengthening**: prove `f(N) ≤ N - ⌊N/k⌋` for some small k, by exhibiting
   k integers in {1,…,N} that *must* be excluded from any Egypt-fraction-free set
   (e.g., highly composite numbers). This would be a genuine, non-trivial improvement
   over the cardinality bound.

3. **Lower-bound refinement**: the half-interval gives `f(N) ≥ ⌈N/2⌉`. With careful
   accounting (handling parity), one can sometimes get `f(N) ≥ ⌈N/2⌉ + 1` for
   specific N. Probably <10 lines of additional Lean.

4. **Upper-bound via simple exclusion**: if `n ∈ A` and `2n ≤ N`, then a chain of
   deductions forces certain other elements out. This is the seed of Van Doorn's
   argument; even partial formalization of it would document the approach concretely.

## Mathlib API Survey (Mathlib 4.26.0)

The file imports `Mathlib.Data.Finset.Basic`, `Mathlib.Data.Rat.Defs`,
`Mathlib.Order.Filter.Basic`, `Mathlib.Tactic`. No specific Mathlib
infrastructure exists for Egyptian fractions or this Erdős problem.
Standard `Finset` / `ℚ` / arithmetic suffices for incremental improvements.

## Blockers

**Disk space tight (2026-04-27): 88% capacity, ~1.7 GB free.** Adding new theorems
requires Docker-build verification; not safe this session per researcher feedback memory.

## Next Action

For a future researcher session (disk > 5 GB free):

1. **Honest renaming (5 minutes)**: change `vanDoorn_upper` to a name reflecting the
   trivial nature of the bound (`trivial_upper_const_5328` or similar), keep the proof.
   Update `meta.json` `originalContributions` if it claims the Van Doorn bound is
   formalized.
2. **Direction #3 (lower-bound parity refinement)** is the lowest-effort genuine
   improvement; ~10–15 lines.
3. Direction #4 (real Van Doorn argument) is a substantial project — a multi-session
   undertaking and may benefit from Aristotle-assisted proof search on supporting
   inequalities.

## Attempt Counts
- Total attempts: 1 (file inspection + Mathlib survey)
- Current approach attempts: 1
- Approaches tried: 1 (scoping pass — identified the misleading-naming issue and
  four incremental directions)
