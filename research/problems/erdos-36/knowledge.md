# Erdős #36 - Knowledge Base

## Problem Statement

Find the optimal constant $c>0$ such that the following holds. For all sufficiently large $N$, if $A\sqcup B=\{1,\ldots,2N\}$ is a partition into two equal parts, so that $\lvert A\rvert=\lvert B\rvert=N$, then there is some $x$ such that the number of solutions to $a-b=x$ with $a\in A$ and $b\in B$ is at least $cN$. The minimum overlap problem. The example (with $N$ even) $A=\{N/2+1,\ldots,3N/2\}$ shows that $c\leq 1/2$ (indeed, Erdős initially conjectured that $c=1/2$). The lower bound of $c\geq 1/4$ is trivial, and Scherk improved this to $1-1/\sqrt{2}=0.29\cdots$. The current records are\[0.379005 View the LaTeX source This page was last edited 30 September 2025.

## Status

**Erdős Database Status**: OPEN

**Tractability Score**: 4/10
**Aristotle Suitable**: No

## Tags

- erdos

## Related Problems

- Problem #337
- Problem #2000
- Problem #62
- Problem #2
- Problem #4
- Problem #35
- Problem #37
- Problem #39
- Problem #1

## References

- Er55
- Er56
- Er61
- Er92c
- Wh22
- Ha16
- Gu04

## Sessions

### 2026-06-04 (researcher-1) — Session 1: STATE-SYNC

The slug knowledge.md and state.md were template "NEW" stubs from
2026-01-12. However, `proofs/Proofs/Erdos36Problem.lean` has been
substantively developed (380 lines, 15 theorems, 3 axioms, 0 sorries,
since pre-claim). This iteration documents the file's content for the
first time in the research tracker; no Lean changes.

#### What's Already in `Erdos36Problem.lean`

**Definitions (9)**: `interval`, `overlap`, `maxOverlap`,
`minMaxOverlap` (misnamed, returns max not min — see below),
`partitions`, `overlapValues`, `M` (the actual min-max overlap),
`maxOverlapC` (computable mirror), `MC` (computable mirror of `M`).

**Axiom-free results (the file's real mathematical content)**:

- `pigeonhole_maxOverlap`: `N² ≤ (4N − 1) · maxOverlap(A, B)` for any
  equal bipartition. Standard pigeonhole on `N²` pairs across the
  `4N − 1` possible integer differences.
- `M_lower_pigeonhole`: instantiates the above on the M-achieving
  partition.
- `trivial_lower_bound`: `M(N)/N > 1/4` for all `N ≥ 1`. The
  elementary Erdős (1955) bound, derived axiom-free from the
  pigeonhole result.
- `small_values`: M(1) = 1, M(2) = 1, M(3) = 2, M(4) = 2, M(5) = 3
  via `native_decide` on the computable mirror `MC`.
- `MC_eq`: `MC N = M N` by `rfl` — the noncomputable spec and
  computable mirror are definitionally equal.
- Several private supporting lemmas: `diff_mem_range`,
  `overlap_zero_not_image`, `overlap_le_max`, `sum_overlap_eq_prod`
  (the fiber-sum identity `∑_k overlap A B k = |A| · |B|`),
  `diff_range_card`, `interval_card`.

**Axiomatized external results (3)**:

- `erdos_36_limit_exists`: existence of the asymptotic constant
  `c = lim M(N)/N`. *Open*: even existence of the limit hasn't
  been proved in full generality.
- `white_lower`: White (2022) lower bound `M(N)/N > 0.379005`,
  obtained via Fourier analysis and convex optimization.
- `upper_bound`: Haugland (2016) / TTT-Discover (2026) upper bound
  `M(N)/N < 0.380876`, obtained via step functions.

**Derived results from the external axioms**:

- `erdos_lower_quarter`: `M(N)/N > 1/4` (chained from `white_lower`).
  Note: this is *redundant* with `trivial_lower_bound` — both prove
  the same conclusion, but `erdos_lower_quarter` adds a needless
  dependency on `white_lower`. Forward Lever 1 (in state.md)
  identifies this as a clean refactor target.
- `scherk_lower`: `M(N)/N > 1 - 1/√2 ≈ 0.293` (chained from
  `white_lower`). Stronger than `1/4`, so not derivable from
  `trivial_lower_bound`. Scherk's original 1955 proof is elementary
  but more involved than pigeonhole — formalization would be a
  multi-session project (Forward Lever 2).
- `constant_bounds`: any candidate `c` must satisfy
  `0.379005 ≤ c ≤ 0.380876` (from `white_lower` and `upper_bound`).

#### Code-Quality Notes

- The `minMaxOverlap` definition at lines 41-44 is *misnamed*: it
  uses `Finset.sup` (max), not `Finset.inf` (min), because Lean's `ℕ`
  lacks `⊤` needed for `inf` on a `Finset`. The actual `M(N)`
  definition at lines 74-75 correctly uses `Finset.min'`. The
  `minMaxOverlap` stub is left in place with an explanatory comment.
- The `M_lower_pigeonhole` proof uses `Finset.exists_subset_card_le`
  to demonstrate `partitions N` is nonempty (an N-element subset of
  `interval N` always exists).
- The computable mirror `MC` allows `native_decide` to verify small
  values, but the combinatorial explosion of `partitions N` (there
  are `C(2N, N)` candidate partitions) limits this to roughly
  N ≤ 5-6 in practice.

#### Forward Levers

See `state.md` for the full forward-lever list. Highlights:

1. **(Recommended)** Refactor `erdos_lower_quarter` to use
   `trivial_lower_bound` instead of `white_lower`, removing one
   axiom-dependency for a named historical result. ~5 LOC.
2. Formalize Scherk's elementary proof of `1 - 1/√2`. Multi-session.
3. Sharpen pigeonhole denominator `4N - 1 → 4N - 3` via parity
   argument on differences `0` and `±(2N - 1)`. ~30-50 LOC.
4. Extend `small_values` table to M(6)…M(10) where computable
   verification still terminates.

#### Files Modified This Session

- `research/problems/erdos-36/state.md` — full rewrite from NEW
  stub to AXIOMATIZED with axiom inventory, axiom-free content
  summary, and forward levers.
- `research/problems/erdos-36/knowledge.md` — this entry.
- `src/data/research/problems/erdos-36.json` — currentState refresh.

No proof code changed.

---

*Generated from erdosproblems.com on 2026-01-12*
