# Current State

**Phase**: ACT
**Path**: full
**Since**: 2026-03-24 (gallery entry shipped)
**Last Updated**: 2026-05-08 (Iteration 5, researcher-11)
**Iteration**: 5

## Current Focus

**2 axioms remain** in `proofs/Proofs/Erdos530Problem.lean` (430 lines, 17
theorems, 5 definitions, 0 sorries on origin/main post-this-PR):

1. `komlos_sulyok_szemeredi` — the KSS 1975 improved √N lower bound;
   stated for ℤ-Finsets with `A.card ≥ 4 → maxSidonSize² ≥ c·|A|`.
   Deep known result; eliminating it would require the full KSS
   probabilistic deletion argument (substantial Mathlib contribution).

2. `alon_erdos_partition_conjecture` — Alon-Erdős 1985 conjecture that
   `N`-element sets partition into `O(√N)` Sidon sets. Open problem.

Both are appropriate as axioms (one is a deep proved theorem, one is
genuinely open).

## Active Approach (this iteration)

Iteration 5 (2026-05-08, researcher-11, this PR): added the **sharp**
interval upper bound `sidon_subset_interval_bound_sharp`:

- `sidon_subset_interval_bound_sharp (S : Finset ℤ) (N : ℕ) (hN : 1 ≤ N)
   (hS : IsSidon S) (hRange : ∀ x ∈ S, 1 ≤ x ∧ x ≤ ↑N) :
   S.card * (S.card + 1) + 2 ≤ 4 * N`

This sharpens the existing `sidon_subset_interval_bound` (which gives
only `|S|² ≤ 4N`) by observing that pairwise sums `a + b` with `a, b ∈ S`,
`a ≤ b` satisfy `2 ≤ a + b ≤ 2N` (since both `a, b ≥ 1`). The sums
therefore lie in `Finset.Icc 2 (2N)` of cardinality `2N − 1` rather than
the looser `Finset.Icc 1 (2N)` of cardinality `2N`. The `k(k+1)/2`
distinct Sidon sums then satisfy `k(k+1)/2 ≤ 2N − 1`, hence
`k(k+1) ≤ 4N − 2`, stated without ℕ-subtraction as `k(k+1) + 2 ≤ 4N`.

Numerically: at `N = 100`, the trivial `k² ≤ 4N` gives `k ≤ 20`; the
sharp `k(k+1) ≤ 398` gives `k ≤ 19`. At `N = 10000`, `k ≤ 200` vs
`k ≤ 199`. The `+1` saving compounds to a meaningful gain at finite
scales, and the bound makes the gap to the conjectured optimal
`k ≤ √N + O(1)` more visible.

## Iteration History

- **Iter 1** (2026-03-24, PR #5840): structural Sidon-set theorems
  (isSidon_empty/singleton/pair/subset, maxSidonSize basics).
- **Iter 2** (2026-03-26, PR #6992): proved `erdos_lower_bound` from the
  KSS axiom (3→2 axioms). Eliminated a redundant axiom.
- **Iter 3** (2026-03-29, PR #7855): proved `interval_sidon_upper`
  (`maxSidonSize²(Icc 1 N) ≤ 4N` for the model interval set), proved
  `sidon_sum_count` (k(k+1)/2 distinct sums) and `card_sorted_pairs`,
  added the `ErdosProblem530Corrected` formulation, proved
  `erdos530_corrected_proof` from KSS + interval bound.
- **Iter 4** (2026-03-28, PR #7636): metadata fix accompanying
  erdos-687 axiom elimination work.
- **Iter 5** (2026-05-08, this PR, researcher-11): sharp interval
  bound `sidon_subset_interval_bound_sharp`. lineCount 381→430,
  theoremCount 16→17.

## Active Approach (next sessions)

Two avenues remain open for substantive progress without touching
the deep `komlos_sulyok_szemeredi` or `alon_erdos_partition_conjecture`
axioms:

1. **Difference-injectivity refinement**: prove `sidon_diff_injOn`,
   the dual of `sidon_sum_injective` for `(a, b) ↦ a − b` on off-diagonal
   pairs. This gives a parallel bound `k(k − 1) ≤ 2N − 2` from differences
   in `{−(N−1), …, −1, 1, …, N−1}`, matching the asymptotic constant of
   the sharp sum bound but illuminating the dual structure. ~25 lines.

2. **Singer-style explicit construction** (lower-bound witness): prove
   that the geometric set `{2^0, 2^1, …, 2^(k−1)}` is Sidon (binary
   uniqueness), giving an explicit construction of arbitrarily large
   Sidon sets. ~20 lines, requires only `Mathlib.Data.Nat.Bits`-style
   tactics. This complements the abstract `maxSidonSize_pos`/`_ge_two`
   bootstrapping by exhibiting concrete witnesses.

Both are independent of each other and of the open axioms.

## Blockers

None for incremental work. The two remaining axioms (`komlos_sulyok_szemeredi`,
`alon_erdos_partition_conjecture`) are appropriate axiomatic limits;
eliminating either requires deep new mathematics (KSS proof, or progress
on the Alon-Erdős conjecture).

## Next Action

**Iter 6 candidate**: prove `sidon_diff_injOn`, the difference-injectivity
characterization of Sidon sets. Statement:

```lean
theorem sidon_diff_injOn (S : Finset ℤ) (hS : IsSidon S) :
    Set.InjOn (fun p : ℤ × ℤ => p.1 - p.2)
      ((S ×ˢ S).filter (fun p => p.1 ≠ p.2) : Set (ℤ × ℤ))
```

Proof: from `a − b = c − d` derive `a + d = b + c`; apply Sidon with
appropriate orderings on the four cases of `(a ≤ d, a > d) × (b ≤ c, b > c)`.
~20–30 lines.

## Attempt Counts

- Total attempts: 5
- Current approach attempts: 1 (sharp interval bound, this PR)
- Approaches tried (axiom-side): bootstrap + KSS axioms, downstream proof
  of corrected statement (Iter 1–4); upper-bound sharpening (Iter 5).

## References

- `proofs/Proofs/Erdos530Problem.lean` — main file (430 lines, 17 theorems,
  2 axioms, 0 sorries).
- `src/data/proofs/erdos-530/meta.json` — gallery integration.
- KSS 1975 paper: Komlós, Sulyok, Szemerédi — "Linear problems in
  combinatorial number theory", *Acta Math. Acad. Sci. Hungar.* 26.
- Alon-Erdős 1985: "An application of graph theory to additive number
  theory", *European J. Combin.* 6.
