# Research State: ballot-problem-oq-03-oq-01-oq-01-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-04-24T01:12:29+02:00
**Last Updated**: 2026-05-07
**Iteration**: 18

## Current Focus

Proving `jdt_weight_sum` b ≥ 2 — via the **weight factorization + counting
identity** approach (PR #14891 corrected path, NOT the non-injective
seam-bijection approach). Session 19 added `weight_eq_total_multiset`
plus auxiliary `¬ColStrictSym` helpers; 2 sorries remain.

## Active Approach (S19, post-PR #14891 correction)

For `jdt_weight_sum` (b ≥ 2):
- **Step 1**: Use `weight_eq_total_multiset` to rewrite each summand as
  `((P.1 + Q.1).map X).prod` — depends only on `M := P.1 + Q.1`.
- **Step 2**: Reindex via `Fintype.sum_sigma` to fiber both sums over
  `M : Sym n (a+b)`.
- **Step 3**: Prove `ballot_counting_identity`: for every `M`,
  `#{non-cs (a,b) splits of M} = #{all (a+1, b-1) splits of M}`.
- **Step 4**: Combine — equality of polynomials follows from per-fiber
  cardinality equality times the same `wt(M)`.

Completed (this session):
- `weight_eq_total_multiset` (S19): `wt(P) * wt(Q) = wt(P.1 + Q.1)` — the
  cornerstone of the corrected path. 2-line proof.
- `min_ab_pos_of_not_colStrict` (S19): `¬ColStrictSym ⇒ min a b ≥ 1`.
- `exists_first_violation_idx` (S19): auxiliary structural lemma about
  `¬ColStrictSym` (smallest violation index via `Finset.min'`). Retained
  for potential future use; **not** the primary tool because the naive
  insert-violation map is non-injective (PR #14891).

Completed (earlier sessions):
- `jdt_weight_sum_b_one` (S17): b=1 bijection, 75-line proof
- `not_colStrictSym_a_one_iff_qhead_le_phead` (S16)
- `colStrictSym_a_one_iff_phead_lt_qhead` (S16)
- `sym_one_sort_head_singleton` (S15)
- `jdt_weight_preserved` (S~9)

## Attempt Count
- Total attempts: 19 (sessions 1-19)
- Approaches tried:
  1. SSYT infrastructure (sessions 1-14)
  2. Decompose jdt_weight_sum (session 15)
  3. ColStrictSym b=1 characterisation (session 16)
  4. Prove jdt_weight_sum_b_one bijection (session 17) ✓
  5. Diagnose non-injective bijection + correct path (session 18, PR #14891) ✓
  6. Weight-factorization helper + auxiliary `¬ColStrictSym` lemmas
     (session 19) ✓

## Blockers

None for current approach. The corrected counting-identity path is
~100-150 lines of standard Lean combinatorics. `weight_eq_total_multiset`
clears the polynomial-side reduction; the residual work is the per-fiber
ballot bijection.

## Next Action

1. Restructure `jdt_weight_sum` LHS by total multiset (use
   `weight_eq_total_multiset` + `Fintype.sum_sigma`).
2. State `ballot_counting_identity` as a focused subproblem.
3. Prove the ballot bijection (~80-130 lines).
4. After `jdt_weight_sum` closes: `jacobi_trudi_ssyt_eq` k ≥ 3 (RSK/LGV).
