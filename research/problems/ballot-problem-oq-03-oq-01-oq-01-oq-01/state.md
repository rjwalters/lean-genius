# Research State: ballot-problem-oq-03-oq-01-oq-01-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-04-24T01:12:29+02:00
**Last Updated**: 2026-05-08
**Iteration**: 20

## Current Focus

`ballot_counting_identity` (S20 stated, sorry remaining): the focused per-fiber
cardinality subproblem extracted from `jdt_weight_sum` b≥2. With this lemma in
hand, the rest of the b≥2 reduction is structural (~80-100 lines using
`weight_eq_total_multiset` + `Finset.sum_fiberwise_of_maps_to`).

## Active Approach (S20, post-S19 weight identity)

For `jdt_weight_sum` (b ≥ 2):
- **Step (i)**: weight factorisation via `weight_eq_total_multiset` (S19).
- **Step (ii)**: regroup both LHS (¬CS subtype) and RHS (Sym a+1 × Sym b-1)
  by total multiset `M : Sym (Fin n) (a+b)` using `totalSym` / `totalSym'`
  (S20) and `Finset.sum_fiberwise_of_maps_to`.
- **Step (iii)**: per-fiber count equality via `ballot_counting_identity`
  (S20 stated, sorry).
- **Step (iv)**: combine to get LHS = RHS.

Steps (i), (ii), (iv) are ~80-100 lines of structural Lean. Step (iii) is the
deep ~150-line ballot bijection — extracted as a clean black-box.

Completed (this session, S20):
- `totalSym` / `totalSym_val` (~5 lines): Sym (Fin n) a × Sym (Fin n) b →
  Sym (Fin n) (a+b) via P.1 + Q.1.
- `totalSym'` / `totalSym'_val` (~7 lines): companion for the (a+1, b-1) shape
  with `hb : 1 ≤ b` baked in.
- `ballot_counting_identity` stated (~20 lines incl. docstring): the
  per-fiber cardinality identity, sorry.
- Updated `jdt_weight_sum` b≥2 comment block to reference the new helpers
  and document steps (i)-(iv).

Completed (earlier sessions):
- `weight_eq_total_multiset` (S19): cornerstone weight identity.
- `min_ab_pos_of_not_colStrict` (S19), `exists_first_violation_idx` (S19):
  auxiliary structural lemmas (latter not on primary path).
- `jdt_weight_sum_b_one` (S17): b=1 base case, 75-line proof.
- `not_colStrictSym_a_one_iff_qhead_le_phead` (S16),
  `colStrictSym_a_one_iff_phead_lt_qhead` (S16),
  `sym_one_sort_head_singleton` (S15), `jdt_weight_preserved` (S~9).

## Attempt Count
- Total attempts: 20 (sessions 1-20)
- Approaches tried:
  1. SSYT infrastructure (sessions 1-14)
  2. Decompose jdt_weight_sum (session 15)
  3. ColStrictSym b=1 characterisation (session 16)
  4. Prove jdt_weight_sum_b_one bijection (session 17) ✓
  5. Diagnose non-injective bijection + correct path (session 18, PR #14891) ✓
  6. Weight-factorization helper + auxiliary `¬ColStrictSym` lemmas
     (session 19) ✓
  7. Extract `ballot_counting_identity` + `totalSym`/`totalSym'` helpers,
     document the structural reduction (session 20) ✓ (this PR)

## Blockers

None for current approach. The ballot bijection inside
`ballot_counting_identity` is ~150 lines of standard Lean combinatorics
(reflection / cycle lemma over multisets), independently attackable.

## Next Action

1. **S21**: Prove `ballot_counting_identity` — bijection at the multiset level
   between non-col-strict (a,b) splits of M and arbitrary (a+1, b-1) splits.
   ~150 lines. Strategy: adapt the cycle / ballot principle for multisets.
2. **S22**: Wire `ballot_counting_identity` into `jdt_weight_sum` b≥2 via the
   structural reduction (steps i-iv documented above). ~80-100 lines using
   `Finset.sum_fiberwise_of_maps_to` + `weight_eq_total_multiset`.
3. **Future**: After `jdt_weight_sum` closes, `jacobi_trudi_ssyt_eq` k ≥ 3
   (RSK / algebraic LGV, ~300 lines).

## File Status

- `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean`: ~992 → ~1050 lines.
- Sorry count: 3 → 4 (added `ballot_counting_identity`; existing
  `jdt_weight_sum` b≥2 sorry unchanged this session).
- 0 axioms.
