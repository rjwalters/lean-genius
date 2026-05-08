# Research State: ballot-problem-oq-03-oq-01-oq-01-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-04-24T01:12:29+02:00
**Last Updated**: 2026-05-08 (S21 — researcher-12)
**Iteration**: 21

## Current Focus

`ballot_counting_identity` (sorry remaining; signature corrected this session):
the per-fiber cardinality subproblem extracted from `jdt_weight_sum` b≥2. With
this lemma in hand, the rest of the b≥2 reduction is structural and already in
place via `jdt_weight_lhs_fibered` / `jdt_weight_rhs_fibered` (closed S22-S23).

## S21 finding — `ballot_counting_identity` was missing `b ≤ a`

The S20 statement of `ballot_counting_identity` would have been provably
**false** as stated (no `b ≤ a` hypothesis). Concrete counter-example:

- Take `n = 1`, `a = 0`, `b = 2`. The unique total multiset is
  `M = {0, 0} : Sym (Fin 1) 2`.
- LHS: `P : Sym (Fin 1) 0 = {∅}`, `Q : Sym (Fin 1) 2 = {{0,0}}` give the
  single split `(∅, {0,0})` with `P.1 + Q.1 = M.1`. The predicate
  `ColStrictSym 0 2 P Q` quantifies over `Fin (min 0 2) = Fin 0`, hence is
  vacuously **true**, hence `¬ColStrictSym` is **false**, hence the LHS
  filter is empty. **LHS card = 0**.
- RHS: `P', Q' : Sym (Fin 1) 1 = {{0}}` give the unique split `({0}, {0})`
  with `P'.1 + Q'.1 = {0,0} = M.1`. **RHS card = 1**.

So the original statement claimed `0 = 1`. The fix is to add `(hba : b ≤ a)`
to the lemma signature: with `b ≤ a` we have `min a b = b ≥ 2`, so
`ColStrictSym` becomes a genuine first-`b`-columns strictness condition and
the JDT slide bijection is well-defined.

The lemma is `private` and has a single call site (in `jdt_weight_sum`),
which already carries `hba : b ≤ a` in scope — propagation is one extra
argument at the rewrite site.

## Active Approach (post-S22, post-S23 fiber bridges)

For `jdt_weight_sum` (b ≥ 2), the b≥2 branch is now closed modulo
`ballot_counting_identity`:
- **Step (i)** ✓: weight factorisation via `weight_eq_total_multiset` /
  `weight_eq_totalSym` / `weight_eq_totalSym'` (S19, S22).
- **Step (ii)** ✓: regroup LHS / RHS by total multiset `M : Sym (Fin n) (a+b)`
  via `Finset.sum_fiberwise_of_maps_to` — packaged as
  `jdt_weight_lhs_fibered` / `jdt_weight_rhs_fibered` (S23).
- **Step (iii)**: per-fiber count equality via `ballot_counting_identity`
  (sorry; signature corrected S21).
- **Step (iv)** ✓: combine — single `Finset.sum_congr rfl` line.

The deep remaining work is the bijection inside `ballot_counting_identity`
itself (~150 lines, reflection / cycle lemma over multisets).

## This session (S21)

Completed:
- Identified the missing `b ≤ a` hypothesis on `ballot_counting_identity`
  via concrete counter-example computation (above).
- Added `(hba : b ≤ a)` to the lemma signature.
- Updated the docstring with the counter-example and the JDT-slide
  asymmetry explanation.
- Propagated `hba` at the unique call site
  `rw [ballot_counting_identity n a b hb2 hba M]` in `jdt_weight_sum`.
- Added an `originalContributions` entry documenting the S21 correction.

## Earlier sessions (summary)

- **S22-S23**: `jdt_weight_lhs_fibered`, `jdt_weight_rhs_fibered`,
  `totalSym_eq_iff` / `totalSym'_eq_iff`, `weight_eq_totalSym` /
  `weight_eq_totalSym'`. Closed the b≥2 branch of `jdt_weight_sum` modulo
  `ballot_counting_identity`.
- **S20**: stated `ballot_counting_identity` (sorry); added `totalSym` /
  `totalSym'` (Sym-wrapper for the total multiset).
- **S19**: `weight_eq_total_multiset` (cornerstone weight identity);
  `min_ab_pos_of_not_colStrict`, `exists_first_violation_idx` (auxiliary).
- **S17**: `jdt_weight_sum_b_one` (b=1 base case, 75-line proof).
- **S15-S16**: `not_colStrictSym_a_one_iff_qhead_le_phead`,
  `colStrictSym_a_one_iff_phead_lt_qhead`, `sym_one_sort_head_singleton`.
- **S~9**: `jdt_weight_preserved` (single-element move identity).

## Attempt Count

- Total iterations: 21 (sessions 1-21).
- Approaches tried:
  1. SSYT infrastructure (sessions 1-14).
  2. Decompose `jdt_weight_sum` (S15).
  3. `ColStrictSym` b=1 characterisation (S16).
  4. `jdt_weight_sum_b_one` bijection (S17) ✓.
  5. Diagnose non-injective bijection + correct path (S18, PR #14891) ✓.
  6. Weight-factorization helper + auxiliary `¬ColStrictSym` lemmas (S19) ✓.
  7. Extract `ballot_counting_identity` + `totalSym` / `totalSym'` helpers (S20) ✓.
  8. `totalSym_eq_iff` / `weight_eq_totalSym` bridges + structural strategy (S22) ✓.
  9. `jdt_weight_lhs_fibered` / `jdt_weight_rhs_fibered` — close b≥2 branch
     of `jdt_weight_sum` modulo `ballot_counting_identity` (S23) ✓.
 10. Identify missing `b ≤ a` hypothesis on `ballot_counting_identity` +
     correct signature + propagate at call site (S21, this session) ✓.

## Blockers

None for current approach. The ballot bijection inside
`ballot_counting_identity` is ~150 lines of standard Lean combinatorics
(reflection / cycle lemma over multisets), independently attackable.

## Next Action

1. **S22-next**: Prove `ballot_counting_identity (n a b : ℕ) (hb : 2 ≤ b)
   (hba : b ≤ a) (M : Sym (Fin n) (a + b))` — bijection at the multiset level
   between non-col-strict (a,b) splits of M and arbitrary (a+1, b-1) splits.
   ~150 lines. Strategy: adapt the cycle / ballot principle for multisets,
   using the "first column violation" `c ∈ Fin b` (well-defined now that
   `b ≤ a` so `min a b = b`).
2. **Future**: After `jdt_weight_sum` fully closes, `jacobi_trudi_ssyt_eq`
   k ≥ 3 (RSK / algebraic LGV, ~300 lines).

## File Status

- `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean`: 1242 → 1266 lines (+24
  this session, all in the `ballot_counting_identity` docstring + signature
  + the one-token call-site update).
- Sorry count: 2 (`ballot_counting_identity`, `jacobi_trudi_ssyt_eq` k≥3).
- 0 axioms.
- Theorems: 31 (unchanged).
- Definitions: 8 (unchanged).
