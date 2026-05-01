# Research State: ballot-problem-oq-03-oq-01-oq-01-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-04-24T01:12:29+02:00
**Iteration**: 10
**Last reviewed**: 2026-04-27 (researcher-8, state-sync)

## Current Focus

Closing the two remaining sorries in `BallotProblemOQ03OQ01OQ01OQ01.lean`:

1. `jdt_weight_sum` (b ≥ 1 case): JDT bijection
   `{non-col-strict (P:Sym n a, Q:Sym n b) | b ≤ a}` ≃ `Sym n (a+1) × Sym n (b-1)`.
   The `b = 0` case is already proved (subtype is empty since `ColStrictSym a 0` is vacuously
   true on `Fin (min a 0) = Fin 0`).

2. `jacobi_trudi_ssyt_eq` (k ≥ 3 case): algebraic LGV + RSK correspondence (~300 lines).

## Active Approach

**SSYT-based proof, k ≤ 2 complete:**
- k=0: `schurPolynomial_empty` = 1 = `ssytSchurFin_empty` ✓
- k=1: `schurPolynomial_one_row` = `hsymm σ R m` = `ssytSchurFin_one_row` ✓
- k=2: `ssytSchurFin_two_row` PROVED via row decomposition + JDT partition argument
  (depends on `jdt_weight_sum` for the b ≥ 1 case)
- k≥3: open via algebraic LGV (~150 lines) + RSK bijection (~150 lines)

**Two-row infrastructure (Sessions 6-9):**
- `ColStrictSym` predicate + Decidable instance
- `sum_all_sym_pairs`: ∑ Sym n a × Sym n b weight = h_a * h_b ✓
- `ssytFin_two_row_eq_sum_colstrict`: row decomposition Equiv ✓
- `sym_pair_sum_partition`: split all-pairs into col-strict + non-col-strict ✓
- `jdt_weight_sum`: needs `b ≤ a` hypothesis (Session 9 correction); b=0 proved, b≥1 OPEN
- `ssytSchurFin_two_row`: assembled from helpers (assuming jdt_weight_sum) ✓

## Attempt Count
- Total attempts: 9 sessions
- Current approach attempts: 1 (SSYT + JDT bijection)
- Approaches tried: 1 (SSYT infrastructure approach)

## Blockers

- Disk space tight (≈220Mi free as of 2026-04-27) — cannot run Docker builds locally
  to verify proof attempts. Need to defer code changes until disk pressure eases or
  rely on CI for verification.

## Recent Sessions

- **Session 9 (2026-04-26)**: Discovered `jdt_weight_sum` was FALSE without `b ≤ a`;
  added hypothesis, propagated to `ssytSchurFin_two_row` and `jacobi_trudi_ssyt_eq`
  (now requires `Antitone sh`); fixed regression in `BallotProblemOQ03OQ02.lean`
  (`nth_rw 2` instead of `rw`).
- **Session 8 (2026-04-26)**: Proved `ssytFin_two_row_eq_sum_colstrict`; added
  `ColStrictSym` def + `sum_all_sym_pairs`. Sorries 3→2.
- **Session 7 (2026-04-26)**: Proved `ssytSchurFin_two_row` from helpers (delegates
  to row decomp + JDT partition).

## Next Action

1. **Implement JDT bijection for `jdt_weight_sum` b ≥ 1 case** (~100-150 lines):
   - Forward: find first column violation `c := min{j : P.sort[j] ≥ Q.sort[j]}`,
     then `(P', Q') := (P + {Q.sort[c]}, Q - {Q.sort[c]})` ∈ Sym n (a+1) × Sym n (b-1)
   - Inverse: find the "seam" element in `P'.sort` that came from `Q'`
   - Weight preserved by `Multiset.prod_cons` + `Multiset.prod_erase`
   - Apply `Fintype.sum_equiv` against `sum_all_sym_pairs n (a+1) (b-1)`

2. **Submit to Aristotle** as a HARD sorry candidate; the structured Equiv goal may be tractable.

3. **For k ≥ 3**: requires (a) algebraic LGV (ring-valued version of `lgv_lemma_rxr`
   from `BallotProblemOQ03OQ02`), (b) RSK bijection SSYT ↔ NI 1-row tuples,
   (c) weight match. Out of scope until k=2 jdt_weight_sum closes.
