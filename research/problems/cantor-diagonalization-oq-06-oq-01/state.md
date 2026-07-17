# Research State: cantor-diagonalization-oq-06-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-09T16:43:20-07:00
**Iteration**: 2

## Current Focus
Core goal COMPLETE on main: `CantorDiagonalizationOQ06OQ01.lean` defines the explicit
`diagonalReal : (ℕ → ℝ) → ℝ` with `diagonalReal_ne`, `uncountable_real`, all cardinality-free,
0 sorry / 0 axiom. Now extending the structural theory around the construction.

## Iteration 2 (researcher-7, 2026-07-12) — injectivity on digit-choices + set-form [VERIFIED, axiom-free]
The file had `diagonalReal_congr` (the diagonal map is *constant* on enumerations sharing
a diagonal digit-sequence) but not its converse. Added the separating direction and the
set-theoretic "missing from the enumeration" form (docker build OK, 7743 jobs; new
capstones `[propext, Classical.choice, Quot.sound]`):
- `db_eq_of_diagonalReal_eq`: `diagonalReal f = diagonalReal g → ∀ n, db f n = db g n` —
  converse of `diagonalReal_congr`, straight from the crux `digit_diagonalReal` (reading
  the n-th digit back off each side).
- `diagonalReal_eq_iff_db`: the exact biconditional `= ↔ ∀ n, db f n = db g n`; sharpens
  `diagonalReal_congr` (sufficient digit-equality hypothesis) to the `{1,2}`-choice level.
- `diagonalReal_ne_of_db_ne`: contrapositive separation — one differing choice forces
  distinct reals; with `diagonalReal_mono` the map is an order-preserving embedding.
- `diagonalReal_notMem_range` / `range_ne_univ`: `Set.range`-level forms matching the
  problem title ("missing from any listed enumeration"); previously only pointwise `≠` and
  `¬ Surjective` were present.

## Active Approach
Structural theory of the explicit diagonal map (locality ↔ injectivity, range forms).

Note (concurrent work): a parallel researcher independently landed the explicit
`(ℕ → Bool) ↪ ℝ` injection (`seqReal`, `seqReal_injective`, `seqEmbedding`,
`mk_seq_le_mk_real`) on `main` — the "large side" (`𝔠 ≤ #ℝ`) direction I had flagged as
next. My contribution merged cleanly alongside it (no name/def collisions) and is in fact
the more general reason their `seqReal_injective` holds: it is the `s = indicator listing`
instance of `db_eq_of_diagonalReal_eq` / `diagonalReal_eq_iff_db`.

Remaining candidates: refactor `seqReal_injective` to go through `db_eq_of_diagonalReal_eq`;
surjectivity of the diagonal map onto the `{1,2}`-digit Cantor set (`Set.range diagonalReal
= {Σ cₙ/10^{n+1} : cₙ ∈ {1,2}}`); a decimal analogue avoiding 0/9 with a full 10-symbol
alphabet.

## Attempt Count
- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
None.

## Next Action
Read problem.md thoroughly and acquire full context.
Then move to ORIENT phase to explore literature and related proofs.

## Update (2026-07-11, researcher-8 — metadata reconciliation)

Verified `CantorDiagonalizationOQ06OQ01.lean` (host `bin/lake env lean`, exit 0): 0 sorries,
axiom-free (`#print axioms uncountable_real` / `uncountable_Ioo` = [propext, Classical.choice,
Quot.sound]; no `Cardinal.not_countable_real`, no `sorryAx`/`ofReduceBool`). The verified/original
badge is accurate. The file had grown past the gallery meta: a unit-interval section (6 theorems:
`tsum_geo_shift`, `diagonalReal_pos`, `diagonalReal_lt_one`, `diagonalReal_mem_Ioo`,
`not_surjective_nat_Ioo`, `uncountable_Ioo`) showing the diagonal lands in (0,1) and hence (0,1) is
uncountable. Reconciled the stale meta: `lineCount` 239→299 and 209→299, `theoremCount` 16→22 and
14→22 (both nested snapshots); added the six unit-interval theorems to the description and enriched
the summary. Pure metadata change (no Lean edit). Problem stays completed.
