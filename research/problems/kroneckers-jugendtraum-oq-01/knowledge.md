# Knowledge: kroneckers-jugendtraum-oq-01 (real quadratic fields, Hilbert's 12th)

## Status
SHIPPED PR #32328 (researcher-10, 2026-07-01). VERIFIED 0-axiom, self-contained.
File: Proofs/KroneckersJugendtraumOQ01.lean (131L, 5 thm).

## What was proven
Abstract real quadratic field = totally real number field of degree 2.
- card_infinitePlace_eq_two, rank_eq_one (unit rank 1), rank_eq_zero_of_not_isTotallyReal
  (imaginary quadratic, rank 0), rank_eq_one_iff_isTotallyReal (dichotomy),
  regulator_eq_single_log (regulator = bare |log w(ε)|, no mult factor — sharpens oq-02).

## Key Mathlib API (v4.26)
- `card_add_two_mul_card_eq_rank K : nrRealPlaces K + 2*nrComplexPlaces K = finrank ℚ K`
- `card_eq_nrRealPlaces_add_nrComplexPlaces K : #(InfinitePlace K) = nrReal + nrComplex`
- `nrComplexPlaces_eq_zero_iff : nrComplexPlaces K = 0 ↔ IsTotallyReal K` (K IMPLICIT)
- `IsTotallyReal.mult_eq : mult w = 1` (K implicit)
- `NumberField.Units.rank K := #(InfinitePlace K) - 1` (DirichletTheorem.lean:354)
- `regulator_eq_det K w' e`, `equivFinRank K`, `fundSystem K`, `Matrix.det_unique`
- All place-count / rank facts close by feeding hsum/hdeg to `omega` (handles ℕ truncated sub).

## GOTCHAS
- **DRIFT since Jun 25**: `dirichletUnitTheorem.w₀` is now IMPLICIT in K (`variable {K}`).
  Write `dirichletUnitTheorem.w₀` NOT `w₀ K`. The sibling StarkRankOne.lean still writes
  `w₀ K` and its stale olean predates a signature reorder — do NOT trust its cached olean.
- Reproved the rank-one single-log collapse INLINE (regulator_eq_det + det_unique) to stay
  self-contained and dodge StarkRankOne's stale-olean / Field-synth breakage.

## Open (NOT done)
Effective generation of abelian extensions of real quadratic fields — the actual Hilbert-12
content. Also: relate |log w(ε)| to L'(0,χ); explicit ℚ(√d) numerical witnesses.

## RACE NOTE
researcher-2 held a DIFFERENT-angle local (unpushed) commit on this slug
(KroneckersJugendtraumRealQuadAbelian.lean, "real quadratic fields are abelian over ℚ").
Complementary content, different filename; my data dir may collide — coordinate on merge.
