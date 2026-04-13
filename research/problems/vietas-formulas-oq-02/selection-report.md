# Problem Selection Report

**Date**: 2026-04-05
**Mode**: SELECT
**Pool Status**: 15 available, 533 in-progress, 1238 completed

## Selected Problem

- **ID**: vietas-formulas-oq-02
- **Name**: Formalize multivariate analogues of Vieta's formulas
- **Tier**: B
- **Significance**: 6/10
- **Tractability**: 7/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Top composite score among unselected candidates**: Composite = 76 (EMPTY tier: 0 penalty + tractability×10=70 + significance=6). Higher-scoring problems (unit-distance-independence-oq-02 score 78, mean-value-theorem-oq-04 score 77, euler-identity-oq-01-oq-04 score 76, erdos-szekeres-oq-01 score 76) were all initialized in prior seeker runs on this branch or main.

2. **EMPTY knowledge tier**: No prior research accumulated in this workspace — fresh territory for the Researcher to explore.

3. **Domain diversity**: Algebra/polynomial theory, distinct from recent selections (burnside-counting: group theory/combinatorics; unit-distance: graph coloring; mean-value: analysis; lhopital: analysis). Avoids the combinatorics/analysis concentration of the last 4 selections.

4. **Strong gallery infrastructure**: `VietasFormulas.lean` provides a fully verified base (0 sorries, 0 axioms, 179 lines) with `vieta_formula_quadratic` and `coeff_eq_esymm_roots_of_card`. The multivariate extension builds directly on `Mathlib.RingTheory.Polynomial.Vieta` and `Mathlib.RingTheory.MvPolynomial.Basic`.

5. **Substantive mathematics**: Multivariate Vieta connects to several deep areas — resultants, discriminants, symmetric function theory in multiple variables, and the theory of algebraic varieties. The gallery's own open question list names this: "What are the analogous formulas for multivariate polynomials?"

## Rejection Summary

- **Candidates considered**: 15 available
- **Candidates rejected**: 14
  - unit-distance-independence-oq-02 (score 78): already initialized in seeker commit 83e3f74152 on this branch
  - mean-value-theorem-oq-04 (score 77): already selected on main (#10163)
  - euler-identity-oq-01-oq-04 (score 76): already initialized with selection-report.md today
  - erdos-szekeres-oq-01 (score 76): already selected on main (#10161)
  - taylor-theorem-oq-02 (score 76): tied with vietas-formulas-oq-02; vietas selected for stronger mathematical depth vs. Lean API exploration framing
  - taylor-sincos-convergence-oq-01 (score 75): C-tier, analysis domain
  - triangular-reciprocals-oq-02 (score 75): C-tier, analysis/number theory
  - factor-remainder-nullstellensatz-oq-02 (score 67): lower score, combinatorics domain
  - buffons-needle-oq-01-oq-04 (score 66): lower score, probability domain
  - erdos-ko-rado-oq-04 (score 57): combinatorics domain (diversity penalty)
  - brouwer-fixed-point-oq-04-oq-04 (score 56): lower score, topology domain
  - szemeredi-theorem-oq-01 (score 48): sig=8 but tractability=4 (low tractability penalty)
  - prime-gap-bounds-oq-03 (score -1923): MODERATE knowledge tier (93-line knowledge.md), large negative penalty
  - wolstenholme-theorem-oq-03 (score -1934): MODERATE knowledge tier (45-line knowledge.md)
- **Confidence**: medium (tight score cluster among EMPTY candidates; diversity filter was the tiebreaker)

## Related Gallery Proofs

- `vietas-formulas`: Direct parent — quadratic and degree-n univariate Vieta's formulas, fully verified (0 sorries, 0 axioms). Provides `vieta_formula_quadratic`, `coeff_eq_esymm_roots_of_card`.
- `vietas-formulas-oq-03`: Extended Vieta work in gallery (OQ-03 direction)
- `sum-of-kth-powers`: Closely related — Newton's identities connect power sums Σrᵢᵏ to elementary symmetric polynomials (exactly Vieta's relations)
- `cayley-hamilton`: Trace and determinant as Vieta-type relations for characteristic polynomials
- `fundamental-theorem-algebra`: Guarantees exactly n roots (with multiplicity) for degree-n polynomials

## Suggested First Steps

1. **OBSERVE**: Read `proofs/Proofs/VietasFormulas.lean` to understand the base infrastructure. Check what `Mathlib.RingTheory.MvPolynomial.Basic` and `Mathlib.RingTheory.Polynomial.Vieta` provide for multivariate symmetric functions (`MvPolynomial.esymm`, `MvPolynomial.esymmAlgEquiv`).

2. **ORIENT**: Clarify the mathematical target — "multivariate analogues of Vieta's formulas" could mean: (a) Vieta's formulas for a polynomial in one variable over a polynomial ring (parametric family), (b) resultant-based relations between roots of two polynomials in two variables, or (c) symmetric polynomial identities in `MvPolynomial`. Scout `Mathlib4` for `MvPolynomial.esymm` and `MvPolynomial.IsSymmetric`.

3. **DECIDE**: Target the most tractable interpretation: likely (a) or (c). The Newton identity generalization (`p_k = Σ e_j * p_{k-j}` for multiple variable sets) has Mathlib support and directly extends the gallery's `sum-of-kth-powers` connection. Formulate a concrete theorem statement before diving into tactics.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 15 |
| In Progress | 533 |
| Completed | 1238 |
| Blocked | 2 |
| **Total** | **1787** |

## Candidate Pool Health

- **Pool depth**: adequate (15 available problems, all with initialized workspaces)
- **Recommendation**: Pool is healthy for now. If Researchers exhaust the 15 available candidates, trigger a replenishment run to add fresh problems from the gallery (currently ~1787 total, most in-progress).
- **Next refresh recommended**: When available drops below 5
