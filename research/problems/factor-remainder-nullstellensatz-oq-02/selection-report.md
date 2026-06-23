# Problem Selection Report

**Date**: 2026-04-05
**Mode**: SELECT
**Pool Status**: 15 available, 533 in-progress, 1238 completed

## Selected Problem

- **ID**: factor-remainder-nullstellensatz-oq-02
- **Name**: Formalize Alon's combinatorial Nullstellensatz in Lean
- **Tier**: B
- **Significance**: 7/10
- **Tractability**: 6/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Top composite score among truly fresh candidates**: Composite = 67 (EMPTY tier: 0 penalty + tractability×10=60 + significance=7). Candidates with higher raw scores were already selected: euler-identity-oq-01-oq-04 (76, selected this branch), unit-distance-independence-oq-02 (78, selected this branch), mean-value-theorem-oq-04 (77, selected via main), erdos-szekeres-oq-01 (76, selected via main), wolstenholme-theorem-oq-03 (66, selected this branch), buffons-needle-oq-01-oq-04 (66, selected via main).

2. **EMPTY knowledge tier**: No prior research accumulated — fresh territory for the Researcher to explore from scratch.

3. **Domain diversity**: Polynomial combinatorics / algebraic method — distinct from recent selections (wolstenholme: p-adic/number theory; taylor-sincos: analysis; triangular-reciprocals: analysis; burnside: combinatorics/group theory; unit-distance: graph coloring geometry). The combinatorial Nullstellensatz belongs to the "polynomial method in combinatorics" tradition — a different flavor from the analytic or group-theoretic recent picks.

4. **Strong gallery infrastructure**: `factor-remainder-nullstellensatz-oq-01` (Strong algebraic Nullstellensatz I(V(J))=√J) is COMPLETED, providing a proof-of-concept for Nullstellensatz-style arguments in Lean. Alon's combinatorial version is mathematically orthogonal (combinatorial coefficient argument vs. algebraic geometry), so the researcher can build fresh rather than depending on completed work.

5. **Substantive mathematics**: Alon's Combinatorial Nullstellensatz (1999) is a powerful theorem: if f ∈ F[x₁,...,xₙ] has a monomial x₁^{t₁}···xₙ^{tₙ} (deg = total deg) with nonzero coefficient, and |S_i| > t_i, then f is nonzero on S₁×···×Sₙ. Applications include additive combinatorics (Cauchy-Davenport), graph coloring (choosability), and combinatorial geometry.

## Rejection Summary

- **Candidates considered**: 15 available
- **Candidates rejected**: 14
  - euler-identity-oq-01-oq-04 (score 76): already selected on this branch (commit e9329934)
  - unit-distance-independence-oq-02 (score 78): already selected on this branch (commit 83e3f741)
  - wolstenholme-theorem-oq-03 (score 66): already selected on this branch (commit 91d73a9b)
  - triangular-reciprocals-oq-02 (score 57): already selected on this branch (commit f908067a)
  - mean-value-theorem-oq-04 (score 77): selected via main (commit 09d5fda2)
  - erdos-szekeres-oq-01 (score 76): selected via main (commit cbe6b4cd)
  - buffons-needle-oq-01-oq-04 (score 66): selected via main (commit 9ca0399c)
  - taylor-theorem-oq-02 (score 76): workspace initialized via main, not freshly available
  - vietas-formulas-oq-02 (score 76): workspace initialized via main, not freshly available
  - prime-gap-bounds-oq-03 (score -2923): RICH knowledge tier (16 items) — deprioritized
  - szemeredi-theorem-oq-01 (score 48): tractability=4, highest significance but low tractability for autonomous research
  - erdos-ko-rado-oq-04 (score 57): lower composite, no advantage over selected
  - brouwer-fixed-point-oq-04-oq-04 (score 56): lower composite, no advantage
  - taylor-sincos-convergence-oq-01 (score 57): C-tier, significance=5 below threshold for preference
  - triangular-reciprocals-oq-02 (see above)
- **Confidence**: high (clear composite ranking after exclusions)

## Related Gallery Proofs

- `factor-remainder-nullstellensatz`: Factor Theorem to Nullstellensatz Bridge (base entry)
- `factor-remainder-nullstellensatz-oq-01`: Strong Nullstellensatz I(V(J))=√J — COMPLETED, provides Lean proof infrastructure
- `factor-remainder-theorem-oq-03`: Multivariate Nullstellensatz from Factor Theorem — in-progress, algebraic variant (different mathematical content)
- `factor-remainder-theorem-oq-01`: Multiplicity version of Factor-Remainder — in-progress, related polynomial theory

## Suggested First Steps

1. **OBSERVE**: Survey Mathlib for polynomial evaluation infrastructure — `Polynomial.eval`, `MvPolynomial.eval`, `Finset.prod`, and any existing degree/coefficient lemmas. Check if `Polynomial.Alon` or similar exists.
2. **ORIENT**: Study Alon's original 1999 proof structure. The key lemma is the "coefficient extraction" argument: if f has degree ≤ Σt_i, evaluate f on a product set and extract the leading coefficient. Assess whether this can be formalized using Mathlib's `MvPolynomial` infrastructure.
3. **DECIDE**: Choose between (a) univariate warm-up via Alon's Cauchy-Davenport application, then multivariate; or (b) direct multivariate formulation. The univariate case might be achievable and gallery-worthy on its own.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 15 |
| In Progress | 533 |
| Completed | 1238 |
| Blocked | 1 |
| **Total** | **1787** |

## Candidate Pool Health

Pool depth: **adequate** (15 available, above the 5-problem threshold).

- Available count is at 15, comfortably above the 5-problem replenishment threshold.
- Many problems in the pool are in domains not recently covered (combinatorics, algebra, number theory extensions still available).
- Next refresh recommended: when available drops below 8 problems.
