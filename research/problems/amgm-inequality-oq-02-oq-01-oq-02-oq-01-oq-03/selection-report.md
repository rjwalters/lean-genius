# Problem Selection Report

**Date**: 2026-05-04
**Mode**: SELECT
**Pool Status**: 28 available, 1267 in-progress, 766 completed

## Selected Problem

- **ID**: `amgm-inequality-oq-02-oq-01-oq-02-oq-01-oq-03`
- **Name**: Newton-Girard Recurrence — Independent Inductive Proof Without Mathlib
- **Tier**: B
- **Significance**: 6/10
- **Tractability**: 5/10 (challenging)
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **EMPTY knowledge tier** (score=0): Highest priority by composite algorithm. No prior
   research has been done on this specific question, making it a fresh exploration target.
2. **Domain diversity**: Last 3 selections covered number theory (Basel), probability
   (ballot-problem), and geometry (area-of-circle). Algebra/symmetric-polynomials domain
   is underrepresented — this provides genuine variety.
3. **Clear mathematical objective**: The task is precisely specified — prove p_k = Σ(±eⱼ·p_{k-j})
   by induction, without the Mathlib lemma. Well-defined start and end states.
4. **Rich parent context**: The parent gallery proof (`amgm-inequality-oq-02-oq-01-oq-02-oq-01`)
   already has the cases k=1,2,3 proved and the Lean infrastructure in place. The researcher
   can directly read the parent Lean file to understand the setup.
5. **Not a moonshot**: Newton-Girard is classical combinatorics; the inductive step is
   challenging to formalize but mathematically standard.

## Rejection Summary

- **Candidates considered**: 28 available problems
- **Candidates rejected**:
  - `prime-number-theorem-oq-01` (Riemann Hypothesis — moonshot)
  - `cantor-diagonalization-oq-01-oq-03` (Woodin's Ultimate-L — moonshot)
  - `cantors-theorem-oq-01-oq-02` (aleph-index of ℶ₂ — open set theory question)
  - `birch-swinnerton-dyer-oq-06-oq-02` (Néron-Tate height computation — BSD-level hard)
  - `brouwer-fixed-point-oq-01-oq-02-oq-03-oq-02` (eliminate singular_homology axiom — requires full homology in Mathlib)
  - `algebraic-numbers-countable-oq-02-oq-03` (formalize CH independence from ZFC — moonshot)
  - `basel-problem-oq-01-oq-01-oq-02-oq-02` — selected LAST cycle, still in NEW state; 
    skipped to provide domain diversity this cycle
  - MODERATE/RICH knowledge problems (cauchy-schwarz, arithmetic-series, angle-trisection,
    birthday-problem, central-limit-theorem, fundamental-arithmetic, erdos-1201) — 
    deprioritized per composite scoring
- **Confidence**: medium — many candidates are tied at composite=56; the Basel problem
  (composite=57) would be selected if not for the recent-selection diversity rule.

## Related Gallery Proofs

- `amgm-inequality-oq-02-oq-01-oq-02-oq-01`: Parent — k=1,2,3 cases proved via Mathlib
- `amgm-inequality-oq-02-oq-01-oq-02`: Off-diagonal symmetry in symmetric functions
- `amgm-inequality-oq-02-oq-01`: Newton-Girard square-of-sum decomposition

## Suggested First Steps

1. **OBSERVE**: Read `proofs/Proofs/AmgmInequalityOQ02OQ01OQ02OQ01.lean` to understand
   the existing MvPolynomial setup and what's already proved.
2. **ORIENT**: Search Mathlib for `newton_girard` or `psum_esymm` lemmas; check whether
   any inductive formulation already exists. Scout may have relevant literature.
3. **DECIDE**: Determine whether to use strong induction on k, or to derive from a
   generating-function identity using formal power series in Mathlib.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 28 |
| In Progress | 1267 |
| Completed | 766 |
| Graduated | 43 |
| Blocked | 8 |
| **Total** | **2112** |

## Candidate Pool Health

- **Pool depth**: Adequate (28 ≥ 15 threshold)
- **Knowledge distribution**: 21 EMPTY, 3 MODERATE, 2 WEAK, 2 RICH — healthy mix
- **Recommendation**: Pool healthy. No replenishment needed this cycle.
- **Next refresh recommended**: +30 minutes (routine cycle)

## Initialized

- [x] Research workspace exists: `research/problems/amgm-inequality-oq-02-oq-01-oq-02-oq-01-oq-03/`
- [x] problem.md populated with full mathematical context
- [x] Registered in `research/db/knowledge.db` (status: available)
- [x] Verified in `candidate-pool.json`
- [ ] Ready for Researcher to claim
