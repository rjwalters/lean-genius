# Current State

**Phase**: SURVEY (downgraded from ACT — see honest assessment in
`sessions/2026-05-13-survey-axiom-tractability-and-structural-followups.md`)
**Since**: 2026-05-13 (researcher-1, honest scope SURVEY)
**Iteration**: 2

## Current Focus

Honest scope assessment of `erdos-8-oq-01` ("optimal minimum modulus
bound"). The two remaining axioms in `Erdos8Problem.lean`
(`hough_minimum_modulus`, `density_conjecture_false`) are **deep
published 2015 Hough results** that are not session-tractable.

## Active Approach

**Not "axiom elimination"** — both axioms are out of session scope.
**Pivot**: identify and prove **structural sub-results** that are not
gated by the deep axioms.

The session note documents:
1. Concrete effort estimate to discharge each deep axiom (~10⁴ LOC each).
2. Three tractable structural sub-questions that would enrich the
   formalization without requiring the deep results:
   - **(SQ-1)** Explicit lower-bound constructions: for each `K ∈ {2, 3,
     4, …, K₀}`, decide whether a covering system with `minModulus = K`
     and distinct moduli exists. Mathematical content: classical
     examples (e.g. Krukenberg systems, LCM-based constructions).
   - **(SQ-2)** Cardinality lower bounds: prove `cs.moduli.card ≥ f(cs.minModulus)`
     for a concrete `f` (e.g., a function involving the prime factorization
     of `cs.minModulus`).
   - **(SQ-3)** "Improved bound placeholder": replace the dummy
     `balister_improved_bound` (currently identical to Hough's bound)
     with an axiomatized but **strictly smaller** explicit Balister et al.
     constant, and prove the implication chain.

## Blockers

- The deep axioms are blockers to **further axiom elimination**, not to
  structural work. Pivot to SQ-1/2/3 unblocks session-level progress.

## Next Action

**S3 ACT (recommended next session)**: pick SQ-1 (smallest concrete
covering system with `minModulus = 2`). Build a `def exampleCS_modulus_2 :
CoveringSystem` together with a `theorem exampleCS_modulus_2_hasDistinctModuli :
exampleCS_modulus_2.hasDistinctModuli` and
`theorem exampleCS_modulus_2_minModulus_eq_2 : exampleCS_modulus_2.minModulus = 2`.
This concretely witnesses the lower endpoint of the optimal bound and
is fully provable (~30-50 LOC). It also forces the formalization to
deal with explicit covering proofs, which is good infrastructure for
SQ-2/SQ-3.

## Attempt Counts

- Total attempts: 2
- Current approach attempts: 1 (axiom elimination — exhausted on deep
  results)
- Approaches tried: 2 (1: axiom elimination, 2: structural-followups)
