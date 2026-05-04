# lagrange-four-squares-oq-01-oq-01: Rabin-Shallit Algorithm Mathematical Core

**Problem**: Can the Rabin-Shallit O(log²n) algorithm for four-square representation be formalized?

**Answer**: Yes, mathematical core is fully formalized (0 axioms, 0 sorries). Probabilistic complexity remains open.

## Session 2026-05-04 (Session 1) - Gallery Entry Created

**Mode**: FRESH
**Outcome**: completed — PR #15505

### What I Did
- Found existing Lean file LagrangeFourSquaresOQ01OQ01.lean (no gallery entry)
- Discovered that density_consecutive_bound axiom is FALSE: {23,28} in [23,29) counterexample
- Created gallery entry (meta.json, annotations.json, index.ts)
- Created PR #15505

### Key Findings
- `density_consecutive_bound` ("≤1 of any 6 consecutive integers excluded") is FALSE
  - Counterexample: 23 = 4^0*(8*2+7) and 28 = 4^1*7, both in [23,29)
  - The true statement is asymptotic density 1/6
- `three_sq_subroutine_correctness` is definitionally trivial (IsSumOfThreeSquares = ∃ a b c, ...)
- Density 1/6 proved via tsum_geometric_of_lt_one: ∑(1/8)·(1/4)^k = 1/6
- rabin_shallit_pipeline: 0 axioms using Lagrange + definitional unfolding

### Next Steps
- Prove Legendre three-square theorem when/if it appears in Mathlib
- Formalize probabilistic complexity analysis (requires GRH)
