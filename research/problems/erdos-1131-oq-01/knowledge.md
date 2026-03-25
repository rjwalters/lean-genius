# Erdős #1131 OQ-01: Lagrange Integral Deep Dive

## Problem Summary
For x₁,...,xₙ ∈ [-1,1], minimize I = ∫₋₁¹ ∑ₖ lₖ(x)² dx where lₖ are Lagrange basis polynomials.
Conjecture: min I = 2 - (1+o(1))/n.

## Session 2026-03-25 (Session 3) - Axiom elimination + structural theorems

**Mode**: REVISIT
**Outcome**: progress

### What I Did
- **Removed false axiom** `lagrangeIntegral_upper_bound` (I ≤ 2n) — this is mathematically false because I can be unbounded when nodes are close together (I ~ 1/ε² for nodes at distance ε)
- **Proved `lagrangeBasis_continuous`**: Each lₖ is continuous (polynomial in x)
- **Proved `sum_sq_lagrangeBasis_continuous`**: ∑lₖ² is continuous
- **Defined `quadratureWeight`** and **proved `quadrature_weights_sum`**: ∑ₖ wₖ = 2 via integral linearity + partition of unity
- **Defined `gramOffDiag`** and **proved `lagrangeIntegral_cross_term_identity`**: I = 2 - ∫ gramOffDiag, connecting I to off-diagonal Gram matrix entries
- **Proved `lagrangeIntegral_single`**: I = 2 for n=1 (empty product gives lₖ ≡ 1)

### Key Findings
- The cross-term identity proof uses a clean chain: `Finset.add_sum_erase` + `Finset.mul_sum` + partition of unity
- `convert Finset.prod_empty` elegantly handles the Fin 1 empty product case
- Parsing issue: `∑ j in S, f` inside `∫ x in a..b, body` causes ambiguity — solved with `gramOffDiag` helper def
- `Finset.filter_ne'` converts between `filter (· ≠ k)` and `erase k`

### Files Modified
- `proofs/Proofs/Erdos1131Problem.lean` (297→419 lines, 9→14 theorems, 3→2 axioms)
- `src/data/proofs/erdos-1131/meta.json`
- `src/data/research/problems/erdos-1131-oq-01.json`

### Stats Change
| Metric | Before | After |
|--------|--------|-------|
| Axioms | 3 | **2** |
| Theorems | 9 | **14** |
| Definitions | 6 | **8** |
| Lines | 297 | **419** |

### Next Steps
- Prove `chebyshev_integral_estimate` (requires Chebyshev polynomial theory — substantial)
- The open conjecture is correctly axiomatized
