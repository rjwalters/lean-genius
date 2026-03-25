# Erdős #1131 OQ-01: Lagrange Integral Deep Dive

## Problem Summary
For x₁,...,xₙ ∈ [-1,1], minimize I = ∫₋₁¹ ∑ₖ lₖ(x)² dx where lₖ are Lagrange basis polynomials.
Conjecture: min I = 2 - (1+o(1))/n.

## Current State
- **File**: `proofs/Proofs/Erdos1131Problem.lean` (548 lines)
- **Sorries**: 0
- **Axioms**: 2 (chebyshev_integral_estimate, erdos_1131_conjecture)
- **Theorems**: 19 (all fully proved)

## Session 2026-03-24 (Session 4) - Gram structure + Gauss identity

**Mode**: REVISIT (RICH knowledge, score 17)
**Outcome**: progress

### What I Did
1. **Proved `sum_sq_plus_gramOffDiag_eq_one`**: Extracted the pointwise Gram identity
   ∑l_k² + gramOffDiag = 1 as a standalone theorem from the cross-term proof
2. **Proved `gramOffDiag_continuous`**: Continuity of the off-diagonal Gram function
3. **Proved `gramOffDiag_at_node`**: gramOffDiag(xⱼ) = 0 at each node — used
   `by_cases` + `rw [hkj] at hi` to avoid `subst` issues with bound variables
4. **Proved `sum_sq_at_node`**: ∑l_k(xⱼ)² = 1 — used `Finset.sum_ite_eq'` pattern:
   convert each term to `if k = j then 1 else 0`, then sum evaluates to 1
5. **Proved `lagrangeIntegral_eq_two_of_sq_exact`**: The Gauss quadrature identity —
   if quadrature is exact for l_k², then I = 2. Uses hexact to show ∫l_k² = w_k,
   then I = ∑w_k = 2 via existing `quadrature_weights_sum`

### Key Mathematical Insight
For Gauss-Legendre nodes, quadrature is exact for degree ≤ 2n-1. Since l_k² has
degree 2(n-1) = 2n-2 ≤ 2n-2 < 2n-1, the Gauss identity applies: I = 2 identically.
This means **the minimum of I is NOT at Gauss nodes** — Chebyshev and optimal nodes
achieve I < 2, which is what makes this problem interesting.

### Key Lean Findings
- `Finset.sum_ite_eq'` + `split_ifs` cleanly handles interpolation property evaluations
- `rw [hkj] at hi` avoids `subst` issues when the substitution variable clashes with
  bound variables in filters/sums
- `simp [lagrangeBasis_self/other]` handles if-then-else + pow simplification
- `intervalIntegral.integral_finset_sum` takes ONE explicit argument (integrability proof),
  not two — `s` (finset) is implicit

### Files Modified
- `proofs/Proofs/Erdos1131Problem.lean` (419→548 lines, 14→19 theorems)
- `src/data/proofs/erdos-1131/meta.json`
- `src/data/research/problems/erdos-1131-oq-01.json`

### Stats Change
| Metric | Before | After |
|--------|--------|-------|
| Theorems | 14 | **19** |
| Lines | 419 | **548** |

### Analysis of chebyshev_integral_estimate
The axiom `chebyshev_integral_estimate` states ∃c>0, |I_cheb - (2-c/n)| ≤ c/n².
Taking c = n(2-I_cheb), this is trivially satisfied if I_cheb < 2.
So the axiom **reduces to proving I(Chebyshev_n) < 2 for n ≥ 2**.
This in turn requires showing ∫gramOffDiag > 0 for Chebyshev nodes.
Estimated infrastructure: ~300-500 lines of Chebyshev polynomial analysis.

### Next Steps
- Prove I(Chebyshev_n) < 2 for all n ≥ 2 (key blocker)
- Consider explicit n=2 computation: I = 5/3 for ±√2/2 nodes
- Build Chebyshev polynomial T_n representation for exact integral computation

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
