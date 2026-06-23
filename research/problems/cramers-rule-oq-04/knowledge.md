# Knowledge Base: cramers-rule-oq-04

Cramer's Rule and Generalized Inverses via Adjugate.

---

## Session 2026-03-17 (Session 1) - Formalization

**Mode**: FRESH
**Outcome**: completed

### What Was Done
Created CramersRuleOQ04.lean formalizing the adjugate as a generalized inverse.

### Key Theorems
1. adjugate_right/left: A * adj(A) = det(A) * I (both sides)
2. adjugate_reflexive: A * adj(A) * A = det(A) * A (1-reflexive property)
3. adjugate_reflexive_sym: adj(A) * A * adj(A) = det(A) * adj(A)
4. adjugate_scaled_is_right_inv: A * (det(A)^(-1) * adj(A)) = I (non-singular case)
5. cramer_generalized: A * adj(A) * b = det(A) * b (general Cramer)
6. adjugate_kernel_singular: A * adj(A) * b = 0 when det(A) = 0
7. adjugate_cols_in_kernel: adj(A) columns in ker(A) when singular
8. det_adjugate: det(adj(A)) = det(A)^(n-1)

### Status
0 axioms, 0 sorries, Docker build verified.
