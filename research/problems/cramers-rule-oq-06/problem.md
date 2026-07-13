# Problem: The Adjugate Algebra - Multiplicative and Conjugation Identities Behind Cramer's Rule

**Slug**: cramers-rule-oq-06
**Created**: 2026-07-01
**Status**: Active
**Source**: proof-suggestion <!-- gallery open-question spawned from verified parent -->
**Parent**: cramers-rule

## Problem Statement

### Formal Statement

$$
\mathrm{adj}(AB)=\mathrm{adj}(B)\,\mathrm{adj}(A),\quad
\mathrm{adj}(A^k)=\mathrm{adj}(A)^k,\quad
\det(\mathrm{adj}\,A)=(\det A)^{n-1},\quad
\mathrm{adj}(\mathrm{adj}\,A)=(\det A)^{n-2}A\ (n\neq 1),
$$
and the original corollary $\mathrm{adj}(UAU^{-1}) = \mathrm{adj}(U)^{-1}\,\mathrm{adj}(A)\,\mathrm{adj}(U)$: similar matrices have similar adjugates.

### Plain Language

Cramer's rule rests on the single adjugate identity $A\cdot\mathrm{adj}(A)=\det(A)I$. This
child studies the adjugate as an operation in its own right, proving its *compositional*
algebra: it is an anti-homomorphism on products, commutes with transpose and powers,
scales its determinant by $(\det A)^{n-1}$, and is an involution up to a determinant factor.
As an original corollary, the adjugate of a conjugate is the conjugate of the adjugate — so
the adjugate descends to conjugacy classes.

### Why This Matters

The parent proves Cramer's rule from $A\cdot\mathrm{adj}(A)=\det(A)I$. This child assembles
the adjugate's algebraic laws and proves two original results (units have invertible
adjugates that respect inversion; similar matrices have similar adjugates) not present in
Mathlib and distinct from siblings oq-04 (two-sided identity, singular case) and oq-05
(det/trace/charpoly conjugation invariance).

## Known Results

### What's Already Proven

- Parent `cramers-rule` is verified (0-axiom).
- Mathlib has `Matrix.adjugate_mul_distrib`, `adjugate_pow`, `det_adjugate`,
  `adjugate_adjugate`, `adjugate_one`.

### What's Still Open

- The target theorems below (currently `sorry`), including the two original conjugation
  results.

### Our Goal

Prove the sketch below as a verified (0-axiom) child. Category: **companion / corollary**.

## Target Lean Sketch

```lean
open Matrix
variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

theorem adjugate_anti_mul (A B : Matrix n n R) :
    (A * B).adjugate = B.adjugate * A.adjugate := by
  sorry -- Matrix.adjugate_mul_distrib

theorem det_adjugate' (A : Matrix n n R) :
    A.adjugate.det = A.det ^ (Fintype.card n - 1) := by
  sorry -- Matrix.det_adjugate

theorem adjugate_adjugate' (A : Matrix n n R) (h : Fintype.card n ≠ 1) :
    A.adjugate.adjugate = A.det ^ (Fintype.card n - 2) • A := by
  sorry -- Matrix.adjugate_adjugate

/-- ORIGINAL: adj sends mutually-inverse pairs to mutually-inverse pairs. -/
theorem adjugate_mul_adjugate_inv {A B : Matrix n n R} (h : A * B = 1) (h' : B * A = 1) :
    A.adjugate * B.adjugate = 1 ∧ B.adjugate * A.adjugate = 1 := by
  sorry -- ← adjugate_mul_distrib; simp [h, h', adjugate_one]

/-- ORIGINAL corollary: similar matrices have similar adjugates. -/
theorem adjugate_conj (A U Uinv : Matrix n n R)
    (h : U * Uinv = 1) (h' : Uinv * U = 1) :
    (U * A * Uinv).adjugate = Uinv.adjugate * A.adjugate * U.adjugate := by
  sorry -- adjugate_mul_distrib twice + reassociate
```

Plus a concrete `Fin 2` example via `adjugate_fin_two_of`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `cramers-rule` | Parent: Cramer's rule | adjugate, determinants |
| `cramers-rule-oq-04` | Sibling: two-sided adjugate identity, singular case | adjugate |
| `cayley-hamilton` | Uses adjugate / characteristic polynomial | matrix algebra |

## Tractability Assessment

**Difficulty**: Low

**Significance**: 5/10  |  **Tractability**: 9/10  |  **Tier**: B

**Justification**: Most content is curated Mathlib wrappers plus two short original lemmas
(~5 lines each) built by chaining `adjugate_mul_distrib`. No hard tactic work; stays
`verified`, `axiomCount: 0`.

### Suggested First Steps

1. Wrap `adjugate_mul_distrib`, `adjugate_pow`, `det_adjugate`, `adjugate_adjugate` as the
   named identities.
2. Prove `adjugate_mul_adjugate_inv` using `← adjugate_mul_distrib` and `adjugate_one`.
3. Prove `adjugate_conj` by chaining `adjugate_mul_distrib` twice; add the `Fin 2` example.

## References

### Mathlib

- `Matrix.adjugate_mul_distrib`, `adjugate_pow`, `adjugate_transpose` — LinearAlgebra/Matrix/Adjugate.lean
- `Matrix.det_adjugate`, `adjugate_adjugate`, `adjugate_one`, `adjugate_fin_two_of` — LinearAlgebra/Matrix/Adjugate.lean
- `Matrix.mul_adjugate` — LinearAlgebra/Matrix/Adjugate.lean (ties back to parent)

### Literature

- Standard linear-algebra treatments of the adjugate/classical adjoint.

## Metadata

```yaml
tags:
  - linear-algebra
  - adjugate
  - cramers-rule
  - determinants
related_proofs:
  - cramers-rule
  - cramers-rule-oq-04
  - cayley-hamilton
difficulty: low
source: proof-suggestion
created: 2026-07-01
```
