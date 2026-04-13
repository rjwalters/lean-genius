# Problem: Does Mathlib's Matrix.smithNormalForm Infrastructure Cover the Axiomatized Linear Diophantine Results?

**Slug**: bezout-identity-oq-04-oq-01-oq-03
**Created**: 2026-04-05T04:27:09-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Given the proof `bezout-identity-oq-04-oq-01` (Linear Diophantine Systems via Smith Normal Form), which axiomatizes results about Smith normal form decomposition for integer matrices, can these axioms be eliminated using Mathlib's existing infrastructure?

Concretely: does Mathlib already provide theorems sufficient to prove:
1. Every integer matrix `A : Matrix m n ℤ` has a Smith normal form `D = PAQ` with `P`, `Q` invertible over `ℤ`
2. The system `Ax = b` has a solution iff each diagonal invariant factor of `D` divides the corresponding entry of `P * b`
3. The solution set is a coset of `ker A`

### Plain Language

The parent proof `bezout-identity-oq-04-oq-01` formalized linear Diophantine systems using Smith normal form, but had to axiomatize some results. The question is whether Mathlib's `Matrix.smithNormalForm` (or equivalent PID-module theory) already provides the machinery to turn those axioms into theorems.

### Why This Matters

If Mathlib already has Smith normal form for integer matrices, we can upgrade a conditional proof to a fully verified one, reducing axiom count in the gallery entry. This is a concrete Mathlib survey task with a clear binary outcome.

## Known Results

### What's Already Proven

- Bézout's identity in Mathlib: `Int.gcd_eq_gcd_ab`, extended Euclidean algorithm
- `bezout-identity` gallery proof: `bezout_int : ∀ a b : ℤ, ∃ u v, u * a + v * b = Int.gcd a b`
- `bezout-identity-oq-04-oq-01` gallery: Linear Diophantine Systems via Smith Normal Form (axiomatized)
- Mathlib: `Mathlib.LinearAlgebra.FreeModule.PID` covers finitely generated modules over PIDs

### What's Still Open

- Whether `Matrix.smithNormalForm` or a concrete equivalent exists in Mathlib for `Matrix m n ℤ`
- Whether the divisibility solvability criterion is directly provable from Mathlib

### Our Goal

Survey Mathlib for Smith normal form infrastructure over `ℤ`. Determine if the axioms in `bezout-identity-oq-04-oq-01` are provable. If yes, sketch the elimination proof. If no, document what is missing and what a Mathlib contribution would need.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| bezout-identity | Parent proof of Bézout's identity | `Int.gcd_eq_gcd_ab`, extended Euclidean |
| bezout-identity-oq-04-oq-01 | Direct parent: linear Diophantine via Smith NF | Smith normal form axioms |

## Initial Thoughts

### Potential Approaches

1. **Mathlib source search**: Grep for `smithNormalForm`, `SmithNormalForm`, `smith_normal_form` in Mathlib
   - Why it might work: Mathlib has strong linear algebra coverage; SNF over PIDs was discussed/added circa 2023-2024
   - Risk: May be stated for abstract modules only, not as matrix decomposition

2. **Check `Mathlib.LinearAlgebra.FreeModule.PID`**: This module proves structure theorem for finitely generated modules over PIDs
   - Why it might work: `ℤ` is a PID; structure theorem implies Smith NF
   - Risk: May not be phrased as a matrix factorization directly

3. **Loogle search**: Query `Matrix` + `smithNormal` or `invariantFactor`
   - Why it might work: Direct lookup, fastest path

### Key Difficulties

- Smith normal form over `ℤ` requires explicit algorithmic reduction (Euclidean algorithm for rows/columns)
- Mathlib's module-theoretic Smith NF may not lift directly to concrete matrix form

### What Would a Proof Need?

- Mathlib: `∃ P Q : GL n ℤ, (P : Matrix n n ℤ) * A * Q = Matrix.diagonal d`
- Mathlib: `Module.Free.smithNormalForm` or equivalent

## Tractability Assessment

**Difficulty**: Low (if Mathlib has concrete matrix SNF) / Medium (if needs adaptation from module theory)

**Justification**:
- Primarily a Mathlib survey question, not a novel proof
- If SNF exists in Mathlib, integration is a refactor of `bezout-identity-oq-04-oq-01`
- If SNF is only in module form, bridging to matrix form may take 1-2 days

**Estimated Effort**:
- Exploration: 1-3 hours (Mathlib search)
- If tractable: 1-3 days (integration)
- If hard: document gap, propose Mathlib PR path

## References

### Mathlib
- `Mathlib.LinearAlgebra.FreeModule.PID` — structure theorem for f.g. modules over PIDs
- `Mathlib.RingTheory.PrincipalIdealDomain` — PID theory
- `Mathlib.LinearAlgebra.Matrix.Determinant` — matrix operations

## Metadata

```yaml
tags:
  - number-theory
  - linear-algebra
  - smith-normal-form
  - diophantine
  - matrices
  - mathlib-survey
  - axiom-elimination
related_proofs:
  - bezout-identity
  - bezout-identity-oq-04-oq-01
difficulty: low-medium
source: gallery-gap
created: 2026-04-05T04:27:09-07:00
```
