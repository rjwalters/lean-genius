# Problem: Non-Commutative Cramer's Rule via Quasideterminants

**Slug**: cramers-rule-oq-03
**Created**: 2026-04-04T21:05:08-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For a 2×2 system over a division ring D with invertible matrix A:

$$
x_0 = |A|_{00}^{-1} \cdot (b_0 - a_{01} \cdot a_{11}^{-1} \cdot b_1)
$$

where $|A|_{ij}$ is the Gelfand-Retakh quasideterminant. Prove this solves $Ax = b$
uniquely, and that it reduces to classical Cramer's Rule when D is commutative.

### Plain Language

Cramer's Rule over commutative fields uses determinants to solve linear systems.
Over non-commutative division rings (like quaternions), determinants are ill-defined.
The Gelfand-Retakh quasideterminant replaces them: for an n×n matrix, the (i,j)
quasideterminant is the inverse of the Schur complement of position (i,j).

This problem asks to formalize in Lean 4:
1. The 2×2 quasideterminant solution formula for non-commutative linear systems
2. Uniqueness of the solution
3. Commutativity reduction: when D is a field, the formula recovers classical Cramer's Rule

### Why This Matters

Quasideterminants are a foundational tool in non-commutative algebra, with applications
to integrable systems, quantum groups, and Lie algebras. Formalizing this 2×2 case
provides the simplest non-trivial instance and validates the infrastructure for
higher-dimensional generalizations.

## Known Results

### What's Already Proven

- `cramers-rule`: Classical Cramer's Rule over commutative rings (gallery)
- `cramers-rule-oq-01`: Adjugate matrix and cofactor expansion (gallery)
- `cramers-rule-oq-02`: Cramer's Rule for non-square overdetermined systems (gallery)
- Gelfand-Retakh (1991, 1992): Quasideterminants theory paper

### What's Still Open

- Full n×n quasideterminant Cramer's Rule in Lean 4
- Connection to Mathlib's `Matrix.det` in commutative specialization

### Our Goal

Formalize the 2×2 case: solution formula, uniqueness, and commutative reduction.
The gallery entry already has a description; we need the Lean proof file.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| cramers-rule | Classical version to reduce to | Matrix invertibility, `det_fin_two` |
| cramers-rule-oq-01 | Adjugate/cofactor machinery | `Matrix.adjugate`, linear maps |
| cramers-rule-oq-02 | Non-square variant | Overdetermined systems |
| cramers-rule-oq-04 | Sibling OQ | Related extension |

## Initial Thoughts

### Potential Approaches

1. **Direct computation**: Define `quasidet₀₀` and `quasidet₁₁` for 2×2 matrices over
   a `DivisionRing`, verify the solution by matrix multiplication, prove uniqueness
   via injectivity of left multiplication.
   - Why it might work: 2×2 case is algebraically explicit
   - Risk: Non-commutativity requires careful left/right distinctions throughout

2. **Schur complement framing**: Frame quasideterminant as Schur complement inverse,
   use existing linear algebra infrastructure in Mathlib.
   - Why it might work: Mathlib has `Matrix.schurComplement` machinery
   - Risk: May not be fully developed for `DivisionRing` (vs `Field`)

### Key Difficulties

- Lean 4 `Matrix` typeclass assumes `CommRing` for determinants; need to work around
- Left vs right inverses require care in a `DivisionRing`
- The reduction to commutative case requires `CommRing` specialization lemma

### What Would a Proof Need?

- Key lemma 1: `quasidet` definition for `Fin 2 × Fin 2` matrices over `DivisionRing`
- Key lemma 2: `mul_quasidet_solution` — A * x = b where x uses the formula
- Key lemma 3: `quasidet_comm_reduces` — specializes to `det / det` when `CommRing`
- Technical requirements: `DivisionRing` instances, `Invertible` typeclass

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- 2×2 restriction makes computation explicit and manageable
- Mathlib has strong `DivisionRing` support
- Gallery already has classical Cramer's Rule to reference
- Main risk: typeclass hierarchy friction between `DivisionRing` and `CommRing`

**Estimated Effort**:
- Exploration: 1-2 days (survey Mathlib DivisionRing, Matrix infrastructure)
- If tractable: 1 week for complete 2×2 formalization
- If hard: Partial result (solution formula only, skip uniqueness/reduction)

## References

### Papers
- Gelfand, Retakh (1991) — "Determinants of matrices over noncommutative rings"
- Gelfand, Retakh (1992) — "Theory of noncommutative determinants, and characteristic functions of graphs"

### Mathlib
- `Mathlib.LinearAlgebra.Matrix.NonsingularInverse` — matrix inverse infrastructure
- `Mathlib.Algebra.GroupWithZero.Units.Lemmas` — division ring lemmas
- `Mathlib.LinearAlgebra.Matrix.DeterminantDivisionRing` — if it exists

## Metadata

```yaml
tags:
  - linear-algebra
  - non-commutative
  - quasideterminants
  - division-rings
  - cramers-rule
related_proofs:
  - cramers-rule
  - cramers-rule-oq-01
  - cramers-rule-oq-02
difficulty: medium
source: gallery-gap
created: 2026-04-04T21:05:08-07:00
```
