# Problem: Cassini's Identity via the Fibonacci Q-Matrix Determinant

**Slug**: fibonacci-identities-oq-01-oq-03
**Created**: 2026-06-24
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

$$
\det\!\left(\begin{pmatrix}1&1\\1&0\end{pmatrix}^{\!n}\right) = (-1)^n,\quad\text{equivalently}\quad F_{n+1}F_{n-1} - F_n^2 = (-1)^n.
$$

### Plain Language

Cassini's identity says F_{n+1}·F_{n-1} − F_n² = (−1)ⁿ. The parent gallery entry derives it by a direct induction on n. This open question asks for the matrix-theoretic derivation: the Fibonacci Q-matrix Q = [[1,1],[1,0]] satisfies Qⁿ = [[F_{n+1}, F_n],[F_n, F_{n-1}]], so taking determinants of both sides and using det(Qⁿ) = (det Q)ⁿ = (−1)ⁿ recovers Cassini's identity in one line. The goal is to formalize the Q-matrix power formula and obtain Cassini as a corollary of multiplicativity of the determinant.

### Why This Matters

- Recasts an inductive number-theoretic identity as a structural consequence of det(AB)=det(A)det(B), illustrating how linear algebra streamlines recurrence identities.
- The Q-matrix power formula Qⁿ = [[F_{n+1},F_n],[F_n,F_{n-1}]] is itself a reusable gallery lemma that yields the addition formula F_{m+n}=F_{m+1}F_n+F_mF_{n-1} (from Q^{m+n}=Q^m·Q^n) as a bonus.
- Mathlib has Matrix.det, the multiplicativity Matrix.det_pow / Matrix.det_mul, and Nat.fib, so all ingredients exist; the work is the bridge lemma and the 2×2 determinant computation.

## Known Results

### What's Already Proven

- Parent fibonacci-identities-oq-01 (verified, 0-axiom): Cassini's identity F_{n+1}F_{n-1}−F_n²=(−1)ⁿ by induction.
- Mathlib: Matrix.det_pow (det (M^n) = (det M)^n), Matrix.det_fin_two (closed form for 2×2 determinant), Nat.fib_add_two recurrence.
- Classical: the Q-matrix identity Qⁿ = [[F_{n+1},F_n],[F_n,F_{n-1}]] (Knuth, TAOCP Vol. 1).

### What's Still Open

- Q1: Prove the Q-matrix power formula Q^n = !![[F (n+1), F n],[F n, F (n-1)]] over ℤ (or as a Matrix (Fin 2) (Fin 2) ℤ), by induction using the recurrence.
- Q2: Derive Cassini F_{n+1}F_{n-1} − F_n² = (−1)ⁿ as a corollary by taking determinants and using det_pow + det_fin_two.
- Q3 (stretch): obtain the addition formula F_{m+n} = F_{m+1}F_n + F_m F_{n-1} from Q^{m+n} = Q^m·Q^n, and Catalan's identity as the generalization of Cassini.

### Our Goal

Formalize the Fibonacci Q-matrix and its n-th power, then derive Cassini's identity as a one-line determinant corollary (det(Qⁿ)=(det Q)ⁿ=(−1)ⁿ), 0 sorries / 0 axioms.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| fibonacci-identities-oq-01 | parent open question | source of this extension |
| fibonacci-identities | ancestor in the same family | shared definitions and lemmas |

## Initial Thoughts

### Potential Approaches

1. **Q-matrix over ℤ with Fin 2 indexing**: Define Q : Matrix (Fin 2) (Fin 2) ℤ := !![1,1;1,0], prove Q^n = !![F(n+1),F n; F n, F(n-1)] by induction (matrix mul of Fin 2 unfolds via Matrix.mul_fin_two), then det both sides.
   - Risk: The (n-1) entry needs care at n=0; index with F by shifting (use F(n+1),F n, F(n-1) with n≥1 or carry an explicit base case).
2. **Direct determinant evaluation**: Use Matrix.det_fin_two to evaluate det of the closed-form matrix as F(n+1)F(n-1)−F n·F n, and Matrix.det_pow for the RHS (−1)^n.
   - Risk: Aligning Mathlib's det_fin_two entry order (a*d−b*c) with the Fibonacci entries.

### Key Difficulties

- Handling the F_{n-1} term at the base case (n=0 gives F_{-1}; restrict to n≥1 or use the shifted recurrence).
- Matching Mathlib's !![..] matrix literal and Fin 2 multiplication unfolding lemmas to keep proofs short.

### What Would a Proof Need?

- Bridge lemma: Q^n equals the Fibonacci matrix (induction on n).
- det_fin_two and det_pow applications.
- The recurrence Nat.fib_add_two / cast to ℤ.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- All ingredients (matrix determinant multiplicativity, 2×2 det, Fibonacci recurrence) are in Mathlib v4.26.
- Sibling Fibonacci OQ entries (e.g. F_{2m}=F_m·L_m) have been formalized verified/0-axiom, establishing the pattern.
- The only subtlety is index bookkeeping at the base case.

**Estimated Effort**:
- Exploration: hours
- If tractable: days

## References

### Papers
- D. E. Knuth, The Art of Computer Programming, Vol. 1 (1968) §1.2.8 — Fibonacci Q-matrix.
- R. Honsberger, Mathematical Gems III (1985) — Cassini and the Q-matrix.

### Online Resources
- https://en.wikipedia.org/wiki/Fibonacci_sequence#Matrix_form
- https://en.wikipedia.org/wiki/Cassini_and_Catalan_identities

### Mathlib
- Mathlib.LinearAlgebra.Matrix.Determinant.Basic — Matrix.det_pow, Matrix.det_mul
- Mathlib.Data.Matrix.Notation — !![..] literals, Matrix.det_fin_two
- Mathlib.Algebra.BigOperators / Mathlib.Data.Nat.Fib.Basic — Nat.fib recurrence

## Metadata

```yaml
tags:
  - seeker-selected
  - number-theory
  - fibonacci
  - cassini
  - determinant
  - matrix
  - recurrence
  - identity
related_proofs:
  - fibonacci-identities
  - fibonacci-identities-oq-01
difficulty: medium
source: proof-suggestion
created: 2026-06-24
```
