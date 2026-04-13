# Problem: Rational Canonical Form Determines Similarity Class

**Slug**: cayley-hamilton-minpoly-oq-02-oq-02-oq-01
**Created**: 2026-04-05T00:00:00-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
A \sim B \iff \text{RCF}(A) = \text{RCF}(B)
$$

More precisely: two square matrices $A, B \in M_n(F)$ over a field $F$ are similar (there exists an invertible $P$ such that $B = PAP^{-1}$) if and only if they have the same rational canonical form — equivalently, the same list of invariant factors.

### Plain Language

The rational canonical form (RCF) provides a complete invariant for matrix similarity over any field. The minimal polynomial alone does NOT determine the similarity class (two matrices can share a minimal polynomial but differ in invariant factors), but the full sequence of invariant factors does.

### Why This Matters

This is a fundamental theorem of linear algebra. The RCF theorem:
1. Gives a computable complete invariant for similarity (no field extension required, unlike JCF)
2. Follows from the structure theorem for finitely generated modules over a PID
3. Generalizes directly to linear operators on modules, not just vector spaces
4. Is strictly stronger than the minimal polynomial characterization

This is the "if" direction of the similarity characterization: same invariant factors implies similar matrices.

## Known Results

### What's Already Proven

- `cayley-hamilton`: Every matrix satisfies its characteristic polynomial
- `cayley-hamilton-minpoly`: The minimal polynomial divides the characteristic polynomial
- `cayley-hamilton-minpoly-oq-02`: Similar matrices have identical minimal polynomials (the "only if" direction)
- Mathlib: Structure theorem for finitely generated modules over a PID (`Module.torsion_over_pid` or similar)
- Mathlib: `minpoly.dvd`, `Polynomial.degree_pos_of_root` — polynomial infrastructure
- Mathlib: `Matrix.charpoly` — characteristic polynomial definition

### What's Still Open

- Formalization of the full RCF theorem in Lean: `A ~ B ↔ invariantFactors A = invariantFactors B`
- The "if" direction: same invariant factors → constructing the conjugating matrix $P$
- Connecting Mathlib's module-theoretic infrastructure to the matrix-theoretic statement
- Showing that the invariant factors uniquely determine a matrix up to similarity

### Our Goal

Prove in Lean 4:

```lean
theorem similar_iff_eq_invariantFactors {F : Type*} [Field F] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) F) :
    Matrix.Similar A B ↔ invariantFactors A = invariantFactors B
```

or an equivalent formulation using the rational canonical form directly.

## Mathematical Approach

### Key Idea

View $F^n$ as an $F[x]$-module via the action $x \cdot v = Av$. Two matrices $A, B$ are similar iff the corresponding $F[x]$-modules $M_A$ and $M_B$ are isomorphic. By the structure theorem for finitely generated torsion modules over the PID $F[x]$:

$$
M_A \cong \bigoplus_i F[x]/(f_i(x))
$$

where $f_1 \mid f_2 \mid \cdots \mid f_k$ are the invariant factors. The module isomorphism class is uniquely determined by these invariant factors.

### Lean Strategy

1. Define `Matrix.toModule` — the $F[x]$-module structure on $F^n$ induced by $A$
2. Apply `Module.torsion_over_pid` (if it exists in Mathlib) to decompose
3. Show that `Matrix.Similar A B ↔ Nonempty (LinearEquiv (F[x]) (toModule A) (toModule B))`
4. Apply the uniqueness part of the structure theorem

### Alternative: Direct Invariant Factor Approach

If the module-theoretic path is too abstract, formalize via:
1. Smith Normal Form of `(xI - A)` gives the invariant factors directly
2. Two matrices have the same SNF of `(xI - A)` iff they are similar
3. Mathlib might have `Matrix.smithNormalForm` available

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| cayley-hamilton | Foundation: matrix satisfies characteristic poly | charpoly evaluation |
| cayley-hamilton-minpoly | Minimal polynomial infrastructure | minpoly, dvd relations |
| cayley-hamilton-minpoly-oq-02 | Same proof family: similar → same minpoly | Matrix.Similar API |
| cayley-hamilton-minpoly-oq-01 | Jordan canonical form (related canonical form) | JCF over algebraically closed fields |

## Related Open Questions

- `cayley-hamilton-minpoly-oq-02-oq-02-oq-02`: Jordan Normal Form over algebraically closed fields (complement approach)
- `cayley-hamilton-minpoly-oq-01-oq-03`: Rational canonical form via companion matrix decomposition (direct construction approach)
- `cayley-hamilton-minpoly-oq-02-oq-03`: Full similarity invariance of rational canonical form

## Suggested First Steps

1. **OBSERVE**: Search Mathlib for existing RCF infrastructure — `Matrix.toList_invariantFactors`, `Matrix.rationCanonicalForm`, or `Module.torsion_over_pid`
2. **ORIENT**: Determine whether to go via Smith Normal Form of `(xI - A)` or via module theory
3. **DECIDE**: If Mathlib has `Matrix.smithNormalForm`, use it; otherwise, formalize via the $F[x]$-module approach
