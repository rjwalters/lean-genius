# Problem: Chebyshev SL₂ Matrix Multiplicativity Packaging T_add, U_add and the Pell Identity

**Slug**: chebyshev-polynomials-oq-01-oq-01-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Let $T_n, U_n$ be the Chebyshev polynomials of the first and second kind. With the $2\times 2$ "Chebyshev rotation" matrix

$$
M(x) \;=\; \begin{pmatrix} x & x^2-1 \\ 1 & x \end{pmatrix}
\quad\bigl(\text{equivalently } \begin{pmatrix} T_1 & U_1(x^2-1) \\ U_0 & T_1\end{pmatrix}\text{-type data}\bigr),
$$

one has a multiplicative law

$$
A_{m+n}(x) \;=\; A_m(x)\,A_n(x),
\qquad
A_k(x) \;=\; \begin{pmatrix} T_k(x) & (x^2-1)\,U_{k-1}(x) \\ U_{k-1}(x) & T_k(x) \end{pmatrix},
$$

whose $(1,1)$ and $(2,1)$ entries package the addition formulas $T_{m+n}$, $U_{m+n-1}$ and whose determinant $\det A_k = T_k^2 - (x^2-1)U_{k-1}^2 = 1$ is the Pell/Chebyshev identity.

### Plain Language

The Chebyshev polynomials satisfy "angle-addition" formulas analogous to $\cos$ and $\sin$: $T_{m+n}$ and $U_{m+n}$ can be written in terms of $T_m, U_m, T_n, U_n$. These are exactly the statement that a single $2\times 2$ matrix $A_k$ built from $T_k$ and $U_{k-1}$ is multiplicative in the index, $A_{m+n}=A_mA_n$ — the polynomial analogue of $R(\alpha+\beta)=R(\alpha)R(\beta)$ for rotation matrices. Its determinant being identically $1$ is the Chebyshev/Pell relation $T_k^2-(x^2-1)U_{k-1}^2=1$. This problem asks for a clean Lean statement of this `SL₂`-style multiplicativity that yields `T_add`, `U_add`, and the Pell identity as corollaries.

### Why This Matters

Packaging the Chebyshev addition formulas as matrix multiplicativity replaces several ad-hoc polynomial induction proofs with one structural fact, and ties the Chebyshev recurrence to the theory of `SL₂` and Pell equations (the $T_k^2-(x^2-1)U_{k-1}^2=1$ identity is the function-field Pell equation). It gives downstream entries — Pell solutions, continued fractions, Lucas sequences — a single multiplicative engine to cite.

## Known Results

### What's Already Proven

- Parent `chebyshev-polynomials-oq-01-oq-01` (verified): the core Chebyshev recurrence/addition groundwork.
- Mathlib: `Polynomial.Chebyshev.T`, `Polynomial.Chebyshev.U`, `T_add_two`, `U_add_two`, `T_mul`, and the relation `T_sq` / `one_sub_X_sq_mul_U_sq`-style Pell identities; `Matrix.det_fin_two_of`, `Matrix.mul_fin_two`.
- Classical: the $2\times 2$ matrix form generating $T$ and $U$, with $\det = 1$.

### What's Still Open

- A Lean statement `A (m+n) = A m * A n` for the explicit $2\times 2$ Chebyshev matrix, plus the determinant lemma `det (A k) = 1`.
- Extraction of `T_add`, `U_add`, and the Pell identity as entry-wise / determinant corollaries.

### Our Goal

Define $A_k$ as a `Matrix (Fin 2) (Fin 2) (Polynomial ℤ)` (or over a commutative ring), prove $A_{m+n}=A_m A_n$ by the Chebyshev recurrence, and read off the addition formulas from matrix entries and the Pell identity from `Matrix.det`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| chebyshev-polynomials-oq-01-oq-01 | Direct parent; Chebyshev recurrence/addition | orthogonal polynomials |
| chebyshev-polynomials-oq-01 | Root entry; defining recurrences for T, U | recurrence relations |

## Initial Thoughts

### Potential Approaches

1. **Define $A_k$ and prove multiplicativity by induction on $n$.** Base case $A_0 = I$; step uses `T_add_two`/`U_add_two` to match $A_{m+(n+1)} = A_m A_{n+1}$ entrywise via `Matrix.mul_fin_two` and `ring`.
   - Why it might work: the recurrence is exactly what the matrix product encodes; entrywise goals close by `ring` after expanding.
   - Risk: index bookkeeping for $U_{k-1}$ at $k=0$; choosing the matrix entries so the recurrence aligns without off-by-one snags.

2. **Identify $A_k = M^k$ for the generator $M = A_1$ and use `Matrix.det_pow`.** Then `T_add`/`U_add` follow from $M^{m+n}=M^mM^n$ and the Pell identity from $\det(M^k)=(\det M)^k = 1$.
   - Why it might work: mirrors the Fibonacci/Lucas Q-matrix entries already in the gallery; `det_pow` gives the Pell identity for free.
   - Risk: proving $A_1 = M$ and $A_k = M^k$ requires the same induction; determinant of $M$ must be shown $=1$ first.
