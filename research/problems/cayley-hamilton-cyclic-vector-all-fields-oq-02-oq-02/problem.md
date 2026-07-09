# Problem: Dimension of the commutant: dim_K C(M) = n for nonderogatory M

**Slug**: cayley-hamilton-cyclic-vector-all-fields-oq-02-oq-02
**Created**: 2026-07-09T16:03:14-07:00
**Status**: Active
**Source**: user-request <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

Let $K$ be a field and $M \in K^{n\times n}$. Write $C(M) = \{A \in K^{n\times n} : AM = MA\}$ for the centralizer (commutant) of $M$, a $K$-subalgebra of $K^{n\times n}$.

$$
M \text{ nonderogatory} \;\Longleftrightarrow\; \mu_M = \chi_M \;\Longleftrightarrow\; \dim_K C(M) = n \;\Longleftrightarrow\; C(M) = K[M].
$$

More generally (Frobenius), if the invariant factors of $M$ have degrees $d_1 \mid d_2 \mid \cdots \mid d_k$ (equivalently, taking the elementary divisors of $M$ into account), then

$$
\dim_K C(M) \;=\; \sum_{i,j} \min(d_i, d_j) \;=\; \sum_{i=1}^{k} (2i - 1)\, d_i,
$$

where in the second form the degrees are ordered $d_1 \ge d_2 \ge \cdots \ge d_k$. This always satisfies $\dim_K C(M) \ge n = \sum_i d_i$, with equality exactly when $k = 1$, i.e. when $M$ is nonderogatory.

### Plain Language

The commutant of a matrix $M$ is the set of all matrices that commute with it. Polynomials in $M$ — things like $c_0 I + c_1 M + c_2 M^2 + \cdots$ — always commute with $M$, so $K[M]$ sits inside the commutant. When $M$ is *nonderogatory* (its minimal polynomial equals its characteristic polynomial, equivalently it has a cyclic vector), there is nothing else: the commutant is exactly $K[M]$ and has dimension $n$. This problem asks to formalize that dimension count — that $\dim_K C(M) = n$ precisely in the nonderogatory case — and the general Frobenius formula $\dim_K C(M) = \sum_i (2i-1) d_i$ that measures how much larger the commutant becomes when $M$ is *derogatory* (has repeated invariant factors).

### Why This Matters

- It completes the standard triple characterization of nonderogatory matrices (minpoly = charpoly $\Leftrightarrow$ cyclic vector $\Leftrightarrow$ commutant $= K[M]$) with a clean *quantitative* invariant, $\dim_K C(M)$, closing the loop opened by the parent gallery entry which proved only the set-level inclusion $C(M) \subseteq K[M]$.
- The Frobenius commutant-dimension formula is a foundational result in the theory of similarity of matrices and modules over a PID; it is the algebraic heart of statements about how many degrees of freedom a matrix can commute with, and appears in representation theory, control theory (controllability of $(M, v)$), and the classification of commuting varieties.
- A machine-checked dimension formula would give Mathlib a reusable bridge between the rational canonical form / invariant-factor decomposition and explicit centralizer computations.

## Known Results

### What's Already Proven

- **Set-level inclusion, cyclic case** — `commuting_matrix_is_polynomial` in the parent gallery entry (`cayley-hamilton-cyclic-vector-all-fields-oq-02`) proves that if $M$ has a cyclic vector then every commuting matrix is a polynomial in $M$, i.e. $C(M) = K[M]$ over an arbitrary field (0 sorries, 0 axioms, Mathlib v4.26.0).
- **Nonderogatory $\Leftrightarrow$ cyclic vector** — the ancestor entries (`cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01` and `cayley-hamilton-cyclic-vector-all-fields`) establish $\mu_M = \chi_M \Leftrightarrow M$ has a cyclic vector, over arbitrary fields.
- **Krylov basis** — `krylov_linearIndependent`: the family $\{M^k v\}_{k<n}$ of a cyclic vector is linearly independent, hence a basis of $K^n$; and $\dim_K K[M] = \deg \mu_M$ is standard (in the nonderogatory case this is $n$).
- Classically (Hoffman & Kunze §7.5; Gantmacher, *Theory of Matrices*, Ch. VIII), the full biconditional $\dim_K C(M) = n \Leftrightarrow M$ nonderogatory and the Frobenius formula $\dim_K C(M) = \sum_i (2i-1)d_i$ are known theorems.

### What's Still Open

- No Lean formalization of the *dimension* statement $\dim_K C(M) = n$ for nonderogatory $M$ (only the set equality $C(M) = K[M]$ is in the gallery).
- The general Frobenius formula $\dim_K C(M) = \sum_{i,j}\min(d_i,d_j)$ for arbitrary (derogatory) $M$ is not formalized.
- The converse edge $C(M) = K[M] \Rightarrow M$ has a cyclic vector (the (iii)$\Rightarrow$(ii) direction) is not yet in the gallery.

### Our Goal

Formalize, over an arbitrary field $K$:
1. **Nonderogatory case (primary target):** $\dim_K C(M) = n$ when $M$ is nonderogatory. This follows from the existing $C(M) = K[M]$ plus $\dim_K K[M] = \deg\mu_M = n$. Package it as a `finrank` equality on the centralizer subalgebra/submodule.
2. **Full biconditional:** $\dim_K C(M) = n \Leftrightarrow M$ nonderogatory (the reverse direction needs the derogatory lower bound $\dim_K C(M) \ge n+1$).
3. **Stretch — Frobenius formula:** $\dim_K C(M) = \sum_i (2i-1)d_i$ in terms of invariant-factor degrees, via the rational canonical form decomposition.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| cayley-hamilton-cyclic-vector-all-fields-oq-02 | Parent — proves $C(M) = K[M]$ (set level) for cyclic $M$; this problem adds the dimension count $\dim_K C(M)=n$ on top | Krylov basis, coordinates of $A\cdot v$, agreement on a basis, column-wise matrix recovery |
| cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01 | Ancestor — biconditional nonderogatory $\Leftrightarrow$ cyclic vector, supplying the equivalence used to translate the hypothesis | Minimal/characteristic polynomial, cyclic vector existence |
| cayley-hamilton-cyclic-vector-all-fields | Ancestor — forward direction nonderogatory $\Rightarrow$ cyclic vector via primary decomposition | Primary decomposition over arbitrary fields |
| cayley-hamilton-minpoly | Related — minimal-polynomial general theory underpinning $\dim_K K[M] = \deg\mu_M$ | `minpoly`, `aeval`, Cayley–Hamilton |

## Initial Thoughts

### Potential Approaches

1. **Approach A — reduce the nonderogatory case to the existing set equality**: Use `commuting_matrix_is_polynomial` to get $C(M) = K[M]$ as sets/submodules, then compute $\dim_K K[M]$. Since $K[M] \cong K[X]/(\mu_M)$ as $K$-algebras and $\dim_K K[X]/(\mu_M) = \deg\mu_M$, and nonderogatory means $\deg\mu_M = \deg\chi_M = n$, conclude $\dim_K C(M) = n$.
   - Why it might work: all three ingredients (the set equality, the quotient dimension, and $\deg\mu_M = n$) are either already proven in the gallery or standard in Mathlib.
   - Risk: plumbing the set equality into a `Submodule.finrank` equality; need the powers $\{I, M, \dots, M^{n-1}\}$ to be independent (equivalently the aeval map $K[X]/(\mu_M) \to K[M]$ is a linear iso), which requires care with $\deg \mu_M = n$.

2. **Approach B — build a basis of $C(M)$ directly**: Exhibit $\{I, M, \dots, M^{n-1}\}$ as a basis of $C(M)$ in the nonderogatory case. Spanning is the parent theorem; independence is $\deg\mu_M = n$.
   - Why it might work: gives the dimension by `Basis.card` / `finrank_eq_card_basis`, avoiding an explicit quotient iso.
   - Risk: proving the independence of matrix powers cleanly and identifying the resulting basis with the centralizer submodule.

3. **Approach C — Frobenius via rational canonical form**: Decompose $M$ into companion blocks of its invariant factors, compute $\dim C$ of block-diagonal matrices as a sum over $\min(d_i,d_j)$ Hom-spaces between cyclic modules ($\dim_K \operatorname{Hom}_{K[X]}(K[X]/(f_i), K[X]/(f_j)) = \deg\gcd(f_i,f_j)$).
   - Why it might work: it is the "right" structural proof and directly yields both the nonderogatory case ($k=1$) and the general formula.
   - Risk: substantial — needs invariant-factor decomposition, Hom-dimension over $K[X]$, and assembling block Hom-spaces; likely a multi-week formalization.

### Key Difficulties

- Turning the *set* equality $C(M) = K[M]$ into a `finrank`/`Submodule` dimension statement (choosing the right submodule structure on the centralizer and matching it with `K[M]`).
- Establishing $\dim_K K[M] = \deg\mu_M$ cleanly in Mathlib (the algebra $K[M] \cong K[X]/(\mu_M)$ isomorphism and its dimension).
- For the biconditional, the derogatory *lower* bound $\dim_K C(M) \ge n+1$ requires exhibiting a matrix in $C(M)\setminus K[M]$ — the hardest elementary step.
- The Frobenius formula needs the invariant-factor / rational-canonical-form machinery and Hom-space dimensions between cyclic $K[X]$-modules, much of which is not yet packaged in Mathlib.

### What Would a Proof Need?

- Key lemma 1: $\dim_K K[M] = \deg\mu_M$ (via $K[M] \cong K[X]/(\mu_M)$ and `Polynomial.finrank_quotient_span` / degree-of-minpoly facts).
- Key lemma 2: the centralizer $C(M)$ is a `Submodule K (Matrix (Fin n) (Fin n) K)` (or a subalgebra) whose carrier equals that of $K[M]$ in the nonderogatory case (from `commuting_matrix_is_polynomial` + `aeval_commute`).
- Key lemma 3 (nonderogatory $\Rightarrow$): combine to get `finrank K C(M) = n`.
- Technical requirements: `Module.finrank`, `Submodule.finrank_le`, `LinearEquiv`/`AlgEquiv` for $K[M]\cong K[X]/(\mu_M)$, `Polynomial.natDegree`, and for the Frobenius case the invariant-factor decomposition (`Matrix`/`Module` structure theorem over the PID $K[X]$).

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The **nonderogatory dimension statement** ($\dim_K C(M)=n$) is the most reachable piece: it is essentially a corollary of the already-proven $C(M)=K[M]$ plus the standard $\dim_K K[M]=\deg\mu_M$. The main work is Submodule/finrank plumbing — moderate, not open-ended.
- The **full biconditional** and especially the **Frobenius formula** are genuinely hard: they need the rational-canonical-form / invariant-factor decomposition and Hom-space dimensions over $K[X]$, machinery that is only partially available in Mathlib. This pushes the overall problem into High.
- Similar solved anchors: the parent entry (set equality) is machine-verified; Mathlib has `minpoly`, `charpoly`, Cayley–Hamilton, and quotient-dimension APIs, so the nonderogatory case has a clear path.

**Estimated Effort**:
- Exploration: 2–4 days (locate `dim K[M]` and centralizer-submodule APIs in Mathlib)
- If tractable (nonderogatory case only): 1–2 weeks
- If hard (full biconditional + Frobenius formula): unknown, likely multi-week to months

## References

### Papers
- K. Hoffman & R. Kunze, *Linear Algebra*, 2nd ed., §7.2 and §7.5 — the triple equivalence and the commutant characterization of nonderogatory matrices.
- F. R. Gantmacher, *The Theory of Matrices*, Vol. I, Ch. VIII — Frobenius's formula $\dim_K C(M) = \sum_i (2i-1)d_i$ for the dimension of the commutant.
- N. Jacobson, *Basic Algebra I* — modules over a PID, invariant factors, and $\operatorname{Hom}$ between cyclic modules.

### Online Resources
- https://en.wikipedia.org/wiki/Commuting_matrices — overview, including the dimension of the commutant.
- https://en.wikipedia.org/wiki/Frobenius_normal_form — rational canonical form and invariant factors underlying the Frobenius formula.

### Mathlib
- `Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly` — minimal and characteristic polynomials of matrices; nonderogatory means `minpoly = charpoly`.
- `Mathlib.RingTheory.Polynomial.Basic` / `Mathlib.FieldTheory.Minpoly.Field` — `minpoly`, `aeval`, and $K[M]\cong K[X]/(\mu_M)$ facts.
- `Mathlib.LinearAlgebra.Dimension.Finrank` / `Mathlib.LinearAlgebra.FiniteDimensional` — `Module.finrank`, `finrank_eq_card_basis`, `Submodule.finrank`.
- `Mathlib.LinearAlgebra.Matrix.Basis` / `Mathlib.LinearAlgebra.FreeModule.PID` — bases and (for the Frobenius stretch goal) the structure theorem / invariant factors over the PID `K[X]`.

## Metadata

```yaml
tags:
  - linear-algebra
  - matrices
  - cyclic-vector
  - cayley-hamilton
  - minimal-polynomial
  - nonderogatory
  - commutant
  - centralizer
  - research
  - open-question
related_proofs:
  - cayley-hamilton-cyclic-vector-all-fields-oq-02
  - cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01
  - cayley-hamilton-cyclic-vector-all-fields
difficulty: high
source: user-request
created: 2026-07-09T16:03:14-07:00
```
