# Problem: Lagrange's Identity as the n = 2 Case of a Formalized Binet–Cauchy Identity

**Slug**: cauchy-schwarz-oq-05-oq-02
**Created**: 2026-07-02T11:12:11-07:00
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

Let $A$ be an $m \times n$ matrix over a commutative ring $R$ (think of $m$ rows, $n \ge m$ columns).
The **Binet–Cauchy / Cauchy–Binet identity** expresses the determinant of a product of a
"wide" and a "tall" matrix as a sum of products of maximal minors:

$$
\det\!\big(A\,B\big) \;=\; \sum_{\substack{S \subseteq \{1,\dots,n\} \\ |S| = m}} \det\!\big(A_{\bullet,\,S}\big)\,\det\!\big(B_{S,\,\bullet}\big),
$$

where $A_{\bullet,S}$ is the $m \times m$ submatrix of $A$ on the column set $S$ and $B_{S,\bullet}$ is
the $m \times m$ submatrix of $B$ on the row set $S$. Specializing $B = A^{\mathsf T}$ gives the
**Gram / Cauchy–Binet square form**

$$
\det\!\big(A\,A^{\mathsf T}\big) \;=\; \sum_{|S| = m} \big(\det A_{\bullet,S}\big)^2 .
$$

Now take $m = 2$, so $A$ has two rows $a = (a_1,\dots,a_n)$ and $b = (b_1,\dots,b_n)$. Then
$A A^{\mathsf T} = \begin{pmatrix} \sum_i a_i^2 & \sum_i a_i b_i \\ \sum_i a_i b_i & \sum_i b_i^2 \end{pmatrix}$,
whose determinant is $(\sum_i a_i^2)(\sum_i b_i^2) - (\sum_i a_i b_i)^2$, and each $2\times 2$ minor on the
column pair $S = \{i,j\}$ is $a_i b_j - a_j b_i$. The $m = 2$ Cauchy–Binet square form is therefore
**exactly** Lagrange's identity in its strict-upper-triangle form:

$$
\Big(\sum_i a_i^2\Big)\Big(\sum_i b_i^2\Big) - \Big(\sum_i a_i b_i\Big)^2 \;=\; \sum_{i < j} \big(a_i b_j - a_j b_i\big)^2 .
$$

**Goal:** Formalize the Binet–Cauchy identity `det (A * Aᵀ) = ∑_{S} (det (A.submatrix id S))^2`
(and ideally the general two-matrix form `det (A * B) = ∑_S det(A_S) · det(B_S)`) in Lean 4 / Mathlib,
and derive the parent's `lagrange_identity` (`cauchy-schwarz-oq-05`) as the `m = 2` specialization.

### Plain Language

The parent entry proves *Lagrange's identity*: for finite real sequences $a$ and $b$, the exact gap in
the Cauchy–Schwarz inequality equals a sum of squared $2\times 2$ minors $(a_i b_j - a_j b_i)^2$ taken
over pairs $i < j$. That identity is not an isolated trick — it is the smallest, two-row instance of a
much more general theorem about determinants, the **Cauchy–Binet formula**, which says the determinant of
a product of matrices is a sum of products of their maximal minors. The task is to write the Cauchy–Binet
formula down in Lean, prove it, and then plug in "two rows" to get Lagrange's identity for free, showing the
parent result is a corner of a determinant-theoretic edifice rather than a bespoke `Finset` computation.

### Why This Matters

Formalizing Cauchy–Binet ties the analytic world (the Cauchy–Schwarz inequality and its exact defect) to
the linear-algebra world (determinants, exterior/wedge products, Gram matrices) inside one proof. It is a
genuinely missing Mathlib theorem: `Matrix.det_mul` handles *square times square*, but there is currently no
`Matrix.det_mul_submatrix`-style Cauchy–Binet for *rectangular* factors. Landing it would:

- unify Cauchy–Schwarz, Lagrange's identity, the wedge-product norm identity
  $\|u\|^2\|v\|^2 - \langle u,v\rangle^2 = \|u\wedge v\|^2$, and Gram-determinant positivity under a single umbrella;
- give Mathlib a tool needed for compound matrices, the Plücker relations, matrix-tree / spanning-tree
  counting (the matrix-tree theorem is a Cauchy–Binet application), and volume-of-parallelepiped formulas;
- turn the parent's ad-hoc "triangle-doubling of a symmetric kernel" argument into a *corollary* of a
  reusable structural result.

## Known Results

### What's Already Proven

- `Matrix.det_mul : det (M * N) = det M * det N` for **square** `M N : Matrix n n R` — `Mathlib.LinearAlgebra.Matrix.Determinant.Basic:138`.
- `Matrix.det_fin_two : det A = A 0 0 * A 1 1 - A 0 1 * A 1 0` — the explicit $2\times2$ determinant, `Mathlib.LinearAlgebra.Matrix.Determinant.Basic:809`.
- `Matrix.cross_dot_cross : u ⨯₃ v ⬝ᵥ w ⨯₃ x = u ⬝ᵥ w * v ⬝ᵥ x - u ⬝ᵥ x * v ⬝ᵥ w` — the scalar quadruple product identity, explicitly annotated "related to the Binet–Cauchy identity", `Mathlib.LinearAlgebra.CrossProduct:125`. This is a fixed-dimension ($\mathrm{Fin}\,3$) fragment, not the general formula.
- `norm_inner_le_norm : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖` — abstract Cauchy–Schwarz in any inner-product space, `Mathlib.Analysis.InnerProductSpace.Basic:441` (the `Finset` sum form is `inner_mul_le_norm_mul_norm` on `EuclideanSpace`).
- The parent `cauchy-schwarz-oq-05` (`Proofs/CauchySchwarzOQ05.lean`): `lagrange_identity`, `cauchy_schwarz`, `cauchy_schwarz_eq_iff` and the reusable `sum_offDiag_eq_two_mul_sum_filter_lt` — the exact `m = 2` target of this specialization, fully verified (0 axioms, 0 sorries).

### What's Still Open

- **There is no general Cauchy–Binet / Binet–Cauchy formula in Mathlib.** A search for `Binet` finds only Binet's Fibonacci formula (`NumberTheory.Real.GoldenRatio`) and the `Fin 3` quadruple product; a search for `cauchy.*binet` / `compound` matrix returns nothing. The rectangular-product determinant identity `det (A * B) = ∑_S det(A_S) · det(B_S)` must be built.
- Whether the cleanest route is the fully general two-matrix statement or the specialized square form `det (A * Aᵀ) = ∑_S (det A_S)²` sufficient to reach Lagrange.

### Our Goal

Prove, in Lean 4 with Mathlib, the Cauchy–Binet identity — at minimum the Gram square form
`det (A * Aᵀ) = ∑_{S : Finset colIdx, |S| = m} (det (A.submatrix id (S.orderEmbOfFin …)))²` — and then instantiate
it at `m = 2` to re-derive the parent's `lagrange_identity`. Success means the strict-upper-triangle
Cauchy–Schwarz defect emerges as `det_fin_two` of `A Aᵀ` plus a reindexing of the size-2 column subsets onto
the `i < j` pairs used in the parent.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| cauchy-schwarz-oq-05 | The parent; its `lagrange_identity` is the `m = 2` target this OQ derives from Cauchy–Binet | Triangle-doubling of a symmetric kernel, swap involution, `Finset.sum_nbij'` |
| cauchy-schwarz-oq-03 | Records the doubled symmetric form `∑ᵢ∑ⱼ(aᵢbⱼ − aⱼbᵢ)² = 2·defect` used inside a Cauchy–Schwarz proof | Symmetric double-sum expansion |
| cauchy-schwarz-oq-04 | Pins the proportionality constant in the equality case via residual-norm decomposition | Inner-product residual/projection |
| cauchy-schwarz | Base finite Cauchy–Schwarz inequality that Lagrange's identity refines to an exact equality | `Finset.sum`, sum-of-squares nonnegativity |

## Initial Thoughts

### Potential Approaches

1. **Approach A — General Cauchy–Binet via `det` as an alternating multilinear sum, then specialize.**
   Expand `det (A * B)` using the Leibniz formula (`Matrix.det_apply` / `Matrix.det_mul` machinery) so
   that the product `(A*B) i k = ∑_j A i j * B j k` distributes; the sum over functions `n → n` collapses,
   by alternation, onto the injective ones, which regroup by their image `S` (a size-`m` column subset)
   giving `∑_S det(A_S) det(B_S)`. Then `m = 2`, `B = Aᵀ`, `det_fin_two`, and a bijection from size-2
   subsets to `i < j` pairs finishes Lagrange.
   - Why it might work: this is the standard textbook proof (Gantmacher, Horn–Johnson); every ingredient
     (`det_apply`, alternation, `Finset.sum_sigma`, `Equiv.Perm` sign bookkeeping) is present in Mathlib.
   - Risk: the "regroup injective functions by image, factoring out the permutation sign" step is the crux
     and is notoriously fiddly to formalize; index/sign bookkeeping over `Finset.powersetCard m` is heavy.

2. **Approach B — Prove only the square Gram form `det (A Aᵀ) = ∑_S (det A_S)²` and go straight to `m = 2`.**
   Skip the general two-matrix theorem; directly target the specialization needed for Lagrange. For `m = 2`,
   `A Aᵀ` is an explicit `2×2` matrix, `det_fin_two` gives the defect, and the RHS is `∑_{S, |S|=2} (det A_S)²`
   which reindexes to `∑_{i<j}(a_i b_j - a_j b_i)²` — the parent's exact statement.
   - Why it might work: sidesteps the general sign bookkeeping; for fixed `m = 2` many steps become concrete
     `Fin 2` computations closable by `ring`/`Finset` reindexing (`Finset.sum_powersetCard`, `orderEmbOfFin`).
   - Risk: proving even the square form still needs the Cauchy–Binet regrouping in general `n` columns, so
     it does not avoid the hard combinatorial core unless one specializes `m = 2` *before* generalizing, at
     which point it risks re-deriving the parent rather than exhibiting it as a genuine `n = 2` case.

### Key Difficulties

- **No Cauchy–Binet in Mathlib to build on.** The general rectangular-product determinant identity is
  simply absent, so this is a build-from-scratch formalization, not a lookup-and-specialize.
- **Sign / injective-function regrouping.** The heart of Cauchy–Binet is rewriting `∑_{f : m → n}` over the
  Leibniz product as a sum over image subsets `S` times an internal permutation, tracking `Equiv.Perm.sign`
  correctly; this is the step where Lean proofs of such identities historically stall.
- **Subset ↔ ordered-tuple plumbing.** Relating `Finset.powersetCard m (Finset.univ : Finset colIdx)`,
  `Finset.orderEmbOfFin`, and the parent's `s.offDiag.filter (·.1 < ·.2)` requires careful `orderEmbOfFin` /
  `orderIsoOfFin` reindexing to line size-2 subsets up with strict pairs `i < j`.
- **Matching conventions with the parent.** The parent works over an arbitrary `Finset ι` on a `LinearOrder`,
  not `Fin n`; the `m = 2` specialization must reproduce that generality (or the derivation only covers `Fin n`).

### What Would a Proof Need?

- Key lemma 1: A Leibniz-style expansion of `det (A * B)` distributing the inner product `∑_j A i j B j k`.
- Key lemma 2: Regrouping the resulting `∑_{f : Fin m → colIdx}` over injective `f` by image subset `S`,
  factoring the internal permutation and its sign — yielding `∑_{S ∈ powersetCard m} det(A_S) det(B_S)`.
- Key lemma 3 (`m = 2` bridge): `det_fin_two (A * Aᵀ)` equals the Cauchy–Schwarz defect, and a bijection
  `powersetCard 2 univ ≃ {p ∈ offDiag | p.1 < p.2}` sending `{i,j}` (with `i<j`) to `(i,j)` with
  `det A_{\{i,j\}} = a_i b_j - a_j b_i`.
- Technical requirements: `Matrix.det_apply`, `Matrix.det_mul`, `Matrix.det_fin_two`, `Matrix.submatrix`,
  `Finset.powersetCard`, `Finset.orderEmbOfFin`, `Equiv.Perm.sign`, `Finset.sum_nbij'`, and the parent's
  `lagrange_identity` as the specialization target.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The `m = 2` bridge (Approach B's back half) is genuinely easy: `det_fin_two` plus a `Finset` reindexing,
  entirely in reach of existing Mathlib API and the parent's own techniques.
- The obstruction is the general Cauchy–Binet core (the injective-function-by-image regrouping with sign
  bookkeeping), which is a well-understood but labor-intensive formalization — comparable to other
  determinant-expansion proofs already in Mathlib (`det_apply`, cofactor/Laplace expansion), so not a
  research-level unknown, but not a one-afternoon task either.
- All required primitives (`det_mul`, `det_fin_two`, `powersetCard`, `orderEmbOfFin`, `Perm.sign`,
  `sum_nbij'`) exist; nothing needs new foundational Mathlib theory, only assembly.
- Scoping to the square Gram form `det (A Aᵀ) = ∑_S (det A_S)²` (rather than the full two-matrix identity)
  keeps the goal focused on exactly what Lagrange needs.

**Estimated Effort**:
- Exploration: 1–2 days (settle the subset/orderEmbOfFin conventions; scope square-form vs full two-matrix; prototype the `m = 2` bridge against the parent).
- If tractable: 1–2 weeks (formalize the Cauchy–Binet regrouping with sign bookkeeping, then wire the `m = 2` specialization to `lagrange_identity`).
- If hard: the general sign/regrouping step could stall for several weeks; fall back to a direct `m = 2`-only Gram-form proof that still re-derives Lagrange but foregoes the fully general Cauchy–Binet theorem.

## References

### Papers
- Gantmacher, F. R., *The Theory of Matrices*, Vol. 1, 1959 — Chapter I develops the Binet–Cauchy formula for products of rectangular matrices and its minor-sum form.
- Horn, R. A. and Johnson, C. R., *Matrix Analysis*, 2nd ed., 2013, Cambridge University Press — §0.8.7 states the Cauchy–Binet formula; Lagrange's identity is its two-row Gram specialization.
- Steele, J. M., *The Cauchy–Schwarz Master Class*, 2004, Cambridge University Press — Chapter 4 derives Lagrange's identity and the minor-vanishing equality condition, the `m = 2` case reached here.

### Online Resources
- https://en.wikipedia.org/wiki/Cauchy%E2%80%93Binet_formula — statement of the general formula `det(AB) = ∑_S det(A_S) det(B_S)`, the square Gram form, and the Lagrange-identity specialization.
- https://en.wikipedia.org/wiki/Lagrange%27s_identity — the target identity and its relation to the Binet–Cauchy identity.

### Mathlib
- `Mathlib.LinearAlgebra.Matrix.Determinant.Basic` — provides `Matrix.det_mul`, `Matrix.det_apply`, and `Matrix.det_fin_two`; the base for a Cauchy–Binet expansion.
- `Mathlib.LinearAlgebra.CrossProduct` — `cross_dot_cross`, the `Fin 3` scalar quadruple product identity explicitly noted as "related to the Binet–Cauchy identity" (a fixed-dimension fragment, not the general theorem).
- `Mathlib.Data.Finset.Powerset` / `Mathlib.Order.Fin.Basic` — `Finset.powersetCard` and `Finset.orderEmbOfFin` for indexing maximal minors by size-`m` column subsets.

## Metadata

```yaml
tags:
  - algebra
  - analysis
  - cauchy-schwarz
  - binet-cauchy
  - determinants
related_proofs:
  - cauchy-schwarz-oq-05
  - cauchy-schwarz-oq-03
  - cauchy-schwarz-oq-04
  - cauchy-schwarz
difficulty: medium
source: gallery-gap
created: 2026-07-02T11:12:11-07:00
```

**Significance**: 5/10
**Tractability**: 6/10
