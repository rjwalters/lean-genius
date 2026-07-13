# Problem: Power-of-a-point ↔ four-point concyclicity determinant

**Slug**: product-of-segments-of-chords-oq-03
**Created**: 2026-05-12
**Status**: Active
**Source**: gallery-gap (extension of `product-of-segments-of-chords`, openQuestion #3)
**Parent file**: `Proofs/ProductOfSegmentsOfChords.lean`
**Parent gallery**: `src/data/proofs/product-of-segments-of-chords/`

## Problem Statement

### Formal Statement

For four distinct points $P_i = (x_i, y_i) \in \mathbb{R}^2$, $i = 1, 2, 3, 4$, define the
**concyclicity determinant**
$$
\Delta(P_1, P_2, P_3, P_4) \;=\; \det
\begin{pmatrix}
x_1^2 + y_1^2 & x_1 & y_1 & 1 \\
x_2^2 + y_2^2 & x_2 & y_2 & 1 \\
x_3^2 + y_3^2 & x_3 & y_3 & 1 \\
x_4^2 + y_4^2 & x_4 & y_4 & 1
\end{pmatrix}.
$$

**Claim (concyclicity criterion)**: Assume $P_1, P_2, P_3$ are non-collinear. Then
$$
\Delta(P_1, P_2, P_3, P_4) = 0 \;\Longleftrightarrow\;
\exists\, O \in \mathbb{R}^2,\, r > 0 \text{ s.t.\ } \|P_i - O\| = r \text{ for all } i.
$$

**Bridge claim (the OQ-03 deliverable)**: This determinantal criterion is equivalent to
the power-of-a-point criterion already used by the parent file's axiomatized converse
(`converse_product_implies_concyclic_axiom`). Specifically, the bridge theorem reads:

> If two chords $AB$ and $CD$ meet at $P$ with $\|P - A\| \cdot \|P - B\| = \|P - C\| \cdot \|P - D\|$,
> and $A, B, C$ are non-collinear, then $\Delta(A, B, C, D) = 0$.

This lets the axiomatized converse be discharged: $\Delta = 0$ together with non-collinearity
of $A, B, C$ produces the circumcircle algebraically (via Cramer's rule on the implicit
equation $x^2 + y^2 + D x + E y + F = 0$), bypassing the synthetic circumcircle argument
the axiom currently hides.

### Plain Language

Four points in the plane lie on a single circle (or line, in the degenerate case) exactly
when the $4 \times 4$ "concyclicity determinant" vanishes. This is the linear-algebra
encoding of the classical fact that three non-collinear points determine a unique circle,
and a fourth point either lies on it or doesn't.

The parent gallery proof builds the **power of a point** invariant: for chords through
$P$, the product $\|P - A\| \cdot \|P - B\|$ depends only on $P$ and the circle, not on
the direction of the chord. The *converse* — that equal products force concyclicity — is
currently an axiom because the parent file lacks an algebraic circumcircle construction.

OQ-03 closes this gap by formalising the determinant criterion and using it to discharge
the axiom: when $\Delta = 0$, Cramer's rule gives explicit coefficients $(D, E, F)$ of the
circle $x^2 + y^2 + D x + E y + F = 0$ through the four points.

### Why This Matters

- **Eliminates a gallery axiom.** The parent currently axiomatises
  `converse_product_implies_concyclic_axiom`. A determinant-based proof would let the
  parent move from `status: "axiomatized"` toward `status: "verified"`.
- **Connects classical and modern formulations.** Power-of-a-point (Steiner 1826) and the
  $4 \times 4$ concyclicity determinant (Möbius / linear algebra) are two presentations
  of the same fact; bridging them in Lean exposes both APIs.
- **Stress-tests Mathlib's `Matrix.det` on a polynomial $4 \times 4$.** The determinant
  is a degree-2 polynomial in $(x_4, y_4)$ when the first three rows are fixed; this is
  a useful concrete instance for `Matrix.det_fin_four` and `Matrix.cramer` benchmarks.
- **Downstream applications.** A formal concyclicity test feeds future gallery work on
  Delaunay triangulations, Ptolemy's theorem (related entry: `ptolemys-theorem`), and
  inversive geometry.

## Known Results

### What's Already Proven (in the parent file)

- `powerOfPoint P C = ‖P - C.center‖² − C.radius²` (line 80, def).
- `chord_quadratic` (108): chord parameter $t$ satisfies a quadratic with roots $t_1, t_2$.
- `chord_roots_product` (133): for a chord through $P$ in a circle of radius $r$ centred
  at the origin, $t_1 \cdot t_2 = \|P\|^2 - r^2 = $ power of $P$.
- `chord_product_algebraic` (204): $\|P - A\| \cdot \|P - B\| = |t_1| \cdot |t_2|$ for
  chord endpoints $A, B$ at parameters $t_1, t_2$.
- `product_of_segments_of_chords` (426): the main theorem.

### What's Still Open

- The implicit-circle formulation: there is no `circleThroughThreePoints` constructor in
  the parent file. The parent axiomatises the converse rather than constructing the
  circle from three points.
- The 4×4 concyclicity determinant has no name in the parent file. Mathlib has
  `Matrix.det_fin_four` for the expansion but no specialised concyclicity lemma.
- The bridge "$\Delta = 0$ ⇒ exists circumscribed circle" is not in Mathlib.

### Our Goal (across S1 → S6)

Build a new companion file `Proofs/ProductOfSegmentsOfChordsOQ03.lean` that:

1. Defines `concyclicityDet (P₁ P₂ P₃ P₄ : Vec2) : ℝ` via `Matrix.det_fin_four`.
2. Proves `Δ(A, B, C, D) = 0 ↔ ∃ O r, r > 0 ∧ all four at distance r` (assuming
   $A, B, C$ non-collinear).
3. Proves the bridge `chord-product equality ⇒ Δ = 0` directly from `chord_roots_product`.
4. Combines (2) and (3) to discharge `converse_product_implies_concyclic_axiom`.

After all sorries close: parent `axiomCount` 1 → 0 (subject to the new companion file
being import-clean).

## Related Gallery Proofs

| Proof | Relevance |
| --- | --- |
| `product-of-segments-of-chords` | Parent — supplies `powerOfPoint`, `chord_quadratic`, `chord_roots_product`, and the axiom we aim to discharge. |
| `ptolemys-theorem` | Sibling concyclicity criterion: $AC \cdot BD = AB \cdot CD + AD \cdot BC$ for cyclic quadrilateral $ABCD$. Both criteria characterise concyclicity. |
| `area-of-circle` | Uses the same `EuclideanSpace ℝ (Fin 2)` infrastructure. |
| `pythagorean-theorem` | Underlies the $\|P - O\|^2$ expansion. |
| `vietas-formulas` | The chord quadratic uses Vieta to recover $t_1 \cdot t_2 = \mathrm{pow}(P)$. |

## References

1. Steiner, J. (1826). *Einige geometrische Betrachtungen* — introduces power of a point.
2. Möbius, A. F. (1827). *Der barycentrische Calcul* — implicit-determinant criterion for
   four points to lie on a conic; the concyclicity case is a corollary.
3. Coxeter, H. S. M. & Greitzer, S. L. (1967). *Geometry Revisited*, §2.1 (power of a
   point) and §6.1 (the concyclicity determinant).
4. Berger, M. (1987). *Geometry I*, Theorem 10.7.6 (Möbius determinant criterion).
5. Mathlib v4.26.0: `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`,
   `Mathlib.LinearAlgebra.Matrix.NonsingularInverse` (Cramer's rule).
