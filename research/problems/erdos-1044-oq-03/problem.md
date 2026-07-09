# Problem: Higher-Dimensional Boundary Measure of Polynomial Sublevel Sets

**Slug**: erdos-1044-oq-03
**Created**: 2026-07-09T15:22:59-07:00
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

For a polynomial $f \in \mathbb{C}[z_1, \dots, z_d]$ whose zero set meets the closed
polydisc, consider the sublevel set $\Omega(f) = \{ z \in \mathbb{C}^d : |f(z)| < 1 \}$.
For each bounded connected component $C$ of $\Omega(f)$ let $\sigma(\partial C)$ denote the
$(2d-1)$-dimensional Hausdorff measure of its topological boundary, and set
$\Lambda_d(f) = \max_C \sigma(\partial C)$. Restricting to polynomials all of whose zeros
lie in the closed unit polydisc $\overline{\mathbb{D}}^d = \{|z_i| \le 1\}$, the conjecture is:

$$
\inf_{f} \Lambda_d(f) \;=\; c_d \;>\; 0, \qquad\text{with}\quad c_1 = 2,
$$

where $c_d$ is a finite positive constant depending only on the dimension $d$, the infimum
is **not attained** by any polynomial, and it is **approached** by a family of high-degree
polynomials (the several-variable analogue of $z^n - 1$, e.g. tensor products
$\prod_{j=1}^{d}(z_j^{n} - 1)$ or Weierstrass-type products on the distinguished boundary).
The one-variable case $c_1 = 2$ is Tang's theorem.

### Plain Language

In one complex variable, Erdős Problem #1044 asks how *short* the boundary of the region
$\{|f| < 1\}$ can be when the polynomial $f$ has all its roots inside the unit disk. Tang
proved the shortest possible boundary length, taken over all polynomials, is exactly $2$
(the diameter of the disk), and that no single polynomial achieves it — instead a sequence
like $z^n - 1$ makes the boundary of each little "petal" shrink toward a segment of length
$2$ as $n \to \infty$.

This problem asks the same question one dimension higher: for polynomials in several
variables $f(z_1, \dots, z_d)$, the sublevel set $\{|f| < 1\}$ is now a region in
$\mathbb{C}^d \cong \mathbb{R}^{2d}$, and its boundary is a real hypersurface of dimension
$2d - 1$. We measure the "size" of that boundary by its $(2d-1)$-dimensional surface
(Hausdorff) measure and ask: over all such polynomials, what is the infimum of the largest
component's boundary measure? We conjecture it is a positive dimensional constant $c_d$,
not attained, and approached by tensor products of the extremal one-variable polynomials.

### Why This Matters

The problem probes whether the delicate one-variable extremal phenomenon — a sharp,
unattained metric bound governed by the degeneration of level sets — survives in higher
dimensions, where the geometry is dramatically richer. Polynomial sublevel sets and their
boundaries (higher-dimensional lemniscates) are central objects in **pluripotential
theory**, where $\log|f|$ is a plurisubharmonic function and $\{|f| < 1\}$ is a
sublevel set of its potential. Sharp metric bounds on these sets connect to
**Bernstein–Markov measures**, **capacities of pluripolar sets**, and quantitative
versions of the **Bernstein–Walsh inequality**. Establishing even the existence and
positivity of $c_d$ would give a genuinely multivariate analogue of Tang's result and
clarify how surface-area minimization interacts with the anisotropy of the polydisc.

## Known Results

### What's Already Proven

- **Tang's theorem (one variable)** — Quanyu Tang, *On the infimum of the length of the
  boundary of polynomial sublevel sets*, Proc. AMS (2021), doi:10.1090/proc/15470:
  $\inf_f \Lambda_1(f) = 2$, the infimum is not attained, and $\Lambda_1(z^n - 1) \to 2$.
  Formalized in this gallery as `erdos-1044` (`Proofs/Erdos1044Problem.lean`), where the
  statement is captured by the axiom `tang_infimum_eq_two`.
- **Metric properties of one-variable lemniscates** — Erdős, Herzog, Piranian, *Metric
  properties of polynomials*, J. Analyse Math. 6 (1958), 125–148: introduced $\Lambda(f)$
  and the whole cluster of level-set metric problems.
- **Pluripotential foundations** — Klimek, *Pluripotential Theory* (1991): the sublevel set
  $\{|f| < 1\} = \{\log|f| < 0\}$ is governed by the plurisubharmonic potential $\log|f|$;
  its boundary is contained in the real-analytic zero set of $|f|^2 - 1$ (hence rectifiable
  away from a lower-dimensional singular set).
- **Coarea / integral-geometric tools** — Federer's coarea formula and the structure theory
  of rectifiable sets provide the machinery to *define* $\sigma(\partial C)$ rigorously as a
  $(2d-1)$-Hausdorff measure.

### What's Still Open

- The exact (or even approximate) value of the dimensional constant $c_d$ for any $d \ge 2$.
- Whether the infimum is finite and strictly positive at all in dimension $d \ge 2$
  (existence/positivity of $c_d$).
- Whether the tensor-product family $\prod_j (z_j^n - 1)$ actually realizes the infimum in
  the limit, or whether a genuinely non-product extremal family exists.
- Whether the "not attained" phenomenon persists in higher dimensions.

### Our Goal

Formalize a precise **statement** of the several-variable conjecture and prove the
tractable structural pieces that support it, rather than the (open) evaluation of $c_d$:

1. **Definitional layer**: Define, in Lean/Mathlib, the sublevel set
   $\Omega(f) = \{z \in \mathbb{C}^d : \|f(z)\| < 1\}$ for a multivariable polynomial and
   its bounded connected components, and axiomatize the boundary-measure functional
   $\Lambda_d(f)$ as a $(2d-1)$-Hausdorff measure (mirroring how `maxBoundaryLength` is
   axiomatized in the parent).
2. **Reduction to $d = 1$**: Prove the compatibility lemma that for a one-variable
   polynomial regarded trivially in $d$ variables, or for a product structure, the
   several-variable functional restricts/factors through the one-variable $\Lambda_1$,
   recovering Tang's constant $2$ on the relevant slices.
3. **Statement of the conjecture**: State `higher_dim_infimum_positive`
   ($\exists\, c_d > 0,\ \forall f,\ \Lambda_d(f) > c_d$ with $c_d$ approached) as an
   axiom/`conjecture`-shaped declaration, with the $d = 1$ specialization *proved* to equal
   Tang's statement.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1044 | Parent problem; the exact one-variable case $c_1 = 2$ this generalizes | Axiomatized potential theory, level-set geometry, roots-of-unity limits |
| erdos-1042 | Number of components / transfinite diameter of polynomial lemniscates — same geometric setup one dimension lower | Lemniscate topology, transfinite diameter |
| erdos-1048 | Diameter of polynomial lemniscate level sets; the limiting slit of diameter 2 controls the one-variable constant | Diameter estimates, extremal configurations |
| erdos-1040 | Transfinite diameter / logarithmic capacity of sublevel sets underpins the potential-theory interpretation | Logarithmic capacity, monic polynomial measure bounds |
| fundamental-theorem-algebra | Root existence used for the polydisc-root hypothesis and the tensor-product extremal family | Complex analysis, algebra |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Tensor-product reduction to the one-variable result.**
   Analyze the extremal family $g_n(z) = \prod_{j=1}^d (z_j^n - 1)$. On the distinguished
   boundary and on coordinate slices, $\{|g_n| < 1\}$ factors (approximately) into products
   of one-variable petals, so the boundary measure should decompose via a Fubini/coarea
   argument into products of one-variable boundary lengths, each $\to 2$.
   - Why it might work: it directly leverages the *proven* one-variable asymptotics and the
     product structure lets Federer's coarea formula split the surface integral.
   - Risk: the boundary of a product sublevel set is **not** the product of one-variable
     boundaries — cross terms and corners appear, and the max-component boundary measure of
     the product need not equal the product of the maxima. Controlling these could dominate
     the difficulty and change the constant $c_d$ away from $2^d$.

2. **Approach B — Pluripotential lower bound via isoperimetry/capacity.**
   Bound $\Lambda_d(f)$ below using an isoperimetric-type inequality relating the
   $(2d-1)$-boundary measure of a component to its enclosed volume, together with a
   capacity lower bound on the volume forced by containing a zero of $f$ (since $\log|f|$ is
   plurisubharmonic and $= -\infty$ at zeros, a definite neighborhood lies in $\{|f|<1\}$).
   - Why it might work: it yields a *dimensional* positive constant $c_d$ without needing the
     exact extremal polynomial, giving existence + positivity (Goal item 3's lower bound).
   - Risk: the sharp constant from isoperimetry will generally be far from the true $c_d$, so
     this proves positivity but not the exact value; matching upper and lower bounds is hard.

### Key Difficulties

- Rigorously defining $\Lambda_d$: the boundary $\partial C$ is a real hypersurface that may
  have singularities (where $\nabla|f|^2$ vanishes), so the $(2d-1)$-Hausdorff measure needs
  the rectifiability/coarea framework, not naive arc length.
- The "not attained" phenomenon and the exact value of $c_d$ are genuinely open — the
  formalization must state these as conjecture/axiom, not prove them.
- Product structure does not commute with taking connected components or with the max over
  components, so the naive $c_d = 2^d$ guess may be wrong.

### What Would a Proof Need?

- Key lemma 1: A well-defined boundary-measure functional $\Lambda_d(f)$ as a
  $(2d-1)$-dimensional Hausdorff measure of the (rectifiable) topological boundary of a
  bounded component, invariant under the relevant symmetries.
- Key lemma 2: A coarea/Fubini decomposition of $\sigma(\partial C)$ for product
  polynomials, reducing (a lower bound of) $\Lambda_d$ to one-variable quantities.
- Key lemma 3: A dimensional isoperimetric/capacity lower bound
  $\Lambda_d(f) \ge c_d > 0$, using plurisubharmonicity of $\log|f|$ to force a definite
  component around each zero.
- Technical requirements: multivariable polynomials over $\mathbb{C}$ (`MvPolynomial`),
  Hausdorff measure and coarea (`MeasureTheory.Measure.hausdorffMeasure`), connectedness of
  sublevel sets, and the parent's axiom `tang_infimum_eq_two` for the $d = 1$ base case.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The core quantitative claim (existence, positivity, and value of $c_d$ for $d \ge 2$) is
  an open research problem with no published answer, so a *complete verified* resolution is
  out of reach; the realistic deliverable is a faithful axiomatized statement plus proved
  structural lemmas and the $d = 1$ specialization — mirroring how the parent `erdos-1044`
  axiomatizes Tang's theorem rather than proving it from scratch.
- Even the definitional layer is heavy: making $\Lambda_d$ rigorous requires Hausdorff
  measure and the coarea formula, and Mathlib's support for rectifiable hypersurface measure
  and pluripotential theory is limited, so much geometry must be axiomatized.
- Comparable already-formalized entries (`erdos-1044`, `erdos-1042`) demonstrate the viable
  pattern: definitions + axiomatized deep theorems + a few proved corollaries.

**Estimated Effort**:
- Exploration: 3–5 days
- If tractable (statement + structural lemmas + $d=1$ specialization): 2–4 weeks
- If hard (any nontrivial lower bound on $c_d$ proved in Lean): unknown

## References

### Papers
- Quanyu Tang, *On the infimum of the length of the boundary of polynomial sublevel sets*,
  Proc. Amer. Math. Soc. (2021), doi:10.1090/proc/15470 — the one-variable base case
  $c_1 = 2$ being generalized here.
- Paul Erdős, Fritz Herzog, George Piranian, *Metric properties of polynomials*,
  J. Analyse Math. 6 (1958), 125–148 — origin of $\Lambda(f)$ and the level-set metric
  program.
- Maciej Klimek, *Pluripotential Theory*, London Math. Soc. Monographs (1991) — several-
  variable potential theory of $\log|f|$ and its sublevel sets.
- Herbert Federer, *Geometric Measure Theory*, Springer (1969) — coarea formula and Hausdorff
  measure of rectifiable sets, the tools needed to define $\sigma(\partial C)$.
- Igor Pritsker, *Chebyshev polynomials on compact sets*, Potential Anal. 40 (2014), 511–521
  — extremal-polynomial / capacity techniques relevant to the conjectured optimizers.

### Online Resources
- https://erdosproblems.com/1044 — Erdős Problem #1044 statement and status (parent problem).
- https://leanprover-community.github.io/mathlib4_docs/ — Mathlib API for `MvPolynomial`,
  Hausdorff measure, and topology of sublevel sets.

### Mathlib
- `Mathlib.Algebra.MvPolynomial.Basic` — polynomials in several complex variables $f(z_1,\dots,z_d)$.
- `Mathlib.MeasureTheory.Measure.Hausdorff` — $(2d-1)$-dimensional Hausdorff measure used to
  define $\sigma(\partial C)$.
- `Mathlib.MeasureTheory.Integral.Coarea` — coarea formula for the product/Fubini decomposition.
- `Mathlib.Topology.Connected.Basic` — connected components of the sublevel set $\Omega(f)$.
- `Mathlib.Analysis.SpecialFunctions.Complex.Circle` — imported by the parent for the
  unit-circle / roots-of-unity geometry.

## Metadata

```yaml
tags:
  - complex-analysis
  - polynomials
  - level-sets
  - boundary-length
  - pluripotential-theory
  - erdos
related_proofs:
  - erdos-1044
  - erdos-1042
  - erdos-1048
  - erdos-1040
difficulty: high
source: proof-suggestion
created: 2026-07-09T15:22:59-07:00
```
