# Problem: The Classical AM-GM Equality Case at Uniform Weights (Indexed over `Fin n`)

**Slug**: amgm-inequality-oq-05-oq-02-oq-01
**Created**: 2026-06-30
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Specialise the parent's **weighted** AM-GM equality characterisation to **equal
weights** $w_i = 1/n$, recovering the classical statement that the geometric mean
of $n$ nonnegative reals equals their arithmetic mean iff all the reals coincide.
Concretely, for $n \ge 1$ and $x : \operatorname{Fin} n \to \mathbb{R}$ strictly
positive, prove

$$
\Bigl(\prod_{i} x_i\Bigr)^{1/n} \;=\; \frac{1}{n}\sum_{i} x_i
\qquad\Longleftrightarrow\qquad
\forall\, i\, j,\; x_i = x_j .
$$

A Lean-flavoured target signature (the researcher may adjust names and the exact
rpow / `n`-th-root spelling):

```lean
theorem amgm_uniform_eq_iff {n : ℕ} (hn : 0 < n) {x : Fin n → ℝ}
    (hx : ∀ i, 0 < x i) :
    ((∏ i, x i) ^ ((1 : ℝ) / n) = (∑ i, x i) / n) ↔ (∀ i j, x i = x j) := by
  sorry
```

This is obtained by instantiating the parent theorem
`AmgmInequalityOQ05OQ02.weighted_amgm_eq_iff_pairwise` (and/or
`weighted_amgm_eq_iff`) at the index set `t = Finset.univ : Finset (Fin n)` and the
constant weight function `w i = 1 / n`. Two small translation steps convert the
parent's shape $\prod_i x_i^{w_i} = \sum_i w_i x_i$ into the familiar
$n$-th-root/average shape above:

- the **geometric side** $\prod_i x_i^{1/n} = \bigl(\prod_i x_i\bigr)^{1/n}$ by a
  lemma of the form "`Real.rpow` distributes over a finite product of positive
  factors" (i.e. $(\prod_i x_i)^{r} = \prod_i x_i^{r}$);
- the **arithmetic side** $\sum_i (1/n)\,x_i = \bigl(\sum_i x_i\bigr)/n$ by
  `Finset.mul_sum` / `Finset.sum_div`.

The weight hypotheses of the parent are discharged immediately at $w_i = 1/n$:
positivity $0 < 1/n$ from `hn`, and the normalisation
$\sum_{i \in \operatorname{univ}} 1/n = n \cdot (1/n) = 1$ from
`Finset.sum_const`, `Finset.card_univ`, `Fintype.card_fin`, and cancellation using
$n \ne 0$.

### Plain Language

The arithmetic mean of $n$ positive numbers is always at least their geometric
mean; the two are *equal* exactly when the numbers are all the same. The parent
gallery entry proved the general **weighted** version of this equality case — for
arbitrary positive weights summing to $1$ — using the strict concavity of the
logarithm. This problem asks for the single most-used consequence: plug in the
uniform weights $1/n$ and restate the result in its textbook form, "the $n$-th
root of a product equals the average iff all the terms are equal," cleanly indexed
over `Fin n` so it reads as the classical AM-GM equality case with no weight
bookkeeping visible.

### Why This Matters

The equal-weight AM-GM equality case is the version quoted in virtually every
textbook and used throughout olympiad-style and analysis arguments; the weighted
form, while strictly more general, is less convenient to apply directly. Packaging
the `Fin n` corollary turns the parent's research result into a plug-and-play
library lemma: any argument that invokes AM-GM and needs to know *when* it is tight
can cite this one statement. It also completes the pedagogical arc of the entry
family — from the two-variable Young equality case (`amgm-inequality-oq-05`), to the
general weighted $n$-term equality case (`amgm-inequality-oq-05-oq-02`), down to the
classical uniform corollary here — and demonstrates the standard
"specialise weighted → uniform" pattern that recurs across the inequality
literature.

## Known Results

### What's Already Proven

- **Weighted AM-GM equality case, `n` terms** (`amgm-inequality-oq-05-oq-02`,
  parent, verified, 0 axioms): for strictly positive weights $w$ summing to $1$
  and strictly positive $x$ over a finite index set,
  $\prod_i x_i^{w_i} = \sum_i w_i x_i$ iff every $x_j$ equals the common mean
  (`weighted_amgm_eq_iff`), equivalently iff all $x_j$ are equal
  (`weighted_amgm_eq_iff_pairwise`); the trivial converse is
  `weighted_amgm_eq_of_const`. Proved via strict concavity of `Real.log`
  (`strictConcaveOn_log_Ioi`) fed to `StrictConcaveOn.map_sum_eq_iff`, with the
  multiplicative equality transported through `log` via `Real.log_injOn_pos`.
- **Two-variable Young equality case** (`amgm-inequality-oq-05`, grandparent):
  the weights $(1/p, 1/q)$ pointwise Young equality case from strict convexity of
  `exp`.
- **The AM-GM inequality itself** (`amgm-inequality`): the underlying inequality
  the equality case sharpens. Mathlib carries the weighted inequality
  (`Real.inner_le_weight_mul_Lp`, the `Real.geom_mean_le_arith_mean*_weighted`
  family, and the `Real.pow_arith_mean_le_arith_mean_pow` / `Real.rpow` AM-GM
  lemmas), but not the equality characterisation the parent supplies.

### What's Still Open

- No standalone `Fin n`, uniform-weight statement of the classical AM-GM equality
  case exists in Mathlib or the gallery — only the general weighted version proved
  by the parent. This is the gap to fill.

### Our Goal

Prove the classical AM-GM equality case at uniform weights as a **standalone
corollary** by instantiating the parent's weighted equality theorem at
$w_i = 1/n$ over `Finset.univ : Finset (Fin n)`. The mathematical content is
entirely inherited from the parent; the work is the (small) translation from the
weighted shape $\prod x_i^{w_i} = \sum w_i x_i$ to the textbook shape
$(\prod x_i)^{1/n} = (\sum x_i)/n$, plus discharging the uniform-weight hypotheses.
Deliver a 0-axiom Lean file with the `Fin n` iff-statement as the headline theorem,
and optionally the two convenience directions (constant $\Rightarrow$ equality, and
the pairwise phrasing).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| amgm-inequality-oq-05-oq-02 | Direct parent: the weighted `n`-term equality case this specialises at $w_i = 1/n$ | Strict concavity of `log`, `StrictConcaveOn.map_sum_eq_iff`, `Real.log_injOn_pos` |
| amgm-inequality-oq-05 | Grandparent: two-variable Young equality case (weights $1/p, 1/q$) | Strict convexity of `exp` |
| amgm-inequality | The base inequality being sharpened; uniform-weight AM-GM is its classical face | Jensen / convexity |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Instantiate the parent, then normalise the shapes (recommended).**
   Apply `weighted_amgm_eq_iff_pairwise` with `t := Finset.univ`,
   `w := fun _ => (1 : ℝ)/n`, `x := x`. Discharge `hw` (each $1/n > 0$ from `hn`),
   `hsum` ($\sum_{\operatorname{univ}} 1/n = 1$ via `Finset.sum_const`,
   `Finset.card_univ`, `Fintype.card_fin`, and $n \cdot (1/n) = 1$), and `hx`. This
   yields $\prod_i x_i^{1/n} = \sum_i (1/n) x_i \iff \forall i j,\, x_i = x_j$. Then
   rewrite the geometric side to $(\prod_i x_i)^{1/n}$ (pull the common exponent out
   of the product of positive factors) and the arithmetic side to
   $(\sum_i x_i)/n$ (`Finset.mul_sum` / `Finset.sum_div`). Done.
   - Why it works: no new mathematics; the equivalence is exactly the parent's,
     re-expressed. Very likely 0 axioms.
   - Risk: only the rpow-of-product bookkeeping (see difficulties).

2. **Approach B — Reprove directly at uniform weights.** Skip the general parent and
   run the log / strict-concavity argument specialised to $1/n$. Not recommended:
   duplicates the parent's proof for no benefit and is strictly more work.

### Key Difficulties

- **Collecting the common exponent out of a product.** The parent's geometric side
  is $\prod_i x_i^{1/n}$; the textbook side is $(\prod_i x_i)^{1/n}$. These agree for
  positive $x_i$ by a lemma of the form $(\prod_i x_i)^{r} = \prod_i x_i^{r}$
  (`Real.rpow` distributing over a finite product of nonnegative/positive factors).
  Confirm the exact Mathlib name and orientation, and that positivity of the factors
  is available.
- **The `1/n` normalisation.** $\sum_{i \in \operatorname{univ}} 1/n = 1$ needs
  `card (univ : Finset (Fin n)) = n` and $n \cdot (1/n) = 1$, which requires
  $n \ne 0$ — hence the `0 < n` hypothesis. The $n = 0$ case is genuinely excluded
  (empty product is $1$, empty sum is $0$, and $1/0$ conventions make the statement
  degenerate), so carry `hn : 0 < n` explicitly.
- **`n`-th root vs. rpow spelling.** "$n$-th root" is cleanest as
  `(·) ^ ((1 : ℝ) / n)` with `Real.rpow`; keep exponents real throughout (matching
  the parent, which uses `Real.rpow`) rather than mixing in `Real.sqrt` / `NNReal`
  roots.

### What Would a Proof Need?

- Key lemma 1: the parent instantiation `weighted_amgm_eq_iff_pairwise` (or
  `weighted_amgm_eq_iff`) at `t = univ`, `w = fun _ => 1/n`.
- Key lemma 2: `∑ i, (1:ℝ)/n = 1` over `Fin n` (via `Finset.sum_const` + cardinality).
- Key lemma 3: geometric-side rewrite $\prod_i x_i^{1/n} = (\prod_i x_i)^{1/n}$
  (rpow over a positive product) and arithmetic-side rewrite
  $\sum_i (1/n) x_i = (\sum_i x_i)/n$ (`Finset.mul_sum`).
- Technical requirements: `Fintype (Fin n)` instances (automatic), positivity facts
  `Real.rpow_pos_of_pos`, and `0 < n` to license the normalisation.

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- This is a **direct corollary** of a fully verified, 0-axiom parent theorem. The
  hard part — the strict-concavity equality argument — is already done and imported.
- The only genuine work is cosmetic algebra: normalising the uniform weights to sum
  to $1$ and reshaping $\prod x_i^{1/n}$ / $\sum (1/n)x_i$ into $(\prod x_i)^{1/n}$ /
  $(\sum x_i)/n$. All tools (`Finset.sum_const`, `Finset.mul_sum`,
  `Finset.card_univ`, `Fintype.card_fin`, `Real.rpow` product/positivity lemmas) are
  standard Mathlib.
- Comparable specialisations (weighted → uniform) are routine one-file ports; the
  parent even names this exact task as its first open question.
- Main residual risk is the naming/orientation of the rpow-over-product lemma,
  resolvable by a short Mathlib search.

**Estimated Effort**:
- Exploration: a few hours (pin the rpow-product lemma name and root spelling).
- If tractable: **~1 day** for a 0-axiom file with the headline `Fin n` iff and a
  couple of convenience corollaries.
- If hard: n/a — this is not expected to be hard.

## References

### Papers
- Hardy, G. H.; Littlewood, J. E.; Pólya, G., *Inequalities*, Cambridge University
  Press, 1934 — the classical treatment of AM-GM and its equality case (the
  equal-weight statement is the canonical Theorem 9 form).
- Steele, J. Michael, *The Cauchy–Schwarz Master Class*, Cambridge University Press,
  2004 — AM-GM, Jensen, and the role of strict convexity in equality cases.

### Online Resources
- https://en.wikipedia.org/wiki/Inequality_of_arithmetic_and_geometric_means —
  statement of AM-GM, the equal-weight equality case, and the convexity proof.

### Mathlib
- `Mathlib.Analysis.MeanInequalities` — the weighted AM-GM inequality and the
  `Real.geom_mean_le_arith_mean*_weighted` / `Real.inner_le_weight_mul_Lp` family the
  parent builds on.
- `Mathlib.Analysis.Convex.SpecificFunctions.Basic` — `strictConcaveOn_log_Ioi`
  (imported transitively through the parent's equality characterisation).
- `Mathlib.Analysis.SpecialFunctions.Pow.Real` /
  `Mathlib.Analysis.SpecialFunctions.Pow.NNRpow` — `Real.rpow`,
  `Real.rpow_pos_of_pos`, and the lemma of the form $(\prod_i x_i)^r = \prod_i x_i^r$
  for the geometric-side rewrite.
- `Mathlib.Algebra.BigOperators.Ring.Finset` (`Finset.mul_sum`, `Finset.sum_div`) —
  reshaping $\sum (1/n) x_i$ into $(\sum x_i)/n$.
- `Mathlib.Algebra.BigOperators.Basic` (`Finset.sum_const`, `Finset.card_univ`) plus
  `Fintype.card_fin` — the $\sum 1/n = 1$ normalisation.
- The parent file `Proofs/AmgmInequalityOQ05OQ02.lean`
  (`weighted_amgm_eq_iff`, `weighted_amgm_eq_iff_pairwise`) — imported directly and
  instantiated at `w i = 1/n`.

## Metadata

```yaml
tags:
  - analysis
  - inequalities
  - amgm
  - equality-case
  - convexity
  - jensen
related_proofs:
  - amgm-inequality-oq-05-oq-02
  - amgm-inequality-oq-05
  - amgm-inequality
difficulty: low
source: gallery-gap
created: 2026-06-30
```
