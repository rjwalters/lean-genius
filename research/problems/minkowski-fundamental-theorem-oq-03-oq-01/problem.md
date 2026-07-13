# Problem: van der Corput's Convex-Body Counting Theorem via the Minkowski Multiplicity Principle

**Slug**: minkowski-fundamental-theorem-oq-03-oq-01
**Created**: 2026-07-02
**Status**: Active
**Source**: proof-suggestion (open question `minkowski-fundamental-theorem-oq-03`)

## Problem Statement

### Formal Statement

Let $L \subset \mathbb{R}^n$ be a full-rank lattice and let $S \subset \mathbb{R}^n$ be a
convex, centrally symmetric body. For an integer $k \ge 1$,

$$
\operatorname{vol}(S) > k \cdot 2^n \cdot \operatorname{covol}(L)
\;\Longrightarrow\;
\bigl|\, (S \cap L) \setminus \{0\} \,\bigr| \;\ge\; 2k,
$$

i.e. $S$ contains at least $k$ pairs $\{\pm v\}$ of nonzero lattice points
(equivalently, at least $k+1$ lattice points counting the origin, in the
"$2k+1$ points" normalization). Minkowski's fundamental theorem is the case
$k = 1$.

### Plain Language

Minkowski's theorem says a centrally symmetric convex body whose volume exceeds
$2^n$ times the lattice covolume must contain a nonzero lattice point. van der
Corput's refinement says that if the volume exceeds $k$ times that threshold,
the body contains not just one but at least $k$ independent pairs of nonzero
lattice points. The proof is the same pigeonhole ("multiplicity") principle used
for Minkowski's theorem, pushed one step further: scaling $S$ by $1/2$ and
reducing mod $L$, a volume bound forces $k+1$ points of $\tfrac12 S$ to be
congruent mod $L$, and central symmetry plus convexity turns each coincidence
into a genuine lattice point of $S$.

### Why This Matters

van der Corput's theorem is the natural quantitative strengthening of the single
most-used result in the geometry of numbers. It underlies counting arguments for
lattice points in convex bodies and sharper forms of Minkowski's linear-forms
and successive-minima results. The parent gallery entry
(`minkowski-fundamental-theorem`) already formalizes the $k = 1$ pigeonhole
machinery; this problem asks to reuse that infrastructure to obtain the general
$k$ multiplicity statement, demonstrating that the formalized proof scales.

## Known Results

### What's Already Proven

- Minkowski's fundamental theorem ($k = 1$) — formalized in the parent gallery
  entry `minkowski-fundamental-theorem`, and available in Mathlib as
  `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`
  / the `ZLattice` / `Zspan` fundamental-domain API.
- The Blichfeldt / pigeonhole "multiplicity principle": if
  $\operatorname{vol}(T) > k \cdot \operatorname{covol}(L)$ then some fibre of the
  quotient map $T \to \mathbb{R}^n / L$ has at least $k+1$ preimages in $T$.

### What's Still Open

- The general-$k$ (van der Corput) statement is not yet in the gallery; only the
  $k = 1$ Minkowski case is formalized.
- The clean "congruent points → genuine lattice points" passage under central
  symmetry and convexity, packaged as a reusable lemma, has to be written.

### Our Goal

State and prove the van der Corput counting theorem for general $k$ by feeding a
$k+1$-fold Blichfeldt/pigeonhole coincidence in $\tfrac12 S$ through central
symmetry and convexity to produce $\ge k$ distinct pairs $\{\pm v\}$ of nonzero
lattice points in $S$, reusing the parent entry's Minkowski infrastructure.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| minkowski-fundamental-theorem | Direct parent; provides the k=1 pigeonhole machinery | Fundamental domain, measure comparison |
| minkowski-fundamental-theorem-oq-03 | Immediate parent open question (Blichfeldt-style generalization) | Convex-body lattice counting |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Blichfeldt multiplicity + symmetrization.** Apply the
   pigeonhole/Blichfeldt principle to $T = \tfrac12 S$: since
   $\operatorname{vol}(T) = 2^{-n}\operatorname{vol}(S) > k\cdot\operatorname{covol}(L)$,
   some coset of $L$ has $\ge k+1$ representatives $x_0,\dots,x_k \in T$. For each
   $i \ge 1$, $x_i - x_0 \in L\setminus\{0\}$, and $x_i - x_0 \in \tfrac12 S -
   \tfrac12 S = S$ by convexity + central symmetry. Show the resulting points
   give $\ge k$ distinct $\pm$-pairs.
   - Why it might work: it is exactly the parent's $k = 1$ argument with the
     pigeonhole strengthened to multiplicity $k+1$; the geometric step is reused
     verbatim.
   - Risk: bookkeeping that the $k$ differences $x_i - x_0$ yield $k$ *distinct*
     unordered pairs (not collapsing) needs care.

2. **Approach B — Induction on k via excision.** Obtain one pair from Minkowski,
   excise a small symmetric neighbourhood, and re-apply the volume bound with
   $k-1$.
   - Why it might work: reduces to repeated use of the already-formalized $k=1$
     case.
   - Risk: controlling volumes after excision is measure-theoretically delicate
     and likely messier than Approach A.

### Key Difficulties

- Formalizing the "at least $k+1$ congruent points" pigeonhole in Mathlib's
  measure/quotient framework at multiplicity $k$ (vs. the plain $k=1$ Minkowski
  statement).
- Proving the $k$ differences are pairwise distinct as $\pm$-pairs to reach the
  full count $2k$.

### What Would a Proof Need?

- Key lemma 1: a multiplicity Blichfeldt lemma — volume $> k\cdot\operatorname{covol}$
  forces a fibre with $\ge k+1$ points.
- Key lemma 2: central symmetry + convexity gives $\tfrac12 S - \tfrac12 S = S$,
  so differences of points of $\tfrac12 S$ land in $S$.
- Technical requirements: Mathlib `ZLattice` / `Zspan` fundamental domain,
  measure of scaled sets ($\operatorname{vol}(cS) = c^n \operatorname{vol}(S)$),
  and a finite pigeonhole with multiplicity.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The $k = 1$ case is already formalized in the parent entry, so the geometric
  core exists; the task is a quantitative upgrade of the pigeonhole step.
- The mathematics is classical (van der Corput, 1930s) and short on paper.
- The main formalization risk is the multiplicity pigeonhole and distinctness
  bookkeeping, not any deep new theory.

**Estimated Effort**:
- Exploration: 1–2 days (review the parent formalization and Mathlib lattice API)
- If tractable: 1–2 weeks
- If hard: unknown (if the multiplicity pigeonhole is awkward in Mathlib's
  measure framework)

## References

### Papers
- J. G. van der Corput, "Verallgemeinerung einer Mordellschen Beweismethode in
  der Geometrie der Zahlen" (1930s) — the multiplicity generalization.
- H. Minkowski, *Geometrie der Zahlen* (1896) — the k = 1 fundamental theorem.

### Online Resources
- Cassels, *An Introduction to the Geometry of Numbers* — van der Corput's
  theorem and Blichfeldt's principle.

### Mathlib
- `Mathlib.Algebra.Module.ZLattice.Basic` / `Mathlib.LinearAlgebra.FreeModule.PID`
  — lattices and covolume.
- `Mathlib.MeasureTheory.Group.FundamentalDomain` — fundamental domains and the
  measure-comparison pigeonhole underlying Minkowski's theorem.

## Metadata

```yaml
tags:
  - number-theory
  - geometry-of-numbers
  - lattices
  - convex-bodies
  - van-der-corput
related_proofs:
  - minkowski-fundamental-theorem
  - minkowski-fundamental-theorem-oq-03
difficulty: medium
source: proof-suggestion
created: 2026-07-02
```
