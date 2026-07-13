# Problem: Polynomial Path-Length Bounds for Cyclotomic Sublevel Sets

**Slug**: erdos-1215-oq-02
**Created**: 2026-07-09T15:40:18-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\exists\, C\!:\! \mathbb{R},\ \forall\, n\!:\!\mathbb{N},\ \forall\, P = \Phi_n \text{ (the } n\text{-th cyclotomic polynomial, normalized so } P(0)=\pm 1\text{)},\ \exists\, \gamma\!:\![0,1]\to\{z\in\mathbb{C} : |P(z)| < 1\},\ \gamma(0)=0,\ |P(\gamma(1))|=1,\ \operatorname{length}(\gamma) \le C\cdot n.
$$

### Plain Language

Erdős Problem #1215 asks whether every polynomial $P$ with $P(0)=1$ and all roots on the unit circle admits a short path (length bounded by a constant times the degree) from the origin to the boundary of the sublevel set $\{|P(z)|<1\}$, staying inside that set. Mac Lane (1953) answered NO in general: he built "labyrinth" polynomials whose sublevel sets force arbitrarily long detours. This sub-question restricts attention to the special, highly structured family of **cyclotomic polynomials** $\Phi_n$ — whose roots are exactly the primitive $n$-th roots of unity, evenly spaced on the unit circle. The question: does the rigidity of cyclotomic root placement rule out labyrinths, so that a polynomial (in $n$) path-length bound *does* hold for this restricted class, even though it fails for arbitrary unit-circle-rooted polynomials?

### Why This Matters

Cyclotomic polynomials are the most arithmetically important family of unit-circle-rooted polynomials, central to number theory (Mahler measure, Lehmer's problem), Galois theory, and harmonic analysis. Mac Lane's negative resolution of #1215 relies on the freedom to cluster roots arbitrarily to sculpt a labyrinth; cyclotomic roots are, by contrast, rigidly and symmetrically distributed. Determining whether this rigidity forces bounded path complexity would sharpen the boundary between "wild" and "tame" polynomial lemniscates, and connect the topology of sublevel sets to the arithmetic of roots of unity. A positive answer would give the first natural sub-class of #1215 with a uniform bound; a negative answer would show even cyclotomic geometry is topologically wild.

## Known Results

### What's Already Proven

- Mac Lane's negative resolution of Erdős #1215 — for arbitrary simply-connected compact $A\subset\{|z|<1\}$ there is a $P$ with $P(0)=1$, unit-circle roots, and $|P|>2$ on $A$ (Mac Lane, *Duke Math. J.*, 1953); see gallery proof `erdos-1215`.
- Cyclotomic polynomial infrastructure in Mathlib: `Polynomial.cyclotomic n R`, its roots are the primitive $n$-th roots of unity, degree $\varphi(n)$, and irreducibility over $\mathbb{Q}$ — `Mathlib.RingTheory.Polynomial.Cyclotomic.Basic`.
- Mahler measure of any monic polynomial with all roots on the unit circle equals $1$ ("flat" polynomials), including all $\Phi_n$ — classical (Kronecker's theorem context).

### What's Still Open

- Whether the sublevel set $\{|\Phi_n(z)|<1\}$ can host a Mac Lane–style labyrinth, or whether the symmetric spacing of primitive $n$-th roots of unity precludes it.
- The exact form of the target bound (linear $C\cdot n$, logarithmic $C\cdot\log n$, or some other function of $n$ or $\varphi(n)$), which is left partially ambiguous by the original #1215 statement.

### Our Goal

Formalize a precise Lean 4 statement of the cyclotomic-restricted path-length question — defining the sublevel set of $\Phi_n$, a rectifiable path, its arc length, and the quantified bound — and prove the tractable building blocks (basic geometry of $\{|\Phi_n(z)|<1\}$ for small $n$, e.g. $n = 1, 2, 3, 4, 6$) rather than the full uniform theorem, which requires analytic infrastructure not yet in Mathlib.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1215 | Parent problem: general path-length question resolved negatively by Mac Lane; this restricts to cyclotomic $P$ | Polynomial lemniscates, approximation, labyrinth construction |
| angle-trisection-cos-20-gal-oq-03-oq-01 | Also concerns polynomials with roots on the unit circle and cyclotomic-type structure | Cyclotomic/Galois computations |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Explicit small-$n$ analysis of $\{|\Phi_n(z)|<1\}$.
   - Why it might work: For $n=1,2,3,4,6$ the cyclotomic polynomials are simple ($z-1$, $z+1$, $z^2+z+1$, $z^2+1$, $z^2-z+1$); their sublevel sets are elementary regions whose connectivity and path lengths can be computed directly and formalized.
   - Risk: Small cases may all be trivially bounded, giving no insight into whether a labyrinth can appear as $n\to\infty$.

2. **Approach B**: Symmetry/rigidity argument ruling out labyrinths for all $n$.
   - Why it might work: Primitive $n$-th roots of unity are equidistributed and $\Phi_n$ has bounded coefficient growth (heights), which may bound the number and winding of lemniscate components, precluding Mac Lane's construction.
   - Risk: The link between coefficient/root regularity and sublevel-set topology is subtle; a clean quantitative bound may not exist, or the labyrinth may reappear via high multiplicity of near-coincident level curves.

### Key Difficulties

- Mathlib lacks a developed theory of rectifiable paths with arc length in $\mathbb{C}$ tied to polynomial sublevel sets, and lacks polynomial-lemniscate topology results.
- Distinguishing "cyclotomic geometry is tame" from "cyclotomic geometry is wild" requires either an explicit labyrinth-free proof or an explicit cyclotomic labyrinth family — neither is known.

### What Would a Proof Need?

- Key lemma 1: A formal definition of the sublevel set $\{z : |\Phi_n(z)| < 1\}$ and its boundary lemniscate $\{|\Phi_n(z)|=1\}$ in Lean via `Polynomial.eval` and `Complex.abs`.
- Key lemma 2: A rectifiable-path type with arc-length functional (via `MeasureTheory.integral` of the derivative norm) and a lower/upper bound on lengths inside the sublevel set.
- Technical requirements: connectivity/topology of the sublevel set, control of the number of components of $\{|\Phi_n(z)|=1\}$ in terms of $\varphi(n)$, and quantitative estimates on $|\Phi_n|$ from root equidistribution.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The full uniform statement inherits all the analytic infrastructure gaps that make the parent `erdos-1215` a stub (arc length, lemniscate topology, polynomial approximation).
- Similar "tame vs. wild geometry" questions for structured polynomial families are genuinely open in the literature, so a complete resolution is a research-level target, not a formalization exercise.
- Mathlib does provide solid cyclotomic-polynomial and complex-analysis basics, so small-$n$ sublevel-set computations and a precise formal statement are attainable near-term.

**Estimated Effort**:
- Exploration: 2–3 days to survey Mathlib path/measure/cyclotomic tools and draft a formal statement.
- If tractable (small-$n$ / statement-only): 1–2 weeks for a formalized statement plus verified small cases.
- If hard (full uniform theorem): unknown — likely requires new Mathlib analytic infrastructure and possibly new mathematics.

## References

### Papers
- G. R. Mac Lane, "Concerning the uniformization of certain Riemann surfaces allied to the inverse-cosine and inverse-gamma surfaces," and related lemniscate work, *Duke Math. J.* (1953) — source of the negative resolution and labyrinth construction for #1215.
- D. H. Lehmer, "Factorization of certain cyclotomic functions," *Ann. of Math.* (1933) — cyclotomic polynomial structure and Mahler measure context.

### Online Resources
- https://erdosproblems.com/1215 — canonical statement and status of the parent Erdős problem.
- https://en.wikipedia.org/wiki/Cyclotomic_polynomial — properties of $\Phi_n$, roots, and degree $\varphi(n)$.

### Mathlib
- `Mathlib.RingTheory.Polynomial.Cyclotomic.Basic` — the cyclotomic polynomials `Polynomial.cyclotomic`, their roots and degree.
- `Mathlib.Analysis.SpecialFunctions.Complex.Circle` and `Complex.abs` — modulus and unit-circle machinery for defining sublevel sets.
- `Mathlib.MeasureTheory.Integral.IntervalIntegral` — arc-length / path-length integrals for a rectifiable-path formulation.

## Metadata

```yaml
tags:
  - erdos
  - complex-analysis
  - polynomial-theory
  - topology
  - unit-circle
related_proofs:
  - erdos-1215
difficulty: high
source: proof-suggestion
created: 2026-07-09T15:40:18-07:00
```
