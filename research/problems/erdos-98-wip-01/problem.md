# Problem: Complete the Erdős #98 General-Position Distances Formalization

**Slug**: erdos-98-wip-01
**Created**: 2026-07-09T17:33:19-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
h(n) = \min_{P \in \mathrm{GenPos}(n)} \bigl|\{\, \|p_i - p_j\| : 1 \le i < j \le n \,\}\bigr|, \qquad \mathrm{GenPos}(n) = \{\text{no 3 collinear, no 4 concyclic}\}, \qquad \text{Conjecture}:\ \frac{h(n)}{n} \to \infty.
$$

### Plain Language

The gallery entry `erdos-98` gives a 75-line Lean 4 skeleton for Erdős Problem #98 — distinct distances among points in general position — but it is `wip`: the general-position predicates and the function $h(n)$ are defined, yet every substantive bound (Pach's $n^{\log_2 3}$, the Erdős–Füredi–Pach $n\cdot e^{c\sqrt{\log n}}$, the Guth–Katz baseline, and the conjecture itself) lives only in source comments with no Lean declaration. This research problem is to turn those comments into precise, clearly-labelled Lean statements, prove the definitional lemmas that are actually provable, and isolate the genuinely open core, advancing the entry toward `verified`.

### Why This Matters

1. **From comments to checkable statements**: A formalization whose main content is prose comments has not really been formalized; converting the bounds and conjecture into typed Lean propositions is the first honest step.
2. **Testing general-position definitions**: Encoding "no 3 collinear" and "no 4 concyclic" correctly over `EuclideanSpace ℝ (Fin 2)` is subtle and reusable across incidence-geometry entries.
3. **Pinpointing the breakthrough gap**: Even $h(n) \ge n$ is unknown; making the weak and strong conjectures precise in Lean clarifies exactly which inequality a future proof must establish.

## Known Results

### What's Already Proven

- Guth–Katz (2015): any $n$ planar points determine $\Omega(n/\log n)$ distinct distances — the unconditional baseline, holding without general position (*Annals of Mathematics* 181).
- Pach: general-position sets exist with $h(n) < n^{\log_2 3} \approx n^{1.585}$ distances (Horton-type recursive constructions), documented in the entry's comments.
- Erdős–Füredi–Pach: the improved upper bound $h(n) < n \cdot e^{c\sqrt{\log n}}$, near-linear since $e^{c\sqrt{\log n}} = n^{o(1)}$.

### What's Still Open

- Whether $h(n)/n \to \infty$ (the strong conjecture) — open in mathematics; can only be stated, not proved.
- Whether $h(n) \ge n$ for large $n$ (the weak conjecture) — also unknown and would itself be a breakthrough.

### Our Goal

Move `erdos-98` from `wip` toward `verified` by: (1) replacing comment-only "results" with typed Lean propositions for the Pach bound, the EFP bound, the Guth–Katz baseline, and both conjectures, each flagged as assumption or open; (2) proving the definitional lemmas that are genuinely provable — `numDistinctDistances` finiteness, `h(n)` well-definedness via `sInf`, and that general position implies injectivity; (3) auditing meta.json so `theoremCount`, `axiomCount`, and `status` reflect the real state. No claim to resolve the conjecture.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-98 | Parent entry being completed; same `h(n)` and general-position definitions | `EuclideanSpace`, `sInf`, `NoThreeCollinear`, `NoFourConcyclic` |
| erdos-89 | Sibling unrestricted distinct-distances problem; shares the distance-counting and Guth–Katz baseline | distinct-distance counting, extremal function via `sInf`, incidence geometry |

## Initial Thoughts

### Potential Approaches

1. **Approach A — typecheck the bounds as propositions**: introduce `PachUpperBound`, `EFPUpperBound`, `GuthKatzBaseline`, and `Erdos98Conjecture` as explicit Lean `Prop`s, marking each assumption vs. open, then prove trivial implications among them.
   - Why it might work: it is pure statement engineering over existing definitions, no deep analysis needed.
   - Risk: getting the asymptotic quantifiers (`Filter.Eventually`, $\Omega$/$o$ notation) faithful requires care to avoid vacuous or wrong statements.

2. **Approach B — prove the definitional core**: show `numDistinctDistances P` is finite and positive, and that `InGeneralPosition` implies the point map is injective, giving real Lean content.
   - Why it might work: these follow from `Finset` and `EuclideanSpace` API already in Mathlib.
   - Risk: the concyclicity predicate (equidistance to a center) may need existence/uniqueness lemmas for the circumscribed circle that are awkward in Lean.

### Key Difficulties

- The strong and weak conjectures are open; they can only be *stated*, so the deliverable is faithful formalization, not resolution.
- Encoding "no 4 concyclic" precisely (existence of a common center) without introducing degenerate or vacuous cases requires careful predicate design.

### What Would a Proof Need?

- Key lemma 1: `numDistinctDistances P` equals the cardinality of a finite `Finset ℝ`, with positivity for $n \ge 2$.
- Key lemma 2: `InGeneralPosition P → Function.Injective P`, plus `h(n)` well-definedness (nonempty, bounded-below family) so the `sInf` is meaningful.
- Technical requirements: faithful asymptotic notation for the upper/lower bounds and a meta.json audit updating `theoremCount`/`axiomCount`.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Converting comments into typed statements and proving definitional lemmas is squarely achievable with current Mathlib.
- The parent file is small (75 lines) and well-structured, so the surface area is manageable.
- Mathlib supplies `EuclideanSpace`, `Finset.card`, `sInf`, and affine/collinearity machinery covering the tractable portion; only the deep bounds stay as assumptions.

**Estimated Effort**:
- Exploration: 1–2 days to design faithful predicates and asymptotic statements.
- If tractable: 1–2 weeks to add the propositions and prove the definitional lemmas.
- If hard: the two conjectures remain open and out of scope.

## References

### Papers
- J. Pach and P. K. Agarwal, *Combinatorial Geometry*, Wiley-Interscience, 1995 — Horton-type constructions and the $n^{\log_2 3}$ bound.
- P. Erdős, Z. Füredi, and J. Pach — the $n \cdot e^{c\sqrt{\log n}}$ general-position upper bound.
- L. Guth and N. H. Katz, "On the Erdős distinct distances problem in the plane", *Annals of Mathematics* 181 (2015), 155–190 — the unconditional $\Omega(n/\log n)$ baseline.

### Online Resources
- https://erdosproblems.com/98 — canonical statement and status.

### Mathlib
- `Mathlib.Analysis.InnerProductSpace.Basic` — Euclidean distance and inner products for the distance set.
- `Mathlib.Data.Finset.Card` and `Mathlib.Order.Bounds.Basic` — cardinality of the distance set and `sInf` for $h(n)$.

## Metadata

```yaml
tags:
  - erdos
  - combinatorial-geometry
  - distinct-distances
  - incidence-geometry
  - general-position
  - formalization
related_proofs:
  - erdos-98
  - erdos-89
difficulty: medium
source: proof-suggestion
created: 2026-07-09T17:33:19-07:00
```

**Significance**: 7/10
**Tractability**: 6/10
