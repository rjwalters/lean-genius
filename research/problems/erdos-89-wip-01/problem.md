# Problem: Complete the Erdős #89 Distinct-Distances Formalization

**Slug**: erdos-89-wip-01
**Created**: 2026-07-09T17:33:18-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
g(n) = \min_{\substack{P \subseteq \mathbb{R}^2 \\ |P| = n}} \bigl|\{\, \|p - q\| : p, q \in P,\ p \neq q \,\}\bigr|, \qquad \text{Erdős89Conjecture}:\ g(n) = \Omega\!\left(\frac{n}{\sqrt{\log n}}\right).
$$

### Plain Language

The gallery entry `erdos-89` formalizes the Erdős distinct-distances problem in Lean 4 but carries a `wip` badge: the Guth–Katz bound and the grid upper bound are recorded as external assumptions rather than derived, and the extremal function is stated but its basic properties are not fully developed. This research problem is to strengthen that formalization — discharge the provable supporting lemmas, tighten the definitions, and clearly isolate the genuinely open core — moving the entry toward a `verified` badge without claiming to resolve the open conjecture.

### Why This Matters

1. **Credibility of the gallery**: A `wip` entry that silently leans on unstated assumptions overclaims what Lean has checked; making every assumption explicit and discharging what is provable keeps the gallery honest.
2. **Reusable geometric infrastructure**: Distinct-distance counting over `EuclideanSpace ℝ (Fin 2)` and the extremal function `g(n)` via `sInf` are building blocks shared by many combinatorial-geometry entries, so hardening them pays dividends elsewhere.
3. **Sharp open/closed boundary**: Separating the one genuinely open statement (the $\Omega(n/\sqrt{\log n})$ lower bound) from the routine scaffolding makes precise exactly what a future proof must supply.

## Known Results

### What's Already Proven

- Guth–Katz (2015): every $n$-point planar set determines $\Omega(n/\log n)$ distinct distances — *Annals of Mathematics* 181 (2015), 155–190. Currently an assumption in the Lean file, not a Lean proof.
- Grid construction: the $\sqrt{n} \times \sqrt{n}$ integer lattice determines $O(n/\sqrt{\log n})$ distinct distances (sums-of-two-squares counting), showing the conjecture would be tight.
- `conjecture_implies_guthKatz` in `Proofs/Erdos89Problem.lean`: the $\Omega(n/\sqrt{\log n})$ conjecture formally entails the weaker Guth–Katz bound — a proved consistency check.

### What's Still Open

- The Erdős $\Omega(n/\sqrt{\log n})$ lower bound itself, closing the residual $\sqrt{\log n}$ gap from Guth–Katz. This is open in mathematics and must remain an explicit assumption, not a Lean theorem.
- Whether the grid is optimal, and the analogous questions in higher dimensions.

### Our Goal

Raise `erdos-89` from `wip` toward `verified` by: (1) proving elementary properties of `distinctDistances` and `minDistinctDistances` (well-definedness, monotonicity in $n$, positivity, small-case values) directly in Lean; (2) replacing informal comments about the grid bound with a stated, clearly-labelled assumption and, where feasible, deriving the finite combinatorial pieces; (3) auditing that every remaining assumption is a genuine external theorem (Guth–Katz) or the open conjecture, with `axiomCount` in meta.json updated to match. No claim that the open conjecture is resolved.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-89 | Parent entry being completed; same definitions and conjecture | `EuclideanSpace`, `Finset.offDiag`, `sInf`, `Filter.Eventually` |
| erdos-98 | Sibling distinct-distances problem in general position; shares distance-counting scaffolding | general-position predicates, `numDistinctDistances`, incidence geometry |

## Initial Thoughts

### Potential Approaches

1. **Approach A — discharge the routine scaffolding first**: prove positivity, monotonicity, and small-$n$ values of `g(n)` from the definitions, leaving only Guth–Katz and the open conjecture as assumptions.
   - Why it might work: these are finite/definitional facts well within Mathlib's `Finset` and `EuclideanSpace` API.
   - Risk: `sInf` over an infinite family may need `BddBelow`/nonemptiness witnesses that are fiddly to supply.

2. **Approach B — formalize the grid upper bound's finite core**: encode the $\sqrt{n}\times\sqrt{n}$ lattice and count its distance set via representations as sums of two squares.
   - Why it might work: the counting reduces to number-theoretic facts (Landau–Ramanujan) that partly exist in Mathlib.
   - Risk: the full $O(n/\sqrt{\log n})$ asymptotic needs analytic number theory Mathlib may not yet have; may stay an assumption.

### Key Difficulties

- The headline lower bound is a genuinely open theorem; it can only be *stated*, never *proved*, so the win is architectural clarity, not resolution.
- Guth–Katz relies on polynomial partitioning and 3D incidence geometry that are far outside current Mathlib, so it must remain an explicit assumption.

### What Would a Proof Need?

- Key lemma 1: `distinctDistances P` is a finite set for finite `P`, with cardinality monotone under the pairing map.
- Key lemma 2: `minDistinctDistances n` is well-defined (the family is nonempty and bounded below), enabling clean statements of the bounds.
- Technical requirements: careful `sInf`/`BddBelow` handling over `EuclideanSpace ℝ (Fin 2)`, and a meta.json audit so `axiomCount` and `status` reflect the remaining Guth–Katz assumption and open conjecture.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The scaffolding lemmas (finiteness, monotonicity, positivity, small cases) are standard Mathlib exercises, so measurable progress toward `verified` is realistic.
- Similar completion work on other `wip` Erdős entries has succeeded by discharging definitional lemmas while isolating one open core.
- Mathlib provides `EuclideanSpace`, `Finset.offDiag`, `sInf`/`csInf` lemmas, and basic sum-of-two-squares results, covering the tractable portion.

**Estimated Effort**:
- Exploration: 1–2 days to inventory which lemmas are definitional versus genuinely deep.
- If tractable: 1–2 weeks to prove the scaffolding lemmas and audit assumptions.
- If hard: the open lower bound remains unbounded and out of scope.

## References

### Papers
- P. Erdős, "On sets of distances of n points", *American Mathematical Monthly* 53 (1946), 248–250 — original conjecture $\Omega(n/\sqrt{\log n})$.
- L. Guth and N. H. Katz, "On the Erdős distinct distances problem in the plane", *Annals of Mathematics* 181 (2015), 155–190 — the $\Omega(n/\log n)$ breakthrough.

### Online Resources
- https://erdosproblems.com/89 — canonical statement, prize ($500), and status.

### Mathlib
- `Mathlib.Analysis.InnerProductSpace.EuclideanDist` — Euclidean distance on `EuclideanSpace ℝ (Fin 2)`.
- `Mathlib.Data.Finset.Basic` and `Mathlib.Order.Bounds.Basic` — `Finset.offDiag`, `sInf`/`csInf` over point sets.

## Metadata

```yaml
tags:
  - erdos
  - combinatorial-geometry
  - distinct-distances
  - incidence-geometry
  - formalization
  - extremal
related_proofs:
  - erdos-89
  - erdos-98
difficulty: medium
source: proof-suggestion
created: 2026-07-09T17:33:18-07:00
```

**Significance**: 7/10
**Tractability**: 6/10
