# Problem: Complete the Erdős #46 Monochromatic Unit-Fraction Formalization

**Slug**: erdos-46-wip-01
**Created**: 2026-07-09T17:33:18-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\forall\, r \ge 1,\ \forall\, c : \mathbb{N} \to \mathrm{Fin}\,r,\ \exists\, S \subseteq \{n : n \ge 2\},\quad \mathrm{IsMonochromatic}(c, S)\ \wedge\ \sum_{n \in S} \frac{1}{n} = 1.
$$

### Plain Language

The gallery entry `erdos-46` formalizes Erdős Problem #46 — every finite colouring of $\mathbb{N}$ contains a monochromatic set of denominators whose reciprocals sum to $1$, proved by Croot (2003) — together with the infinitely-many-disjoint variant and the Erdős–Graham rational generalization. It is `wip`: Croot's theorem, its stronger variant, and the rational generalization are stated as assumptions (the deep density Hales–Jewett input is not in Lean), and some structural facts (singleton exclusion, $|S| \ge 2$) are asserted rather than proved. This research problem is to discharge the provable structural lemmas, tighten the definitions, and clearly isolate Croot's theorem as the single genuine external input, moving the entry toward `verified`.

### Why This Matters

1. **Honest labelling of the deep input**: Croot's result rests on the density Hales–Jewett theorem, well beyond current Mathlib; making it the one explicit, clearly-named assumption keeps the entry from overclaiming.
2. **Provable structural core**: Facts like "the empty set and singletons cannot represent $1$" and "$|S| \ge 2$" are elementary and should be Lean theorems, not assumptions — an easy, high-value tightening.
3. **Reusable Egyptian-fraction framework**: `IsUnitFractionRepr`, `IsRatFractionRepr`, and the colouring predicates over `Finset ℕ` and `Rat` are reusable across unit-fraction entries (#311, #321).

## Known Results

### What's Already Proven

- Croot (2003): every finite colouring of $\mathbb{N}$ admits a monochromatic Egyptian-fraction representation of $1$, via the density Hales–Jewett theorem — *Annals of Mathematics*. An assumption in the Lean file.
- Erdős–Graham rational generalization: every positive rational admits a monochromatic representation, following from the infinitely-many-disjoint variant. An assumption in the file.
- In `Proofs/Erdos46Problem.lean`: $\neg\mathrm{IsUnitFractionRepr}(\emptyset)$, monochromaticity for $r=1$ colourings, and `mono_subset` are proved from Lean primitives.

### What's Still Open

- No part of the *mathematics* is open — Croot settled it in 2003. What is "open" here is the *formalization*: Croot's theorem is not proved in Lean and must remain an assumption pending density Hales–Jewett.
- Effective bounds (minimum number of terms, largest denominator vs. number of colours) are genuinely open quantitative questions, out of scope for this completion.

### Our Goal

Advance `erdos-46` from `wip` toward `verified` by: (1) proving the elementary structural lemmas currently asserted — singleton exclusion ($\neg\mathrm{IsUnitFractionRepr}(\{n\})$ for $n \ge 2$) and the cardinality bound $|S| \ge 2$ — directly from the sum condition; (2) confirming the definitions of `IsUnitFractionRepr`, `IsRatFractionRepr`, and `IsMonochromatic` are tight and free of unused hypotheses; (3) auditing meta.json so the single remaining assumption (Croot's theorem, plus the rational-bridge) is disclosed and `axiomCount`/`status` are accurate. No new mathematical claims.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-46 | Parent entry being completed; same unit-fraction and colouring definitions | `Finset.sum`, `Rat`, `Fin r` colourings, `IsMonochromatic` |
| erdos-321 | Sibling unit-fraction problem (distinct reciprocal subset sums) sharing the harmonic-fraction framework | reciprocal sums over `Finset ℕ`, subset-sum constraints |

## Initial Thoughts

### Potential Approaches

1. **Approach A — discharge the structural lemmas**: prove $\neg\mathrm{IsUnitFractionRepr}(\{n\})$ for $n \ge 2$ (since $1/n \le 1/2 < 1$) and $|S| \ge 2$ (since a single term $\le 1/2$) directly from the reciprocal-sum equation.
   - Why it might work: these are one- or two-line `Rat` inequalities well within Mathlib.
   - Risk: careful handling of the $n \ge 2$ side condition and `Finset.sum` over singletons/empty sets.

2. **Approach B — audit and isolate the deep input**: verify that Croot's theorem, its infinite variant, and `rational_from_infinite` are the only assumptions, and document each as a named external theorem.
   - Why it might work: the file is small (84 lines) and the assumption surface is explicit.
   - Risk: ensuring the rational generalization's bridge lemma is stated without hidden extra assumptions.

### Key Difficulties

- Croot's theorem depends on density Hales–Jewett, which Mathlib does not have, so it cannot be proved in Lean and must stay a labelled assumption.
- The structural lemmas are easy, so the main challenge is disciplined assumption accounting rather than mathematical depth.

### What Would a Proof Need?

- Key lemma 1: for $n \ge 2$, $\sum_{m \in \{n\}} 1/m = 1/n < 1$, hence no singleton represents $1$.
- Key lemma 2: any representation of $1$ has $|S| \ge 2$, since each term is $\le 1/2$.
- Technical requirements: `Rat` arithmetic, `Finset.sum` over small sets, and a meta.json audit disclosing Croot's theorem as the sole substantive assumption.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The structural lemmas are elementary `Rat`/`Finset.sum` facts, so real progress toward `verified` is straightforward.
- The deep input (Croot via density Hales–Jewett) is cleanly isolatable; other `wip` entries have reached a clean state by proving the scaffolding and disclosing one external theorem.
- Mathlib's `Finset.sum`, `Rat`, and `Fin` APIs cover everything except the density Hales–Jewett theorem, which stays an assumption.

**Estimated Effort**:
- Exploration: half a day to a day to confirm the assumption surface.
- If tractable: a few days to prove the structural lemmas and finalize the audit.
- If hard: proving Croot's theorem in Lean is out of scope (requires density Hales–Jewett).

## References

### Papers
- E. Croot, "On a coloring conjecture about unit fractions", *Annals of Mathematics* (2003) — proved the conjecture via density Hales–Jewett.
- P. Erdős and R. Graham, *Old and New Problems and Results in Combinatorial Number Theory*, 1980 — original conjecture and rational generalization.
- D. H. J. Polymath, "A new proof of the density Hales–Jewett theorem", 2012 — simplified the key tool underlying Croot's proof.

### Online Resources
- https://erdosproblems.com/46 — canonical statement and (solved) status.

### Mathlib
- `Mathlib.Algebra.BigOperators.Group.Finset` — `Finset.sum` for the reciprocal sums.
- `Mathlib.Data.Rat.Defs` and `Mathlib.Data.Fin.Basic` — rational arithmetic and `Fin r` colourings.

## Metadata

```yaml
tags:
  - erdos
  - number-theory
  - unit-fractions
  - ramsey-theory
  - colouring
  - formalization
related_proofs:
  - erdos-46
  - erdos-321
difficulty: medium
source: proof-suggestion
created: 2026-07-09T17:33:18-07:00
```

**Significance**: 6/10
**Tractability**: 7/10
