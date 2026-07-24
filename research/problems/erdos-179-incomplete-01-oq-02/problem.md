# Problem: Can a quantitative lower bound on countAPs for structured sets (e.g.

**Slug**: erdos-179-incomplete-01-oq-02
**Created**: 2026-07-09T00:00:00Z
**Status**: Active
**Source**: proof-suggestion (open question spun off from `erdos-179-incomplete-01`)

## Problem Statement

### Formal Statement

$$
\textsf{Open question (extension) extending Erdős #179: Elementary Arithmetic-Progression Combinatorics.}
$$

Precise formalization is the first task for the Researcher; the mathematical
content is stated below.

### Plain Language

Can a quantitative lower bound on countAPs for structured sets (e.g. intervals) be formalized as a counterpoint to the upper bound?

### Why This Matters

This is a challenging extension question arising directly from the completed gallery
entry `erdos-179-incomplete-01` ("Erdős #179: Elementary Arithmetic-Progression Combinatorics").
Resolving it extends the reach of an already-formalized result and clarifies how
far the parent proof's techniques generalize.

## Known Results

### What's Already Proven

- The parent result `erdos-179-incomplete-01` is fully formalized in the gallery and provides the base case and available lemmas.

### What's Still Open

- The precise question stated above; no formalization of it currently exists in the gallery.

### Our Goal

Produce a Lean 4 formalization (or a rigorous obstruction/negative result) for the
question above, reusing the parent entry's definitions and lemmas wherever possible.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `erdos-179-incomplete-01` | Parent / originating gallery entry | see entry meta.json |

## Initial Thoughts

### Potential Approaches

1. **Reuse the parent construction.** Start from the definitions and key lemmas of the
   parent entry and attempt to push them through the generalized hypotheses.
2. **Search Mathlib for supporting theory** covering the tags: additive-combinatorics, arithmetic-progressions, supersaturation, counting, erdos, research.

### Key Difficulties

- Identifying which lemmas from the parent proof survive the generalization.
- Locating (or building) the Mathlib scaffolding the new statement requires.

### What Would a Proof Need?

- A precise Lean statement of the question.
- The parent entry's lemmas, adapted to the new setting.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- Categorized as `challenging` in the extracted problem registry.
- A directly related, fully formalized parent proof exists, giving a concrete starting point.

## References

### Mathlib
- Modules relevant to the tags additive-combinatorics, arithmetic-progressions, supersaturation, counting, erdos, research — to be surveyed during ORIENT.

## Metadata

```yaml
tags:
  - additive-combinatorics
  - arithmetic-progressions
  - supersaturation
  - counting
  - erdos
  - research
related_proofs:
  - erdos-179-incomplete-01
difficulty: challenging
source: proof-suggestion
created: 2026-07-09T00:00:00Z
```

## Adversarial Checklist (SOLVED claim, 2026-07-24)

The claim: `proofs/Proofs/Erdos179Incomplete01OQ02.lean` resolves the question
affirmatively — a quantitative lower bound on `countAPs` for intervals, plus an
exact count. Ways THIS claim could be wrong, and why each is excluded:

- **Wrong counting object (sets vs. parameter pairs).** `countAPs A k` (parent
  def) counts *subsets* of `A` that are k-APs, not (a,d) pairs. If two parameter
  pairs gave the same finset, the sigma-parameterization would overcount.
  Excluded by `arithmeticProgression_inj` (rigidity, k ≥ 2, d, d' > 0) feeding
  `Finset.card_image_of_injOn` — confirm the injectivity is on the EXACT
  parameter set used in `countAPs_range_eq_sum` (differences start at d = 1,
  so positivity holds on every element).
- **d = 0 degenerate APs.** `arithmeticProgression a 0 k = {a}` is a 1-element
  finset; if the parameterization included d = 0 the count would be wrong and
  rigidity false. The index set is `Icc 1 ⌊(N−1)/(k−1)⌋` — d = 0 never occurs.
- **Off-by-one in the index bound.** The AP fits in `range N` iff
  `a + (k−1)d < N` (`arithmeticProgression_subset_range`); the top difference is
  `⌊(N−1)/(k−1)⌋`, derived via `Nat.le_div_iff_mul_le`. Degenerate cases N = 0,
  N = 1 (empty sum, countAPs = 0) are covered because `Icc 1 0 = ∅` and nat
  subtraction truncates — checked by the k = 2 collapse
  `countAPs_range_sum_two` matching the parent's `countAPs_two` = C(N,2).
- **Vacuous lower bound.** `⌊N/(2(k−1))⌋·⌊N/2⌋` is 0 for N < 2(k−1) — the bound
  is only asymptotically quadratic. This is disclosed (order N²/(4(k−1))), and
  the claim is supersaturation ORDER, not a pointwise sharp constant. The
  matching upper bound ≤ N² pins the order to Θ(N²) for fixed k.
- **Circularity.** The file imports only the parent `Proofs.Erdos179Incomplete01`
  and proves everything from Mathlib primitives; no axiom, no hypothesis of
  strength comparable to the target (`#` 0 axioms / 0 sorries; the parent's
  remaining deep sorries live in a different file, `Erdos179Problem.lean`, and
  are NOT imported into any statement here).
- **Near-miss: existence instead of counting.** `containsAP_range_iff` alone
  (k ≤ N) would NOT answer the question — the quantitative content is in
  `countAPs_range_eq_sum` / `countAPs_range_lower_bound`; existence is a
  complement, not the claim.

## Follow-Up (proposed at completion, depth guard: slug depth 1 < cap 3)

- **Extremal characterization**: does the interval maximize `countAPs` among
  all N-element subsets of ℕ (for fixed k ≥ 3)? Equivalent-strength note:
  materially DISTINCT and strictly harder than this thread — proving it does
  not re-derive the interval count (which it presupposes); it needs a
  compression/rearrangement mechanism absent here. Not a blocked-route
  restatement of the parent question.
