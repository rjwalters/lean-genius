# Knowledge Base: erdos-476-oq-05-wip-01

Insights accumulated during research on this problem.

---

## Problem Understanding

**Goal**: Fill 2 sorries in `Erdos476OQ05Problem.lean` to complete Vosper's theorem.

### The Two Sorries

**SORRY 1** (line 166, `vosper_induction`):
```lean
-- Key step: position analysis forces |A \ A.image(·+d)| = 1
sorry
```
The inductive hypothesis gives `|A + B| = |A| + |B| - 1`. If A isn't a singleton,
then for any shift d ∈ B - B, the set `A \ A.image(·+d)` must have cardinality 1.
This follows from: if |A ∩ A.image(·+d)| = |A| - 1, then by `ap_of_near_periodic`,
A is an AP. The counting argument uses Finset inclusion-exclusion.

**SORRY 2** (line 407, main case analysis):
```lean
-- Case 1 existence: counting argument or iterative removal
sorry
```
Need to exhibit a specific `d` such that the shift argument works. In the literature
proof, this is done by taking d to be the common difference of B (which is an AP
by induction hypothesis).

### Proof Strategy (Literature)

The standard proof of Vosper (1956) proceeds:
1. Fix d = common difference of B (by induction, B is an AP)
2. Show A + {d} intersects A in exactly |A|-1 elements (Cauchy-Davenport equality forces this)
3. Apply `ap_of_near_periodic` to conclude A is an AP with difference d

### Key Lean Infrastructure (Already Proved)

- `ap_of_near_periodic`: if `A \ A.image(·+d) = {x}` (singleton), then A is an AP
- `vosper_base`: |A| = 2 case is closed
- `IsArithmeticProgression p d A`: defined as consecutive shifts of a base element
- `ap_iff_card_inter`: A is AP iff `|A ∩ A.image(·+d)| = |A| - 1`

---

## Insights

### Finset API Requirements

For SORRY 1, the key lemmas needed:
- `Finset.card_sdiff` : `B ⊆ A → |A \ B| = |A| - |B|`
- `Finset.card_image_of_injective` : `|A.image f| = |A|` if f injective
- `Finset.card_union_add_card_inter` : inclusion-exclusion

For SORRY 2:
- Existence of d from the AP structure of B (inductive hypothesis)
- `Finset.card_le_card` for comparison arguments

### Aristotle Eligibility

Both sorries are **theorem sorries** (not def sorries) — Aristotle-eligible.
The companion file `Erdos476OQ05Aristotle.lean` exists and exposes these as standalone
theorems. Recommend Aristotle submission as first approach.

---

## Dead Ends

[Approaches known not to work will be documented here]
