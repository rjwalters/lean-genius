# Knowledge Base: szemeredi-regularity-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

The Frieze-Kannan weak regularity lemma (1999) is a simplified variant of Szemerédi's regularity
lemma that achieves exponential partition size (2^O(ε⁻²)) instead of the tower-type bound.
The key difference: Frieze-Kannan approximates edge density in the cut-norm sense, while full
Szemerédi achieves ε-regularity for all pairs.

**Research goal**: Formalize Frieze-Kannan in Lean 4 and prove the strict gap from full regularity.

---

## Key Definitions Needed

- **Cut norm**: `‖f‖_□ = max_{S,T ⊆ V} |∑_{i∈S, j∈T} f(i,j)|`
- **Step function / density function**: bipartite density between partition parts
- **Weak regularity**: cut-norm approximation by step function ≤ ε·|V|²
- **IsWeaklyRegular**: Lean predicate capturing the approximation bound

---

## Mathlib Status

The parent gallery proof `szemeredi-regularity` already provides:
- `Finpartition` API in Mathlib
- `SimpleGraph.regularity` lemmas (ε-regular pairs)
- `Mathlib.Combinatorics.SimpleGraph.Regularity.Energy` for energy increment

Check: does Mathlib have `cutNorm` or related supremum over bipartite subsets? Likely not yet.

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]
