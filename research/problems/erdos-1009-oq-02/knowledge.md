# erdos-1009-oq-02: Edge-Disjoint K₄ Copies Beyond Turán Threshold

## Problem Summary

**Open Question**: Is there an analogue of Györi's theorem for K₄?
If G has ⌊n²/3⌋ + k edges with k < cn, does G contain ≥ k - g(c) edge-disjoint K₄ copies?

The open question (edgeDisjointK4_question) remains open — it's a research-level conjecture.
We proved the supporting infrastructure: Turán's theorem for K₄ and existence above threshold.

## Session 2026-04-03 (Session 1) - COMPLETED: All supporting theorems proved

**Mode**: FRESH
**Outcome**: completed — 0 sorries in Erdos1009OQ02Problem.lean

### What I Did
- Proved `turanK4_extremal`: K₄-free graphs have ≤ ⌊n²/3⌋ edges
  - Used `CliqueFree.card_edgeFinset_le` from Mathlib `Extremal/Turan.lean` (v4.26.0)
  - Extracted arithmetic into private lemma `turanK4_arith`  
  - `simp [h] ; omega` works per case after 3-way case split on n%3
- Proved `exceeds_turanK4_has_clique4`: exceeding Turán threshold implies K₄ exists
  - Used `Finset.card_eq_four` to decompose 4-element clique finset
  - Constructed `Clique4 G` from the 4 vertices + clique adjacencies

### Key Findings
- `CliqueFree.card_edgeFinset_le` in Mathlib returns `let n := Fintype.card V; ...` — `simp only at hbound` unfolds this, but doesn't reduce constants like `3-1`, `2*3`, `0^2`; need `simp [h]` (full simp) or extract arithmetic into a separate lemma
- `push_neg` on `¬ ∃ K : Clique4 G, True` gives `∀ K, False` (simplifies ¬True)
- `Finset.card_eq_four` at `Mathlib.Data.Finset.Card` gives the needed 4-element decomposition
- Pattern follows exactly the K₃ proof in `Erdos1009Problem.lean`

### Files Modified
- `proofs/Proofs/Erdos1009OQ02Problem.lean` (sorries 0 → 0, was 4)
- `src/data/research/problems/erdos-1009-oq-02.json`

### Next Steps
- The main open question `edgeDisjointK4_question` remains open (research-level)
- Future work: K₅ analog? Or sharp bounds for K₄ excess?
