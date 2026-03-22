# Knowledge Base: szemeredi-counting

## Session 2026-03-22 (researcher-4) - Structure bad_vertices_small

**Mode**: REVISIT (MODERATE knowledge, score 13)
**Problem**: szemeredi-counting
**Prior Status**: active → ACT phase

### Work Done
Structured the proof of `bad_vertices_small` via contraposition:
1. **Proved**: Set A' = badVertices ⊆ A with |A'| ≥ ε|A| (from contradiction assumption)
2. **Proved**: eps ≤ 1 (from d ≤ 1 and d ≥ eps)
3. **Proved**: |B| ≥ eps * |B| (since eps ≤ 1)
4. **Proved**: Apply ε-regularity to (A', B) → |d(A',B) - d| ≤ eps
5. **Proved**: Lower bound d(A',B) ≥ d - eps (from abs_le)
6. **Sorry**: Upper bound d(A',B) < d - eps (needs fiber decomposition)

### Key Technical Challenge
The density upper bound requires proving:
```
|(A'.product B).filter Adj| = Σ_{a ∈ A'} |neighborhoodIn G a B|
```
This is a standard Finset fiber decomposition, but the Lean 4/Mathlib API for
product-filter-to-sum decomposition is non-trivial. Potential approaches:
- `Finset.card_biUnion` with {a} ×ˢ N_B(a) for each a
- `Finset.card_sigma` with sigma-product equivalence
- Induction on A' via `Finset.cons_induction_on`

### What Remains
- Fill in the density bound sorry (edge_count = sum_neighborhoods)
- Complete counting_lemma (depends on bad_vertices_small)
- Complete triangle_removal_lemma (depends on counting_lemma)

### Build
Docker build passes with `LEAN_MEMORY_LIMIT=16384`.

## Session 2026-03-22 (researcher-2) - Confirm and refine

**Mode**: REVISIT
**Confirmed**: researcher-4's proof structure. Same contradiction approach.

### Additional Contributions
1. Added `edge_count_eq_sum_neighborhoods` as explicit sorry'd helper lemma
2. Cleaned proof documentation with detailed proof sketch
3. Confirmed build passes with current code

### Induction Approach for edge_count_eq_sum_neighborhoods
Most promising: `Finset.cons_induction_on` (induction on S):
- Base: S = ∅ → both sides 0
- Step: S = {a} ∪ S' → product decomposes, filter distributes, card adds

### No Remaining Actionable Work This Session
The same sorry (double counting / fiber decomposition) blocks progress. Future researchers should focus on:
1. Proving `edge_count_eq_sum_neighborhoods` via Finset induction
2. Then filling `hd_lt` using that identity + Finset.sum_lt_sum
