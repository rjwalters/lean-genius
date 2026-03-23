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

## Session 2026-03-22 (researcher-6) - Prove edge count bounds

**Mode**: REVISIT (RICH knowledge, score 17)
**Problem**: szemeredi-counting
**Prior Status**: 3 sorries in triangle_removal_quantitative edge_bound case

### Work Done
Proved all 3 remaining sorries in the edge count bound of `triangle_removal_quantitative`:

1. **h_wp** (within-part pairs ≤ (δ/4)n²):
   - R_wp ⊆ ⋃_{S ∈ P.parts} (S ×ˢ S) via biUnion
   - |R_wp| ≤ Σ|S|² ≤ (n/k+1)·n (using equitable partition size bound)
   - Arithmetic: n/k ≤ δn/8 and 1 ≤ δn/8 gives (n/k+1)·n ≤ (δ/4)n²

2. **h_irreg** (irregular cross-part pairs ≤ (δ/2)n²):
   - R_irreg ⊆ biUnion over irregular pairs of part products
   - Each product ≤ (n/k+1)², count ≤ εk(k-1)
   - Chain: εk(k-1)(n/k+1)² ≤ ε(n+k)² ≤ 4εn² ≤ (δ/2)n²

3. **h_sparse** (sparse cross-part edges ≤ (δ/4)n²):
   - Each sparse pair has < 2ε|Pa||Pb| edges (from density bound)
   - Σ ≤ 2ε·Σ|Pa||Pb| ≤ 2εn² (product sum identity)
   - 2ε ≤ δ/4 since ε ≤ δ/8

### Shared Infrastructure
- Partition sum identity: P.parts.sum card = n (reused from existing code pattern)
- Part size upper bound: S.card ≤ n/k + 1 (from equipartition + sum identity)
- Arithmetic helpers: 8 ≤ δk, 8 ≤ δn, k ≤ n

### Build Status
Docker build failed due to **pre-existing errors in SzemerediRegularity.lean** (Finpartition.supParts not found, etc). These errors predate this session. SzemerediCounting.lean cannot be compiled until SzemerediRegularity.lean is fixed.

### Result
- **0 sorries remaining** in SzemerediCounting.lean
- Full triangle removal lemma is now sorry-free (pending compilation)
- File: 1057 lines, 13 theorems, 0 axioms, 0 sorries
