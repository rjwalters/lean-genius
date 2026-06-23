# Research State: szemeredi-counting

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-03-22
**Iteration**: 5

## Current Focus
**2 sorries remain in `triangle_removal_quantitative`** — both are partition cleanup budget lemmas (lines 816, 820). Everything else is proved including the full counting lemma (987 lines).

## Active Approach
Generic edge-budget helper: both remaining sorries are the same pattern — bound total vertex pairs by summing over partition pairs with equitability + density constraints. Prove a single reusable lemma, then both become near-one-liners.

## What's Proved
- `counting_lemma` — full quantitative lower bound with d ≥ 2ε
- `counting_lemma_lower_bound` — simplified (1-2ε)ε³|A||B||C|
- `bad_vertices_small` — via fiber decomposition
- `perVertex_density_bound` — degree concentration
- `triangleCount_mono`, `triangleCount_le_total`
- Within-part deletion budget (lines 731-812)
- Triangle-freeness argument (complete)
- Full proof skeleton for `triangle_removal_quantitative`

## Remaining Sorries (2)

### 1. h_irreg (line 816)
```lean
have h_irreg : (R_irreg.card : ℚ) ≤ (delta / 2) * ↑n ^ 2 := by sorry
```
**Strategy**: R_irreg ⊆ union of (Vi ×ˢ Vj) over irregular pairs. Each |Vi ×ˢ Vj| ≤ (n/k+1)². Number of irregular ordered pairs ≤ ε·k·(k-1) from `IsRegularPartition`. Total ≤ ε·k²·(n/k+1)² ≤ 4ε·n². Since ε ≤ δ/8: 4ε·n² ≤ (δ/2)·n².

### 2. h_sparse (line 820)
```lean
have h_sparse : (R_sparse.card : ℚ) ≤ (delta / 4) * ↑n ^ 2 := by sorry
```
**Strategy**: R_sparse filters on G.Adj, so each pair contributes ≤ edgeCountBetween. For sparse pairs density < 2ε, so edge count < 2ε·|Vi|·|Vj|. Total < 2ε·Σ|Vi|·|Vj| ≤ 2ε·n². Since ε ≤ δ/8: 2ε·n² ≤ (δ/4)·n².

### Recommended helper lemma (prove FIRST)
A single `sum_pairCount_le` that bounds total pairs across a set of partition pair indices, given per-pair density bounds and part size bounds. Then:
- **Irregular**: d = 1, S.card ≤ ε·k², m = n/k + 1
- **Sparse**: d = 2ε, S.card ≤ k², m = n/k + 1

## Already Available
- `hmax_part`: ∀ S ∈ P.parts, |S| ≤ n/k + 1 (proved, lines 753-775)
- `hk_ge_inv_delta`: k ≥ 8/δ (line 672)
- `heps_le_delta8`: ε ≤ δ/8 (line 610)
- `card_mul_edgeDensity` from SzemerediRegularity for density↔count conversion
- Equitable partition `hequi`, partition sum = n (`hsum`)

## Lean Engineering Notes
- Keep everything in ℚ
- For irregular pair count: unfold `IsRegularPartition` to get bound on `(parts.product parts).filter ...`
- R_irreg uses ordered pairs — no double-counting issue
- Use `Finset.card_le_card` + `Finset.card_biUnion_le` pattern (same as within-part proof)

## Attempt Count
- Total attempts: 5
- Current approach attempts: 1 (budget lemma approach)
- Approaches tried: 2

## Blockers
None — proof strategies are clear, this is mechanical.

## Next Action
1. Prove generic sum_pairCount_le helper
2. Apply to h_irreg with d=1
3. Apply to h_sparse with d=2ε
4. Update meta.json when 0 sorries achieved
