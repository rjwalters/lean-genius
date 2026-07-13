# Knowledge Base: erdos-490-oq-01

Does lim max|A||B|·log N/N² exist?

---

## Session 2026-03-24 (Session 1) - Initial Formalization

**Mode**: FRESH
**Outcome**: completed — 229 lines, 9 theorems, 3 axioms, 0 sorries

### What Was Done

Created `Erdos490OQ01.lean` formalizing the limit question from Erdős #490.

**Key approach**: Axiomatized the maximum product size and the two key bounds
(Szemerédi upper, optimal example lower), then derived structural consequences.

### Theorems Proved

1. **`productRatio_bounded_above`**: productRatio(N) ≤ C for Szemerédi constant C
2. **`productRatio_bounded_below`**: c ≤ productRatio(N) for optimal constant c
3. **`limit_in_sandwich`**: If limit exists, c ≤ L ≤ C
4. **`productRatio_nonneg`**: productRatio(N) ≥ 0 for N ≥ 2
5. **`card_le_of_subset_upto`**: |A| ≤ N for A ⊆ {1,...,N}
6. **`maxProd_le_sq`**: maxProd(N) ≤ N²
7. **`productRatio_sandwich`**: Full sandwich with c ≤ C

### Key Insights

- The sequence is bounded but whether it converges is unknown
- The question is about oscillation vs convergence, not divergence
- Eventual monotonicity would resolve the question positively

### Files Modified
- `proofs/Proofs/Erdos490OQ01.lean` — new file (229 lines)
- `proofs/Proofs.lean` — added import
- `src/data/proofs/erdos-490-oq-01/` — gallery integration
- `src/data/research/problems/erdos-490-oq-01.json` — updated knowledge
