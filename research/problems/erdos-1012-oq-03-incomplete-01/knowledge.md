# Knowledge: Complete directed Hamiltonian cycle thresholds proof

## Problem Summary

Prove `directed_hamiltonian_threshold` and `ghouila_houri` in `Proofs/Erdos1012OQ03.lean`.
`directed_hamiltonian_threshold`: a strongly connected digraph with arcCount > (n-1)² has a Hamiltonian cycle.

## Session 2026-04-04 (Session 1) — Main proof infrastructure

**Mode**: FRESH
**Outcome**: progress — directed_hamiltonian_threshold now fully proved (modulo hBadFor_bound sorry)

### What I Did

1. Fixed `arcCount` definition: changed from `Fintype.card {p // ...}` (synthesis error) to `haveI : DecidablePred _ := Classical.decPred _; (Finset.univ.filter ...).card`
2. Proved `missing_arcs_le` lemma (arcCount > (n-1)² → ≤ n-2 missing arcs) via `set k := n-1; set a := k²; omega`
3. Proved `h_partition` (Missing.card + arcCount = n*(n-1)):
   - Defined Missing, ArcPairs as disjoint Finsets covering NonLoop
   - Proved NonLoop = univ \ diagonal via Finset.card_sdiff (new API: no argument) + inter_univ + zify+ring
4. Proved `hAllBad_lt` (|AllBad| < n!) via union bound + factorial chain + nlinarith
5. Fixed `hne` (consecutive cycle entries distinct): used `rcases Nat.lt_or_ge (i.val+1) n` to handle variable-modulus modular arithmetic that omega cannot handle
6. Extracted good permutation + constructed Hamiltonian cycle

### Key Findings

- `Finset.card_sdiff` changed API in recent Mathlib: old `(h : s₁ ⊆ s₂) → (s₂\s₁).card = s₂.card - s₁.card` is now the no-argument form `(s\t).card = s.card - (t∩s).card`. Fix: `rw [Finset.card_sdiff, Finset.inter_univ]`
- Variable modular arithmetic `(i+1)%n` cannot be handled by omega — requires explicit case split
- `Classical.decPred _` and `classical` tactic provide definitionally equal instances, so `harcEq := rfl` works after changing arcCount to use filter.card

### Files Modified

- `proofs/Proofs/Erdos1012OQ03.lean` (lines 947-1141)
- `src/data/proofs/erdos-1012-oq-03/meta.json`
- `src/data/research/problems/erdos-1012-oq-03.json`

### Next Steps

- Submit `hBadFor_bound` to Aristotle: prove `|BadFor(a,b)| ≤ n*(n-2)!` by fixing σ(k) and σ((k+1)%n), enumerating n positions, counting (n-2)! completions each
- Prove `ghouila_houri`: directed Dirac theorem (~200 lines, needs longest-path argument)
