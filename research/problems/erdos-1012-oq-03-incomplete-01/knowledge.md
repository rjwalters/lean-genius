# Knowledge: Complete directed Hamiltonian cycle thresholds proof

## Problem Summary

Prove `directed_hamiltonian_threshold` and `ghouila_houri` in `Proofs/Erdos1012OQ03.lean`.
`directed_hamiltonian_threshold`: a strongly connected digraph with arcCount > (n-1)² has a Hamiltonian cycle.

## Session 2026-04-04 (Session 2) — hmissing_count proof

**Mode**: REVISIT
**Outcome**: progress — `hmissing_count` proved, `perm_arc_bad_card_le` submitted to Aristotle

### What I Did

1. Proved `hmissing_count : missingArcs.card ≤ n - 2` (was sorry)
   - Added `arcCount_eq_filter_bij` helper lemma (outside main proof to avoid instance clashes)
   - Used `Finset.offDiag_card` + `simp [mul_tsub, mul_one]` for the counting argument
2. Created `Erdos1012OQ03Aristotle.lean` companion file with `perm_arc_bad_card_le`
3. Submitted to Aristotle: project `73cf466b-e55c-4b03-a282-0ef698c26775`

### Key Findings

- `arcCount`'s internal `letI := Classical.decPred _` creates DecidablePred instances that
  clash with any explicit `haveI` in scope. Fix: extract bijection proof to separate lemma
  with `[DecidableRel D.arc]` parameter, use `classical` tactic in body for uniform instances.
- `simp only [Digraph.arcCount, Fintype.card_subtype]` unfolds `arcCount` AND converts
  `Fintype.card {p // P p}` to `(Finset.univ.filter P).card` in one step.
- `Finset.offDiag_card` gives `n^2 - n` (not `n*(n-1)`). To prove `n^2 - n = n*(n-1)`:
  `omega` fails (nonlinear), `zify + ring` fails (can't expand `↑(n^2-n)` cast).
  Fix: `simp only [mul_tsub, mul_one]` — `mul_tsub` rewrites `n*(n-1)` → `n*n - n*1`.
- `Finset.disjoint_filter.2` takes `fun ⟨a,b⟩ _ ⟨_, hnot⟩ harc => hnot harc` to prove
  missingArcs and presentArcs are disjoint.

### Files Modified

- `proofs/Proofs/Erdos1012OQ03.lean` (arcCount_eq_filter_bij ~line 989, hmissing_count ~line 1064)
- `proofs/Proofs/Erdos1012OQ03Aristotle.lean` (new companion file)
- `src/data/research/problems/erdos-1012-oq-03.json` (knowledge updated)

### Next Steps

- Await Aristotle result for `perm_arc_bad_card_le` (project `73cf466b-e55c-4b03-a282-0ef698c26775`)
- After integration: `directed_hamiltonian_threshold` fully proved (0 sorries in Part V)
- `ghouila_houri` (directed Dirac theorem, ~200 lines) remains as separate work item

---

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
