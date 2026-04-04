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

## Session 2026-04-04 (Session N) - Fix ghouila_houri ceiling condition + GH infrastructure

**Mode**: REVISIT
**Outcome**: progress — corrected critical mathematical error, added proof infrastructure

### What I Did

1. **Fixed critical mathematical bug**: `ghouila_houri` used floor division `Fintype.card V / 2` which makes the theorem FALSE for n=5 (counterexample: SC digraph with δ⁺=δ⁻=2=⌊5/2⌋ has no Hamiltonian cycle). Changed to ceiling `(Fintype.card V + 1) / 2`.

2. **Added PART VI: Ghouila-Houri Infrastructure** with three sorry-based but mathematically sound lemmas:
   - `gh_initial_cycle`: SC + δ⁺ ≥ ⌈n/2⌉ → initial directed cycle exists
   - `gh_cycle_extendable`: key counting argument for k=n-1 case documented:
     * A = {i ∈ [k] : arc(l[i], u)}, |A| = inDegree(u) ≥ ⌈n/2⌉
     * B = {i ∈ [k] : arc(u, l[(i+1)%k])}, |B| = outDegree(u) ≥ ⌈n/2⌉
     * |A|+|B| ≥ 2⌈n/2⌉ ≥ n > k → pigeonhole → insertion point exists
   - `gh_grow_cycle`: induction on gap n-|l| to grow to Hamiltonian

3. **Identified pre-existing compilation errors**: The file has 57+ errors from API changes (List.insertNth → List.insertIdx, List.indexOf, etc.) that pre-date our work. These need separate fixing.

### Key Findings

- Floor vs ceiling is a critical distinction: theorem with ⌊n/2⌋ is FALSE but with ⌈n/2⌉ is TRUE
- The k=n-1 counting argument is the key lemma: A∩B ≠ ∅ because |A|+|B| ≥ n > k=n-1
- Edit tool in this environment doesn't persist writes; Python file I/O works reliably
- Pre-existing API issue: Lean4/Mathlib4 v4.26.0 renamed List.insertNth → List.insertIdx

### Files Modified

- `proofs/Proofs/Erdos1012OQ03.lean` (PART III ghouila_houri + new PART VI)

### Next Steps

- Fix pre-existing compilation errors: List.insertNth → List.insertIdx, indexOf, etc.
- Prove `gh_initial_cycle`: use SC + high out-degree to find closed walk → extract cycle
- Prove `gh_cycle_extendable` k=n-1 case: formalize the A∩B ≠ ∅ argument (needs [DecidableRel D.arc])
- Prove `gh_cycle_extendable` k<n-1 case: SC-based detour argument
