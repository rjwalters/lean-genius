# Knowledge: Complete directed Hamiltonian cycle thresholds proof

## Problem Summary

Formalize Moon-Moser theorem and Ghouila-Houri theorem for strongly-connected
directed graphs in Lean 4, building on the existing Rédei Hamiltonian path proof.

## Session 2026-04-03 (Session 4) - Prove tournament_cycle_extendable Case 1

**Mode**: REVISIT
**Outcome**: progress

### What I Did
- Applied working proof of `tournament_cycle_extendable` Case 1 (insertion case)
- Added `list_idx_congr` helper lemma to handle dependent-type rw failures
- Used `change` tactic to normalize goal bound proofs before `rw`
- Build: 3060 jobs, `Build completed successfully`

### Key Findings

**Critical technique: `change` to normalize bound proofs**

After `set jn := (j+1) % L.length` and `have hjn_lt : jn < L.length := ...`, the
goal has `L[jn]'proof_from_defn` with a DIFFERENT proof term than `hjn_lt`. Lean's
`rw` is syntactic, so `rw [hvtgt]` fails if `hvtgt` uses `hjn_lt` but goal has
`proof_from_defn`. Fix: add `change D.arc (L[j]'hj) (L[jn]'hjn_lt)` which succeeds
by proof irrelevance (both proofs have the same type).

**`list_idx_congr` helper**:
```lean
private lemma list_idx_congr {α : Type*} {l : List α} {i j : Nat} (h : i = j)
    {hi : i < l.length} {hj : j < l.length} : l[i]'hi = l[j]'hj := by
  subst h; rfl
```
Used with `convert harcs j (by omega) using 1; exact list_idx_congr (index_proof)`
to close arc goals without dependent-type rw.

**Avoid `subst` when hypothesis `j = i` where `i` appears in other types**:
Use `have hjn_eq : jn = i+1 := by rw [hjn_val, hji2]` and `list_idx_congr hjn_eq`
instead of `subst hji2`.

### Files Modified
- `proofs/Proofs/Erdos1012OQ03.lean`: added `list_idx_congr`, proved Case 1 of `tournament_cycle_extendable`

### Next Steps

1. Prove `tournament_cycle_non_insertable`: if no i has `l[i]→u` AND `u→l[i+1]`, then tournament forces either all `l[i]→u` or all `u→l[i]`. This follows from: if u beats some l[i] but loses to l[i+1], the non-insertable condition means either u beats l[i] implies u beats l[i+1] (induction around cycle).

2. Close `tournament_cycle_extendable` Case 2: use `h_ni` (all-in or all-out dichotomy) + SC of D to derive contradiction or find longer cycle via path through u.

3. Prove `nodup_insertIdx`: search Mathlib for `List.Nodup.insertIdx` or prove by induction using `List.nodup_cons` and membership facts.

## Technical Context

**Key sorry chain**:
- `tournament_cycle_extendable` Case 2 needs `tournament_cycle_non_insertable` (sorry)
- `tournament_cycle_non_insertable` needs tournament invariant proof (~20 lines)
- Once `tournament_cycle_extendable` closes: `grow_cycle_to_hamiltonian` (proved) → `moon_moser` (proved) → `directed_hamiltonian_threshold` closes partially

**Lean 4.26 API for insertIdx**:
- `List.getElem_insertIdx_of_lt (hn : j < i) (hk : j < (l.insertIdx i x).length)`
- `List.getElem_insertIdx_self (hi : i < (l.insertIdx i x).length)`
- `List.getElem_insertIdx_of_gt (hn : i < j) (hk : j < (l.insertIdx i x).length)`
- `List.length_insertIdx`: conditional on `i ≤ l.length`
