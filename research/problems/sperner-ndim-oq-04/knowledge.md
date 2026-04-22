# Knowledge: n-Dimensional Sperner: Kuhn Path-Following Algorithm Formalization

## Problem Summary

Formalize Kuhn's (1968) constructive proof of Sperner's lemma via path-following in the door adjacency graph. Key goal: starting from a boundary door, follow the unique path to reach a fully-colored simplex.

**Status**: ACT — Lean file created, 3 sorries remain for path termination.
**Gallery entry**: `src/data/proofs/sperner-ndim-oq-04/`
**Lean file**: `proofs/Proofs/SpernerNDimOQ04.lean`

---

## Session 2026-04-22 (Session 1) — Kuhn Algorithm Formalization

**Mode**: FRESH
**Outcome**: progress

### What I Did

1. Surveyed SpernerNDim.lean for available infrastructure (663 lines)
2. Identified `abstract_door_parity`, `isDoorAt`, `IsFC`, `door_transfer` as the key tools
3. Made `door_transfer` public in SpernerNDim.lean (was private)
4. Designed the `IsKuhnCompatible` axiom (door degree ≤ 2) to make algorithm deterministic
5. Created full Lean formalization (~290 lines) at `proofs/Proofs/SpernerNDimOQ04.lean`
6. Created gallery data: meta.json, annotations.json, index.ts

### Key Findings

- `door_degree_parity` proof: use `simp only [hiff]` (not `rw [hiff]`) + `convert h using 2` pattern — same as `per_simplex_door_parity` in SpernerNDim
- `fc_door_count_eq_one` and `nonfc_door_count_zero_or_two` follow immediately from `omega`
- `nonfc_with_door_has_unique_exit` proved fully via `Finset.card_eq_two` extraction
- For `kuhnWalk`, `Finset.Nonempty` is a `Prop` — use `if hne : ...` not `match ... | isTrue`
- For `kuhnStep_door_preserved`, use `simp only [kuhnStep, if_neg, dif_pos hexit]` pattern
- The non-revisiting invariant (why walk never revisits) is the hard unsolved part

### Files Modified

- `proofs/Proofs/SpernerNDimOQ04.lean` (CREATED, ~290 lines)
- `proofs/Proofs/SpernerNDim.lean` (removed `private` from `door_transfer`, `door_transfer_one_dir`)
- `src/data/proofs/sperner-ndim-oq-04/meta.json` (CREATED)
- `src/data/proofs/sperner-ndim-oq-04/annotations.json` (CREATED)
- `src/data/proofs/sperner-ndim-oq-04/index.ts` (CREATED)
- `src/data/research/problems/sperner-ndim-oq-04.json` (UPDATED knowledge)

### Proven This Session

1. `fc_door_count_eq_one` — Under IsKuhnCompatible, FC simplices have exactly 1 door
2. `nonfc_door_count_zero_or_two` — Under IsKuhnCompatible, non-FC simplices have 0 or 2 doors
3. `nonfc_with_door_has_unique_exit` — Non-FC simplex with entry door has unique exit door

### Remaining Sorries (3)

1. `kuhn_path_terminates` — Main existence theorem (derived from `sperner_ndim` via sorry)
2. `kuhn_walk_reaches_fc` — Walk correctness requires non-revisiting invariant
3. `kuhnPathStart_is_fc` — Top-level correctness (depends on above two)

### Next Steps

1. **Prove non-revisiting invariant**: Show `kuhnWalk` visited set strictly grows at each step
2. **Verify IsKuhnCompatible for Freudenthal**: Check sperner-ndim-oq-01's triangulation
3. **Submit to Aristotle**: `kuhn_walk_reaches_fc` may be provable with non-revisiting established
