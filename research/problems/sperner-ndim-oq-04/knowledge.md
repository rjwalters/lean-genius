# Knowledge: n-Dimensional Sperner: Kuhn Path-Following Algorithm Formalization

## Problem Summary

Formalize Kuhn's (1968) constructive proof of Sperner's lemma via path-following in the door adjacency graph. Key goal: starting from a boundary door, follow the unique path to reach a fully-colored simplex.

**Status**: ACT — 3 sorries → 2 sorries. `kuhn_path_terminates` proved via `sperner_ndim`.
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

---

## Session 2026-04-22 (Session 2) — Prove kuhn_path_terminates

**Mode**: FRESH (continuing from Session 1)
**Outcome**: progress — 1 sorry eliminated

### What I Did

1. Analyzed all 3 sorries deeply: `kuhn_path_terminates`, `kuhn_walk_reaches_fc`, `kuhnPathStart_is_fc`
2. Discovered `kuhn_path_terminates` was missing `hc: IsSperner c` and `hbdry_odd` hypotheses
3. Proved `kuhn_path_terminates` by adding those hypotheses and using `sperner_ndim c K hc hbdry_odd` (1-line proof)
4. Documented the non-revisiting proof strategy in `kuhn_walk_reaches_fc` comments
5. Updated meta.json (sorries: 3→2), knowledge files

### Key Findings

- `kuhn_path_terminates` doesn't need the walk at all — FC existence follows from `sperner_ndim` (parity)
- The non-revisiting proof for `kuhn_walk_reaches_fc` requires TWO things not currently in the codebase:
  1. "Adjacent simplices share a unique facet" axiom (not in `SpernerTriangulation`)
  2. Per-visited-simplex door history in `KuhnState` (entry/exit doors per step)
- Proof sketch for non-revisiting (case j < n-1): if s' ∈ visited and K.adj current k_out = some (s', ...), then s' has a 3rd door connecting to current — violates Kuhn compat (degree ≤ 2). This requires knowing s's previous entry/exit doors from walk history.
- Proof sketch for case j = n-1 (immediate predecessor): K.adj current k_out and K.adj current state.entry both reach s', giving two facets of current → unique-facet axiom gives k_out = state.entry, contradicting k_out ≠ state.entry.

### Files Modified

- `proofs/Proofs/SpernerNDimOQ04.lean` (MODIFIED, ~420 lines, sorries: 3→2)
- `src/data/proofs/sperner-ndim-oq-04/meta.json` (UPDATED: sorries 3→2, assumptions)
- `src/data/research/problems/sperner-ndim-oq-04.json` (UPDATED knowledge)
- `research/problems/sperner-ndim-oq-04/knowledge.md` (this file)

### Proven This Session

4. `kuhn_path_terminates` — Given IsSperner c and odd boundary door count, FC exists (proved via `sperner_ndim`)

### Remaining Sorries (2)

1. `kuhn_walk_reaches_fc` — Constructive walk correctness; requires non-revisiting invariant
2. `kuhnPathStart_is_fc` — Main constructive theorem (depends on kuhn_walk_reaches_fc)

### Next Steps

1. **Add unique-facet axiom to SpernerTriangulation**: `∀ s k₁ k₂ s' k₁' k₂', K.adj s k₁ = some (s', k₁') → K.adj s k₂ = some (s', k₂') → k₁ = k₂`
2. **Strengthen KuhnState**: Add per-visited-simplex entry/exit door records (path invariant)
3. **Prove kuhnWalk_never_revisits**: Using the two additions above
4. **Then kuhn_walk_reaches_fc and kuhnPathStart_is_fc** follow from non-revisiting
