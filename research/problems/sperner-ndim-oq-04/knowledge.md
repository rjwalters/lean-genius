# Knowledge: n-Dimensional Sperner: Kuhn Path-Following Algorithm Formalization

## Problem Summary

Formalize Kuhn's (1968) constructive proof of Sperner's lemma via path-following in the door adjacency graph. Key goal: starting from a boundary door, follow the unique path to reach a fully-colored simplex.

**Status**: ACT — 1 sorry remains (non-revisiting invariant in `kuhn_walk_reaches_fc`).
**Gallery entry**: `src/data/proofs/sperner-ndim-oq-04/`
**Lean file**: `proofs/Proofs/SpernerNDimOQ04.lean`

---

## Session 2026-04-23 (Session 2) — Proof Dependency Reduction

**Mode**: REVISIT
**Outcome**: progress (sorries reduced 3→1)

### What I Did

1. Analyzed all three sorries to identify true mathematical blockers
2. Established dependency chain: sorry1 ← sorry3 ← sorry2 (all reduce to sorry2)
3. Filled `kuhn_path_terminates` (sorry 1) via `kuhnPathStart_is_fc` as constructive witness
4. Filled `kuhnPathStart_is_fc` (sorry 3) via `kuhn_walk_reaches_fc` applied to initial state
5. Restructured file: moved `kuhn_path_terminates` to after `kuhnPathStart_is_fc`
6. Added detailed mathematical analysis of sorry 2 blocker in docstring

### Key Findings

**Critical insight**: The three sorries all reduce to ONE core obligation: `kuhn_walk_reaches_fc`.

**Proof structure (now explicit)**:
- `kuhn_walk_reaches_fc` (sorry, one obligation) →
- `kuhnPathStart_is_fc` (proved: applies kuhn_walk_reaches_fc to state₀ with visited=∅) →
- `kuhn_path_terminates` (proved: uses kuhnPathStart as constructive FC witness)

**Why kuhnPathStart_is_fc compiles**: The initial state has `visited = ∅`, so
`visited.card = 0` and `fuel = Fintype.card K.Simplex - 0 = Fintype.card K.Simplex`
(by `Nat.sub_zero`). Definitional equality between `kuhnPathStart`'s internal state
and the explicit `state₀` allows `exact hreach` to close the goal.

**Non-revisiting invariant analysis** (why it's hard):
The `kuhnWalk` terminates (returns `state.current`, which may be non-FC) when:
1. `fuel = 0` — eliminated by sufficient fuel
2. `exit_doors.isEmpty` — eliminated by `nonfc_with_door_has_unique_exit`
3. `K.adj state.current k_out = none` — second boundary door; needs IsSperner+unique-bdry assumption
4. `s' ∈ state.visited ∪ {state.current}` — the revisiting guard (core blocker)

For case (4): By `adj_symm`, `K.adj s' k_out' = some (state.current, k_out)`.
If `s' ∈ state.visited`, it was a previous current with some exit door.
By `nonfc_with_door_has_unique_exit`, the exit from `s'` was the unique other door.
If `s'` exited via `k_out'` → moved to `state.current` → `state.current` gets added
to visited eventually → `state.current ∈ state.visited`, contradicting `current_not_visited`.
If `s'` exited via a different door `k_exit ≠ k_out'` → `s'` has 2 doors: `k_exit` and `k_out'`.
The unique exit from `k_entry` (entry at time j) is the OTHER door by the parity theorem.
But then, following the path from `s'` at time j → ... → `state.current` creates a cycle,
again contradicting `current_not_visited`.

**Blocker**: This argument requires knowing the EXIT DOOR used when `s'` was previously current.
The current `KuhnState` only stores the visited SET — not the sequence or exit doors.
A stronger invariant would track: for each `s ∈ visited`, which door was the exit at time j.

**Case (3) blocker**: The walk can terminate at a SECOND boundary door on face d.
This requires `IsSperner c` + a unique-boundary-door-on-face-d assumption to eliminate.

### Files Modified

- `proofs/Proofs/SpernerNDimOQ04.lean` (restructured: sorries 3→1, added detailed analysis)

### Proven This Session

1. `kuhnPathStart_is_fc` — Now proved (via kuhn_walk_reaches_fc + simp on state₀)
2. `kuhn_path_terminates` — Now proved (via kuhnPathStart as existential witness)

### Remaining Sorry (1)

- `kuhn_walk_reaches_fc` — Core obligation requiring non-revisiting invariant.
  **What's needed**: Either:
  1. Add `prev_simplex : Option K.Simplex` + `prev_exit_invariant` to `KuhnState`
     to track door history, enabling the non-revisiting contradiction proof
  2. OR add `IsSperner c` + unique-boundary-door hypothesis + prove door graph is cycle-free
  3. OR prove directly: in a Kuhn-compatible door graph, no path starting at a
     boundary-door vertex can return to a visited vertex (graph-theoretic argument)

### Next Steps

1. **Add predecessor invariant to KuhnState**: Add `prev : Option K.Simplex` and
   `prev_exit : prev.map (K.adj ·) leads to (current, entry)` — then prove non-revisiting
2. **Check if Aristotle can handle it**: The sorry might be tactic-provable with the right
   induction hypothesis formulated (strong induction on fuel, with non-revisiting as IH)
3. **Alternative**: Use `IsSperner c` + boundary parity to show FC exists without
   tracing the exact walk path (avoid constructive proof, use classical argument)

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
