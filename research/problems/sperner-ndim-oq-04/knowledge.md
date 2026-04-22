# Knowledge: n-Dimensional Sperner: Kuhn Path-Following Algorithm Formalization

## Problem Summary

Formalize Kuhn's (1968) constructive proof of Sperner's lemma via path-following in the
door adjacency graph. Key goal: starting from a boundary door, follow the unique path to
reach a fully-colored simplex.

**Status**: ACT — Lean file created, 3 sorries remain for path termination.
**Gallery entry**: `src/data/proofs/sperner-ndim-oq-04/`
**Lean file**: `proofs/Proofs/SpernerNDimOQ04.lean`

---

## Key Infrastructure (SpernerNDim.lean)

- `isDoorAt` — predicate for a simplex being a door at a given facet
- `IsFC` — fully-colored simplex predicate
- `door_transfer` — public function (was private; made public in this session)
- `abstract_door_parity` — parity theorem for door counting
- `IsKuhnCompatible` — axiom class (door degree ≤ 2) making algorithm deterministic

## Lean Patterns Learned

- For `door_degree_parity`: use `simp only [hiff]` (not `rw [hiff]`) + `convert h using 2`
  — same pattern as `per_simplex_door_parity` in SpernerNDim
- For `kuhnWalk`: `Finset.Nonempty` is a `Prop` — use `if hne : ...` not `match ... | isTrue`
- For `kuhnStep_door_preserved`: use `simp only [kuhnStep, if_neg, dif_pos hexit]` pattern

## Open Problem: Non-Revisiting Invariant

The walk from a boundary vertex in a path-structured component must terminate. Approaches:
1. **Pigeonhole**: Show `Finset.card` of visited set grows at each step; use fuel = `Fintype.card K.Simplex`
2. **Graph structure**: Door graph component containing a boundary vertex is a path (no cycles)

---

## Session 2026-04-22 (Session 1)

**Outcome**: Partial — core lemmas proved, 3 sorries remain

### What Was Done

1. Surveyed SpernerNDim.lean for available infrastructure (663 lines)
2. Identified `abstract_door_parity`, `isDoorAt`, `IsFC`, `door_transfer` as key tools
3. Made `door_transfer` public in SpernerNDim.lean
4. Designed `IsKuhnCompatible` axiom (door degree ≤ 2)
5. Created full Lean formalization (~290 lines) at `proofs/Proofs/SpernerNDimOQ04.lean`
6. Created gallery data: meta.json, annotations.json, index.ts

### Files Modified

- `proofs/Proofs/SpernerNDimOQ04.lean` (CREATED)
- `proofs/Proofs/SpernerNDim.lean` (removed `private` from `door_transfer`, `door_transfer_one_dir`)
- `src/data/proofs/sperner-ndim-oq-04/meta.json` (CREATED)
- `src/data/proofs/sperner-ndim-oq-04/annotations.json` (CREATED)
- `src/data/proofs/sperner-ndim-oq-04/index.ts` (CREATED)
