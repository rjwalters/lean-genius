# Current State

**Phase**: IN_PROGRESS
**Since**: 2026-05-03T22:00:00Z
**Iteration**: 12

## Current Focus

Reducing sorry count in KonigsbergOQ01OQ02.lean. Currently at 1 sorry (remove_circuit_balanced).

## Active Approach

Hierholzer infrastructure: maxTrail greedy trail, open/closed walk counting lemmas, circuit existence.

## Progress (3 → 1 sorries this session)

**Proved**:
- `euler_path_implies_degree_balance`: necessity direction for Eulerian paths. Proved via:
  1. Pigeonhole counting: walk coverage + |image| ≤ n = |G.edges| → G.edges = image → hsteps
  2. `Finset.card_image_iff_injOn`: card equality → injectivity → ∃! unique coverage
  3. `open_walk_first_source_excess` / `open_walk_last_target_excess` for endpoint degree excess
  4. Interior vertex balance via bijection i ↦ i-1 (walk[0]=s≠v and walk[n]=t≠v give bounds)

**Deleted**:
- `maxTrail_used_eq`: private lemma with sorry, unused dead code (no references in file)

## Remaining

1. `remove_circuit_balanced` (1 sorry): removing a directed circuit from a balanced graph preserves balance.
   - Proof sketch complete in comments: degree decrease equals circuit pass-through count,
     balanced by closed_walk_balance
   - Proof requires careful Finset.sdiff algebra

## Blockers

Pre-existing Mathlib API drift in the file:
- `Nat.strong_rec_on` renamed
- `List.length_eq_one.mp` removed
- Several simp lemma API changes
These are in the ORIGINAL committed code, not in recent changes.

## Next Action

Either fix the Mathlib API drift issues (infrastructure repair), or commit current progress
and let mechanic/builder handle the API fixes.

## Attempt Counts

- Total attempts: 12
- Current approach attempts: 2
- Approaches tried: 3
