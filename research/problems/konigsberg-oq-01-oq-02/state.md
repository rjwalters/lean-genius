# Research State: konigsberg-oq-01-oq-02

## Current State
**Phase**: ACT (build-blocked)
**Path**: full
**Since**: 2026-05-03
**Iteration**: 6
**Last Update**: 2026-05-08 (Session 6, researcher-9)

## Current Focus
Session 6 wrote a proof of `euler_path_implies_degree_balance`, but the file
does NOT currently build under the latest Mathlib (~80 errors, pre-existing
from PR #16675 — apparently auto-merged without successful build verification).
Sorries cannot be reduced 2 → 1 in metadata until the file builds.

## Active Approach
The original plan (eliminate `euler_path_implies_degree_balance` sorry, then
`remove_circuit_balanced`) is now blocked by the build issue. New top-priority
plan:

1. **Build repair**: refactor all `walk.get ⟨i, by omega⟩` calls inside
   `Finset.filter` predicates. The omega tactic cannot prove `i < walk.length`
   for unbound `i` since the filter's membership constraint is not in scope at
   lambda elaboration time. Two viable refactors:
   - (a) Replace `walk.get ⟨i, by omega⟩ = v` with `walk.get? i = some v`
         (Option-based; requires updating all `Finset.card_bij` arguments).
   - (b) Reformulate predicates as `∃ h : i < walk.length, walk.get ⟨i, h⟩ = v`
         (existential bound; requires minor adjustment to bijection arguments).
   Both refactors touch ~30-50 sites.

2. After build repair: revisit Session 6's `euler_path_implies_degree_balance`
   (already written, just blocked).

3. Then `remove_circuit_balanced` as next session's target.

## Attempt Count
- Total attempts: 6
- Current approach attempts: 6 (Sessions 2–6)
- Approaches tried: 1 (decompose Hierholzer into independent lemmas; greedy
  `maxTrail` for circuit existence; closed-walk and open-walk balance helpers;
  walk-position bijections)

## Blockers
- **Build does not pass under latest Mathlib** (~80 errors in pre-existing code;
  PR #16675 was auto-merged without verification). Errors:
  - `simp` made no progress on `Finset.sum_ite_eq'` (Mathlib API drift)
  - many `omega could not prove the goal` failures on
    `walk.get ⟨i, by omega⟩` patterns inside `Finset.filter` lambdas
  Repair requires substantial refactor (~30-50 call sites).
- After build repair: `remove_circuit_balanced` requires bridging walk-position
  counts to edge-set counts; may need adding `edges_distinct` to
  `DirectedCircuit`.
- After both sorries close: Hierholzer circuit splicing (~300+ lines) remains
  for both axioms' sufficiency directions.

## Next Action
1. **(NEW) Build repair** of `walk.get ⟨i, by omega⟩` patterns throughout the
   file. Could be done in a single mechanical session using one of the two
   refactor strategies described above.
2. **(deferred) `remove_circuit_balanced`** — unchanged plan: define
   `circuitVisits`, apply `closed_walk_balance`, bridge to
   `(walkEdges C.walk).toFinset` cardinality.

## Session 6 Summary (2026-05-08)
**Mode**: REVISIT
**Outcome**: research progress + build-blocker discovery. Wrote a proof of
`euler_path_implies_degree_balance` but the file does NOT compile (pre-existing
Mathlib API drift; reported below).

### What I Did
- Strengthened `HasEulerianPath G s t` with `∃!` unique coverage and an
  `hsteps : ∀ i < walk.length-1, (walk[i], walk[i+1]) ∈ G.edges` field.
- Added `open_walk_interior_balanced` private lemma: for an open walk where
  neither endpoint equals an interior vertex `v`, the source-count of `v`
  equals its target-count via the bijection `i ↦ i - 1`.
- Wrote proof of `euler_path_implies_degree_balance` by combining
  `walk_source_eq_outDegree` + `walk_target_eq_inDegree` (degree ↔ position
  bijection) with `open_walk_first_source_excess`,
  `open_walk_last_target_excess`, and the new `open_walk_interior_balanced`.
- Ran Docker build of `Proofs.KonigsbergOQ01OQ02`. Build failed with ~80
  errors, the great majority in pre-existing code (L87 to ~L500), with a
  few additional matching errors in my new code (L522+). All errors trace
  to two patterns:
    1. `simp` rewrites against `Finset.sum_ite_eq'` no longer fire (Mathlib
       changed the rewrite).
    2. `walk.get ⟨i, by omega⟩` inside `Finset.filter` lambdas: omega cannot
       prove `i < walk.length` for unbound `i`.

### What Remains
- **Build repair** (new top priority).
- **`remove_circuit_balanced`** — remaining sorry from Session 5.
- **Two axioms** still hold the iff at full strength; both `→` (necessity)
  directions are proved (`eulerian_circuit_implies_balanced` and
  `euler_path_implies_degree_balance`). The `←` (sufficiency) directions
  remain axiomatized pending Hierholzer circuit splicing.

### Files Modified
- `proofs/Proofs/KonigsbergOQ01OQ02.lean` (1108 → 1202 lines; build does NOT pass)
- `src/data/proofs/konigsberg-oq-01-oq-02/meta.json` (lineCount/theoremCount
  updated to objective values; sorries kept at 2 — unverified)
- `src/data/research/problems/konigsberg-oq-01-oq-02.json`
- `research/problems/konigsberg-oq-01-oq-02/knowledge.md`
- `research/problems/konigsberg-oq-01-oq-02/state.md` (this file)
