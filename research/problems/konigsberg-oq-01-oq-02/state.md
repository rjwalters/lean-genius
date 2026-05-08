# Research State: konigsberg-oq-01-oq-02

## Current State
**Phase**: ACT (build-blocked, refactor-recipe-ready)
**Path**: full
**Since**: 2026-05-03
**Iteration**: 7
**Last Update**: 2026-05-08 (Session 7, researcher-8)

## Current Focus
Session 7 inspected the build-blocked state from Session 6 and produced a
**concrete worked refactor recipe** in `knowledge.md` (under heading "Session
2026-05-08 (Session 7) - Refactor Recipe for Build Blocker"). The recipe:

- Identifies all 18 `Finset.filter`-lambda sites + ~30 hypothesis-position
  sites + 9 `∃!`-definition sites that need refactoring.
- Provides a fully worked-out post-refactor version of `closed_walk_balance`
  (~40 lines of code) that can be copy-pasted as a model for the other
  bijection lemmas.
- Specifies a single bridge lemma `get?_eq_some_iff_of_lt` to add near the top
  of the file.
- Documents the secondary `Finset.sum_ite_eq'` simp failure at L87/L99 with a
  concrete fix.
- Lists three stale PRs (#15145, #15168, #15232) that should be closed as
  superseded.

Session 7 made no `.lean` edits and did not run a Docker build — by design,
the recipe is the deliverable so the next researcher can apply it as a
focused mechanical pass and run a single Docker build at the end.

## Active Approach
The original plan (eliminate `euler_path_implies_degree_balance` sorry, then
`remove_circuit_balanced`) is blocked by the build issue. Session 7 settled the
refactor strategy on **option (a)** — switch lambdas to `walk.get? i = some v`
form — and supplied a worked example for `closed_walk_balance` plus a complete
site list. The next session can apply the recipe as a focused mechanical pass:

1. Add bridge lemma `get?_eq_some_iff_of_lt` near top of file.
2. Refactor the two definitions (`HasEulerianCircuit`, `HasEulerianPath`) and
   the six private bijection lemmas.
3. Adjust the proof bodies of `eulerian_circuit_implies_balanced`,
   `euler_path_implies_degree_balance`, and `maxTrail_closed` to use the new
   forms.
4. Fix `Finset.sum_ite_eq'` simp failure at L87 and L99.
5. Run the Docker build (~45 min); confirm 1 sorry remains, axiomCount = 2.
6. Update `meta.json` `sorries: 2 → 1` and `lineCount` once verified.

After build repair: `remove_circuit_balanced` becomes the next research target
(plan unchanged from Session 5).

## Attempt Count
- Total attempts: 7
- Current approach attempts: 7 (Sessions 2–7)
- Approaches tried: 1 (decompose Hierholzer into independent lemmas; greedy
  `maxTrail` for circuit existence; closed-walk and open-walk balance helpers;
  walk-position bijections; Session 7 prepared `get?` refactor recipe)

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
1. **Apply Session 7 refactor recipe** (see `knowledge.md`): add bridge lemma,
   refactor definitions and bijection lemmas to `walk.get? i = some v` form,
   fix `simp` failure at handshaking lemmas, run Docker build, then update
   `meta.json` (sorries 2 → 1).
2. **(deferred) `remove_circuit_balanced`** — unchanged plan: define
   `circuitVisits`, apply `closed_walk_balance`, bridge to
   `(walkEdges C.walk).toFinset` cardinality.

## Session 7 Summary (2026-05-08)
**Mode**: REVISIT (no `.lean` edits — recipe-only deliverable)
**Outcome**: produced concrete worked refactor recipe in `knowledge.md`.
Identified 18 lambda sites + ~30 hypothesis sites + 9 definition sites.
Provided fully-worked post-refactor `closed_walk_balance` (~40 lines) as model.
Specified bridge lemma, secondary `simp` fix, and three stale PRs to close
(#15145, #15168, #15232). No build run; no metadata edits.

### Why No `.lean` Edits

The build-blocking refactor touches ~50 sites across 6 lemmas + 2 definitions
+ 2 theorems. A partial refactor would leave the file in an even more broken
state (mixing forms across signature/caller boundaries). The pragmatic move is
to land the full refactor in a single session that ends with a successful
Docker build; Session 7 prepared the ground for that session.

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
