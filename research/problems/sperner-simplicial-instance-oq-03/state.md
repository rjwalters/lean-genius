# Research State: sperner-simplicial-instance-oq-03

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-14T21:26:07-07:00
**Iteration**: 2

## Current Focus
Reframed the open piece. `boundary_doors_odd` is ALREADY a proven parity-transfer
theorem in `SpernerSimplicialInstance.lean` (line 173): it derives `S = S_n` (all
boundary doors on the top facet) from the Sperner condition, then concludes oddness
FROM the hypothesis `_hLastFace`. The genuine remaining gap is `_hLastFace` (top-facet
door oddness) + the base case, to be discharged by induction on dimension. `_hLowerDim`
is vestigial (unused in the proof body).

## Active Approach
Dimension induction discharging `_hLastFace` for the standard/Kuhn triangulation:
top facet of `Δⁿ` is a `Δⁿ⁻¹` with the induced Sperner coloring; its door count is
odd by IH; base case n=1 = one door. Bridge verified numerically (`verify_boundary_doors.py`)
over 14k+ Sperner colorings (n=1, n=2 Kuhn grids m≤4).

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
- Docker down this session — no Lean build, so the ACT construction is deferred.
- Lean work needs a general standard/Kuhn `Triangulation` instance (file currently
  has only `intervalTriangulation 1` and a single 2-simplex fixture).

## Next Action
ACT (build-gated): construct the standard/Kuhn `Triangulation` instance for general n;
define the facet-restriction map to a dim-(n-1) triangulation and prove the restricted
coloring is Sperner; prove the door bijection; close `_hLastFace` by induction.
~200–400 LOC, medium difficulty. Consider Aristotle for the door-bijection lemma once
the triangulation instance compiles.
