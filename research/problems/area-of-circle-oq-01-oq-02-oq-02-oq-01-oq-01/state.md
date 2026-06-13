# Research State: area-of-circle-oq-01-oq-02-oq-02-oq-01-oq-01

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-13
**Iteration**: 2

## Current Focus
Feasibility of discharging the `exists_nice_reparam` axiom via the inverse function theorem.
ORIENT survey complete — see knowledge.md (session 2026-06-13 s01).

## Active Approach
None viable as-stated. The IFT route is blocked by two specification gaps in the parent
proof (`proofs/Proofs/AreaOfCircleOQ01OQ02OQ02OQ01.lean`):
1. `SmoothClosedCurve` has no regularity field (`|γ'(t)| > 0`), which the IFT requires.
2. `exists_nice_reparam` does not tie `γ'` to `γ`; as written it already implies the
   isoperimetric inequality it is used to prove (circularity).

## Attempt Count
- Total attempts: 0 (survey only — no Lean ACT; build harness down)
- Current approach attempts: 0
- Approaches tried: 1 (direct IFT — rejected as infeasible for the structure as defined)

## Blockers
- Structural: parent `SmoothClosedCurve` needs a regularity field and `exists_nice_reparam`
  needs restating as a genuine reparametrization before the IFT route can work.
- Infrastructure: Docker build harness down + Aristotle backend 404 (2026-06-13), so any
  ~400-800 line arc-length construction is unverifiable this session.

## Next Action
Propose the two parent-proof amendments (regularity field + reparametrization restatement),
then attempt the IFT-based arc-length construction once the build harness returns.
