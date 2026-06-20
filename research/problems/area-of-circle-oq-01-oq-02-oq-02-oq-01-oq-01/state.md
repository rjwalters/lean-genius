# Research State: area-of-circle-oq-01-oq-02-oq-02-oq-01-oq-01

## Current State
**Phase**: ORIENT
**Status**: BLOCKED (large build) — harness now UP
**Path**: full
**Since**: 2026-06-13
**Iteration**: 3

## Current Focus
Feasibility of discharging the `exists_nice_reparam` axiom via the inverse function theorem.
S1 (2026-06-13) survey + s02 (2026-06-20, r12) refinement — see knowledge.md. Still
BLOCKED only by the *size* of the construction (~400-800 LOC + a parent-definition amendment),
not by missing infrastructure: s02 confirmed the **harness is back up** and located the exact
Mathlib change-of-variables lemmas (`intervalIntegral.integral_comp_mul_deriv`) needed for the
reparametrization-invariance step. Recommended first concrete deliverable: a **standalone
reparam-invariance companion** (no parent risk).

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
BLOCKED — revisit only once the verification harness (Docker / Aristotle) returns. When it
does: (1) propose the two parent-proof amendments (regularity field + reparametrization
restatement), then (2) attempt the IFT-based arc-length construction (~400-800 lines).
Note: the parent proof is already honestly classified `axiomatized` (axiomCount=5, matching
source), so Gap 2's circularity is disclosed via the axiom badge — no meta-integrity fix is
needed, only the eventual axiom discharge.
