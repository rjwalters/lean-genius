# Knowledge Base: synthesis-curvature-ptolemy-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

(Initial observations from OBSERVE phase will be recorded here.)

---

## Insights

(Insights from research attempts will be accumulated here.)

---

## Mathlib Coverage Audit

(After ORIENT phase: list of relevant Mathlib lemmas / APIs — Poincaré-disk metric, hyperbolic distance, `Real.sinh` identities — and their applicability.)

---

## Anti-Goals

(Things explicitly NOT to attempt — discovered duplicates, scope creep risks, re-deriving parent `curvatureSin` machinery, etc.)

---

## Session 2026-07-03 (Session 1, researcher-11) — SOLVED

**Mode**: FRESH
**Outcome**: completed (verified, 0 sorries, 0 axioms)

### What I Did
- Recognized the parent's "needs ~800–1200 lines of Poincaré metric infrastructure"
  estimate is unnecessary for the Ptolemy relation itself.
- Key insight (conformal-factor cancellation): with the conformal chord
  s(z,w) = ‖z-w‖/√((1-‖z‖²)(1-‖w‖²)) = sinh(d_H/2), every product s(zᵢ,zⱼ)·s(zₖ,zₗ)
  in the Ptolemy relation carries the SAME denominator √∏(1-‖zᵢ‖²) because
  {i,j,k,l}={1,2,3,4}. Clearing it reduces hyperbolic Ptolemy DIRECTLY to the
  Euclidean ptolemy_inequality / ptolemy_equality_of_proportional.
- Took the disk metric in closed form d_H = 2·arsinh(s); bridge sinh(d_H/2)=s is
  one line (Real.sinh_arsinh), so final theorems are in the exact sinh(d_H/2) =
  curvatureSin(-1)(d_H/2) form of the conjecture.
- Wrote proofs/Proofs/SynthesisCurvaturePtolemyOQ02.lean (300 lines, 8 thms, 2 defs).
  Builds clean under Lean 4.26.0 / Mathlib. #print axioms = only propext/
  Classical.choice/Quot.sound (no sorryAx, no ofReduceBool).
- Added gallery entry src/data/proofs/synthesis-curvature-ptolemy-oq-02/.

### Key Findings
- The hyperbolic case of a curvature-parametrized theorem can be a *change of
  variables* over the Euclidean case, not new infrastructure — when the model's
  conformal factor cancels across the identity.
- Decoupled the file from the parent SynthesisCurvaturePtolemy import because that
  chain (PtolemysTheoremOQ01OQ02.lean) is currently BROKEN by a Mathlib bump:
  it uses ⟪a,b⟫_ℝ without `open scoped RealInnerProductSpace` → "expected token".
  My file imports only the clean Proofs.PtolemysComplexProof + Mathlib.

### Files Modified
- proofs/Proofs/SynthesisCurvaturePtolemyOQ02.lean (new)
- src/data/proofs/synthesis-curvature-ptolemy-oq-02/{meta,annotations}.json (new)

### Next Steps / Follow-ups
- (build repair, NOT this PR) PtolemysTheoremOQ01OQ02.lean and
  SynthesisCurvaturePtolemy.lean need `open scoped RealInnerProductSpace` — mechanic.
- Build the genuine Poincaré-disk MetricSpace and prove poincareDist is its metric.
- Single curvature-parametrized Ptolemy equality curvatureSin K (d_K/2) for all K.
