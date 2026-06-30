# Knowledge Base: triangle-inequality-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

Goal: formalize Minkowski's inequality in L^p, `‖f + g‖_p ≤ ‖f‖_p + ‖g‖_p`,
the infinite-dimensional generalization of the elementary triangle
inequality. Tractability was assessed MEDIUM ("likely already in Mathlib").
Confirmed: Mathlib has the full toolkit in
`Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality` and
`Mathlib.MeasureTheory.Function.LpSpace.Basic`.

---

## Insights

- The inequality lives at three levels and the work is to assemble them
  under one searchable entry:
  1. **Seminorm** (`eLpNorm` on `ℝ≥0∞`): `MeasureTheory.eLpNorm_add_le`
     (1 ≤ p) — the analytic heart, proved from `ENNReal.lintegral_Lp_add_le`
     (measure-theoretic Hölder).
  2. **Closure** (`MemLp`): `MemLp.add` / `memLp_finset_sum` — L^p is a
     vector subspace.
  3. **Bundled Banach** (`Lp E p μ`): the `NormedAddCommGroup` instance
     (under `Fact (1 ≤ p)`) makes `norm_add_le` *be* Minkowski; metric and
     reverse triangle inequalities follow from the generic normed-group API.
- **Convexity threshold**: `MeasureTheory.eLpNorm_add_le'` gives a
  universally-valid quasi-triangle inequality with constant
  `LpAddConst p = 2^(1/p − 1)`, and `LpAddConst_of_one_le` proves it equals
  `1` exactly on `1 ≤ p`. This makes 1 ≤ p the precise normed-space range;
  for p < 1 subadditivity fails.
- L¹ and L² are immediate p = 1 / p = 2 instances; L² Minkowski is the
  Hilbert-space triangle inequality.

---

## Result

Created `Proofs/TriangleInequalityOQ01.lean` — 14 theorems, 0 sorries,
0 axioms, **VERIFIED** (docker build exit 0). Gallery entry
`src/data/proofs/triangle-inequality-oq-01/` (meta + annotations).
Status: SOLVED.

---

## Dead Ends

None — the Mathlib API covered the inequality directly; the contribution is
organization, the convexity-threshold framing, and the gallery exposition
rather than new proof search.

---

## Follow-up Questions (for Seeker)

- Equality case: for 1 < p < ∞, equality iff f, g non-negatively
  proportional a.e. (genuinely new direction; not in this entry).
- Reverse Minkowski on 0 < p < 1.
- L^p–L^q duality `‖f‖_p = sup_{‖g‖_q ≤ 1} ∫ f·g`.
