# Knowledge Base: law-of-cosines-oq-01-oq-05

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

## Session 2026-04-21 - PROOF COMPLETED

**Mode**: REVISIT (continuing euclidean_limit_holds sorry)
**Outcome**: completed

### What I Did
- Eliminated the sole remaining `sorry` in `euclidean_limit_holds`
- K<0 case: replaced `abs_add` (not available after `set u := Real.sqrt (-K)`) with manual `abs_le.mpr` decomposition using `le_abs_self` + `abs_neg`; used `one_le_cosh` private lemma (via `Real.cosh_sq_sub_sinh_sq` + `Real.cosh_pos`)
- K>0 case: used `Real.one_sub_sq_div_two_le_cos` (implicit argument, no `_` needed), `Real.abs_sin_le_abs` (same), rewrote product bounds via `mul_le_mul_of_nonneg_left`
- M_neg definition corrected to `(Real.exp (a^2/2) + 1)*(b^2/2*exp(b^2/2))` factor
- Replaced `nlinarith` assembly steps with explicit `ring`-equation + `linarith` for budget efficiency
- Introduced `hcab` intermediate lemma to reduce final `linarith` hint count
- Increased `maxHeartbeats` from 800000 to 4000000 to accommodate the complex `isDefEq` check in the K>0 `calc` block

### Key Findings
- `abs_add` is not usable as a hint in `linarith` or as a term after `set u := ...` — use `abs_le.mpr` with `le_abs_self` and `abs_neg` instead
- `Real.one_sub_sq_div_two_le_cos` and `Real.abs_sin_le_abs` take no explicit arguments (implicit x)
- `Real.cosh_nonneg` doesn't exist; use `(Real.cosh_pos x).le`
- Lean 4's `rw` closes `X ≤ X` goals automatically; adding `exact le_refl _` causes "No goals" error
- Heartbeat budget is consumed cumulatively; `isDefEq` checks in large `calc` blocks can exhaust 800000 budget

### Files Modified
- `proofs/Proofs/LawOfCosinesOQ05.lean` (0 sorries, 1 axiom: `heuclidean` hypothesis)
- `src/data/research/problems/law-of-cosines-oq-01-oq-05.json` (status → completed)

### Next Steps
- None: proof is complete
- Potential follow-up: generalize to Riemannian manifolds or non-constant curvature
