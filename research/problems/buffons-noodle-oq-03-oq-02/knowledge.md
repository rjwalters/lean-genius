# buffons-noodle-oq-03-oq-02 — Knowledge

**Status: COMPLETED & VERIFIED (0 sorries, 0 axioms).**

## Problem

Generalize the codimension of Buffon's Noodle: for a length-`L` curve and a family
of parallel `k`-dimensional affine subspaces (`k`-flats) of codimension `c = n - k`
in `ℝⁿ`, what is the expected number of intersections? The parent `buffons-noodle-oq-03`
solves the hyperplane case `c = 1` (`E = αₙ·L/d`); sibling `oq-01` evaluates the
crossing factor `αₙ` and explicitly lists "extend to codimension-k" as open.

## Result (the codimension dichotomy)

**For codimension `c ≥ 2`, a rectifiable (Lipschitz) curve almost surely misses every
flat: the expected number of intersections is 0.**

Mechanism (dimension counting): a flat with orthogonal offset `w ∈ ℝᶜ` meets the curve
`Γ` iff `w` lies in the image of the projected curve `P∘Γ : [0,L] → ℝᶜ`. That projected
curve is Lipschitz, so its image has Hausdorff dimension `≤ dimH(ℝ) = 1 < c`, and a set
of dimension below the ambient dimension is Lebesgue-null (`μH[c] = volume`). Hence the
set of hit offsets is null and the crossing count is `0` almost surely.

This is the honest complete answer: codimension 1 (hyperplanes) is the *unique*
nondegenerate parallel-flat Buffon regime for a 1-dimensional needle. The nondegenerate
higher-codimension law of integral geometry (Cauchy–Crofton / Santaló) requires the
*moving* object to have dimension at least the codimension — a different theorem.

## Session 2026-07-01 (Session 1, researcher-6) — FRESH → COMPLETED

**Mode**: FRESH
**Outcome**: completed (new verified gallery entry)

### What I Did
- Selected from the available pool after triaging RICH/MODERATE problems (all blocked or
  live-twinned: CLT-oq0204 blocked on unmerged PR #32388, erdos-263 blocked, erdos-101
  live-twin, ballot blocked-infra).
- Identified the correct math: 1-dim curve × codimension-`c` flats is degenerate for `c ≥ 2`.
- Verified Mathlib support: `LipschitzWith.dimH_image_le`, `Real.dimH_univ`,
  `measure_zero_of_dimH_lt`, `hausdorffMeasure_pi_real`.
- Wrote `proofs/Proofs/BuffonsNoodleOQ03OQ02.lean` (136 lines, 4 theorems).
- Typechecked against Mathlib v4.26 (`lake env lean`, 0 errors), `#print axioms` = only
  `propext, Classical.choice, Quot.sound` (0-axiom VERIFIED).
- Created gallery entry (`meta.json` + `annotations.json`) and research problem JSON.

### Key Findings
- The whole geometric question collapses to: does a Lipschitz curve's image in `ℝᶜ`
  have positive Lebesgue measure? For `c ≥ 2` the answer is no (Hausdorff dim ≤ 1 < c).
- `hausdorffMeasure_pi_real` (`μH[c] = volume` on `Fin c → ℝ`) is the bridge from the
  abstract dimension gap to concrete Lebesgue-nullity.
- Cast bookkeeping ℕ → ℝ≥0 → ℝ≥0∞ / ℝ is the only fiddly part; `exact_mod_cast` and
  `NNReal.coe_natCast` handle it.

### Files Modified
- `proofs/Proofs/BuffonsNoodleOQ03OQ02.lean` (new)
- `src/data/proofs/buffons-noodle-oq-03-oq-02/{meta,annotations}.json` (new)
- `src/data/research/problems/buffons-noodle-oq-03-oq-02.json` (new)
- `research/problems/buffons-noodle-oq-03-oq-02/knowledge.md` (this file)

### Next Steps (follow-up, not blocking)
- Prove the nondegenerate `d ≥ codimension` law (Cauchy–Crofton / Santaló).
- Upgrade `crossing_ae_zero` to an explicit Bochner-integral `E = 0` over a uniform
  offset window.
