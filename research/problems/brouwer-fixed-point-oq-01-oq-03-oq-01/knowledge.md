# Knowledge Base: brouwer-fixed-point-oq-01-oq-03-oq-01

De-Axiomatizing the Ham Sandwich Theorem: topological core from Borsuk–Ulam.

---

## Problem Understanding

The parent entry `brouwer-fixed-point-oq-01-oq-03` derived n-dimensional
Borsuk–Ulam and stated the **Ham Sandwich Theorem** as an axiom
(`ham_sandwich_theorem` in `BrouwerFixedPointOQ01OQ03.lean`), noting the
obstruction is *continuity of the bisecting-measure function*. This sub-question
separates the **topological core** (provable from Borsuk–Ulam) from the **genuine
analytic input** (Lebesgue continuity).

---

## Current State (as of 2026-06-15)

`proofs/Proofs/BrouwerFixedPointOQ01OQ03OQ01.lean` is **complete**: 0 sorries,
0 axiom declarations, registered in `Proofs.lean`. It rests only on
`BorsukUlam.lean`'s single legitimate topological axiom
`no_continuous_odd_nonzero_on_sphere` (→ `borsuk_ulam_antipodal_collapse`).

What is already **proved** (not assumed):
- `ham_sandwich_reduction` — topological core: continuous odd `F : Sⁿ → ℝⁿ` +
  "`F x = 0 ⇒ bisected`" ⇒ a bisecting point (direct from Borsuk–Ulam).
- `discrepancy_odd_of_swap` — discrepancy map is odd from the antipodal swap.
- `ham_sandwich_of_discrepancy` — capstone, given the discrepancy as a continuous
  `SphereFun`.
- `ham_sandwich_of_scalar_continuity` — discharges the vector-assembly step:
  needs only the `2n` **scalar** slice-volume maps continuous.
- `stdPos_neg` / `stdNeg_neg` — antipodal swap is a *theorem* for any **linear**
  direction/threshold extraction (not an assumption).
- `volume_inter_ne_top` — finiteness of slice volumes from finite body volume.
- `ham_sandwich_standard` / `ham_sandwich_standard_of_scalar_continuity` —
  sharpest packaging: under the standard linear half-space assignment the only
  remaining hypotheses are `hbody` (finite body volume) + scalar slice-volume
  continuity.
- `volume_body_eq_slices_add_boundary`, `each_slice_exactly_half` — upgrade
  "equal volumes" to "exactly half" given the boundary slice is null (`hnull`).

---

## The Residual Frontier (the genuine remaining inputs)

Both are stated as **hypotheses**, not sorries; they are the honest analytic
content the file isolates. Neither is verifiable under the current dual backend
blackout (Aristotle `prove` → 404; Docker `ps` hangs / pool unsafe).

### Gap 1 (headline) — scalar slice-volume continuity

  `Continuous fun x => (volume (bodies i ∩ {y | ⟪u x, y⟫ < t x})).toReal`  on `Sⁿ`.

This is the lone deep input. Route: write the slice volume as
`∫ y, (body i).indicator 1 · (halfspace x).indicator 1` and apply **dominated
convergence for continuity** (`MeasureTheory.continuous_of_dominated` /
`continuousAt_of_dominated`), with the a.e.-continuity of the integrand in `x`
following from Gap 2 (the moving boundary hyperplane is null, so the indicator is
a.e. continuous in `x` off a null set). Dominating function: `(body i).indicator 1`
(integrable since `volume (body i) ≠ ⊤`). HARD-not-OPEN; the natural Aristotle
target once a backend returns, but large — submit in pieces.

### Gap 2 (tractable) — boundary hyperplane is null

  `volume {y : EuclideanSpace ℝ (Fin n) | ⟪u x, y⟫ = t x} = 0`  for `u x ≠ 0`.

This discharges the `hnull` hypothesis of `each_slice_exactly_half` for the
standard parameterization, and feeds the a.e.-continuity in Gap 1.

**Repo-confirmed Mathlib entry point** (the non-obvious part — found in
`CayleyHamiltonMinpolyOQ05OQ01OQ02.lean:223`):
`Measure.addHaar_submodule volume S hS : volume (S : Set _) = 0` for a proper
submodule `S ≠ ⊤` of `Fin n → ℝ`. Two adaptations needed, each a real (small)
obligation:
  1. **Affine, not linear.** The boundary `{y | ⟪u,y⟫ = t}` passes through the
     origin only when `t = 0`. For general `t` use the affine analogue
     `MeasureTheory.Measure.addHaar_affineSubspace` (proper affine subspace ⇒
     null), or translate by any point on the hyperplane and reduce to the linear
     kernel `{y | ⟪u,y⟫ = 0} = (LinearMap … u).ker`, proper iff `u ≠ 0`
     (`Submodule.ne_top_iff` / a witness with `⟪u, ·⟫ ≠ 0`).
  2. **`EuclideanSpace` vs `Fin n → ℝ`.** The Ham Sandwich space is
     `EuclideanSpace ℝ (Fin n)` (`PiLp 2`), not the plain `Fin n → ℝ` the repo
     lemma is stated on. They are measure-isomorphic but **not** the same type;
     transfer volume via `EuclideanSpace.volume_preserving_measurableEquiv`
     (or `PiLp` ↔ `Pi` measurable-equiv volume preservation) before applying
     `addHaar_submodule`. This type/measure-transfer is the easy-to-miss trap.

---

## Next Steps

1. When a backend returns: prove **Gap 2** first (isolated, small, repo pattern
   exists) as a companion lemma `volume_std_boundary_eq_zero`, then specialize
   `each_slice_exactly_half` to the standard parameterization with `hnull`
   discharged. Verify with `docker-build.sh Proofs.BrouwerFixedPointOQ01OQ03OQ01`.
2. Then attack **Gap 1** (dominated convergence), in pieces, as the headline
   de-axiomatization completion. Likely Aristotle `prove_file` on a companion.
3. Do **not** blind-write either under dual blackout — both touch `EuclideanSpace`
   measure API where name/type drift is silent and unverifiable.

---

## Dead Ends

(none recorded)
