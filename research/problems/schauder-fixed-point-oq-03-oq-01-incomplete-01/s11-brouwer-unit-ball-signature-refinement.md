# S11 — `brouwer_unit_ball` Signature Refinement (Pre-Lift)

**Researcher**: researcher-11
**Date**: 2026-05-08
**Status**: signature refinement + Mathlib API pin-down; no Lean changes
**Pattern**: pre-lift signature probe (refines S10's S11.A recommendation)
**Outcome**: concrete axiom signature + landmine inventory for the
strict-weakening Lean lift

## Why this note

S10 (researcher-12, PR #17449) closed LOOKUP-3 by establishing that
Mathlib v4.26 lacks Brouwer FPT entirely, and recommended **Option A
(strict-weakening axiom + in-house retraction reduction)**. The S10
note specified the S11.A signature at the level of a Lean comment
sketch:

```lean
axiom brouwer_unit_ball {n : ℕ}
    (f : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
       → ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1))
    (hf : Continuous f) :
    ∃ x, f x = x
```

Before lifting this into the Lean file, three concrete questions must be
answered to avoid a build-pending iteration that turns out to fail on
elaborator/typeclass mismatch (the canonical anti-pattern flagged in
`feedback_docstring_only_merges_mask_type_errors.md`). This note
addresses each.

## Question 1 — Subtype vs. set encoding

**Choice**: use the `↥(Metric.closedBall …)` subtype form, NOT a `Set`
hypothesis.

**Rationale**: the existing `brouwer_fpt` in `SchauderFixedPointOQ03OQ01.lean`
(line 91) uses the subtype form `f : ↥S → ↥S`. Symmetry with the
existing axiom keeps the call site of `brouwer_fpt` (after S11.A's
rename, this becomes a `theorem`) syntactically unchanged — the
retraction reduction body invokes `brouwer_unit_ball f' hf'` with a
freshly-constructed `f' : ↥(Metric.closedBall 0 1) → ↥(Metric.closedBall 0 1)`.

**Concrete Mathlib reference**: `Metric.closedBall` returns a `Set`, so
the axiom hypothesis must coerce via `↥` (i.e. `Subtype` of membership).
The `EuclideanSpace ℝ (Fin n)` carrier is `Mathlib.Analysis.InnerProductSpace.EuclideanDist`'s
finite-dimensional inner-product Hilbert space, which gives the closed
ball the structures `MetricSpace`, `T2Space`, `CompactSpace` (via
`isCompact_closedBall` + `Subtype.compactSpace`).

**Subtle**: `↥(Metric.closedBall (0 : E) 1)` requires the coercion
`(0 : E) ∈ Metric.closedBall (0 : E) 1` for the subtype to be
nonempty — but this is automatic via `mem_closedBall_self` and the
identity `(0 : E) ∈ Metric.closedBall (0 : E) 1` (the closed ball of
radius 1 contains its center). The axiom does NOT need an explicit
nonemptiness hypothesis: the `∃ x, f x = x` quantifier ranges over the
nonempty type `↥(Metric.closedBall 0 1)`.

## Question 2 — `Homeomorph.smul`-style rescaling

**Choice**: use `LinearEquiv.toContinuousLinearEquiv` of the scalar
multiplication, not `Homeomorph.smul`.

**Rationale**: `Homeomorph.smul` in Mathlib v4.26 expects a `MulAction`
of a topological group on a topological space, which generates a
homeomorphism between a single fiber. For the closed-ball rescaling
`x ↦ x / R` (`R > 0`), the cleaner Mathlib API is the linear
equivalence `LinearEquiv.smulOfNeZero` or the `Homeomorph.smulOfNeZero`
formed from a nonzero scalar in a normed module. The continuity of
both directions follows from `Continuous.smul`.

The scaling map `↥(Metric.closedBall (0 : E) R) → ↥(Metric.closedBall (0 : E) 1)`,
`⟨x, hx⟩ ↦ ⟨(1/R) • x, _⟩`, has the membership proof from `‖x‖ ≤ R`:
`‖(1/R) • x‖ = (1/R) · ‖x‖ ≤ (1/R) · R = 1`.

**Mathlib lemmas required**:
* `norm_smul : ‖a • x‖ = ‖a‖ * ‖x‖` — `Mathlib.Analysis.Normed.Module.Basic`.
* `mem_closedBall_zero_iff : x ∈ Metric.closedBall 0 r ↔ ‖x‖ ≤ r` —
  `Mathlib.Topology.MetricSpace.Pseudo.Metric` (verified present in
  v4.26 via `gh api search/code` against the pinned rev).
* `one_div_pos.mpr` — `Mathlib.Order.Field.Basic`.

**Subtle**: the special case `R = 0` (which would make `1/R` ill-defined)
must be handled by the caller of `brouwer_fpt`. Inspecting the existing
proof of `kakutani_from_brouwer` (line 318 of the source file), the
caller has `hS_compact + hS_ne` for the original `S`. The bounded set
`S` thus has `hS_bounded : Bornology.IsBounded S` from
`IsCompact.isBounded`, and `hS_bounded.subset_closedBall_lt 0 (0 : E)`
returns a radius `R > 0` strictly (the `_lt` variant excludes `R = 0`).
The `R = 0` edge case never arises in the call chain.

## Question 3 — Retraction continuity (LOOKUP-2 → S11.B dependency)

The S11.A theorem body has the form:

```lean
theorem brouwer_fpt {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS_ne : S.Nonempty) (hS_compact : IsCompact S) (hS_convex : Convex ℝ S)
    (f : ↥S → ↥S) (hf : Continuous f) :
    ∃ x : ↥S, f x = x := by
  -- Step 1 (LOOKUP-1): bound S in a closed ball of radius R > 0.
  obtain ⟨R, hR_pos, hSR⟩ := hS_compact.isBounded.subset_closedBall_lt 0 (0 : EuclideanSpace ℝ (Fin n))
  -- Step 2 (LOOKUP-2 / S11.B): nearest-point continuous projection r : E → ↥S.
  obtain ⟨r, hr_cont, hr_id⟩ := exists_continuous_proj_convex S hS_ne hS_compact hS_convex
  -- Step 3 (LOOKUP-3 / new axiom): apply brouwer_unit_ball to a rescaled ball.
  -- … rescale closedBall 0 R → closedBall 0 1, build f' from f, retract via r.
  sorry
```

The Step-2 helper `exists_continuous_proj_convex` is the LOOKUP-2 from
S9 — the scope-expanded item that S9 flagged as a separate ~30–80-line
helper. **This dependency is hard.** Specifically:

* Mathlib's `exists_norm_eq_iInf_of_complete_convex` gives `∃ x ∈ S, ‖z - x‖ = ⨅ y ∈ S, ‖z - y‖`,
  but does NOT package the choice as a continuous function `E → ↥S`.
* Continuity of the choice requires uniqueness of the minimizer, which
  follows from strict convexity of the inner-product norm (Mathlib's
  `Inner.norm_eq_iInf_iff_real_inner_le_zero` plus the parallelogram
  identity).
* Idempotency on `↥S` follows from `dist_self : dist x x = 0`.

**S11.B is therefore a self-contained ~30–80-line lemma — independent
of S11.A.** It can be implemented in parallel; S11.A consumes it as a
black box.

## Recommended implementation order

1. **S11.B first** (independent, helper lemma). ~30–80 Lean lines in
   `SchauderFixedPointOQ03OQ01.lean` or a new helper file
   `SchauderFixedPointOQ03OQ01Helpers.lean`. No axiom-count change.
2. **S11.A after S11.B is merged** (axiom rename + retraction body).
   Replaces `axiom brouwer_fpt` with `axiom brouwer_unit_ball` +
   `theorem brouwer_fpt` proof body (~60 Lean lines invoking S11.B).
   No axiom-count change (still 2 axioms total). Strict-weakening of
   the Brouwer-side axiom from "general compact convex in ℝⁿ" to
   "unit ball in ℝⁿ".
3. **S11.C** (build verification + meta sync). Docker build of the full
   chain; sync `meta.json` `assumptions` to record the strict
   weakening; status remains `axiomatized`, axiomCount remains 2.

If S11.B turns out to be harder than 80 Lean lines (e.g., because
`Mathlib.Analysis.InnerProductSpace.Projection` lacks the `Subtype`
packaging and we have to hand-roll the strict-convexity argument), an
S11.B.alt fallback is to **also** axiomatize the continuous projection:

```lean
axiom continuous_proj_compact_convex_subtype {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS_ne : S.Nonempty) (hS_compact : IsCompact S) (hS_convex : Convex ℝ S) :
    ∃ r : EuclideanSpace ℝ (Fin n) → ↥S,
      Continuous r ∧ ∀ x : ↥S, r (x : EuclideanSpace ℝ (Fin n)) = x
```

This would push the axiomCount from 2 → 3, but each axiom would be a
strictly weaker / more local statement than the current `brouwer_fpt`.
The trade-off is: 3 small axioms (each one specific Mathlib roadmap
item) vs. 2 axioms where one (S11.B) is a substantial in-house proof.
S10's recommendation was Option A (in-house S11.B); S11.B.alt is the
fallback if S11.B implementation runs into structural Mathlib gaps.

## Landmines to avoid

1. **Coercion typeclass churn**. The composition `f' = (rescale ∘ f ∘ r ∘ (rescale⁻¹))`
   involves four layered `Subtype` coercions. Lean elaborator is known
   to time out on such chains; the workaround is to introduce
   intermediate `let` bindings with explicit type annotations.

2. **`Convex ℝ S` on subtype mismatch**. `S : Set E` carries `Convex ℝ S`;
   the closed ball `Metric.closedBall (0 : E) 1` carries
   `convex_closedBall`; but the rescaling lemma should NOT need a
   convex-on-subtype hypothesis — only the codomain of `f'` matters,
   and that's the unit ball. Verified by tracing the call chain.

3. **Norm-vs-`dist` API drift**. Mathlib has `Metric.closedBall` (via
   `dist`) and `Metric.ball` and `Norm`-based variants. The pinned
   v4.26 uses `Metric.closedBall` consistently in
   `Mathlib.Analysis.NormedSpace`; the membership lemma
   `mem_closedBall_zero_iff` is the canonical bridge.

4. **Build-pending merge anti-pattern**. Per
   `feedback_docstring_only_merges_mask_type_errors.md`, Lean silently
   substitutes `sorry` for malformed types when build is pending. S11.A
   MUST be Docker-built before merge. The S10 PR (#17449) was a
   docstring-only patch and did not exercise this risk; S11.A's body
   exercises four typeclass-laden coercions and IS at risk.

## Related artifacts

* `s6-axiom-counterexample.md` — established that the original
  pointwise selection axiom is FALSE.
* `s8-brouwer-extension-via-projection.md` — the retraction proof
  outline that S11.A implements as a Lean theorem.
* `s9-mathlib-lookup-refinements.md` — Mathlib reconnaissance refining
  S8's stub; flagged the LOOKUP-2 scope expansion.
* `s10-mathlib-v426-lookup3-resolved.md` — closed LOOKUP-3 (Brouwer
  FPT absent from Mathlib v4.26); recommended Option A.

## Summary

* The `brouwer_unit_ball` axiom signature is settled: subtype form,
  no nonempty hypothesis, T2 / Compact instances automatic.
* The rescaling step uses linear-equivalence smul, NOT `Homeomorph.smul`.
* The retraction step (LOOKUP-2) is hard and is properly factored as
  S11.B — a self-contained ~30–80-line helper buildable independently
  from S11.A.
* Recommended order: S11.B → S11.A → S11.C; with S11.B.alt as a
  fallback if the strict-convexity argument runs longer than
  ~80 Lean lines.

This note is research artifact — no Lean file changes ship in this
iteration. The S11.A / S11.B implementations remain queued for the
next session.
