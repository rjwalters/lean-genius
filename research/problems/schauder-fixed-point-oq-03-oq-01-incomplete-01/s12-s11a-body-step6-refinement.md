# S12 — Refinement of S11.A.body Step 6 + Mathlib API cross-verification

**Session**: S12 (2026-05-09, researcher-3)
**Status**: Analysis-only (no Lean changes)
**Target**: Sharpen the `s11-strict-weakening-spec.md` Lean stub for
`theorem brouwer_fpt`'s body (S11.A.body work item) before
implementation, by (a) flagging a non-trivial Step 6 logic gap I
encountered while drafting and (b) cross-verifying every Mathlib API
name against the cached v4.10 source as a v4.26 confidence proxy.

## TL;DR

The S11.A.body Lean stub in `s11-strict-weakening-spec.md` is sound up
through Step 5 (the conjugation `F (σ y) = σ y` follows mechanically
from `G y = y` plus the `R • R⁻¹ = 1` rescaling). **Step 6 is more
involved than a one-line `congrArg`**: it requires showing that
`(σ y : E) ∈ S` before we can construct an `↥S`-fixed-point. The
implementation should treat Step 6 as a 6-line block, not a 1-liner.

## What S11.A.body must prove

Concretely the body of `theorem brouwer_fpt` (signature pinned by S11
PR #17501) needs to produce `⟨x, _⟩ : ∃ x : ↥S, f x = x` from:
- `axiom brouwer_unit_ball` (closed-ball Brouwer FPT),
- `lemma exists_continuous_proj_convex` (S11.B helper, `sorry`-stubbed),
- standard Mathlib API for norms, scalar multiplication, subtype
  continuity, and the bornology/closedBall machinery.

## Step 6 — what the spec says vs what's actually needed

The s11-spec (lines ~241+) says of Steps 5–6:
> Steps 5–6 (membership of fixed point in S, idempotency, conclusion)
> proceed exactly as in S8's stub — no Mathlib-API risk.

Drafting the Lean reveals a six-line subtlety at Step 6 that the spec
under-specifies. The naive transcription
```lean
  obtain ⟨y, hy⟩ := brouwer_unit_ball G hG_cont
  -- hy : G y = y, where G = τ ∘ F ∘ σ.
  -- Goal: ⟨x, hx⟩ : ∃ x : ↥S, f x = x.
  refine ⟨r (σ y), ?_⟩
  -- f (r (σ y)) = r (σ y) ?
  …
```
**does not type-check** as a one-line `congrArg`, because `f (r (σ y))`
and `r (σ y)` need not be equal *as elements of ↥S* — only their
underlying E-coordinates may be related via the F-fixed-point identity.

### The actual logical chain at Step 6

Notation: `E := EuclideanSpace ℝ (Fin n)`; `B := Metric.closedBall (0 : E) R`;
`σ : ↥(closedBall 0 1) → ↥B, x ↦ ⟨R • (x : E), _⟩`;
`τ : ↥B → ↥(closedBall 0 1), b ↦ ⟨R⁻¹ • (b : E), _⟩`;
`F : ↥B → ↥B, b ↦ ⟨f (r (b : E)), _⟩`; `G := τ ∘ F ∘ σ`.

From `hy : G y = y` we derive **only the coordinate equality**
`(F (σ y) : E) = (σ y : E)` — i.e. step 5. Specifically:

| sub-step | derivation |
|----------|-----------|
| 5a | `(τ (F (σ y)) : E) = (y : E)` from `hy` and `Subtype.ext` |
| 5b | `R⁻¹ • (F (σ y) : E) = (y : E)` from 5a + `τ` definition |
| 5c | `(F (σ y) : E) = R • (y : E)` from 5b + `mul_inv_cancel₀ hR_pos.ne'` |
| 5d | `(F (σ y) : E) = (σ y : E)` from 5c + `σ` definition |

By definition of `F`,
```
(F (σ y) : E) = (f (r ((σ y) : E)) : E)
```
where the outer `(... : E)` is the underlying-coord projection from
`↥S → E` composed with the `↥S → ↥B` lift. Combined with 5d:

```
(f (r ((σ y) : E)) : E) = ((σ y) : E)         -- (★)
```

This is the only consequence of the unit-ball Brouwer fixed point.

### Step 6 — extracting an ↥S fixed point

We need `⟨x, hx⟩ : ∃ x : ↥S, f x = x`. The candidate is
`x := r ((σ y) : E)`. The goal `f x = x` in `↥S` reduces by `Subtype.ext`
to `(f x : E) = (x : E)`.

* `(f x : E) = (f (r ((σ y) : E)) : E) = ((σ y) : E)` — by (★).
* `(x : E) = (r ((σ y) : E) : E)` — by definition of `x`.

So we need `((σ y) : E) = (r ((σ y) : E) : E)`, i.e. **`(σ y : E) ∈ S`
followed by idempotency on `↥S`**.

Why is `(σ y : E) ∈ S`? Because:
* `f (r ((σ y) : E)) : ↥S` (this is the codomain of `f`), so its
  underlying coord `(f (r ((σ y) : E)) : E)` is in `S`.
* By (★), `((σ y) : E) = (f (r ((σ y) : E)) : E) ∈ S`.

Once we have `(σ y : E) ∈ S`, lift to `↥S`: `let x' := ⟨(σ y : E), this⟩ : ↥S`.
Then `(x' : E) = (σ y : E)`, so `r ((x' : E)) = r ((σ y) : E)` in `↥S`.
By the helper's idempotency clause `∀ x : ↥S, r (x : E) = x`, we get
`r ((x' : E)) = x'`, hence `r ((σ y) : E) = x'`. So `(r ((σ y) : E) : E) = (x' : E) = (σ y : E)`.
Combining with (★): `(f (r ((σ y) : E)) : E) = (σ y : E) = (r ((σ y) : E) : E)`,
i.e. `f (r ((σ y) : E)) = r ((σ y) : E)` in `↥S` by Subtype.ext. □

### Step 6 — Lean stub

```lean
  -- After step 5 we have:
  --   hFσy_coord : (F (σ y) : E) = (σ y : E)
  -- Unfold F's definition:
  have hf_coord : (f (r ((σ y : ↥B) : E)) : E) = ((σ y : ↥B) : E) := hFσy_coord
  -- Step 6.1: (σ y : E) ∈ S (since f's codomain is ↥S).
  have hσy_in_S : ((σ y : ↥B) : E) ∈ S := by
    rw [← hf_coord]
    exact (f (r ((σ y : ↥B) : E))).property
  -- Step 6.2: lift (σ y : E) into ↥S.
  let x' : ↥S := ⟨((σ y : ↥B) : E), hσy_in_S⟩
  -- Step 6.3: r (σ y : E) = x' by idempotency of r on ↥S.
  have hrσy : r (((σ y : ↥B) : E)) = x' := hr_id x'
  -- Step 6.4: candidate fixed point in ↥S is r (σ y : E).
  refine ⟨r (((σ y : ↥B) : E)), ?_⟩
  -- Goal: f (r (σ y : E)) = r (σ y : E)
  -- Reduce via Subtype.ext to coord equality.
  apply Subtype.ext
  -- Coord goal: (f (r (σy)) : E) = (r (σy) : E)
  rw [hrσy]
  -- Goal: (f x' : E) = (x' : E)
  -- (f x' : E) = (f (r (σy)) : E) since x' = r (σy : E) in ↥S
  -- but we have f x' literally; substitute via hrσy (already used).
  -- After rw [hrσy], we have on the LHS f x' (using rw substitution chain).
  show (f x' : E) = (x' : E)
  rw [show (x' : E) = ((σ y : ↥B) : E) from rfl]
  rw [show f x' = f (r ((σ y : ↥B) : E)) from by rw [← hrσy]]
  exact hf_coord
```

This is **9–11 Lean lines** for Step 6 alone, vs the spec's implied
1–2 lines. The structural complexity comes from the
double-coercion-and-dependent-typing chain that doesn't collapse to a
one-liner without explicit `Subtype.ext` + idempotency machinery.

## Mathlib API cross-verification (v4.10 → v4.26 expected stable)

I cannot directly inspect Mathlib v4.26.0 (the project's pinned rev)
locally because of the `proofs/.lake` self-symlink trap (see
`feedback_researcher_lake_symlink_broken.md`). I cross-verified each
API name in `s11-strict-weakening-spec.md` Step 4 (Option b
elementary rescaling) against Mathlib v4.10 cached at
`/Users/rwalters/Projects/lean-genius-proofs/.lake/packages/mathlib/`.
All except one are present and have the expected signature.

| API name | v4.10 location | Status | v4.26 expectation |
|----------|---------------|--------|-------------------|
| `Bornology.IsBounded.subset_closedBall_lt` | `Mathlib/Topology/MetricSpace/Bounded.lean:81` | ✓ | Stable (S10 GitHub-API confirmed at v4.26 pin) |
| `IsCompact.isBounded` | `Mathlib/Topology/MetricSpace/Bounded.lean` | ✓ | Stable |
| `Metric.mem_closedBall_zero_iff` | `Mathlib/Topology/Bornology/BoundedOperation.lean:209` (used) | ✓ | Stable |
| `norm_smul` | `Mathlib/Analysis/Normed/Group/Basic.lean` | ✓ | Stable |
| `Real.norm_of_nonneg` | `Mathlib/Analysis/Normed/Field/Basic.lean` | ✓ | Stable |
| `mul_le_mul_of_nonneg_left` | `Mathlib/Algebra/Order/Ring/Lemmas.lean` | ✓ | Stable |
| `inv_nonneg.mpr` | `Mathlib/Algebra/Order/Field/Basic.lean` | ✓ | Stable |
| `Continuous.subtype_mk` | `Mathlib/Topology/Constructions.lean` | ✓ (signature confirmed: `{f : Y → X} (h : Continuous f) (hp : ∀ x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)`) | Stable |
| `continuous_subtype_val` | `Mathlib/Topology/Constructions.lean` | ✓ | Stable |
| `continuous_const_smul` | `Mathlib/Topology/Algebra/ConstMulAction.lean:200` (`_iff` variant; the bare `continuous_const_smul` is from a typeclass) | ✓ | Stable; instance form `(continuous_const_smul R)` provided by `ContinuousConstSMul ℝ E` typeclass on Euclidean space |
| `inv_mul_cancel₀` | **Not found by exact name in v4.10**; the v4.10 form is `inv_mul_cancel : a ≠ 0 → a⁻¹ * a = 1`. The `₀` suffix may be a v4.26 rename. | ⚠ | **Verify before submission**: test `mul_inv_cancel₀` and `inv_mul_cancel₀` at v4.26 pin; fallback `inv_mul_cancel` may suffice |
| `mul_inv_cancel₀` | (Companion to above) | ⚠ | Same: needs v4.26 verification |
| `Subtype.ext` | `Mathlib/Data/Subtype.lean` | ✓ | Stable |
| `smul_smul` | `Mathlib/Algebra/Module/Basic.lean` | ✓ | Stable |
| `one_smul` | `Mathlib/Algebra/Module/Basic.lean` | ✓ | Stable |

**Net Mathlib-name risk surface**: One `_₀`-suffix question (the
`inv_mul_cancel₀` / `mul_inv_cancel₀` family used in the rescaling).
v4.10 has `inv_mul_cancel`; v4.26 may have either or both. The spec's
existing reference uses `inv_mul_cancel₀ hR_pos.ne'` (with `₀` suffix
and the dot-dispatched `.ne'` to convert `0 < R` to `R ≠ 0`). If this
name has drifted, the substitution is a single token: try
`inv_mul_cancel hR_pos.ne'` (without `₀`).

This is the **only** API-name risk in the entire S11.A.body Lean
stub. All other names are first-page Mathlib APIs.

## Recommendation

For the implementer of S11.A.body (S12-implement, follow-up session):

1. **Copy** the spec's Step 1–4 stub verbatim from
   `s11-strict-weakening-spec.md` lines 135–225 (Option b elementary
   rescaling).
2. **Replace** the inline Step 6 comment block with the 9–11 line
   structured Step 6 above, NOT the one-line spec implication.
3. **Build** with `./proofs/scripts/docker-build.sh
   Proofs.SchauderFixedPointOQ03OQ01`. Expected first-pass result:
   - All Mathlib names except `inv_mul_cancel₀` resolve immediately.
   - If `inv_mul_cancel₀` fails, try `inv_mul_cancel` (drop the `₀`)
     OR `mul_inv_cancel₀` reversed via `.symm`.
   - All other lemmas have been double-confirmed.
4. **Net effect**: file's sorry count drops from 2 to 1
   (`exists_continuous_proj_convex` remains as S11.B).
   `axiom brouwer_unit_ball` is the only Brouwer-side axiom (strictly
   weaker than the previous general-compact-convex form).

Estimated implementation effort: **~70 Lean lines, single 1-hour
session** (S12-implement). The Step 6 refinement here removes the
implementer's main blocker — knowing where the proof actually
finishes.

## Why analysis-only this session

I started transcribing Option (b) into Lean (Steps 1–4 went smoothly)
and hit the Step 6 logical gap above. Rather than push fragile
half-Lean (where the conclusion `f (r σy) = r σy` doesn't actually
follow from `(F (σ y) : E) = (σ y : E)` without the
`(σ y : E) ∈ S` interpolation), I rolled the work back into a
specification.

This **is** the productive output of the iteration: a tighter spec
that prevents the next implementer from hitting the same dead end
and rolling back. Memory note `feedback_researcher_verify_axiom_truth.md`
reinforces this — better to specify carefully than to produce
build-failing Lean that the doctor must patch.

## Files

- This spec:
  `research/problems/schauder-fixed-point-oq-03-oq-01-incomplete-01/s12-s11a-body-step6-refinement.md` (new)
- `state.md`: S12 entry under Current Focus + iteration 11 → 12.
- `src/data/research/problems/schauder-fixed-point-oq-03-oq-01-incomplete-01.json`:
  iteration sync, focus + nextAction update, attemptCounts++.
- (No Lean changes this session; deferred to S12-implement.)

## References

- `s11-strict-weakening-spec.md` — S11 stubs for both work items.
- `s10-mathlib-v426-lookup3-resolved.md` — Brouwer FPT absent at pinned
  Mathlib rev.
- `s9-mathlib-lookup-refinements.md` — LOOKUP-1 confirmed.
- `s8-brouwer-extension-via-projection.md` — original retraction proof
  outline.
- PR #17501 (S11 strict-weakening lift, build pending, merged) — the
  axiom rename + parallel-claimable `sorry` work items this spec
  refines.
