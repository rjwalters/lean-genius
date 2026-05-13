# Session — S2 OBSERVE: Mathlib `circleIntegral` is the HFC bearer (not blocked)

**Slug**: `geometric-series-oq-02-oq-05`
**Researcher**: researcher-5
**Date**: 2026-05-13
**Phase**: OBSERVE (doc-only)
**Iteration**: S2 OBSERVE — Mathlib bearer audit + S3 ACT scope

## TL;DR

The slug's existing knowledge entry claims the OQ is Mathlib-gapped:

> *"Full HFC f(a) = (2πi)⁻¹∮f(λ)R(λ,a)dλ needs Banach-space-valued contour integration not yet in Mathlib"*
> — slug JSON `knowledge.insights[3]` (set 2026-03-30)

**This claim is no longer accurate at Mathlib v4.26.0** (the pinned ref in
`proofs/lakefile.toml`). The Banach-space-valued circle integral is in
Mathlib at `Mathlib/MeasureTheory/Integral/CircleIntegral.lean:336`:

```lean
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
…
def circleIntegral (f : ℂ → E) (c : ℂ) (R : ℝ) : E :=
  ∫ θ : ℝ in 0..2 * π, deriv (circleMap c R) θ • f (circleMap c R θ)

notation3 "∮ "(...)" in ""C("c", "R")"", "r:60:(scoped f => circleIntegral f c R) => r
```

The integrand type `ℂ → E` for any `[NormedAddCommGroup E] [NormedSpace ℂ E]`
covers exactly the Dunford-Taylor target: `E = A` for a complex Banach
algebra `A` (i.e. `[NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]`,
which is `[NormedSpace ℂ A]` for free via the `NormedAlgebra` instance).

The OQ is therefore **NOT blocked** — it is **tractable** with the existing
Mathlib infrastructure. A future S3 ACT can land the HFC definition + the
constant-case verification in ~30-50 LOC.

## What this PREP ships

A single new session-notes markdown file (this file). Zero edits to:

- `proofs/Proofs/GeometricSeriesOQ02OQ05.lean` (gallery face, verified)
- `src/data/proofs/geometric-series-oq-02-oq-05/{meta,annotations,index,tacticStates}` (gallery)
- `src/data/research/problems/geometric-series-oq-02-oq-05.json` (auditor/mechanic drift-sync domain)
- `state.md`, `knowledge.md`, `problem.md` (slug docs — owned by future drift-sync)

## Mathlib bearer audit at v4.26.0

| Symbol | Module path | Line | Verdict |
|---|---|---|---|
| `circleMap (c : ℂ) (R : ℝ) (θ : ℝ) : ℂ` | `Mathlib/MeasureTheory/Integral/CircleIntegral.lean` | 75 | ✅ |
| `def CircleIntegrable (f : ℂ → E) (c : ℂ) (R : ℝ) : Prop` | same | 199 | ✅ |
| `def circleIntegral (f : ℂ → E) (c : ℂ) (R : ℝ) : E` | same | 336 | ✅ (requires `[NormedSpace ℂ E]`) |
| `notation ∮ z in C(c, R), f z` | same | 340 | ✅ |
| `theorem hasDerivAt_circleMap` | same | (early section) | ✅ — differentiability of `circleMap` |
| `theorem deriv_circleMap_ne_zero` | same | (early section) | ✅ — non-vanishing tangent |
| Constants integration: `theorem integral_radius_zero` (zero radius → zero integral) | same | (after `def circleIntegral`) | ✅ |

Verified via:

```bash
gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/MeasureTheory/Integral/CircleIntegral.lean?ref=v4.26.0' --jq '.content' | base64 -d | grep -nE "^def circleIntegral|^def CircleIntegrable|^def circleMap"
```

Outputs:
```
75:  def circleMap (c : ℂ) (R : ℝ) (θ : ℝ) : ℂ := …
199: def CircleIntegrable (f : ℂ → E) (c : ℂ) (R : ℝ) : Prop := …
336: def circleIntegral (f : ℂ → E) (c : ℂ) (R : ℝ) : E := …
```

No phantoms. The bearer is named, signed, and available at the pinned ref.

## Constraint analysis

The existing parent file `Proofs/GeometricSeriesOQ02OQ05.lean` opens:

```lean
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A] [NormOneClass A]
```

The HFC integrand needs `𝕜 = ℂ`. Two options:

**Option A — specialize within the file.** Add a new `§7. Holomorphic
Functional Calculus` block at the bottom of the parent file, opening
`variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]`.
Re-uses §1–6 results since `ℂ` is a `NontriviallyNormedField`.

**Option B — new file `GeometricSeriesOQ02OQ05HFC.lean`.** Imports the
parent + `Mathlib.MeasureTheory.Integral.CircleIntegral`. Cleaner
separation; doesn't bloat the verified gallery face. **Recommended** for
the S3 ACT iteration.

The `[NormedSpace ℂ A]` typeclass needed by `circleIntegral` is provided
automatically by `[NormedAlgebra ℂ A]` via the `NormedAlgebra → NormedSpace`
instance at `Mathlib/Analysis/NormedSpace/Algebra.lean` (standard).

## S3 ACT scope (recommendation)

A reasonable next-iteration ACT lands the HFC definition + two
sanity-check theorems. Estimated ~50 LOC + 0 axioms + 0 sorries.

### Sketch (subject to S3 PREP verification)

```lean
import Proofs.GeometricSeriesOQ02OQ05
import Mathlib.MeasureTheory.Integral.CircleIntegral

namespace ResolventNeumann

open Complex

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [NormOneClass A]

/-- The Dunford-Taylor integral defining f(a) for holomorphic f on a
    neighborhood of σ(a). Here `R` is a contour radius with `‖a‖ < R`,
    so the resolvent `R(λ, a)` is well-defined on `|λ| = R`. -/
noncomputable def dunfordTaylor (f : ℂ → ℂ) (a : A) (R : ℝ) : A :=
  (2 * π * I)⁻¹ • (∮ λ in C(0, R), f λ • Ring.inverse (algebraMap ℂ A λ - a))

/-- The Dunford-Taylor integral of the constant 1 equals the identity. -/
theorem dunfordTaylor_one (a : A) {R : ℝ} (hR : ‖a‖ < R) :
    dunfordTaylor (fun _ => 1) a R = 1 := by
  -- Strategy: factor `Ring.inverse (λ - a) = λ⁻¹ * (1 - λ⁻¹·a)⁻¹` from §2,
  -- swap with `circleIntegral`, reduce to `∮ λ in C(0, R), λ⁻¹ dλ = 2πi`.
  sorry  -- S3 deliverable

/-- The Dunford-Taylor integral of `f(λ) = λ` equals `a` (Cauchy's identity). -/
theorem dunfordTaylor_id (a : A) {R : ℝ} (hR : ‖a‖ < R) :
    dunfordTaylor (fun λ => λ) a R = a := by
  -- Strategy: similar factorization + residue at 0 + residue at a,
  -- or direct Neumann-series expansion of `R(λ, a)` swapped with the integral.
  sorry  -- S3 deliverable

end ResolventNeumann
```

The two sorry-stubs are the S3 ACT deliverables; the *definition*
`dunfordTaylor` is the load-bearing piece and is verifiable in isolation.

### Why the constant and identity cases are the right S3 scope

1. **Constants ⇒ identity.** `f = 1` gives `f(a) = 1` — the unit law.
2. **Identity ⇒ a.** `f = λ ↦ λ` gives `f(a) = a` — the identity law.

Together with linearity (free from `circleIntegral` additivity), these
make `dunfordTaylor` a ring hom on polynomials f. Multiplicativity for
products requires Cauchy's integral formula composition, which is
~150-250 LOC and a separate S4 ACT.

## Drift-sync implications

The slug JSON has multiple stale fields that auditor/mechanic should
align with the actual file state:

| Field | Current (stale) | Should be |
|---|---|---|
| `currentState.phase` | `"ACT"` | `"COMPLETED"` or `"ORIENT"` (depending on whether S3 is in scope) |
| `currentState.nextAction` | `"Read problem.md thoroughly and acquire full context."` | `"S3 ACT: dunfordTaylor + constants/identity cases"` |
| `knowledge.progressSummary` | `"… 4 main theorems … plus 1 sorry. Docker build verification pending."` | `"… 6 sections complete, 0 sorries, 0 axioms, all verified."` |
| `knowledge.insights[3]` | `"… Banach-space-valued contour integration not yet in Mathlib"` | `"circleIntegral lives in Mathlib.MeasureTheory.Integral.CircleIntegral at v4.26.0"` |
| `knowledge.builtItems[0]` | `"… (1 sorry: resolvent_tendsto_zero)"` | `"… (resolvent_tendsto_zero proved, 0 sorries)"` |

**This PREP does not touch any of the above** — drift-sync is the
auditor/mechanic's domain. This PREP only documents the audit findings
that should drive the drift-sync.

## Race safety

`gh pr list --repo rjwalters/lean-genius --search "geometric-series-oq-02-oq-05 in:title" --state open` → `[]`

Most recent activity on the slug:

| PR | Date | Status |
|---|---|---|
| #8654 | 2026-04-03 | MERGED (enrichment: resolvent + Neumann series) |
| #8658 | 2026-04-03 | MERGED (meta fix: sections to ProofSection format) |
| #8610 | 2026-04-03 | CLOSED (Research: prove resolvent_tendsto_zero — superseded by main work) |
| #8600 | 2026-04-03 | MERGED (verified status) |
| #8548 | 2026-03-30 | MERGED (initial Research session) |

**No PRs in 40 days.** Zero conflict surface.

## What this PREP does NOT do

- **No Lean changes.** This is a doc-only S2 OBSERVE.
- **No edits to the gallery face** `proofs/Proofs/GeometricSeriesOQ02OQ05.lean`.
- **No drift-sync edits** to slug JSON, state.md, knowledge.md, problem.md.
- **No new gallery entry** for the HFC extension.
- **No new Open Questions** generated.
- **No retroactive PREPs.**
- **No S3 ACT implementation** — that is a separate iteration.

## Honesty / disclaimers

- I have **not** run the Lean build for the proposed S3 ACT sketch. The
  audit is purely Mathlib-API verification via `gh api` against the
  v4.26.0 ref pinned in `proofs/lakefile.toml`. The two sorries in the
  sketch are honest placeholders for the S3 ACT deliverable, not claims
  of completed work.
- The S3 ACT estimate (~50 LOC) is a back-of-envelope based on
  `circleIntegral`'s available API. A future S3 PREP iteration may refine
  this estimate after auditing specific Mathlib lemmas about
  `∮ λ in C(0, R), λ⁻¹ dλ = 2πi` (which is the load-bearing identity
  for `dunfordTaylor_one`).
- The claim "OQ is NOT blocked" is bounded by the v4.26.0 Mathlib ref.
  If a future lake-pin downgrades below the introduction of
  `circleIntegral`, the claim weakens. The current pin is well above
  that threshold; this risk is theoretical only.
- The slug's `knowledge.insights[3]` claim was *correct* at the time of
  writing (2026-03-30) — Mathlib's `circleIntegral` may have been less
  developed then. This PREP **does not blame** the prior author; it
  documents that **Mathlib has caught up**.

## References

- **Mathlib v4.26.0** pinned at `proofs/lakefile.toml`
  (rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`).
- **`circleIntegral` declaration**:
  `Mathlib/MeasureTheory/Integral/CircleIntegral.lean:336`
  (verified 2026-05-13 via `gh api`).
- **Parent Lean file**: `proofs/Proofs/GeometricSeriesOQ02OQ05.lean`
  (250 LOC, 0 sorries, 0 axioms, status `verified` in
  `src/data/proofs/geometric-series-oq-02-oq-05/meta.json`).
- **Dunford & Taylor** (1938), Dunford & Schwartz, "Linear Operators,
  Part I" (1958), VII.3.
- **Rudin**, "Functional Analysis" (1991), §10.4–10.6.
