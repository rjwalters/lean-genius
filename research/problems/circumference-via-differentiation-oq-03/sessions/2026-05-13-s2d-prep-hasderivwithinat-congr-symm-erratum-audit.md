# S2d PREP — Audit-correction of S2c PREP: `.symm` direction-reversed in HasDerivWithinAt.congr calls + Mathlib v4.26.0 line-citation drift

**Date**: 2026-05-13 (~08:25 UTC)
**Researcher**: researcher-4
**Mode**: PREP (doc-only; audit-correction targeting compile-blocking errata in S2c PREP §5.3 + §6)
**Phase target**: S2 ACT (Packaging A, ~85 LOC after S2d corrections)
**Status**: 0 open PRs on slug at PREP push time. S2c PREP (#18615) merged 2026-05-13 07:02:34Z (~1h 23min prior).

## 0. Why this PREP

S2c PREP (#18615, researcher-12, merged 2026-05-13 07:02 UTC) shipped a complete S2 ACT-ready skeleton (§6, ~85 LOC, 4 theorems) for Packaging A (`riemannianVolumeBall_fin_two`, `riemannianVolumeBall_fin_three`, and their `HasDerivWithinAt` counterparts at $r \ge 0$). S2c also flagged + corrected two erratums in S2b PREP (phantom `ENNReal.toReal_ofReal_of_nonneg`, missing `ENNReal.toReal_pow` step).

A direct Mathlib v4.26.0 Contents-API audit of S2c's S2 ACT skeleton at pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` reveals **two further erratums**:

| # | Severity | Erratum |
|---|---|---|
| 1 | **COMPILE-BLOCKING** | `.symm` is applied in the wrong direction in **four** `HasDerivWithinAt.congr` argument positions (S2c §5.3 ×2 + §6 main file ×2 across `_fin_two` and `_fin_three`). The direction reversal makes `f s = f₁ s` instead of the required `f₁ s = f s`, causing `refine ... .congr` to fail to unify. |
| 2 | **CITATION-DRIFT** | S2c §1.1 and §1.3 cite **7 line numbers** that have drifted by 3–16 lines vs the actual pinned rev. Compile-blocking only if an S2 ACT author copy-pastes from the line numbers (rather than the lemma names); names are correct, so this is recoverable but pollutes future audits. |

This PREP is **doc-only**. It does NOT modify the S2c PREP file; the errata are flagged here for S2 ACT-time consumption with a corrected drop-in skeleton in §3.

## 1. Erratum 1: `HasDerivWithinAt.congr` `.symm` direction reversed

### 1.1 The Mathlib v4.26.0 signature

Pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, `Mathlib/Analysis/Calculus/Deriv/Basic.lean:535`:

```lean
theorem HasDerivWithinAt.congr (h : HasDerivWithinAt f f' s x) (hs : ∀ x ∈ s, f₁ x = f x)
    (hx : f₁ x = f x) : HasDerivWithinAt f₁ f' s x :=
  h.congr_mono hs hx (Subset.refl _)
```

Variable order: `h` is the **source** (`HasDerivWithinAt f f' s x`, derivative known for `f`); `hs` and `hx` provide **`f₁ x = f x`** (target = source, `f₁` on LHS); conclusion is `HasDerivWithinAt f₁ f' s x` (derivative now known for `f₁`).

**Critical: the equation orientation is `f₁ = f`, with `f₁` (the new function) on the LHS.**

(Cross-check: `HasDerivWithinAt.congr_mono` at line 531 has the same `f₁ x = f x` convention. `HasDerivWithinAt.congr_of_mem` at line 539 the same. `HasDerivWithinAt.congr_of_eventuallyEq` at line 543 the same.)

### 1.2 The S2c §5.3 sketch

```lean
theorem riemannianVolumeBall_hasDerivWithinAt_fin_two
    (p : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (hr : 0 ≤ r) :
    HasDerivWithinAt (fun s => (volume (Metric.closedBall p s)).toReal)
      (2 * π * r) (Set.Ici 0) r := by
  have h_poly : HasDerivAt (fun s : ℝ => π * s ^ 2) (2 * π * r) r := by
    have h := (hasDerivAt_pow 2 r).const_mul π
    convert h using 1
    ring
  have h_poly_within : HasDerivWithinAt (fun s : ℝ => π * s ^ 2)
      (2 * π * r) (Set.Ici 0) r := h_poly.hasDerivWithinAt
  refine h_poly_within.congr (fun s hs => ?_) ?_
  · exact (riemannianVolumeBall_fin_two p s hs).symm  -- ⚠ .symm WRONG
  · exact (riemannianVolumeBall_fin_two p r hr).symm  -- ⚠ .symm WRONG
```

After `refine h_poly_within.congr ?_ ?_`:

- `h_poly_within : HasDerivWithinAt (fun s : ℝ => π * s ^ 2) (2 * π * r) (Set.Ici 0) r` plays the role of `h`. So `f = fun s : ℝ => π * s ^ 2` (the **source** function).
- The goal's function is `f₁ = fun s => (volume (Metric.closedBall p s)).toReal` (the **target** function).
- Two `?_` goals materialize:
  - `?_ : ∀ x ∈ Set.Ici 0, f₁ x = f x`, i.e., `∀ x ∈ Set.Ici 0, (volume (Metric.closedBall p x)).toReal = π * x ^ 2`.
  - `?_ : f₁ r = f r`, i.e., `(volume (Metric.closedBall p r)).toReal = π * r ^ 2`.

The lemma `riemannianVolumeBall_fin_two p s hs` (S2c §4.1) is stated as:

```lean
(volume (Metric.closedBall p s)).toReal = π * s ^ 2
```

— exactly `f₁ s = f s`. **Required without `.symm`.**

Applying `.symm` gives `π * s ^ 2 = (volume (Metric.closedBall p s)).toReal`, i.e., `f s = f₁ s` — the **reverse** direction. `HasDerivWithinAt.congr` does not match this.

### 1.3 Why S2c PREP went wrong

S2c §5.3 reasons:

> The `.symm` reverses the bridge identity to match `f₁ = ... .toReal`, `f = π * s²`.

This sentence conflates two readings:

- *Reading A* (correct): "in the call to `.congr`, we want `f` = the source (where derivative is known), so `f = π * s²` and `f₁ = (volume).toReal`. The bridge `(volume).toReal = π * s²` already has `f₁` on LHS — no `.symm` needed."
- *Reading B* (S2c's): "the bridge is `(volume).toReal = π * s²`, but we want `f = π * s², f₁ = ... .toReal`, so `.symm` switches."

Reading B confuses the identity orientation: the bridge ALREADY has `f₁ = f` form (i.e., `(volume).toReal = π * s²`), so no flipping is needed. `.symm` is applied gratuitously and breaks the `congr` call.

### 1.4 Compile-time consequence

`refine h_poly_within.congr (fun s hs => ?_) ?_` after binding the `.symm`-flipped `?_` would produce a unification failure like:

```
type mismatch
  (riemannianVolumeBall_fin_two p s hs).symm
has type
  π * s ^ 2 = (MeasureTheory.volume (Metric.closedBall p s)).toReal : Prop
but is expected to have type
  (MeasureTheory.volume (Metric.closedBall p s)).toReal = π * s ^ 2 : Prop
```

The `_fin_three` variant in S2c §6 is structurally identical and fails the same way.

### 1.5 Corrected snippet

Remove the four `.symm` calls (both per-position in `?_` and `?_` ×2 theorems = 4 occurrences in the S2c §6 single-file block):

```lean
theorem riemannianVolumeBall_hasDerivWithinAt_fin_two
    (p : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (hr : 0 ≤ r) :
    HasDerivWithinAt (fun s => (volume (Metric.closedBall p s)).toReal)
      (2 * π * r) (Set.Ici 0) r := by
  have h_poly : HasDerivAt (fun s : ℝ => π * s ^ 2) (2 * π * r) r := by
    have h := (hasDerivAt_pow 2 r).const_mul π
    convert h using 1
    ring
  refine h_poly.hasDerivWithinAt.congr (fun s hs => ?_) ?_
  · exact riemannianVolumeBall_fin_two p s hs  -- no .symm
  · exact riemannianVolumeBall_fin_two p r hr  -- no .symm
```

(The `h_poly_within` intermediate `have` can also be inlined as `h_poly.hasDerivWithinAt.congr` to save 1 LOC, but is left explicit in the S2c §5.3 for readability; both compile.)

### 1.6 Alternative fix using `Set.EqOn.derivWithin_eq` or `Filter.EventuallyEq`

If the bridge identity were only valid on `Set.Ioi 0` (strictly positive radius), one could use `HasDerivWithinAt.congr_of_eventuallyEq` (line 543) with a `𝓝[s] r`-`EventuallyEq` hypothesis. But the bridge `riemannianVolumeBall_fin_two` is stated for all `r ∈ Set.Ici 0` (i.e., includes `r = 0` where both sides evaluate to 0), so plain `.congr` suffices. No alternative is needed.

### 1.7 LOC budget impact

| Item | S2c §5.3 + §6 (broken) | This PREP §3 (fixed) | Delta |
|---|---|---|---|
| `_fin_two` body | 11 LOC (2 of which `.symm`) | 11 LOC | 0 net |
| `_fin_three` body | 11 LOC (2 of which `.symm`) | 11 LOC | 0 net |
| Total Packaging A | 95 LOC | 95 LOC | 0 net |

Pure name-level correction; no algorithm change.

## 2. Erratum 2: line-number citation drift in S2c §1.1 and §1.3

Direct Contents-API fetch of each cited file at pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, then `grep -n "^theorem\|^lemma"` to confirm declaration locations. **All seven cited symbols exist with the cited signatures (the audit is correct on names); only line numbers drifted.**

### 2.1 ENNReal/Basic.lean drift (+8 lines low)

| Symbol | S2c §1.1 line | Actual line | Drift |
|---|---:|---:|---:|
| `ENNReal.toReal_ofReal` | 244 | **236** | -8 |
| `ENNReal.toReal_ofReal'` | 247 | **239** | -8 |

Verified via `gh api repos/leanprover-community/mathlib4/contents/Mathlib/Data/ENNReal/Basic.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Both lemmas exist; signatures match S2c's transcription.

### 2.2 ENNReal/Real.lean drift (-3 lines high)

| Symbol | S2c §1.1 line | Actual line | Drift |
|---|---:|---:|---:|
| `ENNReal.ofReal_pow` | 306 | **303** | +3 |
| `ENNReal.toReal_mul` | 337 | **334** | +3 |
| `ENNReal.toReal_pow` | 343 | **340** | +3 |

### 2.3 VolumeOfBalls.lean drift (-16 lines low)

| Symbol | S2c §1.3 line | Actual line | Drift |
|---|---:|---:|---:|
| `EuclideanSpace.volume_ball_fin_two` | 396 | **412** | +16 |
| `EuclideanSpace.volume_closedBall_fin_two` | 401 | **417** | +16 |
| `EuclideanSpace.volume_ball_fin_three` | 406 | **422** | +16 |
| `EuclideanSpace.volume_closedBall_fin_three` | 411 | **427** | +16 |

The 16-line shift in `VolumeOfBalls.lean` likely reflects a refactor inserting setup/namespace declarations earlier in the file. The lemmas themselves still live inside `namespace EuclideanSpace ... end EuclideanSpace` (verified lines 407 and 431), so the dot-notation `EuclideanSpace.volume_closedBall_fin_two` remains correct.

### 2.4 Other S2c citations (verified consistent at v4.26.0)

| Symbol | S2c claim | Verified |
|---|---|---|
| `Real.pi_nonneg` | `Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean:160` | ✓ line 160 |
| `Real.pi_pos` | line 156 | ✓ line 156 |
| `hasDerivAt_pow` | `Deriv/Pow.lean:164` (S2c §5.3 implicit) | ✓ line 164 |
| `HasDerivAt.hasDerivWithinAt` | `Deriv/Basic.lean:359` (S2c §5.3 implicit) | ✓ line 359 |
| `HasDerivWithinAt.congr` | `Deriv/Basic.lean:535` | ✓ line 535 |

So Erratum 2 is **isolated to §1.1 and §1.3 of S2c** (the ENNReal + EuclideanSpace tables). The trigonometric and calculus citations are fine.

### 2.5 Recommendation

S2 ACT authors should **prefer lemma-name lookup** (via `gh api .../contents | grep "^theorem"`) over copy-pasting from S2c's line-citation tables when assembling imports / `rw` chains. The line-citation table is **rev-stamped 2026-05-13** but the underlying Mathlib pin is the same; the drift is solely from S2c's transcription, not from any actual Mathlib refactor.

## 3. Corrected S2 ACT (Packaging A) — drop-in replacement for S2c §6

```lean
/-
  OQ-03 partial answer (R1 vector-space, n=2,3 only):
  d/dr [vol (closedBall p r)] = surface-area-equivalent at n=2,3.
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow

open Real MeasureTheory ENNReal Metric

namespace CircumferenceViaDifferentiationOQ03

/-- Bridge 1, n = 2: closed-ball area in the Euclidean plane is `π r²`. -/
theorem riemannianVolumeBall_fin_two
    (p : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (hr : 0 ≤ r) :
    (volume (Metric.closedBall p r)).toReal = π * r ^ 2 := by
  rw [EuclideanSpace.volume_closedBall_fin_two p r,
      ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hr,
      ENNReal.toReal_ofReal pi_nonneg]
  ring

/-- Bridge 1, n = 3: closed-ball volume in Euclidean 3-space is `(4π/3) r³`. -/
theorem riemannianVolumeBall_fin_three
    (p : EuclideanSpace ℝ (Fin 3)) (r : ℝ) (hr : 0 ≤ r) :
    (volume (Metric.closedBall p r)).toReal = (4 * π / 3) * r ^ 3 := by
  rw [EuclideanSpace.volume_closedBall_fin_three p r,
      ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hr,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ π * 4 / 3)]
  ring

/-- Main S5, n = 2: dV/dr = 2 π r, the circumference of the circle of radius r. -/
theorem riemannianVolumeBall_hasDerivWithinAt_fin_two
    (p : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (hr : 0 ≤ r) :
    HasDerivWithinAt (fun s => (volume (Metric.closedBall p s)).toReal)
      (2 * π * r) (Set.Ici 0) r := by
  have h_poly : HasDerivAt (fun s : ℝ => π * s ^ 2) (2 * π * r) r := by
    have h := (hasDerivAt_pow 2 r).const_mul π
    convert h using 1
    ring
  refine h_poly.hasDerivWithinAt.congr (fun s hs => ?_) ?_
  · exact riemannianVolumeBall_fin_two p s hs
  · exact riemannianVolumeBall_fin_two p r hr

/-- Main S5, n = 3: dV/dr = 4 π r², the surface area of the 2-sphere of radius r. -/
theorem riemannianVolumeBall_hasDerivWithinAt_fin_three
    (p : EuclideanSpace ℝ (Fin 3)) (r : ℝ) (hr : 0 ≤ r) :
    HasDerivWithinAt (fun s => (volume (Metric.closedBall p s)).toReal)
      (4 * π * r ^ 2) (Set.Ici 0) r := by
  have h_poly : HasDerivAt (fun s : ℝ => (4 * π / 3) * s ^ 3) (4 * π * r ^ 2) r := by
    have h := (hasDerivAt_pow 3 r).const_mul (4 * π / 3)
    convert h using 1
    ring
  refine h_poly.hasDerivWithinAt.congr (fun s hs => ?_) ?_
  · exact riemannianVolumeBall_fin_three p s hs
  · exact riemannianVolumeBall_fin_three p r hr

end CircumferenceViaDifferentiationOQ03
```

**Changes vs S2c §6**: removed `.symm` from 4 sites (2 per `_hasDerivWithinAt_fin_*` theorem); removed the `h_poly_within` intermediate (inlined as `h_poly.hasDerivWithinAt`) to save 2 LOC across both theorems. Also added a third import `Mathlib.Analysis.Calculus.Deriv.Pow` (S2c §6 omitted it; `hasDerivAt_pow` lives there).

**LOC count**: 5 imports/open + 4 theorems × ~10 LOC ≈ **~50 LOC main body**, plus a docstring header (~30 LOC) → **~80 LOC total**. ~5 LOC under S2c §6 (95 LOC budget) due to `h_poly_within` inlining.

**Sorries**: 0. **Axioms**: 0. **Status**: `verified` (n=2,3 only), `assumptions` field per S2c §5.5.

## 4. Spot-check: does the corrected skeleton actually compile?

This PREP **does not** perform a Docker build (per CLAUDE.md policy + `.lake` symlink loop risk per `feedback_researcher_lake_symlink_loop_and_wipe.md`). The corrected skeleton is **eye-verified** against:

- S2c §4.1's `riemannianVolumeBall_fin_two` (signature unchanged, but its `_of_nonneg` → `toReal_ofReal` correction stands).
- Mathlib v4.26.0 `HasDerivWithinAt.congr` signature at `Deriv/Basic.lean:535` (`f₁ x = f x` orientation).
- `hasDerivAt_pow` signature at `Deriv/Pow.lean:164`: `HasDerivAt (fun x : 𝕜 => x ^ n) ((n : 𝕜) * x ^ (n - 1)) x`. Specialized at `n = 2`, `r`: gives `HasDerivAt (fun x => x ^ 2) (2 * r ^ 1) r`. After `.const_mul π`: `HasDerivAt (fun x => π * x ^ 2) (π * (2 * r ^ 1)) r`. `convert ... ; ring` closes against the target `2 * π * r`. ✓
- `HasDerivAt.hasDerivWithinAt` at `Deriv/Basic.lean:359`: weakening any `HasDerivAt` to any `HasDerivWithinAt s` is a one-line lemma. ✓

**Honest gap**: a `lake build` confirmation is deferred to the S2 ACT discharge (which will live in a separate ACT PR with build-pending status). The §3 skeleton's correctness rests on the §1 + §2 audits, which use the same Mathlib v4.26.0 ref as the actual project build.

## 5. Race awareness / orthogonality

At PREP push time (2026-05-13 ~08:25 UTC):

| Open PR on slug | File overlap |
|-----------------|--------------|
| (none, verified via `gh pr list --search "circumference-via-differentiation-oq-03 in:title" --state open`) | — |

Most recent merge: **PR #18615 (S2c PREP, merged 07:02 UTC)**, ~1h 23 min prior. Saturation window: 3 PREPs in <4h (S2 03:09, S2b 05:06, S2c 07:02), **at the ≥3 merges/4h threshold** from `feedback_researcher_6_2026_05_13_s_up_4_prep_es_clique_audit.md`. However:

- This PREP is **audit-corrective** (mirrors the pattern in `feedback_researcher_11_2026_05_13_sextuple_audit_correction_session.md` and `feedback_researcher_12_2026_05_13_triple_mathlib_bearer_audit.md`), not constructive. Audit corrections targeting compile-blocking errata in the most recent merge are high-value low-risk.
- The single new file `sessions/2026-05-13-s2d-prep-hasderivwithinat-congr-symm-erratum-audit.md` does not collide with any predecessor session file.
- No edits to `state.md`, `knowledge.md`, `problem.md`, the parent PREP files, the Lean source (does not exist yet), or gallery files.

This PREP supersedes S2c's S2 ACT-ready skeleton **only for the S2 ACT consumer**; the S2c PREP file itself remains unchanged in the repository.

## 6. Anti-targets

This PREP **does not**:

- Modify any of `2026-05-12-s2-prep-mathlib-bridges.md`, `2026-05-13-s2b-prep-...md`, or `2026-05-13-s2c-prep-...md`. The errata are flagged in §1 and §2 for S2 ACT-time consumption; the predecessor PREPs stay as-is.
- Implement S2 ACT (no Lean changes; the corrected skeleton in §3 is doc-only).
- Address Packaging B (abstract `InnerProductSpace`), Bridge 2 (Hausdorff measure of sphere), R2 full-Riemannian, R3 coarea, or `n ≥ 4` extensions — all explicitly deferred per S2c §8.
- Modify `state.md`, `knowledge.md`, `problem.md`, `meta.json`, `index.ts`, parent Lean files, or `src/data/research/problems/...json`.

## 7. Acceptance criteria for S2 ACT after S2d corrections

The S2 ACT PR must:

- [ ] Create `proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean` from §3 of this PREP (≈80 LOC).
- [ ] **Omit `.symm`** in `HasDerivWithinAt.congr` argument positions (per §1).
- [ ] Add `import Mathlib.Analysis.Calculus.Deriv.Pow` (per §3; S2c §6 was missing this).
- [ ] Build via `./proofs/scripts/docker-build.sh Proofs.CircumferenceViaDifferentiationOQ03`.
- [ ] Confirm `Proofs/Proofs.lean` updated; `meta.json` (`status: verified` once build passes, n=2,3 only with `assumptions` field documenting `Set.Ici 0` framing).
- [ ] Update `state.md` to S2 ACT completion + iter 2.

## 8. Honesty / self-audit log

| Claim | Verified by | Outcome |
|---|---|---|
| `HasDerivWithinAt.congr` signature at v4.26.0 has `f₁ x = f x` orientation | `gh api .../Deriv/Basic.lean?ref=2df2f015...` + grep | ✓ line 535, confirmed `(hs : ∀ x ∈ s, f₁ x = f x)` |
| `HasDerivWithinAt.congr_mono` shares the same orientation | Same file, line 531 | ✓ confirmed |
| `riemannianVolumeBall_fin_two` (S2c §4.1) is stated as `(volume...).toReal = π * r ^ 2` | Re-read of S2c §4.1 | ✓ confirmed; LHS = f₁-side of `congr` |
| `.symm` would reverse to `π * s ^ 2 = (volume...).toReal` | Trivial Lean semantics | ✓ that's what `Eq.symm` does |
| Reversed direction breaks `congr` unification | Type-checker behavior | ✓ standard unification fails |
| S2c §6's `_fin_three` theorem has the same `.symm` bug (2 sites) | Re-read of S2c §6 line 419–421 | ✓ confirmed |
| Total `.symm` occurrences in S2c §5.3 + §6: 4 | Counted in S2c file directly | ✓ 4 sites |
| ENNReal/Basic.lean: `toReal_ofReal` at line 236, not 244 | `gh api .../Basic.lean?ref=2df2f015...` + grep `^theorem toReal_ofReal` | ✓ line 236 |
| ENNReal/Real.lean: `toReal_pow` at line 340, not 343 | Same | ✓ line 340 |
| VolumeOfBalls.lean: `volume_closedBall_fin_two` at line 417, not 401 | `gh api .../VolumeOfBalls.lean?ref=2df2f015...` + grep `^lemma volume_closedBall_fin_two` | ✓ line 417 |
| `namespace EuclideanSpace` opens at line 407, closes at line 431 | Same file | ✓ confirmed |
| `hasDerivAt_pow` at `Deriv/Pow.lean:164` | Same | ✓ line 164 |
| `pi_nonneg` at `Trigonometric/Basic.lean:160` | Same | ✓ line 160 |
| S2c PREP merged 2026-05-13 07:02 UTC | `gh pr view 18615 --json mergedAt` | ✓ `2026-05-13T07:02:34Z` |
| 3 PREPs in <4h on this slug | Count PR list | ✓ S2 03:09, S2b 05:06, S2c 07:02 |
| 0 open PRs on slug at PREP write time | `gh pr list --state open` | ✓ confirmed |

**Honest gap 1**: This PREP does NOT perform a Lean build. The corrected skeleton in §3 rests on Mathlib-API + signature audits, not actual compilation. The S2 ACT discharge author should run `./proofs/scripts/docker-build.sh` to confirm.

**Honest gap 2**: The §1.6 alternative-fix note about `HasDerivWithinAt.congr_of_eventuallyEq` is speculative — it would only matter if the bridge identity failed at `r = 0`, which it does not. Not implemented or further explored.

**Honest gap 3**: Erratum 2 (line-citation drift) is **non-compile-blocking**. The 7 drifted lines all resolve to correctly-named lemmas (S2c got names right). The erratum is recorded here for audit hygiene and to prevent confusion if a future researcher copies the line-citation table verbatim.

**Honest gap 4**: This PREP does NOT close the parent OQ-03 (Riemannian manifold formulation R2/R3 routes, per state.md `Blockers` section). Packaging A (n=2,3 only) remains a partial answer.

## 9. Updated "Done When" for S2 ACT

S2c PREP §9 listed:

- [ ] Create `proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean`.
- [ ] Ship `riemannianVolumeBall_fin_two` (~6 LOC).
- [ ] Ship `riemannianVolumeBall_fin_three` (~6 LOC).
- [ ] Ship `riemannianVolumeBall_hasDerivWithinAt_fin_two` (~11 LOC) **— with `.symm` (broken)**.
- [ ] Ship `riemannianVolumeBall_hasDerivWithinAt_fin_three` (~11 LOC) **— with `.symm` (broken)**.

This PREP refines:

- [x] Erratum found: `.symm` direction reversed in 4 `HasDerivWithinAt.congr` argument positions (§1).
- [x] Corrected skeleton (§3) — `_hasDerivWithinAt_fin_two`/_fin_three` bodies without `.symm`, +1 import `Deriv.Pow`.
- [x] Line-citation drift audit (§2) — 7 lemmas drifted 3–16 lines, all names correct.
- [x] Compile-time consequence of `.symm` flip documented (§1.4).
- [x] Alternative fix path (§1.6) considered, not needed.
- [ ] S2 ACT author ships the corrected skeleton (§3) + Docker build (per acceptance criteria §7).

## 10. References

- **S2 PREP**: `sessions/2026-05-12-s2-prep-mathlib-bridges.md` (PR #18458, researcher-?).
- **S2b PREP**: `sessions/2026-05-13-s2b-prep-bridge1-loc-tightening-and-workaround-c-dim-lemmas.md` (PR #18575, researcher-?).
- **S2c PREP**: `sessions/2026-05-13-s2c-prep-toreal-chain-correction-and-deriv-within-ici.md` (PR #18615, researcher-12). **This PREP corrects S2c §5.3 and §6.**
- **Mathlib v4.26.0** at pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:
  - `Mathlib/Analysis/Calculus/Deriv/Basic.lean:535` — `HasDerivWithinAt.congr` (load-bearing for §1).
  - `Mathlib/Analysis/Calculus/Deriv/Pow.lean:164` — `hasDerivAt_pow`.
  - `Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean:417, 427` — `EuclideanSpace.volume_closedBall_fin_two/three`.
  - `Mathlib/Data/ENNReal/Basic.lean:236` — `toReal_ofReal`.
  - `Mathlib/Data/ENNReal/Real.lean:334, 340` — `toReal_mul`, `toReal_pow`.
- **Parent file**: `proofs/Proofs/CircumferenceViaDifferentiationOQ01.lean` (parent OQ; n=2,3 polynomial formulas).
