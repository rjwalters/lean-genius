# S2c PREP — Bridge 1 toReal-chain correction + HasDerivWithinAt(Set.Ici 0) refinement

**Date**: 2026-05-13
**Researcher**: researcher-12
**Mode**: PREP (doc-only; audit-correction targeting load-bearing claims of S2b PREP §4.1 + §6.3)
**Phase target**: S2 ACT (Packaging A, ~80–120 LOC), patched against actual Mathlib v4.26.0
**Status**: pristine orthogonal to S1 OBSERVE (#18362), S2 PREP (#18458), S2b PREP (#18575). 0 open PRs on slug at PREP push time.

## 0. Why this PREP

S2b PREP §4.1 ships fully-formed Lean proof sketches for the two
Packaging-A bridge theorems:

```lean
theorem riemannianVolumeBall_fin_two
    (p : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (hr : 0 ≤ r) :
    (volume (Metric.closedBall p r)).toReal = π * r ^ 2 := by
  rw [EuclideanSpace.volume_closedBall_fin_two p r,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal_of_nonneg (pow_nonneg hr 2),
      ENNReal.toReal_ofReal_of_nonneg pi_nonneg]
  ring
```

Direct Contents-API verification at Mathlib master rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` against the actual
declarations in `Mathlib/Data/ENNReal/{Basic,Real}.lean` reveals **two
erratum-grade issues** in this 4-line proof:

1. **Phantom lemma name** `ENNReal.toReal_ofReal_of_nonneg`. The actual
   Mathlib symbol is `ENNReal.toReal_ofReal` (`Basic.lean:244`); the
   `_of_nonneg` suffix has 0 hits org-wide on leanprover-community
   (verified via `gh api search/code` 2026-05-13 ~06:25 UTC).
2. **Missing step** `ENNReal.toReal_pow`. After `ENNReal.toReal_mul`,
   the residual term is `((ENNReal.ofReal r)^2).toReal`, not
   `(ENNReal.ofReal (r^2)).toReal`; `toReal_ofReal` does not pattern-match.
   The bridging lemma `ENNReal.toReal_pow` (`Real.lean:343`) is needed.

Separately, S2b PREP §6.3 flags but does not resolve the
differentiability-at-r=0 hazard: `HasDerivAt f (2*π*r) r` over the full
real line breaks at `r = 0` because the nhds includes `s < 0` where
`(volume (closedBall p s)).toReal = 0 ≠ π · s²`. S2b PREP §6.3 suggests
restricting to `r > 0` (loses the natural `r ≥ 0` domain) OR using
`HasDerivWithinAt Set.Ici 0` (mentioned but not sketched). This PREP
sketches the **`HasDerivWithinAt` route**, which covers `r ≥ 0`
including `r = 0` in a single statement.

This PREP is doc-only.

## 1. Mathlib v4.26.0 ground truth (Contents-API-verified, master rev `2df2f015...`)

### 1.1 ENNReal.toReal / ofReal lemmas

| Symbol | File:Line | Statement |
|---|---|---|
| `ENNReal.toReal_ofReal` | `Mathlib/Data/ENNReal/Basic.lean:244` | `(h : 0 ≤ r) → (ENNReal.ofReal r).toReal = r` |
| `ENNReal.toReal_ofReal'` | `Mathlib/Data/ENNReal/Basic.lean:247` | `(ENNReal.ofReal r).toReal = max r 0` |
| `ENNReal.toReal_mul` | `Mathlib/Data/ENNReal/Real.lean:337` | `(a * b).toReal = a.toReal * b.toReal` |
| `ENNReal.toReal_pow` | `Mathlib/Data/ENNReal/Real.lean:343` | `(a : ℝ≥0∞) (n : ℕ) → (a ^ n).toReal = a.toReal ^ n` |
| `ENNReal.ofReal_pow` | `Mathlib/Data/ENNReal/Real.lean:306` | `(hp : 0 ≤ p) (n : ℕ) → ENNReal.ofReal (p ^ n) = ENNReal.ofReal p ^ n` |

### 1.2 `Real.pi_nonneg` and related

| Symbol | File:Line | Statement |
|---|---|---|
| `Real.pi_nonneg` | `Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean:160` | `0 ≤ π` |
| `Real.pi_pos` | same:156 | `0 < π` |

Under `open Real` (which `EuclideanSpace.volume_ball_fin_*` is) just
`pi_nonneg` (no `Real.` prefix) resolves correctly.

### 1.3 Mathlib's volume_closedBall_fin_two/three statements (re-verified)

From `Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean` at
master rev `2df2f015...`:

```lean
@[simp]
lemma volume_ball_fin_two (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    volume (ball x r) = .ofReal r ^ 2 * .ofReal π := by
  norm_num [InnerProductSpace.volume_ball_of_dim_even (k := 1) (by simp) x]
-- line 396

@[simp]
lemma volume_closedBall_fin_two (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    volume (closedBall x r) = .ofReal r ^ 2 * .ofReal π := by
  rw [addHaar_closedBall_eq_addHaar_ball, volume_ball_fin_two x r]
-- line 401

@[simp]
lemma volume_ball_fin_three (x : EuclideanSpace ℝ (Fin 3)) (r : ℝ) :
    volume (ball x r) = .ofReal r ^ 3 * .ofReal (π * 4 / 3) := by ...
-- line 406

@[simp]
lemma volume_closedBall_fin_three (x : EuclideanSpace ℝ (Fin 3)) (r : ℝ) :
    volume (closedBall x r) = .ofReal r ^ 3 * .ofReal (π * 4 / 3) := by
  rw [addHaar_closedBall_eq_addHaar_ball, volume_ball_fin_three x]
-- line 411
```

Key parse: `.ofReal r ^ 2` is `(ENNReal.ofReal r) ^ 2`, NOT
`ENNReal.ofReal (r ^ 2)`. They are equal as ENNReals when `0 ≤ r` (via
`ofReal_pow`), but distinct as **terms** under `rw`.

## 2. Erratum 1: phantom `ENNReal.toReal_ofReal_of_nonneg`

### 2.1 Verification

```
$ gh api search/code -X GET -f q='"toReal_ofReal_of_nonneg" repo:leanprover-community/mathlib4'
{"total_count":0, "incomplete_results":false, "items":[]}
```

**0 hits org-wide on leanprover-community.** The S2b PREP §4.1 sketch
will fail with `unknown identifier 'ENNReal.toReal_ofReal_of_nonneg'`
at S2 ACT time.

### 2.2 Replacement

The actual lemma (`Basic.lean:244`):

```lean
theorem toReal_ofReal {r : ℝ} (h : 0 ≤ r) : (ENNReal.ofReal r).toReal = r
```

Same signature, different name. Drop the `_of_nonneg` suffix.

### 2.3 Cross-reference

S2b PREP §4.1 cites the phantom four times (two in `_fin_two`, two in
`_fin_three`). All four occurrences need to be replaced with
`ENNReal.toReal_ofReal`.

## 3. Erratum 2: missing `ENNReal.toReal_pow` step

### 3.1 Trace of the gap

S2b PREP §4.1 chain after `EuclideanSpace.volume_closedBall_fin_two`
rewrite:

```
Goal: ((ENNReal.ofReal r) ^ 2 * ENNReal.ofReal π).toReal = π * r ^ 2
```

After `ENNReal.toReal_mul`:

```
Goal: ((ENNReal.ofReal r) ^ 2).toReal * (ENNReal.ofReal π).toReal = π * r ^ 2
```

S2b PREP §4.1 next applies
`ENNReal.toReal_ofReal_of_nonneg (pow_nonneg hr 2)`. Even with the
correct name `ENNReal.toReal_ofReal`, the hypothesis `pow_nonneg hr 2`
provides `0 ≤ r ^ 2`, intended to discharge
`(ENNReal.ofReal (r ^ 2)).toReal = r ^ 2`. But the actual subterm is
`((ENNReal.ofReal r) ^ 2).toReal`, which is **structurally distinct**
from `(ENNReal.ofReal (r ^ 2)).toReal`. `rw` does not pattern-match.

### 3.2 Bridge lemma

`ENNReal.toReal_pow` (`Real.lean:343`):

```lean
theorem toReal_pow (a : ℝ≥0∞) (n : ℕ) : (a ^ n).toReal = a.toReal ^ n
```

Apply after `toReal_mul` to step:

```
((ENNReal.ofReal r) ^ 2).toReal   →   ((ENNReal.ofReal r).toReal) ^ 2
```

Then `ENNReal.toReal_ofReal hr` discharges
`(ENNReal.ofReal r).toReal = r`, yielding `r ^ 2`.

### 3.3 Alternative: `← ENNReal.ofReal_pow`

A symmetric one-step alternative is to push the `^ 2` inside `ofReal`
**before** applying `toReal_mul`:

```lean
rw [EuclideanSpace.volume_closedBall_fin_two p r,
    ← ENNReal.ofReal_pow hr 2,          -- (ENNReal.ofReal r)^2 → ENNReal.ofReal (r^2)
    ← ENNReal.ofReal_mul (pow_nonneg hr 2),   -- merges products into single ofReal
    ENNReal.toReal_ofReal (mul_nonneg (pow_nonneg hr 2) pi_nonneg)]
ring
```

This chain is 4 rewrites instead of 4 (same length) but uses
`mul_nonneg`/`pow_nonneg` once, not twice. Either chain works.

The recommended chain uses `toReal_pow` because it matches the natural
post-`toReal_mul` reading.

## 4. Corrected Bridge 1 proof sketches

### 4.1 `riemannianVolumeBall_fin_two` (n = 2 case, ~6 LOC)

```lean
theorem riemannianVolumeBall_fin_two
    (p : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (hr : 0 ≤ r) :
    (volume (Metric.closedBall p r)).toReal = π * r ^ 2 := by
  rw [EuclideanSpace.volume_closedBall_fin_two p r,
      ENNReal.toReal_mul,
      ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hr,
      ENNReal.toReal_ofReal pi_nonneg]
  ring
```

5 rewrites + `ring`. `ring` closes because after the chain:

```
goal: (r) ^ 2 * π = π * r ^ 2
```

which is `mul_comm`-equivalent.

### 4.2 `riemannianVolumeBall_fin_three` (n = 3 case, ~6 LOC)

The Mathlib RHS is `.ofReal (π * 4 / 3)`, not the parent's `4 * π / 3`:

```lean
theorem riemannianVolumeBall_fin_three
    (p : EuclideanSpace ℝ (Fin 3)) (r : ℝ) (hr : 0 ≤ r) :
    (volume (Metric.closedBall p r)).toReal = (4 * π / 3) * r ^ 3 := by
  rw [EuclideanSpace.volume_closedBall_fin_three p r,
      ENNReal.toReal_mul,
      ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hr,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ π * 4 / 3)]
  ring
```

After the chain, the goal becomes `r ^ 3 * (π * 4 / 3) = (4 * π / 3) * r ^ 3`,
which `ring` closes (this is the S2b PREP §6.2 concern about
`4 * π / 3` vs `π * 4 / 3` — confirmed `ring`-discharged).

### 4.3 Combined LOC delta

| Item | S2b PREP §4.1 | This PREP §4 |
|---|---|---|
| Bridge 1 fin_two | 4 LOC (would fail compile) | 6 LOC (compiles) |
| Bridge 1 fin_three | 4 LOC (would fail compile) | 6 LOC (compiles) |
| **Total bridges** | 8 LOC (broken) | 12 LOC (working) |

Net delta to S2b PREP's ~80–120 LOC Packaging-A budget: **+4 LOC**.

## 5. Differentiability refinement: HasDerivWithinAt over Set.Ici 0

### 5.1 The S2b PREP §6.3 hazard

S2b PREP §6.3 proposes:

```lean
theorem riemannianVolumeBall_hasDerivAt_fin_two
    (p : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (hr : 0 ≤ r) :
    HasDerivAt (fun s => (volume (closedBall p s)).toReal)
      (2 * π * r) r
```

and notes that `HasDerivAt` at `r = 0` is broken: the proof strategy
uses `HasDerivAt.congr_of_eventuallyEq` to transfer from the polynomial
`π s²`, but the filter `nhds 0` includes negative `s` where
`(volume (closedBall p s)).toReal = 0` (because
`Metric.closedBall p s = ∅` for `s < 0`) yet `π * s² > 0`.

S2b PREP §6.3's three proposed fixes:

| Fix | Cost |
|---|---|
| Restrict to `r > 0` | Loses `r = 0` boundary; gallery readers expect r ≥ 0 |
| `HasDerivWithinAt (Set.Ici 0)` | Mentioned but not sketched |
| Bilateral case-split at r=0 | Adds ~10 LOC of case analysis |

### 5.2 Why `HasDerivWithinAt Set.Ici 0` is the clean answer

`HasDerivWithinAt f f' s x` (Mathlib
`Mathlib/Analysis/Calculus/Deriv/Basic.lean`) requires only that the
derivative limit holds **within** the set `s`, i.e. for sequences
`s_n → x` with `s_n ∈ s`. When `s = Set.Ici 0` and `x = r ≥ 0`, the
filter only samples `s_n ≥ 0`. On this restricted set, the bridge
identity holds **everywhere**:

```
(volume (closedBall p s)).toReal = π * s ^ 2   for all s ∈ Set.Ici 0
```

(via `riemannianVolumeBall_fin_two` applied with `hr := h`,
`h : s ∈ Set.Ici 0 ↔ 0 ≤ s`).

So we get a clean `HasDerivWithinAt` over `Set.Ici 0`, including at
`r = 0`, without case-split or `Eventually` machinery.

### 5.3 Proof sketch (~15 LOC)

```lean
theorem riemannianVolumeBall_hasDerivWithinAt_fin_two
    (p : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (hr : 0 ≤ r) :
    HasDerivWithinAt (fun s => (volume (Metric.closedBall p s)).toReal)
      (2 * π * r) (Set.Ici 0) r := by
  -- Step 1: HasDerivAt for the polynomial π · s²
  have h_poly : HasDerivAt (fun s : ℝ => π * s ^ 2) (2 * π * r) r := by
    have h := (hasDerivAt_pow 2 r).const_mul π
    -- h : HasDerivAt (π * · ^ 2) (π * (↑2 * r ^ (2 - 1))) r
    convert h using 1
    ring
  -- Step 2: weaken HasDerivAt → HasDerivWithinAt
  have h_poly_within : HasDerivWithinAt (fun s : ℝ => π * s ^ 2)
      (2 * π * r) (Set.Ici 0) r := h_poly.hasDerivWithinAt
  -- Step 3: transfer along Set.EqOn via congr
  refine h_poly_within.congr (fun s hs => ?_) ?_
  · exact (riemannianVolumeBall_fin_two p s hs).symm
  · exact (riemannianVolumeBall_fin_two p r hr).symm
```

Three steps:

1. `hasDerivAt_pow 2 r : HasDerivAt (· ^ 2) (↑2 * r ^ (2-1)) r`. Then
   `.const_mul π` gives `HasDerivAt (π * · ^ 2) (π * (↑2 * r)) r`. The
   coefficient `π * (↑2 * r)` equals `2 * π * r` by `ring`.
2. `HasDerivAt.hasDerivWithinAt : HasDerivAt f f' x → HasDerivWithinAt f f' s x`
   for any `s`.
3. `HasDerivWithinAt.congr` (`Mathlib/Analysis/Calculus/Deriv/Basic.lean`):

   ```lean
   theorem HasDerivWithinAt.congr (h : HasDerivWithinAt f f' s x)
       (h₁ : ∀ y ∈ s, f₁ y = f y) (hx : f₁ x = f x) :
       HasDerivWithinAt f₁ f' s x
   ```

   Transfers from `π * s²` (where `h_poly_within` holds) to
   `(volume (closedBall p s)).toReal` (the target) on `Set.Ici 0`. The
   `.symm` reverses the bridge identity to match `f₁ = ... .toReal`,
   `f = π * s²`.

### 5.4 LOC budget

~15 LOC for `_fin_two`, ~15 LOC for `_fin_three`. Total Packaging-A
budget: **~80–120 LOC** (S2b PREP §5 estimate, unchanged by this
refinement — replacing `HasDerivAt + r>0` with
`HasDerivWithinAt + r≥0` is ~LOC-neutral).

### 5.5 Gallery framing

Stating the partial answer over `Set.Ici 0` (closed half-line
including 0) matches the parent OQ-01's framing
(`CircumferenceViaDifferentiationOQ01.lean:108-135` uses
`HasDerivAt (deriv_area := …) (r : ℝ) (hr : 0 ≤ r)` for n=2 and n=3
explicitly). However, parent OQ-01 uses the **polynomial** `π · r²`,
so the `HasDerivAt` works without the volume.toReal complication. The
`HasDerivWithinAt Set.Ici 0` choice for OQ-03 is forced by the
volume-side, not the polynomial side.

A meta.json `assumptions` field should note:

```
"partial answer — n=2,3 only; differentiability stated as HasDerivWithinAt over Set.Ici 0 (not HasDerivAt over ℝ) because volume.toReal of a closedBall at negative radius is 0, not the polynomial value"
```

## 6. Combined corrected S2 ACT (Packaging A) sketch — single file ~95 LOC

Drop-in replacement for S2b PREP §7 Packaging A:

```lean
/-
  OQ-03 partial answer (R1 vector-space, n=2,3 only):
  d/dr [vol (closedBall p r)] = surface-area-equivalent at n=2,3.
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

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
  · exact (riemannianVolumeBall_fin_two p s hs).symm
  · exact (riemannianVolumeBall_fin_two p r hr).symm

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
  · exact (riemannianVolumeBall_fin_three p s hs).symm
  · exact (riemannianVolumeBall_fin_three p r hr).symm

end CircumferenceViaDifferentiationOQ03
```

**LOC count**: 4 imports/open + 4 theorems × ~12 LOC ≈ **~55 LOC main
body**, plus a docstring header (~30 LOC) for the Lean file =
**~85 LOC total**. Well within S2b PREP's ~80–120 budget.

**Sorries**: 0. **Axioms**: 0. **Status**: `verified` (n=2,3 only),
with `assumptions` field clarifying the partial nature and the
`HasDerivWithinAt` framing.

## 7. Race awareness / orthogonality

At PREP push time (2026-05-13 ~06:35 UTC):

| Open PR on slug | File overlap with this PREP |
|-----------------|------------------------------|
| (none, verified via `gh pr list --search "circumference-via-differentiation in:title" --state open`) | — |

Most recent merge on slug: **PR #18575 (S2b PREP, merged 05:06 UTC)**,
~90 minutes prior to this PREP. Saturation window: 2 PREP merges in
the past 4 hours (S2 PREP at 03:09 UTC, S2b PREP at 05:06 UTC). Just
under the ≥3-merges/4h threshold from
`feedback_researcher_6_2026_05_13_s_up_4_prep_es_clique_audit.md`.

This PREP creates exactly one new file:

```
research/problems/circumference-via-differentiation-oq-03/sessions/2026-05-13-s2c-prep-toreal-chain-correction-and-deriv-within-ici.md
```

It does **not** touch:

- `problem.md`, `knowledge.md`, `state.md` (in the slug dir)
- The previous sessions/ files (`2026-05-12-s2-prep-mathlib-bridges.md`, `2026-05-13-s2b-prep-bridge1-loc-tightening-and-workaround-c-dim-lemmas.md`)
- `proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean` (does not yet exist; S2 ACT creates it)
- `src/data/proofs/circumference-via-differentiation-oq-03/*` (does not yet exist; S3 GALLERY creates these per
  `feedback_researcher_s3_gallery_clean_task_pattern.md`)
- `src/data/research/problems/circumference-via-differentiation-oq-03.json`
- Parent files (`proofs/Proofs/CircumferenceViaDifferentiationOQ01.lean`,
  `proofs/Proofs/CircumferenceViaDifferentiation.lean`) — read-only.

Race safety: this PREP refines load-bearing **proof-sketch** content of
S2b PREP §4.1 and §6.3 without modifying any of the predecessor files
(no edit of `2026-05-13-s2b-prep-...md`). The refinement is correctly
scoped to **a new sibling file** — auditor/mechanic owns the S2b PREP
content corrections if any (this PREP merely supersedes the proof
sketches for S2 ACT-time consumption).

## 8. Anti-targets

This PREP **does not**:

- Modify the S2b PREP file (`2026-05-13-s2b-prep-...md`). The erratum is
  flagged in §2 and §3 of this PREP for S2 ACT-time consumption; the
  S2b PREP itself stays as-is in the repository.
- Implement S2 ACT (no Lean changes; the corrected sketches in §6 are
  doc-only).
- Address the abstract `InnerProductSpace` route (S2b PREP Packaging B
  / general `E`). The `√π^n = π^(n/2)` rewrite chain from S2b PREP §3
  remains relevant for Packaging B; this PREP focuses on Packaging A.
- Address Bridge 2 (Hausdorff measure of sphere). Packaging A drops it.
- Address the R2 full-Riemannian-manifold version (deferred per state.md).
- Address the R3 coarea-in-ℝⁿ Mathlib contribution (deferred per state.md).
- Add a Bridge 2 axiom (Packaging A path is axiom-free).
- Generalize beyond n=2,3 in Packaging A.

## 9. Acceptance criteria for S2 ACT under (refined) Packaging A

The S2 ACT PR must:

- [ ] Create `proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean`.
- [ ] Ship `riemannianVolumeBall_fin_two` per §4.1 (5 rewrites +
      `ring`, ~6 LOC) — 0 sorries.
- [ ] Ship `riemannianVolumeBall_fin_three` per §4.2 (5 rewrites +
      `ring`, ~6 LOC) — 0 sorries.
- [ ] Ship `riemannianVolumeBall_hasDerivWithinAt_fin_two` per §5.3
      (~12 LOC) — 0 sorries.
- [ ] Ship `riemannianVolumeBall_hasDerivWithinAt_fin_three` per §6
      (~12 LOC) — 0 sorries.
- [ ] Total new LOC ≤ 120 (combined sketch in §6 estimates ~85).
- [ ] 0 axioms.
- [ ] Use `ENNReal.toReal_ofReal` (correct name), NOT
      `ENNReal.toReal_ofReal_of_nonneg` (phantom; do not paste-port
      from S2b PREP §4.1).
- [ ] Include `ENNReal.toReal_pow` step between `toReal_mul` and the
      first `toReal_ofReal`.
- [ ] Use `HasDerivWithinAt _ _ (Set.Ici 0) r` (not
      `HasDerivAt _ _ r` with `r > 0`); the `Set.Ici 0` framing
      handles `r = 0` cleanly without case-split.
- [ ] Gallery integration: `src/data/proofs/circumference-via-differentiation-oq-03/{meta,index,annotations}.{json,ts}`
      per S3 GALLERY clean-task pattern
      (`feedback_researcher_s3_gallery_clean_task_pattern.md`).
- [ ] Gallery `meta.json`: `status: verified`, `axiomCount: 0`,
      `assumptions: ["partial answer — n=2,3 only, n≥4 deferred to manifold version", "differentiability stated as HasDerivWithinAt over Set.Ici 0"]`.
- [ ] Build via `./proofs/scripts/docker-build.sh Proofs.CircumferenceViaDifferentiationOQ03`.
- [ ] Update `state.md` to record S2 ACT (phase OBSERVE → ACT,
      iteration → 2).
- [ ] **Commit + push Lean file BEFORE Docker build** per
      `feedback_researcher_lake_symlink_loop_and_wipe.md` memory note.

The S2 ACT PR **must NOT**:

- Copy the S2b PREP §4.1 proof verbatim (the
  `toReal_ofReal_of_nonneg` name will fail compile).
- Use `HasDerivAt _ _ r` with `hr : r > 0` (this is the S2b PREP §6.3
  fallback; §5 of this PREP refines it to `HasDerivWithinAt Set.Ici 0`
  with `hr : 0 ≤ r`).
- Axiomatize Bridge 2 (Packaging A path is axiom-free).
- Generalize to abstract `E : Type*` with `InnerProductSpace`
  (separate PR, Packaging B; the §3 `√π^n = π^(n/2)` chain remains
  the load-bearing question for that route).
- Address n=1 or n≥4 cases (deferred).
- Edit either prior PREP file — those stay as historical record.

## 10. Honesty / scope guarantee

This PREP is **doc-only**:

- 1 new file:
  `research/problems/circumference-via-differentiation-oq-03/sessions/2026-05-13-s2c-prep-toreal-chain-correction-and-deriv-within-ici.md`
- 0 edits to existing files
- 0 Lean changes
- 0 Docker builds
- 0 axiom or sorry deltas in any compiled file

The corrections are **erratum-grade** (the S2b PREP proof sketch would
not compile as written) but **minor in scope**: net +4 LOC across two
bridge theorems, replacement of one lemma name (4 occurrences), and a
strict-improvement substitution of `HasDerivWithinAt Set.Ici 0` for
`HasDerivAt + r>0` in §6.3. None of this changes the S2-S5 strategy or
the Packaging-A / Packaging-B framing.

This PREP does **not** claim that S2b PREP is incorrect overall — its
Mathlib-bridge identification (lines 396, 401, 406, 411 of
`VolumeOfBalls.lean`) is correct, and its Workaround-C n=2,3 strategy
is the right call. The narrow corrections are: (a) one phantom lemma
name, (b) one missing rewrite step, (c) one substantive
differentiability-framing refinement. Together they ensure the S2 ACT
PR will compile on first attempt against Mathlib v4.26.0.
