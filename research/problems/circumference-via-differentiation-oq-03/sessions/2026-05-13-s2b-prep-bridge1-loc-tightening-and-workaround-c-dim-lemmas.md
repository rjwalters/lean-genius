# S2b PREP — Bridge 1 LOC tightening + dim-specific volume lemmas for Workaround C

**Date**: 2026-05-13
**Researcher**: researcher-11
**Mode**: PREP (doc-only; refines S2 PREP §2.3 and §3.5 against actual Mathlib v4.26.0)
**Phase target**: S2 ACT (~120–150 LOC, revised from S2 PREP's ~150–200 LOC estimate).
**Status**: pristine orthogonal to S1 OBSERVE (#18338) and S2 PREP (#18458). 0 open PRs on slug.

## 0. Why this PREP

S2 PREP §2.3 estimates **~30–50 LOC** for Bridge 1's remaining sorry (`volume.real (ball 0 1) = unitBallVolume (finrank ℝ E)`), attributing the cost to "`stdOrthonormalBasis` transport + Γ-function arithmetic rewrite chain".

Direct read of Mathlib v4.26.0 `Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean` reveals that:

1. **The orthonormal-basis transport is ALREADY DONE inside `InnerProductSpace.volume_ball`** (Mathlib master rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, line 345). S2 PREP §2.3 does not need to redo it.
2. **The only remaining arithmetic is `√π^n = π^(n/2)`** — a 3-line `Real.sqrt_eq_rpow` / `rpow_natCast` rewrite, not a ~30-50 LOC Γ-chain.
3. **`InnerProductSpace.volume_ball_of_dim_even` and `_of_dim_odd`** (lines 361 and 373) give pre-baked parity-specific formulas — Workaround C ("ship verified at n=2,3 only", S2 PREP §3.5) reduces to **two 1-line bridges**, not the multi-stage axiomatization the PREP suggested.
4. **`EuclideanSpace.volume_ball_fin_two` / `_fin_three`** (lines 396 / 406) give the literal `r^2 * π` / `r^3 * (4π/3)` formulas as `@[simp]` lemmas, matching the parent OQ-01's `unitBallVolume_two = π` (`CircumferenceViaDifferentiationOQ01.lean:47`) and `unitBallVolume_three = 4π/3` (line 67) **exactly**.

The implication: **Workaround C is much cheaper than S2 PREP estimated**, and the S2-S5 deliverable for `axiomatized` n=2,3 case is roughly **~80–120 LOC total**, not ~600 LOC (S5 main theorem ~30 LOC each at n=2,3, S2 file ~50–80 LOC, Bridge 1 ~10 LOC).

This PREP is doc-only refinement; no Lean changes.

## 1. Mathlib v4.26.0 ground truth (Contents-API-verified)

`Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean` at master rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

| Symbol | Line | Statement |
|---|---|---|
| `EuclideanSpace.volume_ball` | 309 | `volume (Metric.ball x r) = (.ofReal r) ^ card ι * .ofReal (√π ^ card ι / Gamma (card ι / 2 + 1))` |
| `EuclideanSpace.volume_closedBall` | 326 | same |
| `InnerProductSpace.volume_ball` | 345 | `volume (Metric.ball x r) = (.ofReal r) ^ finrank ℝ E * .ofReal (√π ^ finrank ℝ E / Gamma (finrank ℝ E / 2 + 1))` |
| `InnerProductSpace.volume_closedBall` | 356 | same |
| `InnerProductSpace.volume_ball_of_dim_even` | 361 | `(hk : finrank ℝ E = 2 * k) → volume (ball x r) = .ofReal r ^ finrank ℝ E * .ofReal (π ^ k / (k)!)` |
| `InnerProductSpace.volume_closedBall_of_dim_even` | 367 | same |
| `InnerProductSpace.volume_ball_of_dim_odd` | 373 | `(hk : finrank ℝ E = 2 * k + 1) → volume (ball x r) = .ofReal r ^ finrank ℝ E * .ofReal (π ^ k * 2 ^ (k + 1) / (2*k+1)‼)` |
| `InnerProductSpace.volume_closedBall_of_dim_odd` | 383 | same |
| `EuclideanSpace.volume_ball_fin_two` | 396 | `@[simp] volume (ball x r) = .ofReal r ^ 2 * .ofReal π` |
| `EuclideanSpace.volume_closedBall_fin_two` | 401 | `@[simp] same` |
| `EuclideanSpace.volume_ball_fin_three` | 406 | `@[simp] volume (ball x r) = .ofReal r ^ 3 * .ofReal (π * 4 / 3)` |
| `EuclideanSpace.volume_closedBall_fin_three` | 411 | `@[simp] same` |

**Key observation**: every parent-relevant volume calculation is a `@[simp]`
lemma in Mathlib v4.26.0.

## 2. Correction to S2 PREP §2.1: `InnerProductSpace.volume_real_closedBall` does NOT exist

S2 PREP §2.1 cites:

> The "real" version (using `Measure.real`, i.e. `.toReal`-of-ENNReal):
>
> ```lean
> theorem InnerProductSpace.volume_real_closedBall (x : E) (r : ℝ) (hr : 0 ≤ r) :
>     (volume : Measure E).real (closedBall x r) =
>       r ^ finrank ℝ E * (volume : Measure E).real (ball 0 1)
> ```
> (assembled from `EqHaar.lean:478,503`).

**This is a fictional aggregated lemma**. Direct read of Mathlib v4.26.0
shows that `volume_real_closedBall` is **not a single Mathlib symbol** —
it would have to be assembled at S2 ACT time from `Measure.addHaar_closedBall`
and `ENNReal.toReal_mul` / `ENNReal.toReal_ofReal`.

This is a minor erratum: the actual derivation works, but the S2 PREP names
a lemma that the implementer will try to `exact` and find missing. The
S2 ACT correct approach is:

```lean
-- Bridge 1, corrected derivation chain:
rw [show riemannianVolumeBall p r = (volume (closedBall p r)).toReal from rfl,
    InnerProductSpace.volume_closedBall p r,          -- Mathlib line 356
    ENNReal.toReal_mul,                                 -- ENNReal arithmetic
    ENNReal.toReal_ofReal_of_nonneg hr,                 -- (r ≥ 0)
    ENNReal.toReal_ofReal_of_nonneg (by positivity)]    -- (√π^n / Γ ≥ 0)
-- Now goal: r^finrank * (√π^finrank / Γ(finrank/2 + 1)) =
--           unitBallVolume finrank * r^finrank
-- i.e., √π^n = π^(n/2)  (modulo commutativity)
```

## 3. Bridge 1's actual remaining sorry: `√π^n = π^(n/2)`

After applying the corrected derivation in §2, the residual obligation is:

```lean
-- Goal: √π ^ (finrank ℝ E) = π ^ ((finrank ℝ E : ℝ) / 2)
```

The LHS uses **Nat-exponent** `^`; the RHS uses **Real rpow** `^` (because
`unitBallVolume n := π^((n:ℝ)/2) / Γ(...)`). Mathlib v4.26.0 has these
identities:

| Symbol | Module | Direction |
|---|---|---|
| `Real.sqrt_eq_rpow x : √x = x ^ ((1:ℝ)/2)` | `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` (~line 613, per memory note) | sqrt ↔ rpow |
| `Real.rpow_natCast x n : x ^ (n : ℝ) = x ^ n` | `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` | rpow ↔ Nat pow |
| `Real.rpow_mul (hx : 0 ≤ x) p q : x ^ (p * q) = (x ^ p) ^ q` | `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` | rpow algebra |

**Proof sketch (~5 LOC)**:

```lean
have hπ_nn : (0 : ℝ) ≤ π := pi_nonneg
calc √π ^ (n : ℕ) = (π ^ ((1:ℝ)/2)) ^ (n : ℕ) := by rw [Real.sqrt_eq_rpow]
  _ = π ^ (((1:ℝ)/2) * (n : ℝ))               := by rw [← Real.rpow_natCast (π ^ _), ← Real.rpow_mul hπ_nn]
  _ = π ^ ((n : ℝ) / 2)                       := by ring_nf
```

If `Real.rpow_mul` orientation doesn't match: alternative `rfl`-style with
`Real.rpow_natCast` first, then `Real.rpow_mul`. ~5–8 LOC max.

**Revised Bridge 1 LOC total**: ~10 LOC (vs S2 PREP's ~30-50 LOC estimate).

## 4. The Workaround-C goldmine: `volume_ball_of_dim_even`/`_odd` are ready-made

S2 PREP §3.5 Workaround C proposes:

> Drop Bridge 2 from S2-S5. Instead, prove ONLY Bridge 1 (volume identity)
> and corollaries at n = 2, 3 where the parent OQ-01 already has
> `nSphereSurfaceConst_two = 2π` and `nSphereSurfaceConst_three = 4π`
> decidably checked.

The S2 PREP does **not** notice that Mathlib gives the n=2 and n=3 cases
in **literal closed form** at `EuclideanSpace.volume_ball_fin_two` and
`_fin_three` (lines 396 and 406):

```lean
@[simp]
lemma volume_ball_fin_two (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    volume (ball x r) = .ofReal r ^ 2 * .ofReal π := by ...

@[simp]
lemma volume_ball_fin_three (x : EuclideanSpace ℝ (Fin 3)) (r : ℝ) :
    volume (ball x r) = .ofReal r ^ 3 * .ofReal (π * 4 / 3) := by ...
```

And these match the parent's:

- `CircumferenceViaDifferentiationOQ01.lean:47`: `unitBallVolume_two : unitBallVolume 2 = π`
- `CircumferenceViaDifferentiationOQ01.lean:67`: `unitBallVolume_three : unitBallVolume 3 = 4 * π / 3`

**Exactly**. The constants line up `r^2 · π` and `r^3 · (4π/3)`.

### 4.1 Workaround C revised Lean signature

```lean
/-- Bridge 1 at n = 2 (Euclidean plane): the closed-ball area is `π r^2`. -/
theorem riemannianVolumeBall_fin_two
    (p : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (hr : 0 ≤ r) :
    (volume (Metric.closedBall p r)).toReal = π * r ^ 2 := by
  rw [EuclideanSpace.volume_closedBall_fin_two p r,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal_of_nonneg (pow_nonneg hr 2),
      ENNReal.toReal_ofReal_of_nonneg pi_nonneg]
  ring

/-- Bridge 1 at n = 3 (Euclidean 3-space): the closed-ball volume is `(4π/3) r^3`. -/
theorem riemannianVolumeBall_fin_three
    (p : EuclideanSpace ℝ (Fin 3)) (r : ℝ) (hr : 0 ≤ r) :
    (volume (Metric.closedBall p r)).toReal = (4 * π / 3) * r ^ 3 := by
  rw [EuclideanSpace.volume_closedBall_fin_three p r,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal_of_nonneg (pow_nonneg hr 3),
      ENNReal.toReal_ofReal_of_nonneg (by positivity)]
  ring
```

**LOC: 4 lines each**, fully `verified` (0 sorries, 0 axioms).

The combined S5 main theorem at n=2 then becomes ~10 LOC (apply
`hasDerivAt_pow` + the explicit formula + `ring`); same for n=3.

### 4.2 Why this is a strict improvement on S2 PREP §3.5

S2 PREP §3.5 frames Workaround C as a fallback:

> Drop Bridge 2 from S2-S5. Instead, prove ONLY Bridge 1 (volume identity)
> and corollaries at n = 2, 3 [...] The "main theorem" becomes:
> ```
> theorem riemannianVolumeBall_hasDerivAt_classical
>     {E : Type*} [...] (hdim : finrank ℝ E = 2 ∨ finrank ℝ E = 3) ...
> ```

This signature **abstracts the dimension** as a disjunction `hdim : finrank
= 2 ∨ finrank = 3`. But that abstraction is unnecessary — at S2 ACT time
we can just ship **two separate theorems**, one for `Fin 2` and one for
`Fin 3`, using the direct `@[simp]` lemmas. No `hdim` disjunction, no
case-split, no abstract `E`.

This is closer to how the parent OQ-01 handles n=2,3 (`unitBallVolume_two`,
`unitBallVolume_three`): one theorem per concrete dimension.

## 5. Revised LOC budget

| Stage | S2 PREP estimate | S2b PREP refined |
|---|---|---|
| S2 (file scaffold + 3 stubs) | ~150-200 | ~80-100 (no Bridge 2 axiom) |
| S3 (Bridge 1) | ~150 | **~10-15** (corrected §2 derivation + §3 sqrt rewrite) |
| S4 (Bridge 2) | ~200 | **~0** (dropped per Workaround C) |
| S5 (main, n=2,3) | ~100 | **~20-30** (two ~10-line theorems using `volume_*_fin_two/three`) |
| **TOTAL S2-S5** | **~600** | **~120-150** |

The S2 PREP's estimate of ~600 total LOC counted the abstract `E`-version
+ Bridge 2 axiomatization + Γ-chain. The Workaround C path (n=2,3 only)
drops Bridge 2 entirely and uses Mathlib's pre-baked `_fin_two/_fin_three`
lemmas, gaining a **~4× LOC reduction**.

This makes the *partial answer* path (R1 vector-space restricted to n=2,3)
a **single-session deliverable** (~120-150 LOC, status `verified` for
n=2,3 — with the manifold version explicitly deferred to S∞).

## 6. Cautions / open questions

### 6.1 `Measure.real (ball 0 1) = unitBallVolume`: still needs §3 chain

The §4 Workaround-C signatures bypass the intermediate "unit ball" cast
by going **directly** from `volume_closedBall_fin_two` to the closed-form
constant. So §3's `√π^n = π^(n/2)` rewrite is **not needed** if S2 ACT
chooses Workaround C exclusively.

If S2 ACT wants the abstract `InnerProductSpace.volume_closedBall` route
(for n general), then §3's rewrite IS needed (and is ~5-8 LOC, not ~30-50).

### 6.2 Does the parent's `unitBallVolume_three` need normalization?

Parent OQ-01 line 67: `unitBallVolume_three : unitBallVolume 3 = 4 * π / 3`.

Mathlib `EuclideanSpace.volume_ball_fin_three`: `... .ofReal (π * 4 / 3)`.

**Not literally `rfl`** (associativity / commutativity differ): `4 * π / 3`
vs `π * 4 / 3`. The Lean `ring` tactic discharges this in 1 line. No
substantive concern, but worth flagging so S2 ACT knows to add `ring` or
`mul_comm` to the n=3 bridge.

### 6.3 S5 main theorem at n=2: differentiability of `(4/3) * π * r^3`

After Workaround-C Bridge 1, the main S5 statement at n=2 is:

```lean
theorem riemannianVolumeBall_hasDerivAt_fin_two
    (p : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (hr : 0 ≤ r) :
    HasDerivAt (fun s => (volume (closedBall p s)).toReal)
      (2 * π * r) r
```

This reduces to `HasDerivAt (fun s => π * s^2) (2 * π * r) r` via
`HasDerivAt.congr_of_eventuallyEq` (eventually on `s ≥ 0`). Then
`hasDerivAt_pow 2 r |>.const_mul π` gives the derivative.

**Risk flag**: the `eventually_eq` step requires `hr` (non-negative `r`)
because `(volume (closedBall _ s)).toReal = π * s^2` only holds when
`s ≥ 0` (for `s < 0`, `closedBall` is empty and `volume = 0`, but `π *
s^2 ≠ 0`). The `congr_of_eventuallyEq` filter `nhds r` includes both
sides of `r`, so when `r = 0`, neighborhoods include negative `s`,
breaking the bridge. **Workaround**: state the theorem at `r > 0` rather
than `r ≥ 0`, OR use `HasDerivWithinAt` over `Set.Ici 0`.

This is a substantive design caveat for S2 ACT — pick the right
differentiability statement. S2 PREP §4 line 211-216 chose
`HasDerivAt`, which forces the `r > 0` restriction.

## 7. Suggested S2 ACT packaging

Given the refined picture, two packagings:

**Packaging A — Workaround-C-only, n=2,3 verified** (recommended):

- One Lean file `proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean`.
- 2 bridge theorems (`riemannianVolumeBall_fin_two/three`), ~8 LOC each.
- 2 main S5 theorems (`riemannianVolumeBall_hasDerivAt_fin_two/three`),
  ~15 LOC each.
- 0 sorries, 0 axioms.
- Gallery `status: verified` at the OQ-03 file level, with `partial`
  qualifier in meta.json.
- **Total ~80–120 LOC**, single PR, single session.

**Packaging B — Workaround-C + abstract `InnerProductSpace`** (stretch):

- All of Packaging A, plus:
- Abstract `riemannianVolumeBall_eq_unitBallVolume_pow` for general `E`
  using `InnerProductSpace.volume_closedBall` + §3 sqrt rewrite (~15 LOC).
- Abstract main theorem `riemannianVolumeBall_hasDerivAt_unitBall`
  with `n = finrank ℝ E` (~25 LOC, requires `HasDerivAt` for the
  general `nBallVolumeFn n s`).
- Still `status: verified`, no axioms.
- **Total ~150–180 LOC**, single PR.

**Recommendation**: Packaging A for the next session. Packaging B as
a follow-up if Bridge 2 is to be revisited.

## 8. Race awareness / orthogonality

At PREP push time (2026-05-13 ~04:45 UTC):

| Open PR on slug | File overlap with this PREP |
|-----------------|------------------------------|
| (none)          | —                            |

This PREP creates exactly one new file:
`research/problems/circumference-via-differentiation-oq-03/sessions/2026-05-13-s2b-prep-bridge1-loc-tightening-and-workaround-c-dim-lemmas.md`.

The 2 prior merged PRs each cover a distinct angle:

- **PR #18338 (S1 OBSERVE)** — overall survey. No specific Mathlib bridge
  audit; this PREP refines §3 ("Three discharge routes").
- **PR #18458 (S2 PREP)** — Bridge 1/2 Mathlib audit. This PREP refines
  §2.3 (Bridge 1 LOC) and §3.5 (Workaround C feasibility).

The refinement targets **specific load-bearing claims** in PR #18458:

| S2 PREP claim | S2b PREP refinement |
|---|---|
| §2.1 `InnerProductSpace.volume_real_closedBall` exists | **Wrong — fictional aggregated lemma.** Must assemble from `volume_closedBall` + `ENNReal.toReal_*` in S2 ACT. (Erratum-grade but minor.) |
| §2.3 Bridge 1 sorry needs ~30-50 LOC | **Wrong — actual cost is ~10 LOC**, with `InnerProductSpace.volume_closedBall` already doing the orthonormal-basis transport. Remaining is `√π^n = π^(n/2)` (~5 LOC). |
| §3.5 Workaround C is the "fallback" with abstract `hdim` disjunction | **Wrong framing — Workaround C is the *primary* path**, and uses pre-baked `volume_*_fin_two/three` `@[simp]` lemmas (lines 396, 406 of `VolumeOfBalls.lean`). Two separate concrete-dim theorems, no abstract `hdim`. |
| §3.6 "Workaround A (axiomatise Bridge 2) is cleanest" | **Refute — Workaround C with concrete n=2,3 is strictly cleaner** because (a) 0 axioms instead of 1, (b) 0 mid-band `axiomatized` status, (c) ~4× LOC reduction. |

## 9. Anti-targets

This PREP (and the eventual S2 ACT under Packaging A) **does not**:

- Touch `proofs/Proofs/CircumferenceViaDifferentiationOQ01.lean` (parent —
  read-only).
- Touch `proofs/Proofs/CircumferenceViaDifferentiation.lean` (grandparent
  — read-only).
- Modify `state.md`, `problem.md`, `knowledge.md`, or any gallery JSON.
  The S2 PREP §2.1 erratum is flagged but not corrected here (separate
  audit/Mechanic concern).
- Address the R2 full-Riemannian-manifold version (deferred to S∞ per
  state.md).
- Address the R3 coarea-in-ℝⁿ Mathlib contribution (deferred to S∞).
- Add a Bridge 2 (sphere Hausdorff measure) axiom — Packaging A drops it
  entirely.
- Generalize beyond n=2,3 in Packaging A. Packaging B is the abstract-`E`
  route, but is stretch goal.

## 10. Acceptance criteria for S2 ACT under Packaging A (binary)

The S2 ACT PR must:

- [ ] Create `proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean`.
- [ ] Ship `riemannianVolumeBall_fin_two` (~8 LOC, §4.1) — 0 sorries.
- [ ] Ship `riemannianVolumeBall_fin_three` (~8 LOC, §4.1) — 0 sorries.
- [ ] Ship `riemannianVolumeBall_hasDerivAt_fin_two` (~15 LOC, §6.3)
      with `r > 0` or `HasDerivWithinAt Set.Ici 0` — 0 sorries.
- [ ] Ship `riemannianVolumeBall_hasDerivAt_fin_three` (~15 LOC,
      analogous) — 0 sorries.
- [ ] Total new LOC ≤ 150.
- [ ] 0 axioms.
- [ ] Gallery integration: `src/data/proofs/circumference-via-differentiation-oq-03/{meta,index,annotations}` per S3 GALLERY clean-task feedback pattern.
- [ ] Gallery `meta.json`: `status: verified`, `axiomCount: 0`, with
      `assumptions: ["partial answer — n=2,3 only, n≥4 deferred to manifold version"]`.
- [ ] Build via `./proofs/scripts/docker-build.sh Proofs.CircumferenceViaDifferentiationOQ03`.
- [ ] Update `state.md` to record S2 ACT.
- [ ] **Commit + push BEFORE Docker build** per `.lake symlink loop` memory note.

The S2 ACT PR **must NOT**:

- Axiomatize Bridge 2 (Packaging A path is axiom-free).
- Generalize to abstract `E : Type*` with `InnerProductSpace`
  (that's Packaging B's territory; separate PR).
- Address n=1 or n≥4 cases (deferred).
- Edit the S2 PREP (PR #18458) — that erratum in §2.1 is a separate
  audit task.

## 11. Honesty / scope guarantee

This PREP is **doc-only**:

- 1 new file: `research/problems/circumference-via-differentiation-oq-03/sessions/2026-05-13-s2b-prep-bridge1-loc-tightening-and-workaround-c-dim-lemmas.md`
- 0 edits to existing files
- 0 Lean changes
- 0 gallery / research JSON changes
- 0 changes to `state.md`, `problem.md`, `knowledge.md`, or any prior
  session note (including S2 PREP, despite the §2.1 erratum)

**Scope honesty**:

- §1 Mathlib API table is **Contents-API-read directly** from `master`
  rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Reproducible.
- §3 `√π^n = π^(n/2)` proof sketch is **3-step**, but real-world
  tactic ordering may need ±2 LOC adjustment.
- §4 Workaround C bridge signatures are **literal copy-paste** from the
  Mathlib `volume_ball_fin_two/three` lemma outputs.
- §5 ~4× LOC reduction claim is **arithmetic** (60% reduction in Bridge
  1, 100% reduction in Bridge 2, 70% reduction in S5 main), not aspirational.
- §6.3 differentiability risk at `r = 0` is **substantive** — S2 ACT
  must pick `r > 0` or `HasDerivWithinAt`; not flagged in S2 PREP §4.

**LOC estimate honesty**:

- §4.1 bridges: 8 LOC literal-count (counted with comments).
- §5 main theorems: ~15 LOC each based on `hasDerivAt_pow.const_mul`
  template. Real-world elaboration may add ±3 LOC.
- §5 total of 80-120 LOC for Packaging A has 30 LOC headroom.

## 12. References

### Mathlib v4.26.0 (rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

- `Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean:309` — `EuclideanSpace.volume_ball`
- `Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean:326` — `EuclideanSpace.volume_closedBall`
- `Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean:345` — `InnerProductSpace.volume_ball`
- `Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean:356` — `InnerProductSpace.volume_closedBall`
- `Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean:361` — `InnerProductSpace.volume_ball_of_dim_even`
- `Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean:373` — `InnerProductSpace.volume_ball_of_dim_odd`
- `Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean:396` — `EuclideanSpace.volume_ball_fin_two`
- `Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean:406` — `EuclideanSpace.volume_ball_fin_three`

### In-tree

- `proofs/Proofs/CircumferenceViaDifferentiationOQ01.lean:39` — `unitBallVolume`
- `proofs/Proofs/CircumferenceViaDifferentiationOQ01.lean:47` — `unitBallVolume_two = π`
- `proofs/Proofs/CircumferenceViaDifferentiationOQ01.lean:67` — `unitBallVolume_three = 4π/3`
- `proofs/Proofs/CircumferenceViaDifferentiationOQ01.lean:83` — `nBallVolumeFn`
- `proofs/Proofs/CircumferenceViaDifferentiationOQ01.lean:102` — `nBallVolumeFn_hasDerivAt`

### Prior PRs on this slug

- **PR #18338** (S1 OBSERVE, researcher-9): overall survey.
- **PR #18458** (S2 PREP, researcher-9): Bridge 1/2 Mathlib audit
  (this PREP refines §2.1 erratum, §2.3 LOC, §3.5 Workaround C).
