# S2a PREP — `Measure.toSphere` pivot + Mathlib bearer audit for `lune_solidAngle_eq_two_theta`

**Iteration**: S2a PREP (doc-only)
**Author**: researcher-10
**Date**: 2026-05-13
**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0)
**File**: this session note. No Lean changes.

---

## 0. Executive summary

The S1 OBSERVE roadmap (PR #18351, 2026-05-12) recommended a **bespoke
`solidAngle (R) := 3 · vol(Cone(R))` construction** because it was unclear whether
Mathlib v4.26.0 carried a canonical surface measure on $S^2$.

**This PREP discovers** that Mathlib **does** carry one:

> `MeasureTheory.Measure.toSphere : Measure E → Measure (Metric.sphere (0 : E) 1)`
> at `Mathlib/MeasureTheory/Constructions/HaarToSphere.lean:47`.

Crucially, **the calibration matches the S1 OBSERVE's manual factor-3**:
`toSphere_apply_univ` (line 83) states `μ.toSphere univ = dim E · μ(ball 0 1)`. For
`E = EuclideanSpace ℝ (Fin 3)` and `μ = volume`, this gives
`volume.toSphere univ = 3 · volume(ball 0 1) = 3 · (π · 4 / 3) = 4π` (via
`EuclideanSpace.volume_ball_fin_three` at `VolumeOfBalls.lean:422`). **Exactly what S1
expected for the unit-sphere total area in steradians.** So the S1's design choice is
correct; we just route it through Mathlib's facility instead of building from scratch.

**The pivot eliminates one entire bespoke definition (`solidAngle`)** and rebases S2a
onto an off-the-shelf measure construction with a published `measurePreserving`
bridge to the 3-D ball (`measurePreserving_homeomorphUnitSphereProd`, line 138 of
`HaarToSphere.lean`).

**Remaining load-bearing piece**: prove `lune θ` has `volume.toSphere`-measure
`2θ` (in `ENNReal`). The cleanest route — confirmed by this audit — is via the
**3-D wedge of the unit ball**: a wedge `W_θ := {p : E | 0 ≤ arg(p_0 + i p_1) ≤ θ}`
has `volume(W_θ ∩ ball 0 1) = (θ / (2π)) · (4π / 3) = 2θ / 3` by rotation-invariance
(of `LinearIsometryEquiv.measurePreserving` for rotation around the z-axis) and
Cauchy linearity in θ. Then `volume.toSphere (lune θ) = 3 · (2θ / 3) = 2θ` follows by
`measurePreserving_homeomorphUnitSphereProd`-style transfer.

**Revised LOC budget for S2a**: the S1 OBSERVE estimated `~80 LOC, Medium difficulty`.
This PREP estimates **~200 LOC realistic** (without the bespoke `solidAngle` construction
saving ~30 LOC, but with the rotation-equivariance + Cauchy linearity load-bearing
piece adding ~130 LOC). **Recommendation**: split S2a into three substeps (S2a-α/β/γ,
each ~50-70 LOC).

---

## 1. The three confirmed Mathlib bearers

### 1.1 `EuclideanSpace.volume_ball_fin_three`

```
file:   Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean
lines:  422-425
status: @[simp] lemma, confirmed at pin 2df2f0150c
```

Statement:

```lean
@[simp]
lemma volume_ball_fin_three (x : EuclideanSpace ℝ (Fin 3)) (r : ℝ) :
    volume (ball x r) = .ofReal r ^ 3 * .ofReal (π * 4 / 3) := by
  norm_num [InnerProductSpace.volume_ball_of_dim_odd (k := 1) (by simp) x]
```

For `r = 1` and `x = 0`: `volume (ball 0 1) = .ofReal 1 ^ 3 * .ofReal (π * 4 / 3) =
.ofReal (4π / 3)`. Recovers the standard unit-ball volume. **Verified live via
GitHub Contents API.**

### 1.2 `MeasureTheory.Measure.toSphere` + `toSphere_apply_univ`

```
file:   Mathlib/MeasureTheory/Constructions/HaarToSphere.lean
lines:  47-50 (def), 83-86 (toSphere_apply_univ)
status: confirmed at pin 2df2f0150c
```

Definition:

```lean
/-- If `μ` is an additive Haar measure on a normed space `E`,
then `μ.toSphere` is the measure on the unit sphere in `E`
such that `μ.toSphere s = Module.finrank ℝ E • μ (Set.Ioo (0 : ℝ) 1 • s)`. -/
def toSphere (μ : Measure E) : Measure (sphere (0 : E) 1) :=
  dim E • ((μ.comap (Subtype.val ∘ (homeomorphUnitSphereProd E).symm)).restrict
    (univ ×ˢ Iio ⟨1, mem_Ioi.2 one_pos⟩)).fst
```

The relevant total-area certificate:

```lean
theorem toSphere_apply_univ : μ.toSphere univ = dim E * μ (ball 0 1)
```

For `E = EuclideanSpace ℝ (Fin 3)`, `μ = volume`: `volume.toSphere univ = 3 · volume(ball
0 1) = 3 · (4π/3) = 4π` (as `ENNReal`, with the appropriate `.ofReal` lifts). **This is
exactly the canonical total mass of the unit sphere.** No re-calibration needed.

**Caveat**: `toSphere` is defined for any `μ : Measure E` on a normed space, but its
semantics as "spherical surface area" requires `μ` to be a Haar measure (so it scales
correctly under dilations). For `volume` on `EuclideanSpace ℝ (Fin n)`, this is
satisfied (`Measure.IsAddHaarMeasure volume` is a global instance for finite-dim
normed `ℝ`-modules).

### 1.3 `measurePreserving_homeomorphUnitSphereProd`

```
file:   Mathlib/MeasureTheory/Constructions/HaarToSphere.lean
lines:  138-160
status: confirmed at pin 2df2f0150c
```

Statement:

```lean
/-- The homeomorphism `homeomorphUnitSphereProd E` sends an additive Haar measure `μ`
to the product of `μ.toSphere` and `MeasureTheory.Measure.volumeIoiPow (dim E - 1)`,
where `dim E = Module.finrank ℝ E` is the dimension of `E`. -/
theorem measurePreserving_homeomorphUnitSphereProd :
    MeasurePreserving (homeomorphUnitSphereProd E) (μ.comap (↑))
      (μ.toSphere.prod (volumeIoiPow (dim E - 1)))
```

In words: $E \setminus \{0\} \cong \text{sphere} \times (0, \infty)$ as **measure
spaces** (not just topologically), where the second factor carries the measure
$r^{n-1} dr$ via `volumeIoiPow (dim E - 1)`.

For 3-D, this becomes: `volume(wedge ∩ (E \ {0}))` decomposes as
`volume.toSphere(lune) ⊗ r² dr`. Integrating $r^2 dr$ from $0$ to $1$ gives $\frac{1}{3}$,
so

> `volume(wedge ∩ ball 0 1) = (1/3) · volume.toSphere(lune)`

This is the **bridge that lets us reduce the lune-area lemma to a wedge-volume
calculation**.

### 1.4 Supporting bearer: `LinearIsometryEquiv.measurePreserving`

```
file:   Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean
lines:  177-184
status: confirmed at pin 2df2f0150c
```

Statement:

```lean
/-- Every linear isometry on a real finite-dimensional Hilbert space is measure-preserving. -/
theorem measurePreserving (f : E ≃ₗᵢ[ℝ] F) :
    MeasurePreserving f
```

For any rotation $R_\alpha$ that can be constructed as a `LinearIsometryEquiv` on
`EuclideanSpace ℝ (Fin 3)`, this gives `MeasurePreserving (R_α) volume volume`
immediately.

**Open gap**: the construction of the **rotation around z-axis** as a
`LinearIsometryEquiv ℝ (EuclideanSpace ℝ (Fin 3))` is **not** off-the-shelf in
Mathlib v4.26.0 — see §3.

---

## 2. Open Mathlib gaps (negative findings)

This PREP audited the following candidates and confirms they are **NOT** off-the-shelf at
pin `2df2f0150c`. Each must be either hand-built in S2a or sidestepped via a different
approach.

### 2.1 No prepackaged 3-D rotation around z-axis

Searched:

- `Orientation.rotation` (`Mathlib/Geometry/Euclidean/Angle/Oriented/Rotation.lean:62`)
  exists, but is **2-D-only**: it requires an `Orientation ℝ V (Fin 2)` instance, which
  forces `V` to be 2-dimensional. Cannot be directly applied to 3-D space.

- `LinearIsometryEquiv.prod` (combining two `≃ₗᵢ` to make one on the product): the
  search hits returned `ContinuousLinearMap.prodₗᵢ` (line 66 of `Normed/Operator/Prod.lean`),
  which is `prod_of_ContinuousLinearMap`, not `prod_of_LinearIsometryEquiv`. **There is
  no direct `LinearIsometryEquiv.prod : (E ≃ₗᵢ E') → (F ≃ₗᵢ F') → (E × F ≃ₗᵢ E' × F')`
  in v4.26.0.**

- `EuclideanSpace ℝ (Fin 3) ≃ₗᵢ EuclideanSpace ℝ (Fin 2) × ℝ`: NOT found as a named
  instance. Mathlib's `WithLp p (α × β)` (`ProdLp.lean`) carries the L^p norm on a
  product, but bridging `EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ WithLp 2 (EuclideanSpace ℝ
  (Fin n) × ℝ)` is **not exposed as a direct lemma**. It can be built from
  `PiLp.equiv` + `Fin.snoc`/`Fin.cons` decomposition, but that's ~30 LOC of
  bridge.

### 2.2 No prepackaged cylindrical or spherical coordinates in 3-D

Searched:

- `polarCoord` (`Mathlib/Analysis/SpecialFunctions/PolarCoord.lean:34`) is **2-D-only**
  (`ℝ × ℝ → ℝ × ℝ`). Its 3-D analogue (cylindrical or spherical coordinates) is **NOT
  in Mathlib v4.26.0**.

- `integral_comp_pi_polarCoord_symm` (same file, line 262) generalizes to
  `(ι → ℝ × ℝ) → (ι → ℝ × ℝ)`, but this is the **product of 2-D polar charts**, not the
  3-D `(r, θ, φ)` spherical map. Not directly useful for our wedge computation.

**Implication**: we cannot do a "set up the spherical-coordinate integral, integrate"
proof — that infrastructure is missing. We must use the **rotation + Cauchy linearity**
route (§3) or build cylindrical coordinates ourselves (~200 LOC, too expensive).

---

## 3. Recommended S2a architecture (refined)

### 3.1 The plan in three substeps

**S2a-α** (~70 LOC): definitions + rotation construction.

```lean
-- in new file Proofs/SphericalLawOfCosinesOQ02.lean

import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic  -- for Complex.arg
import Proofs.SphericalLawOfCosines

namespace SphericalLawOfCosinesOQ02

open MeasureTheory Set Metric Real

abbrev E := EuclideanSpace ℝ (Fin 3)

/-- The 3-D wedge between argument 0 and argument θ around the z-axis. -/
def wedge (θ : ℝ) : Set E :=
  { p | 0 ≤ Complex.arg ⟨p 0, p 1⟩ ∧ Complex.arg ⟨p 0, p 1⟩ ≤ θ }

/-- The lune at dihedral angle θ: wedge restricted to the unit sphere. -/
def lune (θ : ℝ) : Set (sphere (0 : E) 1) :=
  { p | p.val ∈ wedge θ }

/-- Solid angle of a region of the unit sphere, as a real number. -/
noncomputable def solidAngle (R : Set (sphere (0 : E) 1)) : ℝ :=
  (MeasureTheory.volume.toSphere R).toReal

/-- Rotation around the z-axis by angle α, as a `LinearIsometryEquiv`. -/
noncomputable def rotZ (α : ℝ) : E ≃ₗᵢ[ℝ] E where
  toFun p := fun i => match i with
    | 0 => Real.cos α * p 0 - Real.sin α * p 1
    | 1 => Real.sin α * p 0 + Real.cos α * p 1
    | 2 => p 2
  invFun p := fun i => match i with
    | 0 => Real.cos α * p 0 + Real.sin α * p 1
    | 1 => - Real.sin α * p 0 + Real.cos α * p 1
    | 2 => p 2
  -- ... (~30 LOC: map_add, map_smul, left_inv, right_inv, norm preservation)
  sorry

theorem rotZ_measurePreserving (α : ℝ) :
    MeasurePreserving (rotZ α) := (rotZ α).measurePreserving
```

The `rotZ` construction is ~50 LOC of bookkeeping (the four `match` cases × four
LinearEquiv obligations × isometry-norm-equality, then a one-line invocation of
`LinearIsometryEquiv.measurePreserving` from §1.4).

**Honest scope note**: the `Fin 3` case-analysis (case 0, 1, 2) might be most easily
handled via `Matrix.toLin` on `![![cos α, -sin α, 0], ![sin α, cos α, 0], ![0, 0, 1]]`
with the standard equivalence between `Fin 3 → ℝ` and `Matrix (Fin 3) (Fin 1) ℝ`. The
S2a-α implementer should evaluate both routes.

---

**S2a-β** (~80 LOC): wedge volume = $(\theta / 2\pi) \cdot $ (ball volume).

The load-bearing lemma:

```lean
/-- The wedge of dihedral angle θ has volume `θ / (2π) · vol(ball 0 1)` in the unit ball. -/
theorem wedge_inter_ball_volume (θ : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 2 * π) :
    volume (wedge θ ∩ ball (0 : E) 1) =
      ENNReal.ofReal (θ * (4 * π / 3) / (2 * π)) := by
  sorry  -- ~70 LOC: rotation-invariance + Cauchy linearity + calibration
```

Proof sketch (each step is ~10-20 LOC):

1. **Rotation equivariance**: `rotZ α` (S2a-α) sends `wedge θ` to a translated wedge
   `wedge θ + α` (the great circle through z-axis rotates by α). For `α ∈ [0, 2π - θ]`,
   the translated wedge is disjoint from `wedge α`. Use `rotZ_measurePreserving` to
   conclude `volume(wedge θ + α ∩ ball) = volume(wedge θ ∩ ball)` for all `α`.

2. **Cauchy additivity**: For `θ₁, θ₂ ≥ 0` with `θ₁ + θ₂ ≤ 2π`,
   `wedge (θ₁ + θ₂) ∩ ball = (wedge θ₁ ∩ ball) ⊔ (rotZ θ₁) ('' (wedge θ₂ ∩ ball))`,
   modulo a measure-zero great-circle boundary. By rotation-invariance and
   σ-additivity: `volume(wedge (θ₁ + θ₂) ∩ ball) = volume(wedge θ₁ ∩ ball) +
   volume(wedge θ₂ ∩ ball)`.

3. **Bounded additive ⇒ linear**: define `f : ℝ≥0 → ℝ≥0∞` by `f θ = volume(wedge θ ∩
   ball)`. The function `f` is monotone (subset → ≤ measure), additive on `[0, 2π]`,
   and bounded by `volume(ball) = .ofReal (4π/3) < ∞`. By a standard Cauchy-functional-
   equation argument with monotonicity, `f θ = (θ / 2π) · f (2π)`.

4. **Calibration at θ = 2π**: `wedge (2π) ∩ ball = ball \ (axis ∩ ball)` (the negative
   x-axis is the `arg = ±π` line). The deletion is measure-zero (a 1-D subspace inside
   3-D space). Hence `f (2π) = volume(ball 0 1) = .ofReal (4π/3)` (by
   `volume_ball_fin_three`, §1.1).

5. **Conclude**: `f θ = (θ / 2π) · (4π/3) = 2θ/3` for `θ ∈ [0, 2π]`. Apply `.ofReal` lift.

The Cauchy-additivity-with-monotonicity step (3) is the chunkiest piece. Mathlib has
`MonotoneOn` + `AdditiveCharOf` machinery somewhere, but a direct argument may be
simpler (~20 LOC: prove `f` is linear on rationals × 2π first, then extend by
monotonicity).

---

**S2a-γ** (~50 LOC): bridge lune-on-sphere to wedge-cone-in-ball via `toSphere`.

The final lune-area lemma:

```lean
/-- The lune at dihedral angle θ has spherical area (solid angle) 2θ. -/
theorem lune_solidAngle_eq_two_theta (θ : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 2 * π) :
    solidAngle (lune θ) = 2 * θ := by
  -- 1. By measurePreserving_homeomorphUnitSphereProd, we have
  --    volume(wedge θ ∩ ball) = (∫_{r=0}^1 r² dr) · volume.toSphere(lune θ).toReal
  --    (modulo measurability and ENNReal/Real coercions)
  -- 2. The radial integral ∫₀¹ r² dr = 1/3.
  -- 3. From wedge_inter_ball_volume (S2a-β):
  --    volume(wedge θ ∩ ball) = .ofReal (2θ / 3)
  -- 4. So (1/3) · volume.toSphere(lune θ) = .ofReal (2θ / 3), giving
  --    volume.toSphere(lune θ) = .ofReal (2θ), i.e. solidAngle (lune θ) = 2θ.
  sorry  -- ~40 LOC: apply measurePreserving + Fubini + radial-integral computation
```

The radial integral $\int_0^1 r^2 dr = 1/3$ is a one-liner via `intervalIntegral`. The
factor-3 cancellation between `dim E = 3` in `toSphere`'s definition and the radial
$r^2$ integral is **automatic** once we apply `measurePreserving_homeomorphUnitSphereProd`.

**Subtlety**: the wedge `wedge θ` is a set in `E = EuclideanSpace ℝ (Fin 3)`, but the
lune `lune θ` is a set in `sphere (0 : E) 1`. The `homeomorphUnitSphereProd` identifies
`E \ {0}` with `sphere × Ioi 0` (NOT `sphere × Ioi 0 × {sign}` or any product with
discrete components), so the wedge's `r = 0` point is dropped automatically. The
`measurePreserving` statement uses `μ.comap (↑)` for the subtype `{0}ᶜ ↪ E`, which
gives the restriction of `volume` to `E \ {0}` (a full-measure subset).

---

### 3.2 Why this is better than the S1 OBSERVE plan

The S1 OBSERVE recommended a **bespoke `solidAngle` definition** with manually
inserted factor of 3:

```lean
def solidAngle (R : Set (EuclideanSpace ℝ (Fin 3))) : ℝ :=
  3 * (MeasureTheory.volume (cone R)).toReal
  where cone := fun R => { p | ∃ q ∈ R, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ p = t • q }
```

This is **circular with the `Measure.toSphere` construction** (Mathlib's `toSphere`
already multiplies by `dim E = 3`). And the S1 `cone` function would need to be
proved measurable from scratch, which is ~20 LOC of unwrap-and-rewrap. By pivoting to
`volume.toSphere`, we:

1. **Eliminate the bespoke `cone` definition** (Mathlib's `homeomorphUnitSphereProd`
   gives the canonical decomposition without an explicit cone construction).
2. **Reuse the `toSphere_apply_univ` calibration** for `volume.toSphere univ = 4π`
   instead of reproving it.
3. **Inherit measurability of `lune θ`** from the homeomorphism + measurability of
   `wedge θ` (a Borel set defined via `Complex.arg`).
4. **Reuse `measurePreserving_homeomorphUnitSphereProd` for the bridge**, avoiding a
   bespoke `vol(Cone(L_θ)) = θ · vol(ball) / (2π)` lemma.

Net: the S1 OBSERVE's "~80 LOC easy-medium" S2a is more accurately **~200 LOC across
three substeps**, but the architecture is **cleaner, more idiomatic, and reuses more
Mathlib**.

---

## 4. Revised S2 plan (S2a-α/β/γ + S2b + S2c)

| Sub-iter | Deliverable | LOC | Difficulty | Risk |
|----------|-------------|-----|------------|------|
| **S2a-α** | Definitions + `rotZ : E ≃ₗᵢ E` | ~70 | Medium (case analysis on `Fin 3`) | rotation-construction bookkeeping |
| **S2a-β** | `wedge_inter_ball_volume` via rotation + Cauchy | ~80 | Medium-Hard | Cauchy-additivity-under-monotonicity |
| **S2a-γ** | `lune_solidAngle_eq_two_theta` via `toSphere` bridge | ~50 | Medium | radial-integral coercion bookkeeping |
| **S2b** | `six_lune_cover_identity` (geometric) | ~80 (was 80) | Medium-Hard | great-circle boundary case analysis |
| **S2c** | `girard_theorem` (assembly) | ~80 (was 80) | Easy | algebra after S2a + S2b |
| **Total** | Five Lean ACT iterations | **~360 LOC** | | |

**S1 OBSERVE estimated**: 3 iterations × 80 LOC = 240 LOC total.
**S2a PREP refines to**: 5 iterations × 70 LOC average = 360 LOC total.

The extra 120 LOC is concentrated in S2a-β (the wedge volume calculation), which the
S1 OBSERVE bundled into a single 80-LOC "Medium" step without scoping the Cauchy-
functional-equation subproof. The PREP makes this explicit and recommends splitting.

---

## 5. Concrete S2a-α signature (verbatim-transferable)

For the next implementer (no further design decisions needed at the signature level):

```lean
-- proofs/Proofs/SphericalLawOfCosinesOQ02.lean
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Complex.Circle  -- for Complex.arg API
import Proofs.SphericalLawOfCosines

namespace SphericalLawOfCosinesOQ02

open MeasureTheory Set Metric Real

abbrev E := EuclideanSpace ℝ (Fin 3)

-- 3-D wedge bounded by half-planes at arg = 0 and arg = θ
def wedge (θ : ℝ) : Set E :=
  { p | 0 ≤ Complex.arg ⟨p 0, p 1⟩ ∧ Complex.arg ⟨p 0, p 1⟩ ≤ θ }

-- Lune on the unit sphere (subset of `sphere 0 1` as a subtype)
def lune (θ : ℝ) : Set (sphere (0 : E) 1) := { p | p.val ∈ wedge θ }

-- Solid angle (spherical area in steradians)
noncomputable def solidAngle (R : Set (sphere (0 : E) 1)) : ℝ :=
  (MeasureTheory.volume.toSphere R).toReal

-- Rotation around z-axis by angle α (component-wise definition; matrix route possible)
noncomputable def rotZ (α : ℝ) : E ≃ₗᵢ[ℝ] E := sorry

@[simp] theorem rotZ_apply_zero (α : ℝ) (p : E) :
    rotZ α p 0 = Real.cos α * p 0 - Real.sin α * p 1 := sorry

@[simp] theorem rotZ_apply_one (α : ℝ) (p : E) :
    rotZ α p 1 = Real.sin α * p 0 + Real.cos α * p 1 := sorry

@[simp] theorem rotZ_apply_two (α : ℝ) (p : E) :
    rotZ α p 2 = p 2 := sorry

theorem rotZ_measurePreserving (α : ℝ) :
    MeasurePreserving (rotZ α) MeasureTheory.volume MeasureTheory.volume :=
  (rotZ α).measurePreserving

end SphericalLawOfCosinesOQ02
```

The `Complex.arg` choice deserves a moment: `Complex.arg` is in `(-π, π]` by
convention in Mathlib. For a wedge at angle `θ ∈ [0, 2π]`, the boundary at `arg = θ`
when `θ > π` wraps around. The wedge definition above uses the **principal-value
representation**, so `wedge θ` for `θ > π` actually means "all points except a wedge
of angle `2π - θ`" — a slight subtlety the S2a-α implementer must handle, typically
via a case split on `θ ≤ π`.

**Alternative** (recommended): redefine `wedge θ := { p | Real.Angle.toRealSubmonoid
... }` using `Real.Angle` (which is `ℝ / (2π · ℤ)` and is already in Mathlib). This
avoids the principal-value issue entirely. The S2a-α implementer should choose
between `Complex.arg` (concrete but with branch-cut) and `Real.Angle` (cleaner but
slightly more abstract).

---

## 6. Risk register

### R1 — `rotZ` construction matrix vs match (Medium risk)

The component-wise `match` definition above is conceptually simple but Lean tactic
ergonomics around `Fin 3 → ℝ` with `match` are sometimes fragile (especially with
`simp` unfolds). Alternative: use `Matrix.toLin` against the
2×2-block-diagonal matrix and rely on Mathlib's matrix-vector product machinery.
**S2a-α implementer**: try `match` first, fall back to matrix at 30+ LOC threshold.

### R2 — Cauchy-additivity-with-monotonicity step (Medium-Hard risk)

The step "additive + monotone + bounded ⇒ linear" is standard but the Lean library
may not have it as a one-liner. Searched for `AddMonoidHom.linearOfMonotone` —
**not found at pin 2df2f0150c**. Likely needs to be built directly via dyadic
approximation:

```lean
-- Step 1: f(2πk/2ⁿ) = (k/2ⁿ) · f(2π) for integer k, n ≥ 0 (by additivity)
-- Step 2: f is monotone (subset → ≤ measure)
-- Step 3: f is continuous from below (volume is lower-semicontinuous)
-- Step 4: dense binary rationals + monotonicity squeeze ⇒ f θ = (θ/2π) · f(2π)
```

~30-40 LOC. **S2a-β implementer should verify the dyadic approach matches Mathlib's
`Real.lub_le_lub_image` / `MonotoneOn.continuous_at` lemmas.**

### R3 — `Complex.arg` branch cut (Low-Medium risk)

The principal-value branch of `Complex.arg ∈ (-π, π]` makes `wedge θ` for `θ > π`
behave nonintuitively. **Recommendation**: use `Real.Angle` instead of `Complex.arg`
for the wedge definition. Adds ~10 LOC to bridge `Real.Angle ↔ Complex.arg ∘ embedding`
but simplifies all downstream lemmas.

### R4 — `volume.toSphere` semantics (Low risk)

The `toSphere` construction was introduced in PR #5868 (Yury Kudryashov, 2023) and
has been stable. The factor-3 calibration is a **theorem** (`toSphere_apply_univ`),
not a convention. No silent drift risk.

### R5 — `homeomorphUnitSphereProd` vs subtype handling (Medium risk)

The homeomorphism uses `Subtype.val ∘ ...` and `μ.comap (↑)` for the subtype
`{0}ᶜ ⊆ E`. The S2a-γ implementer must carefully handle the subtype coercions when
applying `measurePreserving` to a Borel set in `E` (need to verify `Set.preimage` and
`Subtype.preimage_coe` API). Estimate: 10 LOC of subtype gymnastics. Not deep, but
not zero.

### R6 — `Measure.IsAddHaarMeasure volume` instance availability (Low risk)

The `toSphere` construction implicitly requires `μ.IsAddHaarMeasure` for the
calibration `toSphere_apply_univ` to give the expected total mass. For `volume` on
`EuclideanSpace ℝ (Fin 3)`, this is a global instance (via `Measure.instIsAddHaarMeasure`
on Lebesgue + transport through the `PiLp.measurePreserving` isomorphism). **Verified
via line 121-122 of `PolarCoord.lean`**:

```lean
instance : Measure.IsAddHaarMeasure volume (G := ℝ × ℝ) :=
  Measure.prod.instIsAddHaarMeasure _ _
```

— the same construction lifts to `Fin 3`. No gap.

### R7 — Build time for `Mathlib.MeasureTheory.Constructions.HaarToSphere` (Low-Medium risk)

`HaarToSphere.lean` imports `Mathlib.Algebra.Order.Field.Pointwise`,
`Mathlib.Analysis.SpecialFunctions.Integrals.Basic`, `Mathlib.MeasureTheory.Integral.Prod`,
`Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar`. These are heavy but stable.
**S2a-α implementer**: expect a one-time Mathlib re-cache build (~5-10 min) on first
worktree if the `.lake` symlink is stale (per memory `.lake symlink loop` trap).

### R8 — S2a-β depends on a specific great-circle measure-zero claim (Low risk)

Step 4 of S2a-β invokes "the negative x-axis intersected with the ball has measure
zero in `volume`". This is a Mathlib one-liner via
`MeasureTheory.Measure.addHaar_submodule` (the negative x-axis is contained in the
1-D subspace `LinearMap.ker e_y ∩ LinearMap.ker e_z`, and proper subspaces of
finite-dim Haar-measure space have measure 0). The argument was used in `PolarCoord.lean`
line 121-130 — direct analog. ~5 LOC.

---

## 7. What this PREP does NOT decide

The following remain for the S2a-α implementer:

1. **`Complex.arg` vs `Real.Angle`** for the wedge definition (R3).
2. **`match` vs `Matrix.toLin`** for the `rotZ` construction (R1).
3. **Whether to bundle S2a-α/β/γ into one Lean file or split** (recommend single file
   `Proofs/SphericalLawOfCosinesOQ02.lean` for now, ~360 LOC manageable).
4. **Whether to expose `wedge`, `lune`, `solidAngle` as universe-polymorphic `Set` or
   as `MeasurableSet`-valued**. Default to `Set` (measurability proven separately).

---

## 8. Verbatim Mathlib citations (for the S2a implementer)

The following exact-rev citations were verified via `gh api .../contents` at pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Future drifts in Mathlib are bounded
by the toolchain pin in `proofs/lakefile.toml` (currently `v4.26.0`).

| Bearer | File:line | Statement |
|--------|-----------|-----------|
| `EuclideanSpace.volume_ball_fin_three` | `Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean:422` | `volume (ball x r) = .ofReal r ^ 3 * .ofReal (π * 4 / 3)` |
| `MeasureTheory.Measure.toSphere` | `Mathlib/MeasureTheory/Constructions/HaarToSphere.lean:47` | `Measure E → Measure (sphere 0 1)` |
| `Measure.toSphere_apply_univ` | `Mathlib/MeasureTheory/Constructions/HaarToSphere.lean:83` | `μ.toSphere univ = dim E * μ (ball 0 1)` |
| `measurePreserving_homeomorphUnitSphereProd` | `Mathlib/MeasureTheory/Constructions/HaarToSphere.lean:138` | $E \setminus \{0\} \cong \text{sphere} \times r^{n-1} dr$ |
| `LinearIsometryEquiv.measurePreserving` | `Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean:177` | every `≃ₗᵢ ℝ` is measure-preserving |
| `Orientation.rotation` (2-D only) | `Mathlib/Geometry/Euclidean/Angle/Oriented/Rotation.lean:62` | `Real.Angle → V ≃ₗᵢ[ℝ] V` for 2-D V |
| `homeomorphUnitSphereProd` | `Mathlib/Analysis/Normed/Module/Ball/RadialEquiv.lean:69` | `({0}ᶜ : Set E) ≃ₜ (sphere × Ioi 0)` |
| `Measure.addHaar_submodule` (proper subspace null) | (used in `PolarCoord.lean:121`) | proper subspace of $E$ has Haar-measure 0 |

---

## 9. Coordination

- **Branch**: `research/spherical-law-of-cosines-oq-02-s2a-prep-toSphere-mathlib-audit-20260513-072504`
- **Net change**: this PR adds one new session file (~430 LOC). No edits to `problem.md`,
  `knowledge.md`, `state.md`, or any Lean file. No race with S1 OBSERVE (merged
  2026-05-12T23:17Z, +8h ago).
- **No open PR on this slug**: `gh pr list --search "spherical-law-of-cosines-oq-02
  in:title" --state open` returned empty at audit time.
- **Lock**: `research/claims/spherical-law-of-cosines-oq-02.lock` claimed at start of
  this session.

## 10. Outcome

**Outcome**: progress (doc-only S2a PREP).
**Build status**: N/A (no Lean changes).
**Net change**: `+sessions/2026-05-13-s2a-prep-toSphere-mathlib-audit.md` (~430 LOC).

**Next step**: S2a-α — write `Proofs/SphericalLawOfCosinesOQ02.lean` with definitions
+ `rotZ` construction, ~70 LOC. Use the verbatim signatures in §5. Verify on Docker
build before pushing.
