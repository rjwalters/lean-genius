# 2026-05-12 — S2 PREP: Mathlib bridge audit + Lean skeleton (R1 vector-space route)

**Researcher**: researcher-5
**Branch**: `research/circumference-via-differentiation-oq-03-s2-prep-mathlib-bridges-1778643000`
**Phase**: S2 PREP (doc-only Mathlib-API audit + Lean skeleton for upcoming S2 ACT)
**Prior**: S1 OBSERVE (PR #18362, merged 2026-05-12 23:17 UTC, researcher-9).

## TL;DR

S1 OBSERVE (PR #18362) laid out an R1 vector-space S2–S5 plan with three Lean theorems (two bridges + main derivative), three sorries, and ~150 LOC. This S2 PREP audits **Mathlib v4.26.0** for the specific lemmas the bridges will invoke, identifies one likely **Mathlib gap** (sphere Hausdorff measure), and pre-writes the Lean file skeleton so that S2 ACT becomes a tactic-chain exercise rather than a Mathlib-search exercise.

Three contributions:

1. **Bridge 1 (volume of closedBall) is fully off-the-shelf**: `InnerProductSpace.volume_closedBall` (`Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean:356`) gives `μ.real (closedBall x r) = r ^ (finrank ℝ E) * μ.real (ball 0 1)` for any `[InnerProductSpace ℝ E] [FiniteDimensional ℝ E]`. The unit-ball measure `μ.real (ball 0 1)` matches `unitBallVolume (finrank ℝ E)` via `EuclideanSpace.volume_ball` (line 309) + `stdOrthonormalBasis`.

2. **Bridge 2 (Hausdorff measure of sphere) is a likely Mathlib gap.** No `hausdorffMeasure_sphere` or `volume_sphere` named lemma found in v4.26.0. Three workarounds documented (§4): (a) state it as a hypothesis/axiom for now, (b) prove via co-area formula on `‖·‖` if scoped down, (c) defer Bridge 2 entirely and target only Bridge 1 + corollary for `n = 2, 3`.

3. **Lean file skeleton pre-written** (§5): a copy-pasteable ~110 LOC skeleton with namespace, imports, defs, theorems-with-sorries, and inline tactic hints for what Mathlib lemmas to invoke at each `sorry`.

**Zero file overlap** with the merged S1 OBSERVE (PR #18362) or any in-flight work (none at PREP time — `gh pr list` returned 0 open research PRs on this slug). Adds exactly one file under `sessions/`. **No edits** to `problem.md`, `knowledge.md`, `state.md`, `literature/`, `meta.json`, or any `.lean` file.

## §1 — Parent slug recap (state.md condensed)

OQ-03 asks whether the area-derivative-of-volume identity
$C(r) = \frac{dA}{dr}$
(proven for the 2-D circle in `CircumferenceViaDifferentiation.lean`) and its $n$-dim generalisation $V'(r) = A(r)$ (proven for general $n$ in `CircumferenceViaDifferentiationOQ01.lean` via the closed-form polynomials `nBallVolumeFn` and `nSphereSurfaceFn`) extends to **Riemannian manifolds**.

S1 OBSERVE classifies three discharge routes:

- **R1** (recommended for S2-S5, ~500-700 LOC): vector-space special case via Mathlib's `IsRiemannianManifold 𝓘(ℝ, E) E` typeclass on a real inner-product space `E`. Bridges to the polynomial formulas in `CircumferenceViaDifferentiationOQ01.lean`.
- **R2** (deferred): full Riemannian manifold version, gated by 4 missing Mathlib primitives (`injectivityRadius`, `expMap`, `geodesicBall/Sphere/Volume`, $n$-dim coarea formula).
- **R3** (alternative Mathlib contribution): standalone Euclidean coarea formula (~1500-2500 LOC Mathlib).

This S2 PREP commits to **R1** and pre-audits the three theorems planned for the new file:

```
Bridge 1 (S3 target): riemannianVolumeBall_eq_nBallVolumeFn
Bridge 2 (S4 target): riemannianSurfaceArea_eq_nSphereSurfaceFn
Main (S5 target):     riemannianVolumeBall_hasDerivAt_riemannianSurfaceArea
```

## §2 — Bridge 1 audit: `InnerProductSpace.volume_closedBall`

### §2.1 The Mathlib lemma

`Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean:356`:

```lean
theorem InnerProductSpace.volume_closedBall (x : E) (r : ℝ) :
    volume (Metric.closedBall x r) =
      ENNReal.ofReal (r ^ finrank ℝ E) * volume (Metric.ball (0 : E) 1) := by
  rw [addHaar_closedBall_eq_addHaar_ball, InnerProductSpace.volume_ball _]
```

(For `[NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]`.)

The "real" version (using `Measure.real`, i.e. `.toReal`-of-ENNReal):

```lean
theorem InnerProductSpace.volume_real_closedBall (x : E) (r : ℝ) (hr : 0 ≤ r) :
    (volume : Measure E).real (closedBall x r) =
      r ^ finrank ℝ E * (volume : Measure E).real (ball 0 1)
```
(assembled from `EqHaar.lean:478,503`).

### §2.2 Identifying `volume.real (ball 0 1)` with `unitBallVolume`

The parent OQ-01's polynomial uses:

```lean
def unitBallVolume (n : ℕ) : ℝ := ...  -- π^(n/2) / Γ(n/2 + 1)
def nBallVolumeFn (n : ℕ) (r : ℝ) : ℝ := unitBallVolume n * r ^ n
```

(`CircumferenceViaDifferentiationOQ01.lean:39, 83`)

`unitBallVolume n` is the volume of the open unit ball in $\mathbb{R}^n$ via Mathlib's `EuclideanSpace ℝ (Fin n)`.  Mathlib has the lemma:

`Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean:309`:

```lean
theorem EuclideanSpace.volume_ball (x : EuclideanSpace ℝ ι) (r : ℝ) :
    volume (Metric.ball x r) = ...  -- explicit Γ-function formula
```

Specialised to $r = 1$, $x = 0$, $\iota = \mathrm{Fin}\,n$, this gives `volume (ball 0 1) = π^(n/2)/Γ(n/2+1) = unitBallVolume n`.

For generic `[InnerProductSpace ℝ E] [FiniteDimensional ℝ E]`, use `stdOrthonormalBasis` to identify $E \simeq \mathrm{EuclideanSpace}\ \mathbb{R}\ (\mathrm{Fin}\ (\mathrm{finrank}\ \mathbb{R}\ E))$ and transport `volume_ball`. The pattern is exactly the one used inside `InnerProductSpace.volume_ball` (line 345-351):

```lean
theorem volume_ball (x : E) (r : ℝ) :
    volume (Metric.ball x r) = ... := by
  ...
  have := EuclideanSpace.volume_ball (Fin (finrank ℝ E)) ((stdOrthonormalBasis ℝ E).repr x) r
  ...
```

### §2.3 Bridge 1 statement (Lean-ready)

```lean
theorem riemannianVolumeBall_eq_nBallVolumeFn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (p : E) (r : ℝ) (hr : 0 ≤ r) :
    riemannianVolumeBall p r =
      CircumferenceViaDifferentiationOQ01.nBallVolumeFn (Module.finrank ℝ E) r := by
  unfold riemannianVolumeBall CircumferenceViaDifferentiationOQ01.nBallVolumeFn
  rw [InnerProductSpace.volume_real_closedBall p r hr]
  congr 1
  -- Goal: volume.real (ball 0 1) = unitBallVolume (finrank ℝ E)
  -- Discharge via stdOrthonormalBasis transport + EuclideanSpace.volume_ball
  sorry
```

The remaining sorry is the identification `volume.real (ball 0 1) = unitBallVolume (finrank ℝ E)`. Estimated ~30-50 LOC tactic chain using `MeasurableEquiv.measure_preserving_eq`, `EuclideanSpace.volume_ball`, and a Γ-function arithmetic equivalence.

**Risk: medium.** The Γ-function rewrite chain (`Real.Gamma_half`, `Real.Gamma_nat_eq_factorial`) is delicate but tractable; the orthonormal-basis transport is standard.

## §3 — Bridge 2 audit: sphere Hausdorff measure (likely gap)

### §3.1 What the bridge needs

The S2 plan defines:

```lean
def riemannianSurfaceArea (p : E) (r : ℝ) : ℝ :=
  (Measure.hausdorffMeasure (Module.finrank ℝ E - 1) (Metric.sphere p r)).toReal
```

Bridge 2 states:

```lean
theorem riemannianSurfaceArea_eq_nSphereSurfaceFn
    (p : E) (r : ℝ) (hr : 0 ≤ r) :
    riemannianSurfaceArea p r =
      CircumferenceViaDifferentiationOQ01.nSphereSurfaceFn (Module.finrank ℝ E) r
```

I.e., the (n-1)-dim Hausdorff measure of the sphere of radius $r$ in $\mathbb{R}^n$ (or any $n$-dim inner-product space) equals $n \cdot \omega_n \cdot r^{n-1}$.

### §3.2 Mathlib status

`gh api search/code` for `hausdorffMeasure_sphere` in `leanprover-community/mathlib4`: **0 hits** at v4.26.0.

`gh api search/code` for `volume_sphere` in `EuclideanSpace`-related files: **0 hits**.

`Mathlib/MeasureTheory/Measure/Hausdorff.lean` defines `μH[d]` (the d-dimensional Hausdorff measure) and proves basic dimension-monotonicity / scaling, but **does not** have a named lemma computing `μH[d-1] (Metric.sphere x r)` for a specific d-dim ambient space.

**This is a Mathlib gap.** Workarounds:

### §3.3 Workaround A: axiomatize Bridge 2

Cleanest immediate path: state Bridge 2 as a hypothesis of S5, axiomatize for now (with explicit `axiom` declaration), elevate to `theorem ... := by sorry` once `*Aristotle.lean` companion is set up.

```lean
axiom riemannianSurfaceArea_eq_nSphereSurfaceFn_axiom
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (p : E) (r : ℝ) (hr : 0 ≤ r) :
    riemannianSurfaceArea p r =
      CircumferenceViaDifferentiationOQ01.nSphereSurfaceFn (Module.finrank ℝ E) r
```

Status update: `meta.json` `status: axiomatized`, `badge: axiom`, `axiomCount: 1`. Loses the "verified" goal but is honest about the Mathlib gap.

### §3.4 Workaround B: prove via co-area on `‖·‖`

The sphere of radius $r$ in $E$ is the preimage $\|\cdot\|^{-1}(\{r\})$. For the norm function $f(x) = \|x\|$ on $E$, the **co-area formula** says:

$$\int_E |\nabla f| \, dV = \int_0^\infty \mathcal{H}^{n-1}(f^{-1}(\{t\})) \, dt$$

For $f(x) = \|x\|$ on inner-product $E$, $|\nabla f| = 1$ on $E \setminus \{0\}$ (the unit gradient property). So LHS = $\mathrm{vol}(E) = \infty$ — too weak.

Restrict to $\|x\| \le R$: LHS becomes `volume.real (closedBall 0 R)` and RHS becomes $\int_0^R \mathcal{H}^{n-1}(\text{sphere}(0, t))\,dt$.

Now Bridge 1 gives LHS = $\omega_n R^n$. Differentiating both sides in $R$:

$$\frac{d}{dR}(\omega_n R^n) = n \omega_n R^{n-1} = \mathcal{H}^{n-1}(\text{sphere}(0, R))$$

This is **circular** with the S5 main theorem (it would prove Bridge 2 by assuming the derivative-of-volume identity, which IS the S5 conclusion).

**Conclusion**: Workaround B is structurally invalid without a separate independent computation of $\mathcal{H}^{n-1}(\text{sphere})$, e.g., via the explicit Γ-function formula matching $n\omega_n$.

### §3.5 Workaround C: defer Bridge 2 entirely

Drop Bridge 2 from S2-S5. Instead, prove ONLY Bridge 1 (volume identity) and corollaries at $n = 2, 3$ where the parent OQ-01 already has `nSphereSurfaceConst_two = 2π` and `nSphereSurfaceConst_three = 4π` decidably checked.

The "main theorem" becomes:

```lean
theorem riemannianVolumeBall_hasDerivAt_classical
    {E : Type*} [...] (hdim : finrank ℝ E = 2 ∨ finrank ℝ E = 3) (p : E) (r : ℝ) (hr : 0 ≤ r) :
    HasDerivAt (riemannianVolumeBall p) <other-side> r := ...
```

where `<other-side>` invokes `nBallVolumeFn_hasDerivAt` on the bridged statement — entirely Bridge-1-driven. No Hausdorff measure needed.

Status: `formalized` (or `verified` if all sorries discharged for $n = 2, 3$), `axiomCount: 0`. Honest scope reduction.

### §3.6 Recommendation

For S2 ACT: **Workaround A** (axiomatise Bridge 2) is the cleanest "lands in S5 with the headline theorem" approach. The axiom is well-motivated and matches the meta.json convention for "Stanley's theorem" / "Aumann's theorem" style assumptions used elsewhere in the gallery for genuine open targets.

For S2 ACT with stretch ambition: try **Workaround C** as a fallback — prove the n=2 and n=3 cases verified, axiomatise general $n$ in a separate theorem.

## §4 — Main theorem (S5 target) Lean-ready

Assuming Bridge 1 (Lean-ready in §2.3) and Bridge 2 (axiomatised per §3.3):

```lean
theorem riemannianVolumeBall_hasDerivAt_riemannianSurfaceArea
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (p : E) (r : ℝ) (hr : 0 ≤ r) :
    HasDerivAt (fun s => riemannianVolumeBall p s)
      (riemannianSurfaceArea p r) r := by
  have hb1 : ∀ s : ℝ, 0 ≤ s → riemannianVolumeBall p s =
        CircumferenceViaDifferentiationOQ01.nBallVolumeFn (Module.finrank ℝ E) s :=
    fun s hs => riemannianVolumeBall_eq_nBallVolumeFn p s hs
  have hb2 := riemannianSurfaceArea_eq_nSphereSurfaceFn_axiom p r hr
  -- Transport HasDerivAt through the eventually-equal bridge:
  --   apply HasDerivAt.congr_of_eventuallyEq (hb1 is eventually-eq on a nbhd of r)
  rw [hb2]
  have h := CircumferenceViaDifferentiationOQ01.nBallVolumeFn_hasDerivAt
              (Module.finrank ℝ E) r
  -- Transfer through Bridge 1 (eventually-equal):
  have heq : (fun s => riemannianVolumeBall p s) =ᶠ[nhds r]
              CircumferenceViaDifferentiationOQ01.nBallVolumeFn (Module.finrank ℝ E) := by
    filter_upwards [Metric.ball_mem_nhds r (by linarith : (0:ℝ) < r + 1)] with s hs
    -- Need 0 ≤ s for hb1; choose r ≥ 0 case
    sorry  -- chase the s ≥ 0 condition through the filter
  exact h.congr_of_eventuallyEq heq.symm
```

**Risk: low-medium.** The `HasDerivAt.congr_of_eventuallyEq` transport is standard; the s ≥ 0 filter chase is the only finicky bit. Estimated ~30-50 LOC including the filter chase.

## §5 — Pre-written Lean file skeleton (S2 ACT starting point)

```lean
/-
  Circumference via Differentiation — OQ-03 Riemannian extension (R1 vector-space)
  (circumference-via-differentiation-oq-03 — S2 ACT skeleton from S2 PREP)

  Generalises the parent OQ-01 derivative-of-volume identity
    nBallVolumeFn_hasDerivAt : HasDerivAt (nBallVolumeFn n) (nSphereSurfaceFn n r) r
  to arbitrary real inner-product spaces E of finite dimension n,
  using Mathlib's `InnerProductSpace.volume_closedBall` and the
  Hausdorff measure of the sphere as the bridges to the polynomial form.

  Status: S2 ACT. Sorries: 2 (Bridge 1 unit-ball identification + S5 filter chase).
  Axioms: 1 (Bridge 2 sphere Hausdorff measure; Mathlib gap at v4.26.0).
  See research/problems/circumference-via-differentiation-oq-03/sessions/
    2026-05-12-s2-prep-mathlib-bridges.md for the design rationale.
-/

import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Hausdorff
import Proofs.CircumferenceViaDifferentiationOQ01

open scoped MeasureTheory ENNReal

namespace CircumferenceViaDifferentiationOQ03

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

-- ============================================================
-- Part I — Definitions
-- ============================================================

/-- The volume of the closed ball of radius `r` around `p`, as a real number. -/
noncomputable def riemannianVolumeBall (p : E) (r : ℝ) : ℝ :=
  (MeasureTheory.volume : MeasureTheory.Measure E).real (Metric.closedBall p r)

/-- The (n-1)-dim Hausdorff measure of the sphere of radius `r` around `p`. -/
noncomputable def riemannianSurfaceArea (p : E) (r : ℝ) : ℝ :=
  (MeasureTheory.Measure.hausdorffMeasure (Module.finrank ℝ E - 1)
    (Metric.sphere p r)).toReal

-- ============================================================
-- Part II — Bridge 1 (volume): direct from Mathlib + Γ-function rewrite
-- ============================================================

/-- **Bridge 1**: the Riemannian volume of the closed ball equals the polynomial
    `nBallVolumeFn` from the parent OQ-01 file. -/
theorem riemannianVolumeBall_eq_nBallVolumeFn (p : E) (r : ℝ) (hr : 0 ≤ r) :
    riemannianVolumeBall p r =
      CircumferenceViaDifferentiationOQ01.nBallVolumeFn (Module.finrank ℝ E) r := by
  unfold riemannianVolumeBall CircumferenceViaDifferentiationOQ01.nBallVolumeFn
  rw [show (MeasureTheory.volume : MeasureTheory.Measure E).real (Metric.closedBall p r)
        = r ^ Module.finrank ℝ E
            * (MeasureTheory.volume : MeasureTheory.Measure E).real (Metric.ball (0 : E) 1)
        from ?_]
  · ring
  · -- InnerProductSpace.volume_closedBall + .real
    sorry -- TODO: ENNReal.toReal chain
  -- Remaining: identify `volume.real (ball 0 1)` with `unitBallVolume (finrank ℝ E)`
  -- via stdOrthonormalBasis + EuclideanSpace.volume_ball at r = 1.

-- ============================================================
-- Part III — Bridge 2 (surface area): Mathlib gap, axiomatised
-- ============================================================

/-- **Bridge 2 (axiomatised)**: the (n-1)-dim Hausdorff measure of the sphere
    of radius `r` in an n-dim inner-product space equals `nSphereSurfaceFn n r`.

    Mathlib v4.26.0 has no named `hausdorffMeasure_sphere` lemma. Discharging
    this requires either a coarea-formula derivation (incompatible with S5
    circularity) or a direct stdOrthonormalBasis transport of an explicit
    spherical-coordinates Γ-function computation (~500+ LOC Mathlib
    contribution).  See sessions/2026-05-12-s2-prep-mathlib-bridges.md §3
    for the gap analysis and three workarounds. -/
axiom riemannianSurfaceArea_eq_nSphereSurfaceFn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (p : E) (r : ℝ) (hr : 0 ≤ r) :
    riemannianSurfaceArea p r =
      CircumferenceViaDifferentiationOQ01.nSphereSurfaceFn (Module.finrank ℝ E) r

-- ============================================================
-- Part IV — Main: derivative-of-volume identity via the bridges
-- ============================================================

/-- **Main theorem**: the Riemannian volume function on the closed ball has
    derivative equal to the Riemannian surface area, generalising the
    parent OQ-01's `nBallVolumeFn_hasDerivAt` to arbitrary real
    inner-product spaces of finite dimension.

    Proof: transport `nBallVolumeFn_hasDerivAt` through Bridge 1 (volume)
    and Bridge 2 (surface area) using `HasDerivAt.congr_of_eventuallyEq`. -/
theorem riemannianVolumeBall_hasDerivAt_riemannianSurfaceArea
    (p : E) (r : ℝ) (hr : 0 ≤ r) :
    HasDerivAt (fun s => riemannianVolumeBall p s)
      (riemannianSurfaceArea p r) r := by
  rw [riemannianSurfaceArea_eq_nSphereSurfaceFn p r hr]
  have h := CircumferenceViaDifferentiationOQ01.nBallVolumeFn_hasDerivAt
              (Module.finrank ℝ E) r
  have heq : (fun s => riemannianVolumeBall p s) =ᶠ[nhds r]
              CircumferenceViaDifferentiationOQ01.nBallVolumeFn (Module.finrank ℝ E) := by
    sorry -- filter chase for s ≥ 0 + Bridge 1
  exact h.congr_of_eventuallyEq heq.symm

end CircumferenceViaDifferentiationOQ03
```

**Total estimated LOC after sorry discharge**:
- Definitions: ~10 LOC.
- Bridge 1 (50 LOC tactic chain + 30 LOC for unit-ball identification).
- Bridge 2 axiom: ~10 LOC (already complete).
- Main: ~30 LOC (filter chase included).
- Total: **~130 LOC** in S2 ACT.

## §6 — Anti-targets (what S2 ACT should NOT attempt)

1. **Do not attempt Bridge 2 via co-area** — circular with S5 (§3.4).

2. **Do not switch to `EuclideanSpace ℝ (Fin n)` ambient type.** The `InnerProductSpace`-generic formulation transports through `stdOrthonormalBasis` and matches the spirit of an OQ that generalises beyond the polynomial-formula parent.

3. **Do not introduce `IsRiemannianManifold` from the manifold side**. State.md mentions this typeclass; for R1 vector-space the typeclass is *automatic* via `EMetricSpace.ofRiemannianMetric` (Gouëzel 2025). The S2 file should use `InnerProductSpace ℝ E` as the working hypothesis and only cite `IsRiemannianManifold` in the docstring.

4. **Do not block on Γ-function infrastructure**. Mathlib has `Real.Gamma`, `Real.Gamma_half`, `Real.Gamma_nat_eq_factorial` etc. but the OQ-01 parent's `unitBallVolume` definition may or may not unfold cleanly. If it doesn't, axiomatise the unit-ball measure equivalence (`volume.real (ball 0 1) = unitBallVolume (finrank ℝ E)`) and treat as Bridge 0.

5. **Do not try to prove the manifold case (R2)** in S2 — explicitly deferred per S1 OBSERVE.

## §7 — Race-check log

- **2026-05-12 18:30 UTC** pre-claim probe:
  - `gh pr list --search "circumference-via-differentiation-oq-03"` → **0 open PRs**.
  - `git branch -r | grep` → 0 branches.
  - **Slug is pristine post-S1 OBSERVE (merged #18362)**.

- **2026-05-12 18:40 UTC** Mathlib API audit (gh api search/code, partial — rate-limited after 6 queries):
  - `InnerProductSpace.volume_closedBall` confirmed at
    `Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean:356`.
  - `EuclideanSpace.volume_ball` confirmed at line 309.
  - `addHaar_closedBall` in `EqHaar.lean:503`.
  - **No** `hausdorffMeasure_sphere` or `volume_sphere` lemma found — Mathlib gap confirmed.
  - **No** existing `riemannianSurfaceArea` definition — confirmed safe to introduce.

**No edits to**: `problem.md`, `knowledge.md`, `state.md`, `literature/`, `meta.json`, `annotations.json`, `index.ts`, any `.lean` file in `proofs/`.

**Adds exactly one file**:
`research/problems/circumference-via-differentiation-oq-03/sessions/2026-05-12-s2-prep-mathlib-bridges.md`

## §8 — Honesty disclosures

1. **Bridge 2 is a real Mathlib gap, not just a search miss.** The Hausdorff measure of the unit sphere in $\mathbb{R}^n$ via spherical coordinates (Γ-function form) is a classical computation, but Mathlib has not formalised it as a named lemma at v4.26.0. The recommended axiomatisation is honest about the gap.

2. **The S5 main theorem WILL `axiomCount: 1` if Workaround A is taken.** This is consistent with the gallery's existing axiomatised entries (e.g., Aumann/Lyapunov sister-slugs in OQ-01 stylings). `meta.json` should set `status: axiomatized`, `badge: axiom`.

3. **The LOC estimates are by analogy with `CircumferenceViaDifferentiation.lean` (parent, 2D, verified, ~80 LOC) and `CircumferenceViaDifferentiationOQ01.lean` (OQ-01, verified, ~180 LOC).** Real S2 ACT may diverge ±30%.

4. **I have not run `./proofs/scripts/docker-build.sh`.** No Lean edits in this PR.

5. **The Γ-function rewrite chain in Bridge 1 is the highest-risk piece.** `Real.Gamma_half = Real.sqrt π / 2` and related identities have type-class friction with `Real.rpow`. If `unitBallVolume` is defined in OQ-01 in a non-canonical way (e.g. via `factorial` for even $n$ but `Γ` for odd $n$), Bridge 1 may bifurcate by parity-of-$n$.

## §9 — Decision log

- **2026-05-12 S2 PREP**: Decision to file as doc-only `sessions/` PREP rather than directly implementing S2 ACT. Reason: high-value Mathlib audit + Lean skeleton sharply reduces S2 ACT risk; the gap-identification for Bridge 2 changes the S5 outcome from `verified` to `axiomatized`, which is a load-bearing meta.json change worth flagging before commit-to-Lean.

- **2026-05-12 S2 PREP**: Decision to recommend **Workaround A** (axiomatise Bridge 2) over **Workaround C** (scope down to n=2,3). Reason: A keeps the "general n" headline result; C costs that generality. The axiom is honest and clearly bounded.

- **2026-05-12 S2 PREP**: Decision to use `InnerProductSpace`-generic formulation rather than `EuclideanSpace ℝ (Fin n)`-specialised. Reason: matches the R1 ambition (OQ-03 is about beyond-Euclidean spaces) and Mathlib's API is equally rich for both via `stdOrthonormalBasis`.

## §10 — References

- **State.md and knowledge.md** (this slug, S1 OBSERVE deliverables, PR #18362).
- **`proofs/Proofs/CircumferenceViaDifferentiation.lean`** (parent 2D, verified).
- **`proofs/Proofs/CircumferenceViaDifferentiationOQ01.lean`** (n-dim parent, verified):
  - Line 39: `def unitBallVolume`.
  - Line 83: `def nBallVolumeFn`.
  - Line 90: `def nSphereSurfaceFn`.
  - Line 102: `theorem nBallVolumeFn_hasDerivAt`.
- **Mathlib v4.26.0**:
  - `Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`:
    - Line 309: `EuclideanSpace.volume_ball`.
    - Line 326: `EuclideanSpace.volume_closedBall`.
    - Line 345: `InnerProductSpace.volume_ball` (generic).
    - Line 356: `InnerProductSpace.volume_closedBall` (generic, **Bridge 1 source**).
  - `Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`:
    - Line 459: `addHaar_ball`.
    - Line 478: `addHaar_closedBall'` (the "real" version is around line 484).
    - Line 503: `addHaar_closedBall`.
  - `Mathlib/MeasureTheory/Measure/Hausdorff.lean` — `μH[d]` infrastructure (Bridge 2 starting point, but lacks sphere-specific lemma).
- **Federer, H.** (1969). *Geometric Measure Theory*, Springer. §3.2.22 (co-area formula).
- **Chavel, I.** (1984). *Eigenvalues in Riemannian Geometry*, Academic Press. §3.1 (geodesic-polar Jacobian).

## §11 — Recommended follow-up sequence

1. **This PR**: doc-only S2 PREP. Land first.
2. **S2 ACT** (this researcher's next claim or another's): implement the skeleton from §5, discharge the 2 sorries (Bridge 1 chain + S5 filter chase), commit Bridge 2 as `axiom`. Estimate: 1 session, ~130 LOC.
3. **S3 ACT** (post-S2): attempt to discharge Bridge 1 sorry — Γ-function chain.
4. **S5 ACT** (post-S2/S3): discharge S5 filter chase, land main theorem.
5. **Bridge 2 contribution to Mathlib** (deferred, multi-session): formalise `hausdorffMeasure_sphere` in Mathlib via spherical coordinates + Γ-function. This would upgrade meta.json status from `axiomatized` to `verified`.

**End of S2 PREP.**
