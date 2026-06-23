/-
# Fourier Series OQ-04-OQ-01: 2D Carleson Spherical-Summation Conjecture (axiomatized)

## Research Question

For $f \in L^2(\mathbb{T}^2)$ with $\mathbb{T}^2 = (\mathbb{R}/\mathbb{Z})^2$, does the
spherical partial Fourier sum
$$
S_R^{\text{sph}} f(x) = \sum_{|k| \le R} \widehat f(k)\, e^{2\pi i k \cdot x},
\quad |k| = \sqrt{k_1^2 + k_2^2}
$$
converge to $f(x)$ for almost every $x \in \mathbb{T}^2$ as $R \to \infty$?

This is the L²-endpoint of the **Bochner–Riesz / spherical-summation** family
and the natural higher-dimensional generalisation of the 1D Carleson theorem.

## Status (as of 2024)

**OPEN in mathematics.** No improvement on Fefferman's 1971 ball-multiplier
barrier; no conditional approach (Kakeya, restriction) discharges the L²
endpoint. References: Stein 1971 ICM; Tao 2002 restriction-conjecture survey.

This entry **axiomatises** the conjecture (per the gallery's Axiom Integrity
Policy for unresolved open problems) and surrounds it with the unconditional
companion result that L² *norm* convergence holds via Plancherel (sorried —
the engine of the proof is `tsum_sq_fourierCoeff`-style Parseval on the
2-torus, which is implicit in Mathlib's `lp 2` framework but not yet exposed
as a named lemma).

## Architecture

### Definitions (rigorous)
- `T2` — the 2-torus `Fin 2 → AddCircle (1 : ℝ)`.
- `haarT2` — product Haar (= Lebesgue) measure on `T2`.
- `multiFourierCoeff f k` — multi-index Fourier coefficient
  `∫ f(x) · fourier (-k₀) (x 0) · fourier (-k₁) (x 1) dμ`.
- `latticeDisc R` — the finite set `{k ∈ ℤ² : k₀² + k₁² ≤ R²}` realised as a
  `Finset` (intersected with a bounding box `|kᵢ| ≤ ⌈|R|⌉`).
- `sphPartialSum f R x` — the spherical partial sum over `latticeDisc R`.

### Axiom (the open conjecture)
- `carleson_2d_sph` — for `f : T2 → ℂ` with `MemLp f 2 haarT2`, the spherical
  partial sums converge to `f` almost everywhere as `R → ∞`. **Open.**

### Companion (unconditional, proved — S15)
- `sphPartialSum_L2_norm_converge` — the L²-norm version of convergence,
  proved sorry-free via Mathlib's multivariate Fourier engine
  `UnitAddTorus.hasSum_mFourier_series_L2` (whose ambient measure on
  `UnitAddTorus (Fin 2)` is definitionally `haarT2`) plus the `latticeDisc`
  cofinality. See the "S15 ACT" section at the end of this file.

## References

- Stein, "Singular Integrals and Differentiability Properties of Functions"
  (1970), Ch. VII (Bochner-Riesz).
- Fefferman, "The multiplier problem for the ball" (1971), Annals of Math 94.
- Carleson, "On convergence and growth of partial sums of Fourier series"
  (1966), Acta Math 116 — the 1D analogue this conjecture extends.
- Tao, "Some recent progress on the restriction conjecture" (2002).
- Parent file: `Proofs/FourierSeriesOQ04.lean` (n-torus stub).
-/

import Mathlib

namespace FourierSeriesOQ04OQ01

set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Complex Filter Topology AddCircle
open scoped ENNReal NNReal Real

/-- The 2-torus `𝕋² = (ℝ/ℤ)²`, modelled as `Fin 2 → AddCircle 1`. -/
abbrev T2 : Type := Fin 2 → AddCircle (1 : ℝ)

/-- `Fact (0 < 1)` so that `AddCircle (1 : ℝ)` inherits its measure-theoretic
    instances (`Fact (0 < T)` is the standard hypothesis for `AddCircle T`). -/
instance : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩

/-- Product Haar measure on `𝕋²`: tensor product of two copies of
    `haarAddCircle` on `AddCircle 1`. -/
noncomputable def haarT2 : Measure T2 :=
  Measure.pi fun _ => (haarAddCircle : Measure (AddCircle (1 : ℝ)))

/-- Multi-index Fourier coefficient at `k ∈ ℤ²`:
    $\widehat f(k) = \int_{\mathbb{T}^2} f(x) \cdot e^{-2\pi i (k_0 x_0 + k_1 x_1)}\, d\mu(x)$.

    Using Mathlib's `fourier n : AddCircle T → ℂ` (which equals
    `exp (2π i n x / T)` on `AddCircle T`), the factor `fourier (-(k 0)) (x 0)`
    contributes `exp (-2π i (k 0) x_0)` (with `T = 1`); similarly for the second
    coordinate. The product is the desired multi-character. -/
noncomputable def multiFourierCoeff (f : T2 → ℂ) (k : Fin 2 → ℤ) : ℂ :=
  ∫ x, f x * fourier (-(k 0)) (x 0) * fourier (-(k 1)) (x 1) ∂haarT2

/-- The lattice disc $\{k \in \mathbb{Z}^2 : k_0^2 + k_1^2 \le R^2\}$ as a
    `Finset`. Implemented as the filter of a bounding box, since the integer
    pairs with $|k_i| \le |R|$ form a finite set; the disc condition is then
    a decidable predicate (classical decidability on the reals).

    For `R ≤ 0` the disc may still contain the zero index (since `0 ≤ R²`),
    consistent with the analytic convention `S_R^{sph} f = ĉ_0` for `R < 1`. -/
noncomputable def latticeDisc (R : ℝ) : Finset (Fin 2 → ℤ) :=
  letI : DecidablePred (fun k : Fin 2 → ℤ =>
    ((k 0 : ℝ))^2 + ((k 1 : ℝ))^2 ≤ R^2) := Classical.decPred _
  (Finset.Icc (fun _ : Fin 2 => -⌈|R|⌉) (fun _ : Fin 2 => ⌈|R|⌉)).filter
    (fun k => ((k 0 : ℝ))^2 + ((k 1 : ℝ))^2 ≤ R^2)

/-- Spherical partial Fourier sum on `𝕋²`:
    $S_R^{\text{sph}} f(x) = \sum_{|k| \le R} \widehat f(k)\, e^{2\pi i (k_0 x_0 + k_1 x_1)}$.

    The index set is `latticeDisc R`, a finite (`Finset`-realised) set of
    lattice points. The character `e^{2\pi i k \cdot x}` factors as
    `fourier (k 0) (x 0) * fourier (k 1) (x 1)`. -/
noncomputable def sphPartialSum (f : T2 → ℂ) (R : ℝ) (x : T2) : ℂ :=
  ∑ k ∈ latticeDisc R, multiFourierCoeff f k * fourier (k 0) (x 0) * fourier (k 1) (x 1)

/-! ## The conjecture (axiomatised)

This is genuinely open mathematics. The axiom states the L²-pointwise-a.e.
convergence claim with all qualifiers spelled out.
-/

/-- **2D Carleson spherical-summation conjecture** (Stein 1971; Tao 2002 survey).

    For every `f ∈ L²(𝕋²)`, the spherical partial Fourier sums `S_R^{sph} f`
    converge to `f` for almost every `x ∈ 𝕋²` as `R → ∞`.

    **Status (as of 2024): open.** No conditional reduction (e.g. to the Kakeya
    or restriction conjectures) is known at the L² endpoint. -/
axiom carleson_2d_sph
    (f : T2 → ℂ) (_hf : MemLp f 2 haarT2) :
    ∀ᵐ x ∂haarT2, Tendsto (fun R : ℝ => sphPartialSum f R x) atTop (𝓝 (f x))

/-! ## Unconditional companion (Plancherel-direct)

The norm-version of the convergence statement holds without any conjectural
input, by Plancherel. The full close `sphPartialSum_L2_norm_converge` is in the
**S15 ACT** section at the end of this file, where the `latticeDisc` cofinality
(S9) and the `Lp` coercion helpers (S10) are in scope. It is discharged via
Mathlib's multivariate Fourier engine `UnitAddTorus.hasSum_mFourier_series_L2`
(`Mathlib.Analysis.Fourier.AddCircleMulti`), whose ambient measure on
`UnitAddTorus (Fin 2) = T2` is definitionally `haarT2`.
-/

/-! ## Sanity-check lemmas (no sorries, definitional)

These exist to verify the definitions are not vacuous / well-typed.
-/

/-- The Fourier coefficient of the zero function at any multi-index is zero. -/
theorem multiFourierCoeff_zero (k : Fin 2 → ℤ) :
    multiFourierCoeff (fun _ : T2 => (0 : ℂ)) k = 0 := by
  simp [multiFourierCoeff]

/-- The spherical partial sum of the zero function is zero. -/
theorem sphPartialSum_zero (R : ℝ) (x : T2) :
    sphPartialSum (fun _ : T2 => (0 : ℂ)) R x = 0 := by
  simp [sphPartialSum, multiFourierCoeff_zero]

/-! ## S2c — `latticeDisc` cardinality bound (Gauss-circle prep)

Quantitative bound on `(latticeDisc R).card`. The disc is realised as a
`Finset.filter` of a bounding box `[-⌈|R|⌉, ⌈|R|⌉]²`, so its cardinality is
bounded above by the box cardinality. This is the trivial pre-Gauss bound;
the sharper Gauss-circle estimate `card ≤ ⌈π·R²⌉ + O(R)` is deferred to a
later session. For crude `ℓ¹` majorisation of the spherical partial sum,
the bounding-box bound suffices.
-/

/-- The lattice disc is a subset of the integer bounding box
    `[-⌈|R|⌉, ⌈|R|⌉]²`. -/
theorem latticeDisc_subset_bbox (R : ℝ) :
    latticeDisc R ⊆ Finset.Icc (fun _ : Fin 2 => -⌈|R|⌉)
      (fun _ : Fin 2 => ⌈|R|⌉) := by
  unfold latticeDisc
  exact Finset.filter_subset _ _

/-- The cardinality of the lattice disc is bounded by the cardinality of
    the integer bounding box `[-⌈|R|⌉, ⌈|R|⌉]²`. -/
theorem latticeDisc_card_le_bbox (R : ℝ) :
    (latticeDisc R).card ≤
      (Finset.Icc (fun _ : Fin 2 => -⌈|R|⌉) (fun _ : Fin 2 => ⌈|R|⌉)).card :=
  Finset.card_le_card (latticeDisc_subset_bbox R)

/-! ## S2d — Explicit bounding-box cardinality `(2⌈|R|⌉+1)²`

Sharpen `latticeDisc_card_le_bbox` to the explicit numerical bound
`card ≤ (2⌈|R|⌉+1)²` via `Pi.card_Icc` (which expands the bounding box's
cardinality as a product over `Fin 2` of the 1D `Int.card_Icc` formula).
This bridges the qualitative S2c subset bound to a numerical estimate
usable for ℓ¹ majorisation of `sphPartialSum`. The sharper Gauss-circle
bound `card ≤ ⌈π·R²⌉ + O(R)` remains deferred (separate boundary-lattice
analysis required).
-/

/-- The integer bounding box `[-⌈|R|⌉, ⌈|R|⌉]² ⊂ ℤ²` has cardinality
    `(2⌈|R|⌉+1).toNat ^ 2`. Direct from `Pi.card_Icc` + `Int.card_Icc`. -/
theorem bbox_card (R : ℝ) :
    (Finset.Icc (fun _ : Fin 2 => -⌈|R|⌉) (fun _ : Fin 2 => ⌈|R|⌉)).card
      = ((2 * ⌈|R|⌉ + 1).toNat) ^ 2 := by
  rw [Pi.card_Icc]
  simp only [Int.card_Icc]
  have h : (⌈|R|⌉ + 1 - -⌈|R|⌉ : ℤ) = 2 * ⌈|R|⌉ + 1 := by ring
  simp [h, Finset.prod_const, Fintype.card_fin]

/-- Explicit upper bound on the lattice-disc cardinality:
    `(latticeDisc R).card ≤ (2⌈|R|⌉+1)²`. Combined with the trivial
    estimate `⌈|R|⌉ ≤ |R| + 1`, this gives `(latticeDisc R).card = O(R²)`,
    the qualitative Gauss-circle bound. The sharp constant `π` requires
    boundary-lattice analysis (separate session). -/
theorem latticeDisc_card_le_explicit (R : ℝ) :
    (latticeDisc R).card ≤ ((2 * ⌈|R|⌉ + 1).toNat) ^ 2 :=
  (latticeDisc_card_le_bbox R).trans_eq (bbox_card R)

/-! ## S2-Gauss-real — Real-form qualitative Gauss-circle bound

Bridge S2d's `Nat`-valued explicit bound `(latticeDisc R).card ≤ (2⌈|R|⌉+1)²`
to a `Real`-form analytic bound `((latticeDisc R).card : ℝ) ≤ (2|R| + 3)²`
suitable for downstream `ℓ¹`-majorisation / Plancherel estimates on
`sphPartialSum`. The constant `4|R|² + 12|R| + 9` is the expanded form;
the `(2|R|+3)²` form is the natural closure under `Int.ceil_lt_add_one`
and `pow_le_pow_left₀`. The sharp constant `π` remains deferred (separate
boundary-lattice analysis).
-/

/-- **Real-form qualitative Gauss-circle bound**:
    `((latticeDisc R).card : ℝ) ≤ (2|R| + 3)²`.

    Combines S2d's `latticeDisc_card_le_explicit` with `Int.ceil_lt_add_one`
    (`⌈|R|⌉ < |R| + 1`) under cast to `ℝ`. The bound is qualitative
    (constant 4 vs sharp π); useful for `O(R²)`-class estimates of the
    spherical partial sum's ℓ¹-norm. -/
theorem latticeDisc_card_le_real (R : ℝ) :
    ((latticeDisc R).card : ℝ) ≤ (2 * |R| + 3) ^ 2 := by
  -- Integer-side nonneg facts (so toNat is identity-on-Int and squaring monotone)
  have hceil_nn : (0 : ℤ) ≤ ⌈|R|⌉ := Int.ceil_nonneg (abs_nonneg R)
  have hpos : (0 : ℤ) ≤ 2 * ⌈|R|⌉ + 1 := by linarith
  -- Cast S2d's Nat bound to ℝ, then use Int.toNat_of_nonneg to drop .toNat
  have h_card_le_Nat : ((latticeDisc R).card : ℝ)
                       ≤ (((2 * ⌈|R|⌉ + 1).toNat : ℝ)) ^ 2 := by
    have h := latticeDisc_card_le_explicit R
    exact_mod_cast h
  have h_toNat : (((2 * ⌈|R|⌉ + 1).toNat : ℝ)) = ((2 * ⌈|R|⌉ + 1 : ℤ) : ℝ) := by
    have := Int.toNat_of_nonneg hpos
    exact_mod_cast this
  rw [h_toNat] at h_card_le_Nat
  -- ⌈|R|⌉ ≤ |R| + 1 (strict, but ≤ suffices)
  have h_ceil_lt : (⌈|R|⌉ : ℝ) < |R| + 1 := Int.ceil_lt_add_one |R|
  -- 2⌈|R|⌉ + 1 ≤ 2|R| + 3 (in ℝ)
  have h_lin : ((2 * ⌈|R|⌉ + 1 : ℤ) : ℝ) ≤ 2 * |R| + 3 := by
    push_cast
    linarith
  -- Nonneg of the integer cast (for monotone squaring)
  have h_nn_R : (0 : ℝ) ≤ ((2 * ⌈|R|⌉ + 1 : ℤ) : ℝ) := by exact_mod_cast hpos
  -- Square the linear inequality
  have h_sq : ((2 * ⌈|R|⌉ + 1 : ℤ) : ℝ) ^ 2 ≤ (2 * |R| + 3) ^ 2 :=
    pow_le_pow_left₀ h_nn_R h_lin 2
  linarith

/-! ## S2e-cofinality — `latticeDisc R` eventually contains any fixed lattice-point set

Stepping-stone for the S2e ACT discharge of `sphPartialSum_L2_norm_converge`:
the cofinality lemma `latticeDisc_eventually_supset` says that for every
finite set `S` of lattice points, `S ⊆ latticeDisc R` for all sufficiently
large `R`. Combined with the eventual identification of `sphPartialSum` with
a finset-sum projection onto the multi-Fourier basis, this turns the
Plancherel residual `‖S_R^{sph} f - f‖₂² = ∑_{k ∉ latticeDisc R} |fk|²`
into a tail of a convergent series — the engine of the unconditional
L²-norm-convergence close.

Pure ℝ/ℤ arithmetic — no measure-theoretic dependencies. -/

/-- **Singleton-case cofinality**: every fixed lattice point `k ∈ ℤ²` is
    eventually contained in `latticeDisc R` as `R → ∞`. Proof: for
    `R ≥ (k 0)² + (k 1)² + 1`, both the disc condition
    `(k 0)² + (k 1)² ≤ R²` and the bounding-box condition
    `|k i| ≤ ⌈|R|⌉` hold. -/
theorem latticeDisc_mem_eventually (k : Fin 2 → ℤ) :
    ∀ᶠ R in (atTop : Filter ℝ), k ∈ latticeDisc R := by
  refine Filter.eventually_atTop.mpr ?_
  refine ⟨((k 0 : ℝ))^2 + ((k 1 : ℝ))^2 + 1, fun R hR => ?_⟩
  -- Setup: nonneg facts, R ≥ 1, |R| = R, R² ≥ R
  have h0 : (0 : ℝ) ≤ ((k 0 : ℝ))^2 := sq_nonneg _
  have h1 : (0 : ℝ) ≤ ((k 1 : ℝ))^2 := sq_nonneg _
  have hR1 : (1 : ℝ) ≤ R := by linarith
  have hRnn : (0 : ℝ) ≤ R := by linarith
  have hRabs : |R| = R := abs_of_nonneg hRnn
  -- For R ≥ 1: R ≤ R²  (since R² - R = R(R-1) ≥ 0)
  have hRR : R ≤ R^2 := by nlinarith
  -- Disc condition: (k 0)² + (k 1)² ≤ R²
  have hsum : ((k 0 : ℝ))^2 + ((k 1 : ℝ))^2 ≤ R^2 := by linarith
  -- Component-wise squared bounds (explicit indices to avoid fin_cases atom mismatch)
  have hbox0_sq : ((k 0 : ℝ))^2 ≤ R^2 := by linarith
  have hbox1_sq : ((k 1 : ℝ))^2 ≤ R^2 := by linarith
  -- Absolute-value bounds via sqrt monotonicity
  have habs0 : |((k 0 : ℝ))| ≤ R := by
    have := Real.sqrt_le_sqrt hbox0_sq
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq hRnn] at this
  have habs1 : |((k 1 : ℝ))| ≤ R := by
    have := Real.sqrt_le_sqrt hbox1_sq
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq hRnn] at this
  -- ⌈|R|⌉ ≥ R: chain |R| = R with |R| ≤ ⌈|R|⌉
  have hceil_ge : R ≤ (⌈|R|⌉ : ℝ) := by
    have h : (|R| : ℝ) ≤ (⌈|R|⌉ : ℝ) := Int.le_ceil _
    linarith
  -- Per-index bounds combining |k i| ≤ R with R ≤ ⌈|R|⌉
  have hki_le0 : (k 0 : ℝ) ≤ (⌈|R|⌉ : ℝ) :=
    (le_abs_self _).trans habs0 |>.trans hceil_ge
  have hki_le1 : (k 1 : ℝ) ≤ (⌈|R|⌉ : ℝ) :=
    (le_abs_self _).trans habs1 |>.trans hceil_ge
  have hki_ge0 : -(⌈|R|⌉ : ℝ) ≤ (k 0 : ℝ) := by
    have : -((k 0 : ℝ)) ≤ R := (neg_le_abs _).trans habs0
    linarith
  have hki_ge1 : -(⌈|R|⌉ : ℝ) ≤ (k 1 : ℝ) := by
    have : -((k 1 : ℝ)) ≤ R := (neg_le_abs _).trans habs1
    linarith
  -- Discharge latticeDisc membership
  unfold latticeDisc
  rw [Finset.mem_filter]
  refine ⟨?_, hsum⟩
  rw [Finset.mem_Icc]
  refine ⟨fun i => ?_, fun i => ?_⟩
  · -- Lower bound: -⌈|R|⌉ ≤ k i in ℤ
    fin_cases i
    · exact_mod_cast hki_ge0
    · exact_mod_cast hki_ge1
  · -- Upper bound: k i ≤ ⌈|R|⌉ in ℤ
    fin_cases i
    · exact_mod_cast hki_le0
    · exact_mod_cast hki_le1

/-- **Cofinality of `latticeDisc R`**: for any finite set `S ⊂ ℤ²` of lattice
    points, `S ⊆ latticeDisc R` for all sufficiently large `R`. Direct
    consequence of `latticeDisc_mem_eventually` by induction on `S`.

    This is the cofinality bearer noted in the S2e PREP / S7 audit (`atTop`
    cofinality of `latticeDisc`) used by the S2e ACT to discharge
    `sphPartialSum_L2_norm_converge` via the standard Plancherel argument:
    Bessel's inequality on the multi-Fourier basis gives
    `‖S_R^{sph} f - f‖₂² = ∑_{k ∉ latticeDisc R} |fk|²`, and this cofinality
    lemma converts the right-hand sum into a tail of the convergent
    Plancherel series `∑_k |fk|² = ‖f‖₂²`. -/
theorem latticeDisc_eventually_supset (S : Finset (Fin 2 → ℤ)) :
    ∀ᶠ R in (atTop : Filter ℝ), S ⊆ latticeDisc R := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact Filter.Eventually.of_forall (fun _ => Finset.empty_subset _)
  | @insert k S _hkS ih =>
    filter_upwards [ih, latticeDisc_mem_eventually k] with R hSR hkR
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hjS
    · exact hkR
    · exact hSR hjS

/-! ## S2e step 2 — `Lp.coeFn_finset_sum` helper on `haarT2`

A pure measure-theoretic helper paste-recipe noted in the S7
audit-at-pick-time review (`feedback_researcher_act_picker_must_recheck_prep_bearer_typeclasses_via_section_header.md`)
as a documented Mathlib gap at pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(`Lp.coeFn_finset_sum` is absent in `MeasureTheory.Function.LpSpace.Basic.lean`
at line ~195 where `Lp.coeFn_add` sits).

Specialised to `Lp ℂ 2 haarT2` to match the rest of this file. The
generic statement (with `{E p μ}` parameters) is the obvious Mathlib-bound
generalisation — straightforward consequence of `Lp.coeFn_add` and
`Lp.coeFn_zero` via `Finset.induction_on`.

This is step 2 of the S7 audit §4 ACT recipe for discharging
`sphPartialSum_L2_norm_converge`. Steps 1 (haarT2/volume setup), 4 (bridge
`sphPartialSum` → Lp finset-sum), 5 (cite `hasSum_mFourier_series_L2`), and
6 (close `eLpNorm`-form via `Lp.norm_def`) remain. Independent of step 1.
-/

/-- **`Lp.coeFn_finset_sum` on `haarT2`** (Mathlib gap helper).

    For a finite family of `Lp ℂ 2 haarT2` elements indexed by `s`, the
    pointwise coercion of the finset-sum agrees almost everywhere with the
    pointwise finset-sum of coercions. Proof: induction on `s`, using
    `Lp.coeFn_zero` (empty case) and `Lp.coeFn_add` (insert case). -/
private theorem coeFn_finset_sum_haarT2
    {ι : Type*} (s : Finset ι) (f : ι → Lp ℂ 2 haarT2) :
    ⇑(∑ k ∈ s, f k) =ᵐ[haarT2] fun x => ∑ k ∈ s, (f k : T2 → ℂ) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℂ 2 haarT2
  | @insert k s hkS ih =>
    simp only [Finset.sum_insert hkS]
    refine (Lp.coeFn_add (f k) _).trans ?_
    exact (Filter.EventuallyEq.refl _ (⇑(f k))).add ih

/-! ## S2e step 1 (contingency) — `haarT2 = volume` bridge on `Fin 2 → AddCircle 1`

The S2e ACT recipe's step 1 includes a "haarT2/volume contingency" (per
`research/problems/fourier-series-oq-04-oq-01/state.md`): the Mathlib engine
`hasSum_mFourier_series_L2` (in `Mathlib.Analysis.Fourier.AddCircleMulti`,
verified at pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` aka v4.26.0) is
stated over `L²(UnitAddTorus d) = (d → UnitAddCircle) → ℂ`, where the L² space
uses the **default `volume` measure** on `Fin 2 → AddCircle 1`. This file's
`haarT2` is defined as the product of `haarAddCircle` (the normalised Haar
measure). To invoke the Mathlib engine on our `haarT2`-stated theorems we
need the measure-equality bridge.

The arithmetic is trivial because `T = 1`: the scaling factor
`ENNReal.ofReal 1 = 1` in `volume_eq_smul_haarAddCircle` collapses, so
`volume = haarAddCircle` on `AddCircle 1`, and `volume_pi` (a `rfl` lemma)
extends this to the product. -/

/-- **`haarT2 = volume`** — the product Haar measure on `𝕋²` equals the
    standard `volume` measure on `Fin 2 → AddCircle 1`.

    Combines `AddCircle.volume_eq_smul_haarAddCircle` (1D scaling identity
    `volume = ENNReal.ofReal T • haarAddCircle`) with `ENNReal.ofReal_one`,
    `one_smul`, and `volume_pi` (a `rfl` lemma:
    `volume = Measure.pi (fun _ => volume)` on a `Pi` type). At `T = 1`
    the scaling is trivial. -/
theorem haarT2_eq_volume : haarT2 = (volume : Measure T2) := by
  have key : (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))) = volume := by
    rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]
  show Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))))
       = (volume : Measure T2)
  simp_rw [key]
  rfl

/-! ## S14 ACT step-4a / step-6 — `MemLp` / `eLpNorm` measure-bridge corollaries

Direct corollaries of `haarT2_eq_volume` (S11 ACT). These paste-ready the S12
PREP §5 sub-tactics for the eventual S2e ACT close of
`sphPartialSum_L2_norm_converge`:

- **Step 4a** (`MemLp` lift to volume): convert `MemLp f 2 haarT2` to
  `MemLp f 2 volume` so that `MemLp.toLp` and the Mathlib engine
  `hasSum_mFourier_series_L2` (stated over `volume` on `UnitAddTorus`) become
  invokable on our `haarT2`-stated hypothesis.
- **Step 6** (`eLpNorm` swap, option-(c) workaround): rewrite the goal's
  `eLpNorm _ 2 haarT2` to `eLpNorm _ 2 volume` directly, avoiding `Lp`-element
  transport.

Both are propositional consequences of the measure equality; no new
analytic content. -/

/-- **`MemLp` measure-bridge** — `f` is in `L^p(haarT2)` iff `f` is in
    `L^p(volume)` on `𝕋²`. Direct corollary of `haarT2_eq_volume`. -/
theorem memLp_haarT2_iff_volume (f : T2 → ℂ) (p : ℝ≥0∞) :
    MemLp f p haarT2 ↔ MemLp f p (volume : Measure T2) := by
  rw [haarT2_eq_volume]

/-- **`eLpNorm` measure-bridge** — the `L^p` extended norm of `f` against
    `haarT2` equals the `L^p` extended norm against `volume` on `𝕋²`.
    Direct corollary of `haarT2_eq_volume`. -/
theorem eLpNorm_haarT2_eq_volume (f : T2 → ℂ) (p : ℝ≥0∞) :
    eLpNorm f p haarT2 = eLpNorm f p (volume : Measure T2) := by
  rw [haarT2_eq_volume]

/-! ## S15 ACT — unconditional L²-norm convergence (sorry-free close)

`sphPartialSum_L2_norm_converge` is discharged by transporting the problem to
Mathlib's multivariate Fourier engine `UnitAddTorus.hasSum_mFourier_series_L2`
(`Mathlib.Analysis.Fourier.AddCircleMulti`), which states that the Fourier
series of an `L²` function on `UnitAddTorus d = d → AddCircle 1` sums to it in
the `L²` norm. Since `T2 = UnitAddTorus (Fin 2)` and the engine's ambient
measure is `Measure.pi (fun _ => haarAddCircle)` — definitionally our `haarT2` —
the engine applies natively, with no `volume` measure-cast required.

The bridge identifies our `multiFourierCoeff` / `sphPartialSum` with the
engine's `mFourierCoeff` / Fourier partial sums, then uses the `latticeDisc`
cofinality (S9, `latticeDisc_eventually_supset`) to pass from the
`Finset`-directed `HasSum` to the `R → ∞` limit.
-/

/-- The engine's multi-character `mFourier k` evaluated on `T2` factors as the
    product of the two 1-D characters — the form used by `sphPartialSum`. -/
theorem mFourier_fin2 (k : Fin 2 → ℤ) (x : T2) :
    UnitAddTorus.mFourier k x = fourier (k 0) (x 0) * fourier (k 1) (x 1) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Fin.prod_univ_two]

/-- The engine's coefficient functional `mFourierCoeff` agrees with our
    `multiFourierCoeff` on any `Lp` representative `fhat` of `f`.

    The engine integral is over its ambient measure, which is definitionally
    `haarT2`; combined with `fhat =ᵐ f` and the character factorisation, the two
    coefficient functionals coincide. -/
theorem mFourierCoeff_eq_multiFourierCoeff
    (f : T2 → ℂ) (fhat : Lp ℂ 2 haarT2) (hfhat : (fhat : T2 → ℂ) =ᵐ[haarT2] f)
    (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff (fhat : T2 → ℂ) k = multiFourierCoeff f k := by
  rw [UnitAddTorus.mFourierCoeff, multiFourierCoeff]
  refine integral_congr_ae ?_
  filter_upwards [hfhat] with t ht
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Fin.prod_univ_two,
    Pi.neg_apply, smul_eq_mul, ht]
  ring

/-- **L² norm convergence** of spherical Fourier partial sums on `𝕋²`
    (unconditional, by Plancherel via the multivariate Fourier `HasSum`).

    For `f ∈ L²(𝕋²)`, the spherical partial sums `S_R^{sph} f` converge to `f`
    in the `L²` norm as `R → ∞`. This is the norm-version companion of the
    (open, axiomatised) a.e.-convergence conjecture `carleson_2d_sph`. -/
theorem sphPartialSum_L2_norm_converge
    (f : T2 → ℂ) (hf : MemLp f 2 haarT2) :
    Tendsto (fun R : ℝ => eLpNorm (fun x => sphPartialSum f R x - f x) 2 haarT2)
      atTop (𝓝 0) := by
  classical
  -- The `Lp` representative of `f` and its defining a.e. equality.
  set fhat : Lp ℂ 2 haarT2 := hf.toLp f with hfhatdef
  have hfhat : (fhat : T2 → ℂ) =ᵐ[haarT2] f := hf.coeFn_toLp
  -- The engine summand `mFourierCoeff fhat k • mFourierLp 2 k`, as an `Lp` element.
  set g : (Fin 2 → ℤ) → Lp ℂ 2 haarT2 :=
    fun k => UnitAddTorus.mFourierCoeff (fhat : T2 → ℂ) k • UnitAddTorus.mFourierLp 2 k
    with hgdef
  -- Mathlib engine: the multivariate Fourier series sums to `fhat` in `L²`.
  have hSum : Tendsto (fun s : Finset (Fin 2 → ℤ) => ∑ k ∈ s, g k) atTop (𝓝 fhat) :=
    UnitAddTorus.hasSum_mFourier_series_L2 fhat
  -- `latticeDisc` is cofinal in the `Finset` filter (S9 cofinality).
  have htend : Tendsto latticeDisc (atTop : Filter ℝ) atTop := by
    rw [tendsto_atTop_atTop]
    intro S
    obtain ⟨R₀, hR₀⟩ := Filter.eventually_atTop.mp (latticeDisc_eventually_supset S)
    exact ⟨R₀, fun R hR => Finset.le_iff_subset.mpr (hR₀ R hR)⟩
  -- Pass from the `Finset`-directed limit to the `R → ∞` limit.
  have hConv : Tendsto (fun R : ℝ => ∑ k ∈ latticeDisc R, g k) atTop (𝓝 fhat) :=
    hSum.comp htend
  -- `Lp` convergence ⟺ the norm of the difference tends to `0`.
  have hnorm : Tendsto (fun R : ℝ => ‖(∑ k ∈ latticeDisc R, g k) - fhat‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hConv
  -- Identify the `Lp` partial sum with `sphPartialSum`, a.e.
  have hbridge : ∀ R : ℝ,
      (⇑(∑ k ∈ latticeDisc R, g k) : T2 → ℂ) =ᵐ[haarT2] fun x => sphPartialSum f R x := by
    intro R
    have hstep : ∀ s : Finset (Fin 2 → ℤ),
        (⇑(∑ k ∈ s, g k) : T2 → ℂ) =ᵐ[haarT2]
          fun x => ∑ k ∈ s, multiFourierCoeff f k *
            (fourier (k 0) (x 0) * fourier (k 1) (x 1)) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        simp only [Finset.sum_empty]
        exact Lp.coeFn_zero ℂ 2 haarT2
      | @insert k s hkS ih =>
        simp only [Finset.sum_insert hkS]
        refine (Lp.coeFn_add (g k) _).trans ?_
        have hk : (⇑(g k) : T2 → ℂ) =ᵐ[haarT2]
            fun x => multiFourierCoeff f k *
              (fourier (k 0) (x 0) * fourier (k 1) (x 1)) := by
          simp only [hgdef]
          have h1 := Lp.coeFn_smul (UnitAddTorus.mFourierCoeff (fhat : T2 → ℂ) k)
            (UnitAddTorus.mFourierLp 2 k)
          have h2 := UnitAddTorus.coeFn_mFourierLp (d := Fin 2) 2 k
          filter_upwards [h1, h2] with x hx1 hx2
          rw [hx1]
          simp only [Pi.smul_apply, hx2, smul_eq_mul]
          rw [mFourier_fin2, mFourierCoeff_eq_multiFourierCoeff f fhat hfhat k]
        filter_upwards [hk, ih] with x hxk hxs
        simp only [Pi.add_apply]
        rw [hxk, hxs]
    filter_upwards [hstep (latticeDisc R)] with x hx
    rw [hx]
    simp only [sphPartialSum]
    exact Finset.sum_congr rfl (fun k _ => (mul_assoc _ _ _).symm)
  -- The difference `⇑(P R - fhat)` agrees a.e. with `sphPartialSum f R - f`.
  have hdiff : ∀ R : ℝ,
      (⇑((∑ k ∈ latticeDisc R, g k) - fhat) : T2 → ℂ) =ᵐ[haarT2]
        fun x => sphPartialSum f R x - f x := by
    intro R
    filter_upwards [Lp.coeFn_sub (∑ k ∈ latticeDisc R, g k) fhat, hbridge R, hfhat]
      with x hsub hb hfx
    rw [hsub]
    simp only [Pi.sub_apply, hb, hfx]
  -- Rewrite the `Lp` norm as the `eLpNorm` of `sphPartialSum f R - f`.
  have heq : ∀ R : ℝ, ‖(∑ k ∈ latticeDisc R, g k) - fhat‖
      = (eLpNorm (fun x => sphPartialSum f R x - f x) 2 haarT2).toReal := by
    intro R
    rw [Lp.norm_def]
    congr 1
    exact eLpNorm_congr_ae (hdiff R)
  -- Each `eLpNorm` is finite (the difference is an `Lp` element).
  have hfin : ∀ R : ℝ,
      eLpNorm (fun x => sphPartialSum f R x - f x) 2 haarT2 ≠ ∞ := by
    intro R
    rw [← eLpNorm_congr_ae (hdiff R)]
    exact Lp.eLpNorm_ne_top _
  -- Conclude: the real norms tend to `0`, hence the `ℝ≥0∞` `eLpNorm`s do too.
  refine (ENNReal.tendsto_toReal_iff hfin ENNReal.zero_ne_top).mp ?_
  rw [ENNReal.toReal_zero]
  have hfun : (fun R : ℝ =>
      (eLpNorm (fun x => sphPartialSum f R x - f x) 2 haarT2).toReal)
      = fun R : ℝ => ‖(∑ k ∈ latticeDisc R, g k) - fhat‖ := by
    funext R; exact (heq R).symm
  rw [hfun]
  exact hnorm

end

end FourierSeriesOQ04OQ01
