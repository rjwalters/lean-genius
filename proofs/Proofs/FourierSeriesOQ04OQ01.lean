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

### Companion (unconditional, sorried)
- `sphPartialSum_L2_norm_converge` — the L²-norm version of convergence.
  Provable from Plancherel; left as `sorry` pending the Plancherel-on-`T²`
  lemma (Mathlib gap; see `research/problems/fourier-series-oq-04-oq-01/knowledge.md`).

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

/-! ## Unconditional companion (Plancherel-direct, sorried)

The norm-version of the convergence statement holds without any conjectural
input, by Plancherel applied to the increasing sequence of partial-sum
projections onto the lattice-disc-indexed sub-basis. The Plancherel identity
on the 2-torus is implicit in Mathlib's `lp 2` machinery (the tensor product
of two 1D `fourierBasis` instances gives an orthonormal basis of
`Lp (T₂ → ℂ) 2 haarT2`), but is not exposed as a named lemma — see
`research/problems/fourier-series-oq-04-oq-01/knowledge.md` for the Mathlib gap.
-/

/-- **L² norm convergence** of spherical Fourier partial sums on `𝕋²`
    (unconditional, by Plancherel). The proof is left as `sorry` pending the
    `Plancherel_ntorus` lemma (Mathlib gap; the engine is the orthonormal-basis
    Bessel-equality on `lp 2`). -/
theorem sphPartialSum_L2_norm_converge
    (f : T2 → ℂ) (_hf : MemLp f 2 haarT2) :
    Tendsto (fun R : ℝ => eLpNorm (fun x => sphPartialSum f R x - f x) 2 haarT2)
      atTop (𝓝 0) := by
  -- Outline:
  --   1. Let `T_R : Lp (T2 → ℂ) 2 → Lp (T2 → ℂ) 2` be the projection onto
  --      `span {fourier_k · fourier_k' : (k, k') ∈ latticeDisc R}`.
  --   2. The `T_R` form an increasing family of orthogonal projections
  --      whose union is dense in `lp 2`; this gives `‖T_R f - f‖ → 0`.
  --   3. Identify `T_R f x = sphPartialSum f R x` a.e. by Fubini on the
  --      product Haar measure.
  -- Step 2 is the Plancherel-on-T² Bessel-equality (Mathlib gap).
  sorry

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

end

end FourierSeriesOQ04OQ01
