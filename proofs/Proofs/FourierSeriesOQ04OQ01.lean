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

open MeasureTheory Complex Filter Topology
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

end

end FourierSeriesOQ04OQ01
