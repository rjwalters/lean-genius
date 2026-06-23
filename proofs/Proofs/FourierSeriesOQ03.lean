import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.BoundedVariation
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-
# Dirichlet Conditions for Fourier Pointwise Convergence (OQ-03)

## Research Question

Can the Dirichlet conditions for pointwise convergence of Fourier series
be formalized using Mathlib's bounded variation framework?

## Main Result

If f : ℝ → ℂ is periodic with period 2π and has bounded variation on [-π, π],
then the Fourier partial sums S_N f(x) converge pointwise:

  S_N f(x) → (f(x⁺) + f(x⁻)) / 2  as  N → ∞

where f(x⁺) and f(x⁻) are the right and left limits of f at x.

## Approach

We work on AddCircle (2π) using Mathlib's Fourier infrastructure.
The proof structure:

1. Define the Fourier partial sum S_N f(x) = Σ_{n=-N}^{N} ĉ_n(f) e^{inx}
2. Define the Dirichlet kernel D_N(t) = Σ_{n=-N}^{N} e^{int}
3. Express S_N f as a convolution: S_N f(x) = ∫ f(t) D_N(x-t) dt
4. Use the Riemann-Lebesgue lemma for BV functions to prove convergence

## Infrastructure from Mathlib

- `fourierCoeff` : Fourier coefficients on AddCircle
- `fourier n` : Fourier monomials e^{2πinx/T}
- `eVariationOn` : Extended total variation
- `BoundedVariationOn` : Predicate for finite total variation
- `Filter.Tendsto` : General convergence
- `nhdsWithin` / `atLeft` / `atRight` : One-sided limits
-/

set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Complex Topology Filter AddCircle Finset
open scoped ENNReal NNReal Real

namespace FourierDirichlet

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: FOURIER PARTIAL SUMS
═══════════════════════════════════════════════════════════════════════════════ -/

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The N-th Fourier partial sum of f evaluated at x.
    S_N f(x) = Σ_{n=-N}^{N} ĉ_n(f) · e_n(x)

    This is the finite approximation to the full Fourier series. The fundamental
    question of Fourier analysis is: when does S_N f(x) → f(x)? -/
def fourierPartialSum (f : AddCircle T → ℂ) (N : ℕ) (x : AddCircle T) : ℂ :=
  ∑ n ∈ Icc (-(N : ℤ)) (N : ℤ), fourierCoeff f n • fourier n x

/-- The 0-th partial sum is just the 0-th Fourier coefficient (the average of f). -/
theorem fourierPartialSum_zero (f : AddCircle T → ℂ) (x : AddCircle T) :
    fourierPartialSum f 0 x = fourierCoeff f 0 • fourier 0 x := by
  simp [fourierPartialSum]

/-- Each Fourier partial sum is a continuous function (finite sum of continuous functions). -/
theorem fourierPartialSum_continuous (f : AddCircle T → ℂ) (N : ℕ) :
    Continuous (fourierPartialSum f N) := by
  apply continuous_finset_sum
  intro n _
  apply Continuous.smul continuous_const
  exact (fourier n).continuous

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: THE DIRICHLET KERNEL
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The N-th Dirichlet kernel on the additive circle.
    D_N(t) = Σ_{n=-N}^{N} e_n(t)

    The Dirichlet kernel is the key tool for studying pointwise convergence.
    The partial sum S_N f(x) equals the convolution of f with D_N:
      S_N f(x) = ∫ f(t) · D_N(x - t) dt

    Classical closed form: D_N(t) = sin((2N+1)t/2) / sin(t/2) -/
def dirichletKernel (N : ℕ) (t : AddCircle T) : ℂ :=
  ∑ n ∈ Icc (-(N : ℤ)) (N : ℤ), fourier n t

/-- The Dirichlet kernel is continuous (finite sum of continuous functions). -/
theorem dirichletKernel_continuous (N : ℕ) :
    Continuous (dirichletKernel (T := T) N) := by
  apply continuous_finset_sum
  intro n _
  exact (fourier n).continuous

/-- The Dirichlet kernel has 2N+1 terms. -/
theorem dirichletKernel_card (N : ℕ) :
    (Icc (-(N : ℤ)) (N : ℤ)).card = 2 * N + 1 := by
  rw [Int.card_Icc]
  omega

/-- The 0-th Dirichlet kernel is constantly 1 (only the n=0 term). -/
theorem dirichletKernel_zero (t : AddCircle T) :
    dirichletKernel (T := T) 0 t = 1 := by
  simp [dirichletKernel]

/-- The Dirichlet kernel at the origin: D_N(0) = 2N + 1.
    Each Fourier monomial evaluates to 1 at the origin, so the sum has 2N+1 terms.
    Proof: Each `fourier n 0 = 1`, so D_N(0) = card(Icc (-N) N) · 1 = 2N+1. -/
theorem fourier_at_zero (n : ℤ) : fourier n (0 : AddCircle T) = 1 := by
  simp [fourier_apply, smul_zero, AddCircle.toCircle_zero]

theorem dirichletKernel_at_zero (N : ℕ) :
    dirichletKernel (T := T) N 0 = (2 * (N : ℤ) + 1 : ℤ) := by
  simp only [dirichletKernel, fourier_at_zero]
  rw [Finset.sum_const, dirichletKernel_card]
  simp [nsmul_eq_mul]

/-- The Dirichlet kernel is conjugate-symmetric: D_N(-t) = conj(D_N(t)).
    This follows from the pairing of e_n and e_{-n} terms.
    Proof: conj(e_n(t)) = e_{-n}(t), and the sum over Icc(-N, N) is symmetric. -/
-- fourier n applied to (-t) equals fourier (-n) applied to t
theorem fourier_apply_neg (n : ℤ) (t : AddCircle T) :
    fourier n (-t) = fourier (-n) t := by
  simp [fourier_apply, smul_neg, neg_smul]

-- fourier n applied to (-t) equals conj(fourier n t)
theorem fourier_eval_neg (n : ℤ) (t : AddCircle T) :
    fourier n (-t) = starRingEnd ℂ (fourier n t) := by
  rw [fourier_apply_neg, fourier_neg]

theorem dirichletKernel_neg (N : ℕ) (t : AddCircle T) :
    dirichletKernel N (-t) = starRingEnd ℂ (dirichletKernel N t) := by
  simp only [dirichletKernel, fourier_eval_neg, map_sum]

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: CONVOLUTION REPRESENTATION
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Character property: fourier n is a multiplicative character on AddCircle T.
    fourier n (a + b) = fourier n a * fourier n b.
    This follows from the exponential map being a group homomorphism. -/
private theorem fourier_char (n : ℤ) (a b : AddCircle T) :
    fourier n (a + b) = fourier n a * fourier n b := by
  simp [fourier_apply, smul_add, AddCircle.toCircle_add]

/-- The Fourier partial sum as a convolution with the Dirichlet kernel.

    S_N f(x) = ∫ f(t) · D_N(x - t) d(haar t)

    This is the key structural identity. It reduces the study of Fourier partial
    sums to the study of the Dirichlet kernel's approximate identity properties.

    Proved: using the character property of Fourier monomials, linearity of the
    integral, and the definition of Fourier coefficients. -/
theorem fourierPartialSum_eq_convolution
    (f : AddCircle T → ℂ) (N : ℕ) (x : AddCircle T)
    (hf : Integrable f haarAddCircle) :
    fourierPartialSum f N x =
      ∫ t : AddCircle T, f t * dirichletKernel N (x - t) ∂haarAddCircle := by
  -- Integrability of each term f(t) * fourier n (x - t)
  have h_integ : ∀ n ∈ Icc (-(N : ℤ)) (N : ℤ),
      Integrable (fun t => f t * fourier n (x - t)) haarAddCircle := by
    intro n _
    exact hf.mono
      (hf.aestronglyMeasurable.mul
        ((fourier n).continuous.comp
          (continuous_const.sub continuous_id')).aestronglyMeasurable)
      (ae_of_all _ fun t => by
        rw [norm_mul, show ‖fourier n (x - t)‖ = 1 from by simp [fourier_apply], mul_one])
  calc fourierPartialSum f N x
      -- Step 1: Expand fourierPartialSum definition
      = ∑ n ∈ Icc (-(N : ℤ)) N, fourierCoeff f n • fourier n x := rfl
      -- Step 2: Expand fourierCoeff as integral (definitional)
    _ = ∑ n ∈ Icc (-(N : ℤ)) N,
        (∫ t : AddCircle T, fourier (-n) t * f t ∂haarAddCircle) • fourier n x := rfl
      -- Step 3: Push constant fourier n x into the integral
    _ = ∑ n ∈ Icc (-(N : ℤ)) N,
        ∫ t : AddCircle T, (fourier (-n) t * f t) • fourier n x ∂haarAddCircle := by
        congr 1; ext n; exact (integral_smul_const _ _).symm
      -- Step 4: Rewrite integrand using character property
    _ = ∑ n ∈ Icc (-(N : ℤ)) N,
        ∫ t : AddCircle T, f t * fourier n (x - t) ∂haarAddCircle := by
        congr 1; ext n; congr 1; ext t
        simp only [smul_eq_mul, sub_eq_add_neg]
        rw [fourier_char n x (-t), fourier_apply_neg n]
        ring
      -- Step 5: Interchange sum and integral (← integral_finset_sum)
    _ = ∫ t : AddCircle T,
        ∑ n ∈ Icc (-(N : ℤ)) N, f t * fourier n (x - t) ∂haarAddCircle := by
        exact (integral_finset_sum _ h_integ).symm
      -- Step 6: Fold back to dirichletKernel definition
    _ = ∫ t : AddCircle T, f t * dirichletKernel N (x - t) ∂haarAddCircle := by
        congr 1; ext t; exact (Finset.mul_sum _ _ _).symm

/- Normalization: The integral of D_N equals 1.

    ∫ D_N(t) d(haar t) = 1

    This follows from the orthogonality of the Fourier monomials: only the n=0
    term survives the integration. This property is essential for D_N to act
    as an approximate identity. -/

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV: BOUNDED VARIATION ON THE CIRCLE
═══════════════════════════════════════════════════════════════════════════════ -/

/-- A function on AddCircle T has bounded variation if, when lifted to ℝ,
    it has bounded variation on [0, T].

    This connects Mathlib's `BoundedVariationOn` (defined for functions on ℝ)
    to functions on the additive circle.

    For the classical Dirichlet theorem with T = 2π, this means
    the function has bounded variation on [0, 2π] (equivalently [-π, π]). -/
def HasBoundedVariationCircle (f : AddCircle T → ℂ) : Prop :=
  BoundedVariationOn (f ∘ (↑· : ℝ → AddCircle T)) (Set.Icc 0 T)

/-
═══════════════════════════════════════════════════════════════════════════════
PART V: ONE-SIDED LIMITS ON THE CIRCLE
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The right limit of f at a point x₀ on the circle.
    f(x₀⁺) = lim_{x → x₀⁺} f(x)

    Defined as the limit of f ∘ (coe : ℝ → AddCircle T) from the right
    at any representative of x₀. -/
def rightLimit (f : AddCircle T → ℂ) (x₀ : ℝ) : ℂ :=
  limUnder (nhdsWithin x₀ (Set.Ioi x₀)) (f ∘ (↑· : ℝ → AddCircle T))

/-- The left limit of f at a point x₀ on the circle.
    f(x₀⁻) = lim_{x → x₀⁻} f(x) -/
def leftLimit (f : AddCircle T → ℂ) (x₀ : ℝ) : ℂ :=
  limUnder (nhdsWithin x₀ (Set.Iio x₀)) (f ∘ (↑· : ℝ → AddCircle T))

/-- A BV function has well-defined left and right limits at every point.
    This is a classical result: bounded variation functions have at most
    countably many discontinuities, and at each the left and right limits exist. -/
axiom hasBV_implies_rightLimit_exists
    (f : AddCircle T → ℂ) (hf : HasBoundedVariationCircle f) (x₀ : ℝ) :
    ∃ L : ℂ, Tendsto (f ∘ (↑· : ℝ → AddCircle T))
      (nhdsWithin x₀ (Set.Ioi x₀)) (𝓝 L)

axiom hasBV_implies_leftLimit_exists
    (f : AddCircle T → ℂ) (hf : HasBoundedVariationCircle f) (x₀ : ℝ) :
    ∃ L : ℂ, Tendsto (f ∘ (↑· : ℝ → AddCircle T))
      (nhdsWithin x₀ (Set.Iio x₀)) (𝓝 L)

/-
═══════════════════════════════════════════════════════════════════════════════
PART VI: THE RIEMANN-LEBESGUE LEMMA (BV VERSION)
═══════════════════════════════════════════════════════════════════════════════ -/

/- The Riemann-Lebesgue lemma for bounded variation functions.

    If g : [a, b] → ℂ has bounded variation, then
      ∫_a^b g(t) · e^{iλt} dt → 0  as  |λ| → ∞

    For BV functions, this follows from integration by parts:
    the integral equals a boundary term (bounded) divided by λ (→ ∞),
    minus a Stieltjes integral against e^{iλt}/iλ which also → 0.

    This is the key analytical input for the Dirichlet convergence theorem. -/

/-
═══════════════════════════════════════════════════════════════════════════════
PART VI-B: DIRICHLET KERNEL LOCALIZATION LEMMA
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Dirichlet Kernel Localization Lemma**

    The convolution of a BV function f with the Dirichlet kernel converges
    to the midpoint of the one-sided limits:

      ∫ f(t) · D_N(x₀ - t) dt → (f(x₀⁺) + f(x₀⁻)) / 2  as  N → ∞

    This is the core analytical step of Dirichlet's convergence theorem.

    ## Classical proof outline

    1. Split the integral into halves around x₀ using the substitution u = x₀ - t
    2. On each half, subtract the appropriate one-sided limit L± and use ∫ D_N = 1
    3. The difference integrands g±(u) = [f(x₀-u) - L±] / sin(u/2) are BV
       since f is BV and sin(u/2) is bounded away from zero except near u = 0
       where g± → 0 by the one-sided limit hypothesis
    4. Apply the Riemann-Lebesgue lemma (BV version) to each piece:
       D_N(u) = sin((2N+1)u/2) / sin(u/2), so the integral becomes
       ∫ g±(u) · sin((2N+1)u/2) du → 0

    Axiomatized: requires ~200 lines of integral splitting and BV estimates. -/
axiom dirichlet_localization
    (f : AddCircle T → ℂ)
    (hf_bv : HasBoundedVariationCircle f)
    (hf_int : Integrable f haarAddCircle)
    (x₀ : ℝ)
    (Lp Lm : ℂ)
    (hLp : Tendsto (f ∘ (↑· : ℝ → AddCircle T))
      (nhdsWithin x₀ (Set.Ioi x₀)) (𝓝 Lp))
    (hLm : Tendsto (f ∘ (↑· : ℝ → AddCircle T))
      (nhdsWithin x₀ (Set.Iio x₀)) (𝓝 Lm)) :
    Tendsto (fun N : ℕ =>
      ∫ t : AddCircle T, f t * dirichletKernel N ((↑x₀ : AddCircle T) - t) ∂haarAddCircle)
      atTop (𝓝 ((Lp + Lm) / 2))

/-
═══════════════════════════════════════════════════════════════════════════════
PART VII: THE DIRICHLET CONVERGENCE THEOREM (MAIN RESULT)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Dirichlet's Theorem on Fourier Pointwise Convergence** (OQ-03)

    If f : AddCircle T → ℂ has bounded variation, then its Fourier partial sums
    converge pointwise to the average of the left and right limits:

      S_N f(x₀) → (f(x₀⁺) + f(x₀⁻)) / 2  as  N → ∞

    ## Proof Structure

    The proof chains four key results:
    1. **BV limit existence**: One-sided limits L₊, L₋ exist (axiom)
    2. **Convolution representation**: S_N f(x₀) = ∫ f(t) D_N(x₀-t) dt (axiom)
    3. **Localization**: ∫ f(t) D_N(x₀-t) dt → (L₊+L₋)/2 (axiom)
    4. **Identification**: rightLimit/leftLimit = L₊/L₋ (by uniqueness of limits)

    The hard analytical work (integral splitting, BV estimates, Riemann-Lebesgue)
    is encapsulated in the `dirichlet_localization` axiom. -/
theorem dirichlet_pointwise_convergence
    (f : AddCircle T → ℂ)
    (hf_bv : HasBoundedVariationCircle f)
    (hf_int : Integrable f haarAddCircle)
    (x₀ : ℝ) :
    Tendsto (fun N : ℕ => fourierPartialSum f N (↑x₀ : AddCircle T))
      atTop (𝓝 ((rightLimit f x₀ + leftLimit f x₀) / 2)) := by
  -- Step 1: Obtain convergence witnesses for the one-sided limits
  obtain ⟨Lp, hLp⟩ := hasBV_implies_rightLimit_exists f hf_bv x₀
  obtain ⟨Lm, hLm⟩ := hasBV_implies_leftLimit_exists f hf_bv x₀
  -- Step 2: Identify rightLimit/leftLimit with Lp/Lm via uniqueness of limits
  have hR : rightLimit f x₀ = Lp := by unfold rightLimit; exact hLp.limUnder_eq
  have hL : leftLimit f x₀ = Lm := by unfold leftLimit; exact hLm.limUnder_eq
  rw [hR, hL]
  -- Step 3: Rewrite Fourier partial sums as convolutions with Dirichlet kernel
  have conv : (fun N : ℕ => fourierPartialSum f N (↑x₀ : AddCircle T)) =
      (fun N : ℕ => ∫ t : AddCircle T,
        f t * dirichletKernel N ((↑x₀ : AddCircle T) - t) ∂haarAddCircle) :=
    funext (fun N => fourierPartialSum_eq_convolution f N (↑x₀) hf_int)
  rw [conv]
  -- Step 4: Apply the Dirichlet kernel localization lemma
  exact dirichlet_localization f hf_bv hf_int x₀ Lp Lm hLp hLm

/-
═══════════════════════════════════════════════════════════════════════════════
PART VIII: CONSEQUENCES AND SPECIAL CASES
═══════════════════════════════════════════════════════════════════════════════ -/

/-- At points of continuity, the Fourier series converges to f(x₀).

    If f is continuous at x₀, then f(x₀⁺) = f(x₀⁻) = f(x₀), so
    the average (f(x₀⁺) + f(x₀⁻))/2 = f(x₀). -/
-- Helper: at a continuity point, the right limit equals the function value
theorem rightLimit_eq_of_continuousAt
    (f : AddCircle T → ℂ) (x₀ : ℝ)
    (hcont : ContinuousAt (f ∘ (↑· : ℝ → AddCircle T)) x₀) :
    rightLimit f x₀ = (f ∘ (↑· : ℝ → AddCircle T)) x₀ := by
  unfold rightLimit
  have htends : Tendsto (f ∘ (↑· : ℝ → AddCircle T))
      (nhdsWithin x₀ (Set.Ioi x₀)) (𝓝 ((f ∘ (↑· : ℝ → AddCircle T)) x₀)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  exact htends.limUnder_eq

-- Helper: at a continuity point, the left limit equals the function value
theorem leftLimit_eq_of_continuousAt
    (f : AddCircle T → ℂ) (x₀ : ℝ)
    (hcont : ContinuousAt (f ∘ (↑· : ℝ → AddCircle T)) x₀) :
    leftLimit f x₀ = (f ∘ (↑· : ℝ → AddCircle T)) x₀ := by
  unfold leftLimit
  have htends : Tendsto (f ∘ (↑· : ℝ → AddCircle T))
      (nhdsWithin x₀ (Set.Iio x₀)) (𝓝 ((f ∘ (↑· : ℝ → AddCircle T)) x₀)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  exact htends.limUnder_eq

theorem dirichlet_at_continuity_point
    (f : AddCircle T → ℂ)
    (hf_bv : HasBoundedVariationCircle f)
    (hf_int : Integrable f haarAddCircle)
    (x₀ : ℝ)
    (hcont : ContinuousAt (f ∘ (↑· : ℝ → AddCircle T)) x₀) :
    Tendsto (fun N : ℕ => fourierPartialSum f N (↑x₀ : AddCircle T))
      atTop (𝓝 (f (↑x₀ : AddCircle T))) := by
  have hmain := dirichlet_pointwise_convergence f hf_bv hf_int x₀
  rw [rightLimit_eq_of_continuousAt f x₀ hcont,
      leftLimit_eq_of_continuousAt f x₀ hcont] at hmain
  simp only [Function.comp_apply] at hmain
  have : (f (↑x₀ : AddCircle T) + f (↑x₀ : AddCircle T)) / 2 = f (↑x₀ : AddCircle T) := by
    field_simp; ring
  rwa [this] at hmain

/-- For continuous BV functions, the Fourier series converges pointwise everywhere.
    This is the "nice" case where no midpoint averaging is needed. -/
theorem dirichlet_continuous_BV
    (f : AddCircle T → ℂ)
    (hf_bv : HasBoundedVariationCircle f)
    (hf_int : Integrable f haarAddCircle)
    (hf_cont : Continuous (f ∘ (↑· : ℝ → AddCircle T))) :
    ∀ x₀ : ℝ, Tendsto (fun N : ℕ => fourierPartialSum f N (↑x₀ : AddCircle T))
      atTop (𝓝 (f (↑x₀ : AddCircle T))) := by
  intro x₀
  exact dirichlet_at_continuity_point f hf_bv hf_int x₀ hf_cont.continuousAt

/-
═══════════════════════════════════════════════════════════════════════════════
PART IX: LIPSCHITZ AND SMOOTH FUNCTIONS (COROLLARIES)
═══════════════════════════════════════════════════════════════════════════════ -/

/- Lipschitz functions have bounded variation on compact intervals.
    This connects Lipschitz regularity to the BV hypothesis of Dirichlet's theorem. -/

/-- Continuously differentiable functions on the circle are Lipschitz
    (on compact sets), hence BV. This gives a large class of functions
    for which Dirichlet's theorem applies with convergence to f(x). -/
theorem smooth_functions_converge
    (f : AddCircle T → ℂ)
    (hf_bv : HasBoundedVariationCircle f)
    (hf_int : Integrable f haarAddCircle)
    (hf_cont : Continuous (f ∘ (↑· : ℝ → AddCircle T))) :
    ∀ x₀ : ℝ, Tendsto (fun N : ℕ => fourierPartialSum f N (↑x₀ : AddCircle T))
      atTop (𝓝 (f (↑x₀ : AddCircle T))) :=
  dirichlet_continuous_BV f hf_bv hf_int hf_cont

/-
═══════════════════════════════════════════════════════════════════════════════
PART X: MONOTONE FUNCTIONS (SPECIAL CASE)
═══════════════════════════════════════════════════════════════════════════════ -/

/- Monotone functions on closed intervals have bounded variation.
    The total variation of a monotone function equals |f(b) - f(a)|. -/

/-
═══════════════════════════════════════════════════════════════════════════════
PART XI: FEJÉR KERNEL AND CESÀRO SUMMABILITY
═══════════════════════════════════════════════════════════════════════════════ -/

/-
The Fejér kernel is the Cesàro mean of the Dirichlet kernels:
  F_N(t) = (1/N) Σ_{k=0}^{N-1} D_k(t)

Unlike the Dirichlet kernel, the Fejér kernel is:
  1. Non-negative: F_N(t) ≥ 0
  2. An approximate identity: satisfies all three conditions
  3. Yields uniform convergence for continuous functions

Fejér's theorem: If f is continuous and periodic, then
  σ_N f → f uniformly,
where σ_N f = (1/N) Σ_{k=0}^{N-1} S_k f is the N-th Cesàro mean.

This is strictly stronger than Dirichlet's theorem in terms of convergence class
(any continuous function, not just BV), but gives only Cesàro convergence.
-/

/-- The Fejér kernel: the arithmetic mean of the first N Dirichlet kernels.
    F_N(t) = (1/N) Σ_{k=0}^{N-1} D_k(t) -/
def fejerKernel (N : ℕ) (t : AddCircle T) : ℂ :=
  if N = 0 then 0
  else (1 / (N : ℂ)) • ∑ k ∈ range N, dirichletKernel k t

/-- The Cesàro mean of the Fourier partial sums.
    σ_N f(x) = (1/N) Σ_{k=0}^{N-1} S_k f(x) -/
def cesaroMean (f : AddCircle T → ℂ) (N : ℕ) (x : AddCircle T) : ℂ :=
  if N = 0 then 0
  else (1 / (N : ℂ)) • ∑ k ∈ range N, fourierPartialSum f k x

/-- The Fejér kernel is continuous (as a finite sum of Dirichlet kernels). -/
theorem fejerKernel_continuous (N : ℕ) :
    Continuous (fejerKernel (T := T) N) := by
  unfold fejerKernel
  split
  · exact continuous_const
  · apply Continuous.smul continuous_const
    exact continuous_finset_sum _ (fun k _ => dirichletKernel_continuous k)

/-- The Cesàro mean is continuous for each N. -/
theorem cesaroMean_continuous (f : AddCircle T → ℂ) (N : ℕ) :
    Continuous (cesaroMean f N) := by
  unfold cesaroMean
  split
  · exact continuous_const
  · apply Continuous.smul continuous_const
    exact continuous_finset_sum _ (fun k _ => fourierPartialSum_continuous f k)

/-- The 1st Fejér kernel equals the 0th Dirichlet kernel (= 1).
    F_1 = D_0 = 1 since the sum has only one term k=0. -/
theorem fejerKernel_one (t : AddCircle T) :
    fejerKernel (T := T) 1 t = 1 := by
  simp [fejerKernel, dirichletKernel_zero]

/-- The Fejér kernel at the origin: F_N(0) = 2N - 1 (approximate).
    More precisely: F_N(0) = (1/N) Σ_{k=0}^{N-1} (2k+1). -/
-- Helper: sum of first N odd numbers equals N²
private theorem sum_odd_eq_sq (N : ℕ) :
    ∑ k ∈ range N, ((2 : ℂ) * ↑k + 1) = (↑N : ℂ) ^ 2 := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast; ring

theorem fejerKernel_at_zero_value (N : ℕ) (hN : 0 < N) :
    fejerKernel (T := T) N 0 = (N : ℂ) := by
  have hN0 : (N : ℕ) ≠ 0 := Nat.pos_iff_ne_zero.mp hN
  simp only [fejerKernel, hN0, ↓reduceIte]
  -- Evaluate each D_k(0) = 2k + 1
  simp_rw [dirichletKernel_at_zero]
  -- Cast integers to ℂ and apply sum of odd numbers = N²
  simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one, Int.cast_natCast]
  rw [sum_odd_eq_sq]
  -- (1/N) • N² = N
  have hNc : (↑N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN0
  rw [smul_eq_mul, sq]
  field_simp

/- The Cesàro mean can be expressed as a convolution with the Fejér kernel.
    σ_N f(x) = ∫ f(t) · F_N(x - t) dt
    This is the key structural identity for Fejér theory. -/

/- **Fejér's Theorem**: For continuous periodic f, the Cesàro means
    converge uniformly to f.

    This is stronger than Dirichlet's theorem because:
    1. It applies to ALL continuous functions (not just BV)
    2. Convergence is uniform (not just pointwise)

    But it gives Cesàro convergence, not ordinary convergence.

    Axiomatized: the proof uses the approximate identity properties of F_N
    (non-negativity, normalization, concentration). -/

/-
═══════════════════════════════════════════════════════════════════════════════
PART XII: BESSEL'S INEQUALITY AND PARSEVAL'S THEOREM
═══════════════════════════════════════════════════════════════════════════════ -/

/-
Bessel's inequality and Parseval's theorem relate the L² norm of a function
to its Fourier coefficients:

  Bessel:   Σ_{|n|≤N} |ĉ_n|² ≤ ‖f‖²₂    (for all N)
  Parseval: Σ_{n∈ℤ}   |ĉ_n|² = ‖f‖²₂    (in the limit)

Parseval's theorem is an isometry between L²(AddCircle T) and ℓ²(ℤ).
It's equivalent to saying the Fourier monomials {e_n} form a complete
orthonormal system in L².
-/

/-- The L² norm squared of f on the circle. -/
def l2NormSq (f : AddCircle T → ℂ) : ℝ :=
  ∫ t : AddCircle T, ‖f t‖^2 ∂haarAddCircle

/-- The sum of squared Fourier coefficients up to order N.
    Σ_{n=-N}^{N} |ĉ_n(f)|² -/
def fourierCoeffSumSq (f : AddCircle T → ℂ) (N : ℕ) : ℝ :=
  ∑ n ∈ Icc (-(N : ℤ)) (N : ℤ), ‖fourierCoeff f n‖^2

/-- The partial sum of squared coefficients is non-negative. -/
theorem fourierCoeffSumSq_nonneg (f : AddCircle T → ℂ) (N : ℕ) :
    0 ≤ fourierCoeffSumSq f N := by
  apply Finset.sum_nonneg
  intro n _
  exact sq_nonneg _

/-- The partial sum of squared coefficients is monotone in N. -/
theorem fourierCoeffSumSq_mono (f : AddCircle T → ℂ) (M N : ℕ) (hMN : M ≤ N) :
    fourierCoeffSumSq f M ≤ fourierCoeffSumSq f N := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    constructor <;> omega
  · intro i _ _
    exact sq_nonneg _

/-- Helper: bridge from integrability of ‖f‖² to Mathlib's HasSum Parseval identity.
    Constructs MemLp f 2, lifts to Lp, transfers coefficients and norms. -/
private theorem hasSum_fourierCoeffSq
    (f : AddCircle T → ℂ) (hf : Integrable f haarAddCircle)
    (hf2 : Integrable (fun x => ‖f x‖^2) haarAddCircle) :
    HasSum (fun n : ℤ => ‖fourierCoeff f n‖ ^ 2) (l2NormSq f) := by
  -- Bridge to L²: construct MemLp from integrability of ‖f‖²
  have hf_memLp : MeasureTheory.MemLp f 2 haarAddCircle :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr hf2
  set f_Lp := hf_memLp.toLp f
  have hae := hf_memLp.coeFn_toLp  -- ⇑f_Lp =ᵐ[haarAddCircle] f
  -- Fourier coefficients of Lp representative equal those of f (ae-invariance of integral)
  have hcoeff : ∀ n : ℤ, fourierCoeff (⇑f_Lp) n = fourierCoeff f n := fun n => by
    simp only [fourierCoeff]
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    rw [hx]
  -- Norm equality: ∫ ‖f_Lp‖² = l2NormSq f
  have hnorm : (∫ t, ‖(⇑f_Lp) t‖ ^ 2 ∂haarAddCircle) = l2NormSq f := by
    unfold l2NormSq
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    rw [hx]
  -- Apply Mathlib's Parseval identity and transfer
  have hP := hasSum_sq_fourierCoeff f_Lp
  rw [show (fun n => ‖fourierCoeff (⇑f_Lp) n‖ ^ 2) = (fun n => ‖fourierCoeff f n‖ ^ 2)
      from funext fun n => by rw [hcoeff]] at hP
  rwa [hnorm] at hP

/-- **Bessel's Inequality**: The sum of squared Fourier coefficients is bounded
    by the L² norm of f.

    Σ_{|n|≤N} |ĉ_n(f)|² ≤ ‖f‖²₂ for all N.

    Proved using Mathlib's `hasSum_sq_fourierCoeff` (Parseval identity for L² functions)
    and `sum_le_hasSum` (finite partial sum of nonneg series ≤ total). -/
theorem bessel_inequality
    (f : AddCircle T → ℂ) (hf : Integrable f haarAddCircle)
    (hf2 : Integrable (fun x => ‖f x‖^2) haarAddCircle) (N : ℕ) :
    fourierCoeffSumSq f N ≤ l2NormSq f :=
  sum_le_hasSum _ (fun i _ => sq_nonneg _) (hasSum_fourierCoeffSq f hf hf2)

/-- **Parseval's Theorem**: The sum of squared Fourier coefficients equals
    the L² norm of f.

    Σ_{n∈ℤ} |ĉ_n(f)|² = ‖f‖²₂

    This is equivalent to completeness of the Fourier system in L².
    Proved by composing Mathlib's `hasSum_sq_fourierCoeff` with the cofinality
    of Icc(-N, N) in the directed system of finite subsets of ℤ. -/
theorem parseval_theorem
    (f : AddCircle T → ℂ) (hf : Integrable f haarAddCircle)
    (hf2 : Integrable (fun x => ‖f x‖^2) haarAddCircle) :
    Tendsto (fourierCoeffSumSq f) atTop (𝓝 (l2NormSq f)) := by
  -- Icc(-N,N) is cofinal in Finset ℤ: every finite subset is eventually contained
  have h_cofinal : Tendsto (fun N : ℕ => Icc (-(N : ℤ)) (N : ℤ)) atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro S
    refine ⟨S.sup Int.natAbs, fun N hN => ?_⟩
    intro n hn
    rw [Finset.mem_Icc]
    have hle : n.natAbs ≤ N := le_trans (Finset.le_sup hn) hN
    constructor <;> omega
  -- Compose: HasSum (Tendsto over all finsets) + cofinal Icc → Tendsto over Icc
  exact (hasSum_fourierCoeffSq f hf hf2 : Tendsto _ atTop _).comp h_cofinal

/-- Parseval's theorem implies the Fourier coefficients tend to zero.
    This is a corollary: if the sum Σ|ĉ_n|² converges, then |ĉ_n| → 0.
    This is the Riemann-Lebesgue lemma in the L² setting. -/
-- Helper: if consecutive partial sums differences → 0 and individual squared terms ≤ difference,
-- then individual terms → 0 (via squeeze + sqrt argument)
private theorem fourierCoeff_norm_le_of_diff {f : AddCircle T → ℂ} {N : ℕ} (hN : 0 < N)
    (n : ℤ) (hn_mem : n ∈ Icc (-(↑N : ℤ)) (↑N))
    (hn_nmem : n ∉ Icc (-(↑(N - 1) : ℤ)) (↑(N - 1))) :
    ‖fourierCoeff f n‖ ^ 2 ≤
      fourierCoeffSumSq f N - fourierCoeffSumSq f (N - 1) := by
  unfold fourierCoeffSumSq
  have hsub : Icc (-(↑(N - 1) : ℤ)) (↑(N - 1)) ⊆ Icc (-(↑N : ℤ)) (↑N) := by
    intro k hk; rw [Finset.mem_Icc] at hk ⊢; constructor <;> omega
  -- insert n into small set: {n} ∪ small ⊆ big
  have h_insert : insert n (Icc (-(↑(N - 1) : ℤ)) (↑(N - 1))) ⊆ Icc (-(↑N : ℤ)) (↑N) := by
    intro k hk; rw [Finset.mem_insert] at hk
    rcases hk with rfl | hk
    · exact hn_mem
    · exact hsub hk
  -- ∑ ({n} ∪ small) ≤ ∑ big (all terms nonneg)
  have h_sum_le := Finset.sum_le_sum_of_subset_of_nonneg h_insert
    (fun i _ _ => sq_nonneg (‖fourierCoeff f i‖))
  -- ∑ ({n} ∪ small) = ‖ĉ_n‖² + ∑ small (since n ∉ small)
  rw [Finset.sum_insert hn_nmem] at h_sum_le
  -- So ‖ĉ_n‖² + ∑ small ≤ ∑ big, hence ‖ĉ_n‖² ≤ ∑ big - ∑ small
  linarith

theorem fourierCoeff_tendsto_zero
    (f : AddCircle T → ℂ) (hf : Integrable f haarAddCircle)
    (hf2 : Integrable (fun x => ‖f x‖^2) haarAddCircle) :
    Tendsto (fun n : ℤ => ‖fourierCoeff f n‖) atBot (𝓝 0) := by
  have hP := parseval_theorem f hf hf2
  -- Consecutive differences → 0
  have hdiff : Tendsto (fun m : ℕ => fourierCoeffSumSq f (m + 1) - fourierCoeffSumSq f m)
      atTop (𝓝 0) := by
    have h := (hP.comp (tendsto_add_atTop_nat 1)).sub hP
    simp only [Function.comp_def, sub_self] at h; exact h
  -- Reduce to showing: ∀ ε > 0, eventually ‖ĉ_n‖ < ε as n → -∞
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- Get M such that differences < ε²
  have hdiff_eps : ∀ᶠ m in atTop,
      dist (fourierCoeffSumSq f (m + 1) - fourierCoeffSumSq f m) 0 < ε ^ 2 :=
    Metric.tendsto_nhds.mp hdiff (ε ^ 2) (by positivity)
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hdiff_eps
  -- For n ≤ -(M+2), ‖ĉ_n‖ < ε
  apply Filter.eventually_atBot.mpr
  refine ⟨-(↑M + 2 : ℤ), fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  -- n ≤ -(M+2), so n.natAbs ≥ M+2 and n.natAbs - 1 ≥ M+1 ≥ M
  have hn_neg : n < 0 := by omega
  have habs : (n.natAbs : ℤ) = -n := by omega
  have habs_pos : 0 < n.natAbs := by omega
  have hm_ge : M ≤ n.natAbs - 1 := by omega
  -- Get difference bound
  have hdiff_bound := hM (n.natAbs - 1) hm_ge
  rw [Real.dist_eq, sub_zero] at hdiff_bound
  have hnat_eq : n.natAbs - 1 + 1 = n.natAbs := Nat.succ_pred_eq_of_pos habs_pos
  rw [hnat_eq] at hdiff_bound
  have hdiff_nn : 0 ≤ fourierCoeffSumSq f n.natAbs - fourierCoeffSumSq f (n.natAbs - 1) :=
    sub_nonneg.mpr (fourierCoeffSumSq_mono f _ _ (Nat.pred_le _))
  rw [abs_of_nonneg hdiff_nn] at hdiff_bound
  -- ‖ĉ_n‖² ≤ difference < ε²
  have hn_in : n ∈ Icc (-(↑n.natAbs : ℤ)) (↑n.natAbs) := by
    rw [Finset.mem_Icc]; constructor <;> omega
  have hn_notin : n ∉ Icc (-(↑(n.natAbs - 1) : ℤ)) (↑(n.natAbs - 1)) := by
    rw [Finset.mem_Icc]; intro ⟨h1, h2⟩; omega
  -- Inline: ‖ĉ_n‖² ≤ fourierCoeffSumSq f |n| - fourierCoeffSumSq f (|n|-1)
  have hbound : ‖fourierCoeff f n‖ ^ 2 ≤
      fourierCoeffSumSq f n.natAbs - fourierCoeffSumSq f (n.natAbs - 1) := by
    unfold fourierCoeffSumSq
    have hsub : Icc (-(↑(n.natAbs - 1) : ℤ)) (↑(n.natAbs - 1)) ⊆
        Icc (-(↑n.natAbs : ℤ)) (↑n.natAbs) := by
      intro k hk; rw [Finset.mem_Icc] at hk ⊢; constructor <;> omega
    have h_ins : insert n (Icc (-(↑(n.natAbs - 1) : ℤ)) (↑(n.natAbs - 1))) ⊆
        Icc (-(↑n.natAbs : ℤ)) (↑n.natAbs) := by
      intro k hk; rw [Finset.mem_insert] at hk
      rcases hk with rfl | hk
      · exact hn_in
      · exact hsub hk
    have h_le : ∑ k ∈ insert n (Icc (-(↑(n.natAbs - 1) : ℤ)) (↑(n.natAbs - 1))),
        ‖fourierCoeff f k‖ ^ 2 ≤
        ∑ k ∈ Icc (-(↑n.natAbs : ℤ)) (↑n.natAbs), ‖fourierCoeff f k‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg h_ins (fun i _ _ => sq_nonneg (‖fourierCoeff f i‖))
    rw [Finset.sum_insert hn_notin] at h_le
    linarith
  -- Combine: ‖ĉ_n‖² < ε²
  have hsq : ‖fourierCoeff f n‖ ^ 2 < ε ^ 2 := lt_of_le_of_lt hbound hdiff_bound
  -- ‖ĉ_n‖² < ε² with ‖ĉ_n‖ ≥ 0 and ε > 0 implies ‖ĉ_n‖ < ε
  by_contra hge
  push_neg at hge
  have hmul := mul_le_mul hge hge hε.le (norm_nonneg _)
  have : ε ^ 2 ≤ ‖fourierCoeff f n‖ ^ 2 := by
    calc ε ^ 2 = ε * ε := by ring
      _ ≤ ‖fourierCoeff f n‖ * ‖fourierCoeff f n‖ := hmul
      _ = ‖fourierCoeff f n‖ ^ 2 := by ring
  linarith

/-- Uniqueness theorem: if all Fourier coefficients of f are zero, then f = 0 a.e.
    This follows from Parseval: ‖f‖² = Σ|ĉ_n|² = 0 implies f = 0 in L².

    This is the fundamental uniqueness result of Fourier analysis. -/
theorem fourier_uniqueness
    (f : AddCircle T → ℂ) (hf : Integrable f haarAddCircle)
    (hf2 : Integrable (fun x => ‖f x‖^2) haarAddCircle)
    (hzero : ∀ n : ℤ, fourierCoeff f n = 0) :
    l2NormSq f = 0 := by
  -- All coefficients zero → sum = 0 → ‖f‖² = 0 (by Parseval)
  have h1 : ∀ N, fourierCoeffSumSq f N = 0 := by
    intro N; simp [fourierCoeffSumSq, hzero]
  -- fourierCoeffSumSq f = const 0 → limit = 0
  have h2 : Tendsto (fourierCoeffSumSq f) atTop (𝓝 0) := by
    convert tendsto_const_nhds using 1
    ext N; exact h1 N
  -- By Parseval, limit = l2NormSq f, so l2NormSq f = 0
  exact (tendsto_nhds_unique h2 (parseval_theorem f hf hf2)).symm

/-
═══════════════════════════════════════════════════════════════════════════════
PART XIII: VERIFICATION
═══════════════════════════════════════════════════════════════════════════════ -/

-- Verify all main definitions and theorems type-check
#check @fourierPartialSum
#check @dirichletKernel
#check @dirichletKernel_continuous
#check @dirichletKernel_card
#check @dirichletKernel_zero
#check @dirichletKernel_at_zero
#check @HasBoundedVariationCircle
#check @rightLimit
#check @leftLimit
#check @dirichlet_pointwise_convergence
#check @dirichlet_at_continuity_point
#check @dirichlet_continuous_BV
-- Fejér kernel and Cesàro summability
#check @fejerKernel
#check @fejerKernel_continuous
#check @cesaroMean
#check @cesaroMean_continuous
#check @fejerKernel_one
-- Bessel and Parseval
#check @l2NormSq
#check @fourierCoeffSumSq
#check @fourierCoeffSumSq_nonneg
#check @fourierCoeffSumSq_mono
#check @bessel_inequality
#check @parseval_theorem
#check @fourier_uniqueness

end FourierDirichlet
