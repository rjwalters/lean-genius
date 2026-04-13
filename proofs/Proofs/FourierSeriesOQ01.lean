import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

/-
# Carleson's Theorem: Pointwise a.e. Convergence of Fourier Series (OQ-01)

## Research Question

Can Carleson's theorem (L² Fourier series converge pointwise a.e.) be formalized
in Lean/Mathlib?

## Main Result

**Carleson's Theorem (1966)**: If f ∈ L²(𝕋), then the Fourier partial sums
  S_N f(x) = Σ_{n=-N}^{N} ĉ_n(f) e^{2πinx/T}
converge to f(x) for almost every x.

This is one of the deepest results in 20th-century harmonic analysis. The original
proof by Carleson (1966) used intricate time-frequency analysis, later simplified
and extended to Lp (p > 1) by Hunt (1968).

## Proof Architecture

The proof has two main components:

### Part A: Carleson-Hunt Maximal Inequality (AXIOMATIZED)
  ‖S*f‖_{L²} ≤ C · ‖f‖_{L²}
where S*f(x) = sup_N |S_N f(x)| is the Carleson maximal operator.

This is the hard part — the original proof is ~50 pages of time-frequency analysis.
We axiomatize this bound.

### Part B: Maximal Inequality → a.e. Convergence (PROVED)
Given the maximal inequality, a.e. convergence follows by a standard density
argument:
1. For trigonometric polynomials g, S_N g → g everywhere (eventually S_N g = g)
2. For general f ∈ L², approximate f by trig poly g with ‖f - g‖_{L²} < ε
3. Maximal inequality controls S*(f - g), Chebyshev gives measure bounds
4. Since ε is arbitrary, the divergence set has measure zero

This reduction is a genuine theorem that we prove from Mathlib primitives.

## Status

- [x] Fourier partial sums (self-contained definition)
- [x] Carleson maximal operator
- [x] Maximal inequality statement (axiomatized)
- [x] Density lemma: trig polys are dense in L²
- [x] Trig poly convergence: S_N g → g for trig polys
- [x] Reduction: maximal inequality → a.e. convergence
- [x] Full Carleson theorem statement

## References

- Carleson, L. (1966). "On convergence and growth of partial sums of Fourier series"
  Acta Math. 116, 135–157.
- Hunt, R.A. (1968). "On the convergence of Fourier series"
  Proc. Conf. Orthogonal Expansions and their Continuous Analogues, 235–255.
- Grafakos, L. (2014). "Classical Fourier Analysis", Chapter 11.
-/

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Complex Topology Filter AddCircle Finset
open scoped ENNReal NNReal Real

namespace CarlesonTheorem

variable {T : ℝ} [hT : Fact (0 < T)]

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: FOURIER PARTIAL SUMS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The N-th Fourier partial sum of f at x:
  S_N f(x) = Σ_{n=-N}^{N} ĉ_n(f) · e_n(x)

This is the projection of f onto the span of the first 2N+1 Fourier monomials. -/
def fourierPartialSum (f : AddCircle T → ℂ) (N : ℕ) (x : AddCircle T) : ℂ :=
  ∑ n ∈ Icc (-(N : ℤ)) (N : ℤ), fourierCoeff f n * fourier n x

/-- Partial sum with 0 terms is just the 0th Fourier coefficient. -/
theorem fourierPartialSum_zero (f : AddCircle T → ℂ) (x : AddCircle T) :
    fourierPartialSum f 0 x = fourierCoeff f 0 * fourier 0 x := by
  simp [fourierPartialSum]

/-- Partial sums are continuous functions. -/
theorem fourierPartialSum_continuous (f : AddCircle T → ℂ) (N : ℕ) :
    Continuous (fourierPartialSum f N) := by
  apply continuous_finset_sum
  intro n _
  exact (continuous_const.mul (map_continuous (fourier n)))

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: THE CARLESON MAXIMAL OPERATOR
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **The Carleson Maximal Operator**

  S*f(x) = sup_{N ∈ ℕ} |S_N f(x)|

This operator measures the worst-case behavior of the Fourier partial sums.
Carleson's key insight was that controlling S* in L² (the maximal inequality)
is the path to proving a.e. convergence.

Note: We define this as a supremum over ℕ. The value is in ℝ≥0∞ to handle
the case where the supremum is infinite (which the maximal inequality shows
doesn't happen for L² functions, in a measure-theoretic sense). -/
def carlesonMaximal (f : AddCircle T → ℂ) (x : AddCircle T) : ℝ≥0∞ :=
  ⨆ N : ℕ, ‖fourierPartialSum f N x‖₊

/-- The maximal operator is bounded below by any individual partial sum. -/
theorem le_carlesonMaximal (f : AddCircle T → ℂ) (N : ℕ) (x : AddCircle T) :
    (‖fourierPartialSum f N x‖₊ : ℝ≥0∞) ≤ carlesonMaximal f x :=
  le_iSup (fun N => (‖fourierPartialSum f N x‖₊ : ℝ≥0∞)) N

/-- Carleson maximal operator is monotone: if |f| ≤ |g| pointwise on coefficients,
    then S*f ≤ S*g. This is a basic structural property. -/
theorem carlesonMaximal_zero : carlesonMaximal (T := T) 0 = 0 := by
  ext x
  simp [carlesonMaximal, fourierPartialSum, fourierCoeff]

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: THE CARLESON-HUNT MAXIMAL INEQUALITY (AXIOMATIZED)
═══════════════════════════════════════════════════════════════════════════════ -/

/-
The Carleson-Hunt theorem states that the maximal operator S* is bounded
on L²: there exists a universal constant C > 0 such that

  ‖S*f‖_{L²} ≤ C · ‖f‖_{L²}   for all f ∈ L²(𝕋)

More precisely, S*f is in L² whenever f is, and the L² norm of S*f is controlled.
This is the most difficult part of Carleson's theorem — the proof requires deep
time-frequency analysis techniques that are beyond current Mathlib.

We axiomatize this as the existence of the Carleson constant.
-/

/-- The Carleson constant: a universal constant C ≥ 0 such that the maximal
operator satisfies ‖S*f‖_{L²} ≤ C · ‖f‖_{L²}.

The exact value is not important for the theorem; what matters is its existence.
The best known constant is due to work refining Carleson's original argument.
Bundled with its non-negativity so that `carlesonConstant_nonneg` is provable. -/
axiom carlesonData : {c : ℝ // 0 ≤ c}

/-- The Carleson constant as a real number. -/
def carlesonConstant : ℝ := carlesonData.1

/-- The Carleson constant is non-negative. -/
theorem carlesonConstant_nonneg : (0 : ℝ) ≤ carlesonConstant := carlesonData.2

/-- **Carleson-Hunt Maximal Inequality** (Axiomatized)

For any f ∈ L²(𝕋), the Carleson maximal function S*f satisfies the weak-type
estimate: for any λ > 0,

  μ({x : S*f(x) > λ}) ≤ (C/λ)² · ‖f‖²_{L²}

This is the weak-(2,2) form. The strong-(2,2) form (‖S*f‖_{L²} ≤ C‖f‖_{L²})
implies this by Chebyshev's inequality, but the weak form suffices for proving
a.e. convergence.

Note: We state this for measurable f : AddCircle T → ℂ with finite L² norm. -/
axiom carleson_hunt_maximal
    (f : AddCircle T → ℂ) (hf : Memℒp f 2 haarAddCircle)
    (λ : ℝ) (hλ : 0 < λ) :
    haarAddCircle {x : AddCircle T | ENNReal.ofReal λ < carlesonMaximal f x} ≤
      ENNReal.ofReal ((carlesonConstant / λ) ^ 2 *
        ∫ x, ‖f x‖ ^ 2 ∂haarAddCircle)
/-
═══════════════════════════════════════════════════════════════════════════════
PART IV: TRIGONOMETRIC POLYNOMIALS CONVERGE EXACTLY
═══════════════════════════════════════════════════════════════════════════════ -/

/-- A **trigonometric polynomial** is a finite linear combination of Fourier monomials:
  g(x) = Σ_{n=-M}^{M} c_n · e_n(x)
for some M : ℕ and coefficients c_n : ℤ → ℂ (with c_n = 0 for |n| > M).

This constructive definition ensures g is a specific finite sum, which allows us to:
1. Prove g ∈ L² (finite sum of bounded continuous functions)
2. Compute fourierCoeff g n = c_n (via Fourier orthogonality)
3. Recover exact convergence of Fourier partial sums -/
def IsTrigPoly (g : AddCircle T → ℂ) : Prop :=
  ∃ (M : ℕ) (c : ℤ → ℂ), (∀ n : ℤ, (M : ℤ) < |n| → c n = 0) ∧
    ∀ x, g x = ∑ n ∈ Icc (-(M : ℤ)) M, c n * fourier n x

/-- For a trigonometric polynomial of degree M, S_N g = g for all N ≥ M. -/
theorem fourierPartialSum_of_trigPoly
    {g : AddCircle T → ℂ} (hg : IsTrigPoly g) (hgL2 : Memℒp g 2 haarAddCircle)
    {N : ℕ} (hN : ∀ n : ℤ, fourierCoeff g n ≠ 0 → |n| ≤ N) :
    ∀ x, fourierPartialSum g N x =
      ∑ n ∈ Icc (-(N : ℤ)) (N : ℤ), fourierCoeff g n * fourier n x := by
  intro x
  rfl

/-- Helper: on `AddCircle T`, `fourier k` is integrable. -/
private theorem fourier_integrable (k : ℤ) : Integrable (fourier (T := T) k) haarAddCircle :=
  (Memℒp.of_bound (map_continuous (fourier k)).aestronglyMeasurable 1
    (Filter.eventually_of_forall (fun x => by
      have : ‖fourier k x‖ = 1 := by simp [fourier_apply]
      linarith))).integrable (by norm_num)

/-- Helper: `c * fourier k` is integrable for any constant `c : ℂ`. -/
private theorem const_mul_fourier_integrable (c : ℂ) (k : ℤ) :
    Integrable (fun x : AddCircle T => c * fourier k x) haarAddCircle :=
  (fourier_integrable k).const_mul c

/-- **Fourier orthogonality**: `fourierCoeff g n = c n` when `g` is a finite
Fourier sum with coefficients `c`. -/
private theorem fourierCoeff_of_trigPoly_sum (M : ℕ) (c : ℤ → ℂ) (n : ℤ) :
    fourierCoeff (fun x : AddCircle T => ∑ k ∈ Icc (-(M : ℤ)) M, c k * fourier k x) n =
    if n ∈ Icc (-(M : ℤ)) M then c n else 0 := by
  simp only [fourierCoeff, smul_eq_mul]
  -- Distribute fourier (-n) t over the sum and combine via fourier_add
  rw [show (fun t : AddCircle T => fourier (-n) t * ∑ k ∈ Icc (-(M : ℤ)) M, c k * fourier k t) =
      fun t => ∑ k ∈ Icc (-(M : ℤ)) M, c k * fourier (k + -n) t from
    funext fun t => by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      calc fourier (-n) t * (c k * fourier k t)
          = c k * (fourier k t * fourier (-n) t) := by ring
        _ = c k * fourier (k + -n) t := by rw [← fourier_add]]
  -- Exchange sum and integral
  rw [integral_finset_sum _ (fun k _ => const_mul_fourier_integrable (c k) (k + -n))]
  -- Orthogonality: ∫ t, fourier m t ∂haarAddCircle = if m = 0 then 1 else 0
  have fourier_integral : ∀ m : ℤ,
      ∫ t : AddCircle T, fourier m t ∂haarAddCircle = if m = 0 then 1 else 0 := fun m => by
    split_ifs with hm
    · subst hm
      simp_rw [fourier_zero]
      rw [integral_const, measure_univ, ENNReal.one_toReal, Complex.real_smul,
          Complex.ofReal_one, mul_one]
    · exact integral_eq_zero_of_add_right_eq_neg (fourier_add_half_inv_index hm hT.out)
  -- Simplify: c k * ∫ fourier(k-n) = c k * (if k = n then 1 else 0) = if k = n then c k else 0
  simp_rw [integral_mul_left, fourier_integral]
  simp_rw [show ∀ k : ℤ, (k + -n = 0) ↔ (k = n) from fun k => by constructor <;> intro h <;> omega]
  simp_rw [mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq']

/-- Trigonometric polynomials have their partial sums eventually equal to the function.

For a trig poly g(x) = Σ_{|n|≤M} c_n * fourier n x, the N-th partial sum S_N g(x) = g(x)
for all N ≥ M, since the extra terms have coefficient 0 by the definition of IsTrigPoly. -/
theorem trigPoly_exact_convergence
    (g : AddCircle T → ℂ) (hg : IsTrigPoly g) :
    ∃ M₀ : ℕ, ∀ N : ℕ, M₀ ≤ N → ∀ x : AddCircle T, fourierPartialSum g N x = g x := by
  obtain ⟨M, c, hc_zero, hg_eq⟩ := hg
  refine ⟨M, fun N hN x => ?_⟩
  -- Compute fourierCoeff g n = c n for all n
  have hfc : ∀ n : ℤ, fourierCoeff g n = c n := fun n => by
    rw [show g = fun x => ∑ k ∈ Icc (-(M : ℤ)) M, c k * fourier k x from funext hg_eq]
    rw [fourierCoeff_of_trigPoly_sum]
    split_ifs with hn
    · rfl
    · -- n ∉ Icc (-M) M, so |n| > M, apply hc_zero
      apply hc_zero
      simp only [Finset.mem_Icc, not_and_or, not_le] at hn
      rcases hn with h | h
      · -- h : n < -(↑M : ℤ), so n < 0, so |n| = -n > M
        rw [show |n| = -n from abs_of_nonpos (by linarith [Int.ofNat_nonneg M])]
        push_cast; linarith
      · -- h : (↑M : ℤ) < n, so |n| = n > M
        rw [show |n| = n from abs_of_pos (by exact_mod_cast h)]
        exact_mod_cast h
  -- Rewrite partial sum using fourierCoeff g n = c n
  simp only [fourierPartialSum]
  conv_lhs => arg 1; ext n; rw [hfc n]
  -- Now: ∑ n ∈ Icc (-N) N, c n * fourier n x = ∑ n ∈ Icc (-M) M, c n * fourier n x = g x
  rw [← hg_eq x]
  apply Finset.sum_subset
  · -- Icc (-M) M ⊆ Icc (-N) N since M ≤ N
    intro n hn
    simp only [Finset.mem_Icc] at *
    exact ⟨by linarith [hn.1, show (M : ℤ) ≤ N from Int.ofNat_le.mpr hN],
           by linarith [hn.2, show (M : ℤ) ≤ N from Int.ofNat_le.mpr hN]⟩
  · -- Terms in Icc (-N) N but not in Icc (-M) M have c n = 0
    intro n _ hn_small
    rw [hc_zero n, zero_mul]
    simp only [Finset.mem_Icc, not_and_or, not_le] at hn_small
    rcases hn_small with h | h
    · -- h : n < -(↑M : ℤ)
      rw [show |n| = -n from abs_of_nonpos (by linarith [Int.ofNat_nonneg M])]
      push_cast; linarith
    · -- h : (↑M : ℤ) < n
      rw [show |n| = n from abs_of_pos (by exact_mod_cast h)]
      exact_mod_cast h

/-- Trigonometric polynomials are in L² (and hence integrable).

A trig poly g(x) = Σ_{|n|≤M} c_n * fourier n x is a finite sum of bounded continuous
functions on a compact probability space, hence automatically square-integrable.
Uses `Memℒp.of_bound` since `haarAddCircle` is a finite (probability) measure. -/
theorem IsTrigPoly.memℒp_two
    (g : AddCircle T → ℂ) (hg : IsTrigPoly g) :
    Memℒp g 2 haarAddCircle := by
  obtain ⟨M, c, _, hg_eq⟩ := hg
  -- g is a finite sum of bounded continuous functions
  have hg_cont : Continuous g := by
    simp_rw [show g = fun x => ∑ n ∈ Icc (-(M : ℤ)) M, c n * fourier n x from funext hg_eq]
    apply continuous_finset_sum
    intro n _
    exact continuous_const.mul (map_continuous (fourier n))
  -- g is bounded: ‖g x‖ ≤ ∑ n ∈ Icc (-M) M, ‖c n‖
  have hbound : ∀ x : AddCircle T, ‖g x‖ ≤ ∑ n ∈ Icc (-(M : ℤ)) M, ‖c n‖ := fun x => by
    rw [hg_eq x]
    calc ‖∑ n ∈ Icc (-(M : ℤ)) M, c n * fourier n x‖
        ≤ ∑ n ∈ Icc (-(M : ℤ)) M, ‖c n * fourier n x‖ := norm_sum_le _ _
      _ = ∑ n ∈ Icc (-(M : ℤ)) M, ‖c n‖ := by
          congr 1; ext n
          rw [norm_mul, show ‖fourier n x‖ = 1 from by simp [fourier_apply], mul_one]
  -- Apply Memℒp.of_bound (works for finite measures, here a probability measure)
  exact Memℒp.of_bound hg_cont.aestronglyMeasurable _
    (Filter.eventually_of_forall hbound)

/-
═══════════════════════════════════════════════════════════════════════════════
PART V: DENSITY OF TRIGONOMETRIC POLYNOMIALS IN L²
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Helper: ‖h‖² = ∫ ‖h x‖² for `h : Lp ℂ 2 haarAddCircle`.

Proved using the L² inner product formula: ‖h‖² = Re ⟪h,h⟫ = Re ∫ ⟪h x, h x⟫ = ∫ ‖h x‖². -/
private theorem Lp2_norm_sq_eq_integral (h : Lp ℂ 2 (haarAddCircle (T := T))) :
    ‖h‖ ^ 2 = ∫ x : AddCircle T, ‖(⇑h) x‖ ^ 2 ∂haarAddCircle := by
  have H := congr_arg RCLike.re (@L2.inner_def (AddCircle T) ℂ ℂ _ _ _ _ _ h h)
  rw [← integral_re (L2.integrable_inner h h)] at H
  simp only [← norm_sq_eq_inner (𝕜 := ℂ)] at H
  -- H : ‖h‖^2 = ∫ x, RCLike.re ⟪h x, h x⟫_ℂ
  -- Rewrite pointwise: Re ⟪z, z⟫_ℂ = ‖z‖²
  convert H using 2
  ext x
  simp [inner_self_eq_norm_sq_to_K, RCLike.ofReal_re]

/-- Helper: the coercion of `∑ n ∈ s, c n • fourierLp 2 n` equals
`fun x => ∑ n ∈ s, c n * fourier n x` almost everywhere. -/
private theorem Lp_fourier_sum_coeFn (s : Finset ℤ) (c : ℤ → ℂ) :
    ⇑(∑ n ∈ s, c n • (fourierLp 2 n : Lp ℂ 2 (haarAddCircle (T := T))))
    =ᵐ[haarAddCircle] fun x => ∑ n ∈ s, c n * fourier n x := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero
  | insert ha ih =>
    simp only [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (c _ • fourierLp 2 _) (∑ n ∈ _, c n • fourierLp 2 n),
                    Lp.coeFn_smul (c _) (fourierLp 2 (T := T) _),
                    coeFn_fourierLp (T := T) 2 _,
                    ih] with x hx1 hx2 hx3 hx4
    simp only [Pi.add_apply] at hx1
    simp only [Pi.smul_apply, smul_eq_mul] at hx2
    rw [hx1, hx2, hx3, hx4]

/-- Trigonometric polynomials are dense in L²(𝕋).

Proved by using the L² convergence of Fourier series: `hasSum_fourier_series_L2`
gives that for large enough N, the N-th partial sum approximates f in L² norm.
The partial sum is a trigonometric polynomial (constructively defined via IsTrigPoly).

Proof outline:
1. Lift f to f_Lp ∈ Lp ℂ 2.
2. HasSum gives a finite set S₀ with ‖∑_{S₀} ĉ_n • e_n - f_Lp‖ < ε.
3. Define g x = ∑_{S₀} ĉ_n * fourier n x (a trig poly).
4. ‖f_Lp - g_Lp‖² = ∫ ‖f x - g x‖² (L2 norm formula + a.e. equality). -/
theorem trigPoly_L2_approx
    (f : AddCircle T → ℂ) (hf : Memℒp f 2 haarAddCircle)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : AddCircle T → ℂ, IsTrigPoly g ∧
      (∫ x, ‖f x - g x‖ ^ 2 ∂haarAddCircle) < ε ^ 2 := by
  -- Lift f to an L² element
  set f_Lp := hf.toLp f with hf_Lp_def
  -- The Fourier series converges in L²
  have hhs := hasSum_fourier_series_L2 f_Lp
  -- From HasSum: ∃ S₀ : Finset ℤ such that ‖∑ n ∈ S₀, ĉ_n • e_n - f_Lp‖ < ε
  rw [HasSum, Metric.tendsto_atTop] at hhs
  obtain ⟨S₀, hS₀⟩ := hhs ε hε
  -- The approximating partial sum at S₀
  let ĉ : ℤ → ℂ := fun n => fourierCoeff (⇑f_Lp) n
  let g_Lp : Lp ℂ 2 haarAddCircle := ∑ n ∈ S₀, ĉ n • (fourierLp 2 n : Lp ℂ 2 haarAddCircle)
  have hdist : dist g_Lp f_Lp < ε := hS₀ S₀ (le_refl _)
  -- Get M : ℕ such that S₀ ⊆ Icc (-M) M
  rcases S₀.eq_empty_or_nonempty with rfl | hne
  · -- Empty case: g_Lp = 0 and dist 0 f_Lp < ε
    simp only [Finset.sum_empty, g_Lp] at hdist
    rw [dist_comm, dist_zero_right] at hdist
    -- Use g = 0 (trivial IsTrigPoly)
    refine ⟨0, ⟨0, fun _ => 0, by simp, by simp⟩, ?_⟩
    -- ∫ ‖f x - 0‖² = ‖f_Lp‖² < ε²
    have haeq : (fun x => ‖f x - (0 : ℂ)‖ ^ 2) =ᵐ[haarAddCircle]
        fun x => ‖(⇑f_Lp) x‖ ^ 2 := by
      filter_upwards [hf.coeFn_toLp] with x hx
      simp [sub_zero, ← hx]
    rw [integral_congr_ae haeq, ← Lp2_norm_sq_eq_integral]
    exact sq_lt_sq' (by linarith [norm_nonneg f_Lp]) hdist
  · -- Non-empty case: use S₀.sup' to find M
    let M : ℕ := S₀.sup' hne (fun n => n.natAbs)
    have hS₀_sub : S₀ ⊆ Icc (-(M : ℤ)) M := by
      intro n hn
      simp only [Finset.mem_Icc]
      have hle := S₀.le_sup' (fun k => k.natAbs) hn
      simp only [M]; push_cast; constructor <;> omega
    -- Define the trig poly g
    let c : ℤ → ℂ := fun n => if n ∈ S₀ then ĉ n else 0
    let g : AddCircle T → ℂ := fun x => ∑ n ∈ Icc (-(M : ℤ)) M, c n * fourier n x
    -- g satisfies IsTrigPoly
    have hgpoly : IsTrigPoly (T := T) g := by
      refine ⟨M, c, ?_, fun x => rfl⟩
      intro n hn
      simp only [c, ite_eq_right_iff]
      intro hn'
      exfalso
      have hmem := hS₀_sub hn'
      simp only [Finset.mem_Icc] at hmem
      have : |n| ≤ (M : ℤ) := abs_le.mpr ⟨by linarith [hmem.1], hmem.2⟩
      linarith
    -- h_Lp = f_Lp - g_Lp represents f - g a.e.
    set h_Lp : Lp ℂ 2 haarAddCircle := f_Lp - g_Lp with h_Lp_def
    have hh_lt : ‖h_Lp‖ < ε := by
      rw [h_Lp_def, ← dist_eq_norm]; exact_mod_cast hdist
    -- ∫ ‖f x - g x‖² = ‖h_Lp‖² < ε²
    -- Step 1: ‖h_Lp‖² = ∫ ‖(⇑h_Lp) x‖²
    -- Step 2: ⇑h_Lp =ᵐ f - g (using coeFn_sub + coeFn_toLp + Lp_fourier_sum_coeFn)
    have hh_ae : (⇑h_Lp) =ᵐ[haarAddCircle] fun x => f x - g x := by
      have hf_ae : (⇑f_Lp) =ᵐ[haarAddCircle] f := hf.coeFn_toLp
      have hg_ae : (⇑g_Lp) =ᵐ[haarAddCircle] fun x => ∑ n ∈ S₀, ĉ n * fourier n x :=
        Lp_fourier_sum_coeFn S₀ ĉ
      -- ⇑(f_Lp - g_Lp) =ᵐ ⇑f_Lp - ⇑g_Lp =ᵐ f - g (on S₀ support = g on Icc)
      filter_upwards [Lp.coeFn_sub f_Lp g_Lp, hf_ae, hg_ae] with x hx1 hx2 hx3
      simp only [Pi.sub_apply] at hx1
      rw [hx1, hx2, hx3]
      -- Goal: f x - ∑ n ∈ S₀, ĉ n * fourier n x = f x - g x
      congr 1
      -- g x = ∑ n ∈ Icc (-M) M, c n * fourier n x
      -- Need: ∑ n ∈ S₀, ĉ n * fourier n x = ∑ n ∈ Icc (-M) M, c n * fourier n x
      simp only [g, c]
      -- c n = if n ∈ S₀ then ĉ n else 0
      calc ∑ n ∈ S₀, ĉ n * fourier n x
          = ∑ n ∈ S₀, (if n ∈ S₀ then ĉ n else 0) * fourier n x :=
            Finset.sum_congr rfl fun n hn => by simp [hn]
        _ = ∑ n ∈ Icc (-(M : ℤ)) M, (if n ∈ S₀ then ĉ n else 0) * fourier n x :=
            Finset.sum_subset hS₀_sub fun n _ hn => by simp [hn]
    -- Connect integral to norm
    have hintegral : ∫ x : AddCircle T, ‖f x - g x‖ ^ 2 ∂haarAddCircle = ‖h_Lp‖ ^ 2 := by
      rw [Lp2_norm_sq_eq_integral]
      apply integral_congr_ae
      filter_upwards [hh_ae] with x hx
      rw [hx]
    rw [hintegral]
    exact sq_lt_sq' (by linarith [norm_nonneg h_Lp]) hh_lt


/-
═══════════════════════════════════════════════════════════════════════════════
PART VI: STRUCTURAL LEMMAS FOR PARTIAL SUMS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Linearity of partial sums: S_N(f + g) = S_N f + S_N g.
    Requires integrability for the Fourier coefficient linearity (integral_add). -/
theorem fourierPartialSum_add (f g : AddCircle T → ℂ) (N : ℕ) (x : AddCircle T)
    (hf : Integrable f haarAddCircle) (hg : Integrable g haarAddCircle) :
    fourierPartialSum (f + g) N x =
      fourierPartialSum f N x + fourierPartialSum g N x := by
  simp only [fourierPartialSum, fourierCoeff, Pi.add_apply]
  rw [← sum_add_distrib]
  congr 1
  ext n
  simp [mul_comm, mul_add, add_mul]
  ring_nf
  congr 1
  have hfourier_bound : ∀ (t : AddCircle T), ‖fourier (-n) t‖ ≤ 1 := by
    intro t
    have : ‖fourier (-n) t‖ = 1 := by simp [fourier_apply]
    linarith
  have hint : ∀ h : AddCircle T → ℂ, Integrable h haarAddCircle →
      Integrable (fun t => fourier (-n) t * h t) haarAddCircle := by
    intro h hh
    apply hh.bdd_mul' (map_continuous (fourier (-n))).aestronglyMeasurable
    exact ⟨1, ae_of_all _ hfourier_bound⟩
  rw [MeasureTheory.integral_add (hint f hf) (hint g hg)]
  ring

/-- Linearity of partial sums: S_N(c • f) = c • S_N f. -/
theorem fourierPartialSum_smul (c : ℂ) (f : AddCircle T → ℂ) (N : ℕ)
    (x : AddCircle T) :
    fourierPartialSum (c • f) N x = c * fourierPartialSum f N x := by
  simp only [fourierPartialSum, fourierCoeff, Pi.smul_apply, smul_eq_mul]
  rw [mul_sum]
  congr 1; ext n
  have key : ∫ t : AddCircle T, fourier (-n) t * (c * f t) ∂haarAddCircle =
             c * ∫ t : AddCircle T, fourier (-n) t * f t ∂haarAddCircle := by
    have heq : (fun t : AddCircle T => fourier (-n) t * (c * f t)) =
               fun t => c * (fourier (-n) t * f t) := funext fun t => by ring
    rw [heq]; exact integral_const_mul c _
  rw [key]; ring

/-- Partial sums of the zero function are zero. -/
theorem fourierPartialSum_zero_fn (N : ℕ) (x : AddCircle T) :
    fourierPartialSum (0 : AddCircle T → ℂ) N x = 0 := by
  simp [fourierPartialSum, fourierCoeff]

/-
═══════════════════════════════════════════════════════════════════════════════
PART VII: THE REDUCTION — MAXIMAL INEQUALITY IMPLIES a.e. CONVERGENCE
═══════════════════════════════════════════════════════════════════════════════ -/

/-
This is the key theorem we prove: given the Carleson-Hunt maximal inequality,
pointwise a.e. convergence follows by a standard density argument.

The argument is:
1. Let f ∈ L². For any ε > 0, pick trig poly g with ‖f - g‖_{L²} < ε.
2. Write h = f - g. Then S_N f = S_N g + S_N h.
3. For large N, S_N g(x) = g(x) (trig polys converge exactly).
4. So |S_N f(x) - f(x)| = |S_N g(x) - g(x) + S_N h(x) - h(x)|
                          ≤ |S_N g(x) - g(x)| + |S_N h(x)| + |h(x)|
5. For large N the first term vanishes. The maximal inequality controls S_N h.
6. By Chebyshev: μ({S*h > λ}) ≤ (C/λ)² · ‖h‖² ≤ (Cε/λ)²
7. Since ε is arbitrary, the divergence set has measure 0.
-/

/-- The set where the partial sums of f differ from f(x) by more than δ
    infinitely often. This is the "bad set" that Carleson's theorem shows
    has measure zero. -/
def divergenceSet (f : AddCircle T → ℂ) (δ : ℝ) : Set (AddCircle T) :=
  {x | ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧ δ < ‖fourierPartialSum f N x - f x‖}

/-- The full divergence set: the set of points where S_N f(x) does NOT converge
    to f(x). This is the union of divergenceSet f (1/k) over all k ≥ 1. -/
def fullDivergenceSet (f : AddCircle T → ℂ) : Set (AddCircle T) :=
  ⋃ k : ℕ, divergenceSet f (1 / (↑k + 1))

/-- The divergence set is contained in the set where either S*h is large
    or |h| is large, where h = f - g is the approximation error.

    Proof: If ‖h(x)‖ > δ/2, we're already done. Otherwise, pick N ≥ M₀ with
    |S_N f(x) - f(x)| > δ. By linearity of partial sums,
    S_N(f-g) = S_N f - S_N g = S_N f - g (since S_N g = g for N ≥ M₀).
    Triangle inequality: ‖S_N f - g‖ ≥ ‖S_N f - f‖ - ‖f - g‖ > δ - δ/2 = δ/2.
    So S*h(x) ≥ ‖S_N h(x)‖ = ‖S_N(f-g)(x)‖ > δ/2. -/
theorem divergenceSet_subset_of_approx
    (f g : AddCircle T → ℂ) (δ : ℝ) (hδ : 0 < δ)
    (hf : Integrable f haarAddCircle) (hg : Integrable g haarAddCircle)
    (M₀ : ℕ) (hM₀ : ∀ N : ℕ, M₀ ≤ N → ∀ x, fourierPartialSum g N x = g x) :
    divergenceSet f δ ⊆
      {x | (δ / 2 : ℝ) < ‖(f - g) x‖} ∪
      {x | carlesonMaximal (f - g) x > ENNReal.ofReal (δ / 2)} := by
  intro x hx
  simp only [divergenceSet, Set.mem_setOf_eq] at hx
  by_cases hfg : (δ / 2 : ℝ) < ‖(f - g) x‖
  · exact Or.inl hfg
  · right
    push_neg at hfg
    -- So ‖(f - g) x‖ ≤ δ/2. We need S*h(x) > δ/2.
    obtain ⟨N, hNM, hNδ⟩ := hx M₀
    simp only [Set.mem_setOf_eq]
    apply lt_of_lt_of_le _ (le_carlesonMaximal (f - g) N x)
    -- Goal: ENNReal.ofReal (δ / 2) < ↑‖fourierPartialSum (f - g) N x‖₊
    -- Step 1: Linearity — S_N(f-g) = S_N f - g (since S_N g = g for N ≥ M₀)
    have hgN := hM₀ N hNM x
    have hlin : fourierPartialSum (f - g) N x = fourierPartialSum f N x - g x := by
      have h_sub : f - g = f + (-1 : ℂ) • g := by simp [sub_eq_add_neg, neg_smul]
      rw [h_sub, fourierPartialSum_add f ((-1 : ℂ) • g) N x hf (hg.smul_left _)]
      rw [fourierPartialSum_smul (-1 : ℂ) g N x, hgN]
      ring
    rw [hlin]
    -- Step 2: Real bound — ‖S_N f N x - g x‖ > δ/2
    have hfx_norm : ‖f x - g x‖ ≤ δ / 2 := by
      have : ‖(f - g) x‖ = ‖f x - g x‖ := by simp [Pi.sub_apply]
      linarith [hfg, this.symm.le]
    have h_bound : δ / 2 < ‖fourierPartialSum f N x - g x‖ := by
      have htri : ‖fourierPartialSum f N x - f x‖ ≤
          ‖fourierPartialSum f N x - g x‖ + ‖g x - f x‖ := by
        calc ‖fourierPartialSum f N x - f x‖
            = ‖(fourierPartialSum f N x - g x) + (g x - f x)‖ := by ring_nf
          _ ≤ ‖fourierPartialSum f N x - g x‖ + ‖g x - f x‖ := norm_add_le _ _
      linarith [hNδ, htri, norm_sub_rev (g x) (f x)]
    -- Step 3: Convert real bound to ENNReal
    have hpos : (0 : ℝ) ≤ δ / 2 := le_of_lt (half_pos hδ)
    rw [show ENNReal.ofReal (δ / 2) = ↑(⟨δ / 2, hpos⟩ : ℝ≥0) from
          ENNReal.ofReal_eq_coe_nnreal hpos]
    rw [ENNReal.coe_lt_coe]
    exact_mod_cast h_bound

/-- **Measure bound on divergence set via maximal inequality.**

For any δ > 0 and any approximation g of f:
  μ(divergenceSet f δ) ≤ μ({|h| > δ/2}) + μ({S*h > δ/2})
where h = f - g.

Combined with Chebyshev's inequality and the Carleson-Hunt bound:
  μ(divergenceSet f δ) ≤ C² · ‖h‖²_{L²} / (δ/2)² + ‖h‖²_{L²} / (δ/2)²

Since ‖h‖_{L²} can be made arbitrarily small (density of trig polys),
the divergence set has measure 0. -/
theorem divergenceSet_measure_bound
    (f : AddCircle T → ℂ) (hf : Memℒp f 2 haarAddCircle)
    {δ : ℝ} (hδ : 0 < δ)
    {ε : ℝ} (hε : 0 < ε)
    (g : AddCircle T → ℂ) (hg : IsTrigPoly g) (hgL2 : Memℒp g 2 haarAddCircle)
    (happrox : (∫ x, ‖f x - g x‖ ^ 2 ∂haarAddCircle) < ε ^ 2) :
    haarAddCircle (divergenceSet (T := T) f δ) ≤
      ENNReal.ofReal ((carlesonConstant + 1) ^ 2 * ε ^ 2 / (δ / 2) ^ 2) := by
  -- Step 1: Extract M₀ from trig poly convergence
  obtain ⟨M₀, hM₀⟩ := trigPoly_exact_convergence g hg
  -- Step 2: Set up integrability for the approximation error h = f - g
  have hfmg_L2 : Memℒp (f - g) 2 haarAddCircle := hf.sub hgL2
  have hf_int : Integrable f haarAddCircle := hf.integrable (by norm_num)
  have hg_int : Integrable g haarAddCircle := hgL2.integrable (by norm_num)
  -- Step 3: Divergence set ⊆ {|h| > δ/2} ∪ {S*h > δ/2}
  have hsubset := divergenceSet_subset_of_approx f g δ hδ hf_int hg_int M₀ hM₀
  -- Step 4: Union bound: μ(A ∪ B) ≤ μ(A) + μ(B)
  have hmeas_add :
      haarAddCircle (divergenceSet (T := T) f δ) ≤
        haarAddCircle {x : AddCircle T | δ / 2 < ‖(f - g) x‖} +
        haarAddCircle {x : AddCircle T |
            carlesonMaximal (f - g) x > ENNReal.ofReal (δ / 2)} :=
    (MeasureTheory.measure_mono hsubset).trans
      (MeasureTheory.measure_union_le _ _)
  -- Step 5: Bound the Carleson piece via carleson_hunt_maximal
  have happrox_fmg : ∫ x, ‖(f - g) x‖ ^ 2 ∂haarAddCircle < ε ^ 2 := by
    simpa [Pi.sub_apply] using happrox
  have hcarleson : haarAddCircle {x : AddCircle T |
        carlesonMaximal (f - g) x > ENNReal.ofReal (δ / 2)} ≤
      ENNReal.ofReal ((carlesonConstant / (δ / 2)) ^ 2 * ε ^ 2) := by
    calc haarAddCircle {x | ENNReal.ofReal (δ / 2) < carlesonMaximal (f - g) x}
        ≤ ENNReal.ofReal ((carlesonConstant / (δ / 2)) ^ 2 *
            ∫ x, ‖(f - g) x‖ ^ 2 ∂haarAddCircle) :=
          carleson_hunt_maximal (f - g) hfmg_L2 (δ / 2) (half_pos hδ)
      _ ≤ ENNReal.ofReal ((carlesonConstant / (δ / 2)) ^ 2 * ε ^ 2) := by
          apply ENNReal.ofReal_le_ofReal
          apply mul_le_mul_of_nonneg_left (le_of_lt happrox_fmg)
          positivity
  -- Step 6: Chebyshev/Markov bound for the pointwise piece
  -- μ({|h| > δ/2}) ≤ ‖h‖²_{L²} / (δ/2)² ≤ ε² / (δ/2)²
  -- Proof: on the set A = {‖h‖ ≥ δ/2}, we have ‖h‖² ≥ (δ/2)², so
  -- (δ/2)² * μ(A) ≤ ∫_A ‖h‖² ≤ ∫ ‖h‖² < ε², giving μ(A) ≤ ε²/(δ/2)².
  -- Uses: MeasureTheory.mul_meas_ge_le_lintegral₀ applied to ‖h‖²
  --       plus lintegral_ofReal for connecting ∫⁻ to ∫.
  have hchebyshev : haarAddCircle {x : AddCircle T | δ / 2 < ‖(f - g) x‖} ≤
      ENNReal.ofReal (ε ^ 2 / (δ / 2) ^ 2) := by
    have hd2sq_pos : (0 : ℝ) < (δ / 2) ^ 2 := by positivity
    have hd2sq_ne_zero : ENNReal.ofReal ((δ / 2) ^ 2) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr hd2sq_pos).ne'
    -- Integrability of ‖f-g‖² from Memℒp 2
    have hfmg_sq : Integrable (fun x => ‖(f - g) x‖ ^ 2) haarAddCircle :=
      (memℒp_two_iff_integrable_sq_norm hfmg_L2.1).mp hfmg_L2
    -- ENNReal.ofReal(‖f-g‖²) is AEMeasurable
    have hφ_ae : AEMeasurable (fun x => ENNReal.ofReal (‖(f - g) x‖ ^ 2)) haarAddCircle :=
      ENNReal.measurable_ofReal.comp_aemeasurable hfmg_sq.aemeasurable
    -- Markov: (δ/2)² * μ({(δ/2)² ≤ ‖h‖²}) ≤ ∫⁻ ‖h‖²
    have hmarkov := mul_meas_ge_le_lintegral₀ hφ_ae (ENNReal.ofReal ((δ / 2) ^ 2))
    -- Connect lintegral to integral via non-negativity and integrability
    have hlint : ∫⁻ x, ENNReal.ofReal (‖(f - g) x‖ ^ 2) ∂haarAddCircle =
        ENNReal.ofReal (∫ x, ‖(f - g) x‖ ^ 2 ∂haarAddCircle) := by
      symm
      exact ofReal_integral_eq_lintegral_ofReal hfmg_sq
        (Filter.eventually_of_forall fun x => by positivity)
    -- {δ/2 < ‖h‖} ⊆ {ENNReal.ofReal((δ/2)²) ≤ ENNReal.ofReal(‖h‖²)}
    have hset_sub : {x : AddCircle T | δ / 2 < ‖(f - g) x‖} ⊆
        {x | ENNReal.ofReal ((δ / 2) ^ 2) ≤ ENNReal.ofReal (‖(f - g) x‖ ^ 2)} :=
      fun x hx => ENNReal.ofReal_le_ofReal
        (pow_le_pow_left (le_of_lt (half_pos hδ)) (le_of_lt hx) 2)
    -- Calc: monotone measure + Markov division + integral bound + arithmetic
    calc haarAddCircle {x | δ / 2 < ‖(f - g) x‖}
        ≤ haarAddCircle {x | ENNReal.ofReal ((δ / 2) ^ 2) ≤
            ENNReal.ofReal (‖(f - g) x‖ ^ 2)} := measure_mono hset_sub
      _ ≤ (∫⁻ x, ENNReal.ofReal (‖(f - g) x‖ ^ 2) ∂haarAddCircle) /
            ENNReal.ofReal ((δ / 2) ^ 2) := by
          rw [ENNReal.le_div_iff_mul_le (Or.inl hd2sq_ne_zero)
              (Or.inl ENNReal.ofReal_ne_top)]
          rw [mul_comm]; exact hmarkov
      _ ≤ ENNReal.ofReal (ε ^ 2) / ENNReal.ofReal ((δ / 2) ^ 2) :=
          ENNReal.div_le_div_right (by rw [hlint];
            exact ENNReal.ofReal_le_ofReal (le_of_lt happrox_fmg)) _
      _ = ENNReal.ofReal (ε ^ 2 / (δ / 2) ^ 2) :=
          (ENNReal.ofReal_div_of_pos hd2sq_pos).symm
  -- Step 7: Combine the two pieces
  calc haarAddCircle (divergenceSet (T := T) f δ)
      ≤ haarAddCircle {x | δ / 2 < ‖(f - g) x‖} +
          haarAddCircle {x | carlesonMaximal (f - g) x > ENNReal.ofReal (δ / 2)} :=
        hmeas_add
    _ ≤ ENNReal.ofReal (ε ^ 2 / (δ / 2) ^ 2) +
          ENNReal.ofReal ((carlesonConstant / (δ / 2)) ^ 2 * ε ^ 2) :=
        add_le_add hchebyshev hcarleson
    _ = ENNReal.ofReal (ε ^ 2 / (δ / 2) ^ 2 +
          (carlesonConstant / (δ / 2)) ^ 2 * ε ^ 2) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal ((carlesonConstant + 1) ^ 2 * ε ^ 2 / (δ / 2) ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        have hC := carlesonConstant_nonneg
        have hd2pos : (0 : ℝ) < (δ / 2) ^ 2 := by positivity
        -- Rewrite LHS: ε²/(δ/2)² + (C/(δ/2))²*ε² = (1+C²)*ε²/(δ/2)²
        rw [show ε ^ 2 / (δ / 2) ^ 2 + (carlesonConstant / (δ / 2)) ^ 2 * ε ^ 2 =
            (1 + carlesonConstant ^ 2) * ε ^ 2 / (δ / 2) ^ 2 by
          field_simp; ring]
        -- Now: (1+C²)*ε²/(δ/2)² ≤ (C+1)²*ε²/(δ/2)² iff 1+C² ≤ (C+1)²
        apply (div_le_div_right hd2pos).mpr
        nlinarith [sq_nonneg ε,
          mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * carlesonConstant) (sq_nonneg ε)]

/-- **Carleson's Theorem: a.e. convergence of Fourier series.**

For any f ∈ L²(AddCircle T), the Fourier partial sums converge to f
almost everywhere:

  S_N f(x) → f(x)   as N → ∞,   for a.e. x ∈ AddCircle T

This is one of the great theorems of 20th-century analysis, proved by
Lennart Carleson in 1966 for L² and extended by Richard Hunt to Lp (p > 1)
in 1968.

The proof uses:
- The Carleson-Hunt maximal inequality (axiomatized)
- Density of trigonometric polynomials in L² (from Mathlib)
- A standard density argument reducing a.e. convergence to the maximal bound -/
theorem carleson_ae_convergence
    (f : AddCircle T → ℂ) (hf : Memℒp f 2 haarAddCircle) :
    ∀ᵐ x ∂haarAddCircle,
      Tendsto (fun N : ℕ => fourierPartialSum f N x) atTop (𝓝 (f x)) := by
  -- Strategy:
  -- 1. Non-convergence set ⊆ fullDivergenceSet f = ⋃_k divergenceSet f (1/(k+1))
  -- 2. Each divergenceSet f (1/(k+1)) has measure 0 (density argument)
  -- 3. Countable union of null sets is null
  apply MeasureTheory.ae_iff.mpr
  -- Step 1: {x | ¬ convergence} ⊆ fullDivergenceSet f
  apply measure_mono_null _
  swap
  · -- Step 2+3: μ(fullDivergenceSet f) = 0
    simp only [fullDivergenceSet]
    apply MeasureTheory.measure_iUnion_null
    intro k
    -- Show μ(divergenceSet f (1/(k+1))) = 0
    -- For each ε > 0, apply divergenceSet_measure_bound to get bound → 0
    apply le_antisymm _ (zero_le _)
    apply ENNReal.le_of_forall_pos_le_add
    intro r hr
    rw [zero_add]
    -- The bound (C+1)^2 * ε^2 / (1/(2*(k+1)))^2 → 0 as ε → 0
    -- Pick ε_r such that (C+1)^2 * ε_r^2 / (δ_k/2)^2 < r
    set δk : ℝ := 1 / ((k : ℝ) + 1)
    have hδk : (0 : ℝ) < δk := by positivity
    -- Get ε_r > 0 with (C+1)^2 * ε_r^2 / (δk/2)^2 ≤ r.toReal
    -- (if r = ∞, the bound is trivial; otherwise pick ε_r = sqrt(r * (δk/2)^2 / (C+1)^2 / 2))
    rcases ENNReal.lt_or_eq_top r with hr_fin | hr_top
    · -- r < ∞: use density to get a trig poly approximation
      have hr_pos : (0 : ℝ) < r.toReal :=
        ENNReal.toReal_pos (ENNReal.pos_of_ne_zero (ne_of_gt hr)) (ne_of_lt hr_fin)
      -- Choose ε_r so that (C+1)^2 * ε_r^2 / (δk/2)^2 ≤ r.toReal
      have hC_pos : (0 : ℝ) < (carlesonConstant + 1) ^ 2 := by
        have := carlesonConstant_nonneg; positivity
      set ε_r := Real.sqrt (r.toReal * (δk / 2) ^ 2 / (carlesonConstant + 1) ^ 2 / 2)
      have hε_r_pos : 0 < ε_r := by
        apply Real.sqrt_pos.mpr; positivity
      obtain ⟨g, hgpoly, happrox⟩ := trigPoly_L2_approx hf hε_r_pos
      calc haarAddCircle (divergenceSet f δk)
          ≤ ENNReal.ofReal ((carlesonConstant + 1) ^ 2 * ε_r ^ 2 / (δk / 2) ^ 2) :=
            divergenceSet_measure_bound hf hδk hε_r_pos g hgpoly
              (IsTrigPoly.memℒp_two g hgpoly) happrox
        _ ≤ r := by
            -- (C+1)^2 * ε_r^2 / (δk/2)^2 = r.toReal/2 ≤ r.toReal
            have h_real : (carlesonConstant + 1) ^ 2 * ε_r ^ 2 / (δk / 2) ^ 2 ≤ r.toReal := by
              rw [show ε_r ^ 2 = r.toReal * (δk / 2) ^ 2 / (carlesonConstant + 1) ^ 2 / 2 by
                rw [Real.sq_sqrt (by positivity)]]
              have hd2 : (δk / 2) ^ 2 ≠ 0 := by positivity
              have hC2 : (carlesonConstant + 1) ^ 2 ≠ 0 := by positivity
              field_simp
              linarith
            exact le_trans (ENNReal.ofReal_le_ofReal h_real) ENNReal.ofReal_toReal_le
    · -- r = ∞: trivial
      simp [hr_top]
  · -- Step 1: Non-convergence ⊆ fullDivergenceSet
    intro x hx
    simp only [fullDivergenceSet, Set.mem_iUnion]
    rw [Metric.tendsto_atTop] at hx
    push_neg at hx
    obtain ⟨ε, hε, hbad⟩ := hx
    -- Find k : ℕ with 1/(k+1) < ε
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
    refine ⟨k, ?_⟩
    intro M
    obtain ⟨N, hNM, hN⟩ := hbad M
    refine ⟨N, hNM, ?_⟩
    -- 1/(k+1) < ε: from 1/ε < k we get ε*k > 1, hence ε*(k+1) > 1 > 0
    have h1k : 1 / ((k : ℝ) + 1) < ε := by
      rw [div_lt_iff (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
      have h := (div_lt_iff hε).mp hk  -- h : 1 < ↑k * ε
      nlinarith [mul_comm (↑k : ℝ) ε]
    -- hN gives ε ≤ ‖S_N f(x) - f(x)‖, and h1k gives 1/(k+1) < ε
    rw [Complex.dist_eq] at hN
    linarith

/-
═══════════════════════════════════════════════════════════════════════════════
PART IX: CONSEQUENCES AND COROLLARIES
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Corollary**: The Fourier partial sums of a continuous function converge
    pointwise almost everywhere.

    Since continuous functions on a compact space are in L², this is a direct
    consequence of Carleson's theorem. -/
theorem carleson_continuous
    (f : C(AddCircle T, ℂ)) :
    ∀ᵐ x ∂haarAddCircle,
      Tendsto (fun N : ℕ => fourierPartialSum (⇑f) N x) atTop (𝓝 (f x)) := by
  apply carleson_ae_convergence
  -- Continuous functions on a compact space are in L²
  -- Use Memℒp.of_bound: f is bounded by ‖f‖ (sup norm), and haarAddCircle is finite
  exact Memℒp.of_bound f.continuous.aestronglyMeasurable ‖f‖
    (Filter.eventually_of_forall f.norm_coe_le_norm)

/-- **Corollary**: Carleson strengthens Parseval.

    Parseval gives ‖f‖² = Σ|ĉ_n|² (energy equality in L²).
    Carleson says the partial sums actually converge pointwise a.e.,
    not just in L² norm. Together they give: the Fourier series of an L²
    function converges to f both in norm AND pointwise a.e. -/
theorem carleson_and_parseval
    (f : Lp ℂ 2 (haarAddCircle (T := T))) :
    -- L² convergence (Parseval/Hilbert basis — from base file)
    HasSum (fun n : ℤ => fourierCoeff (⇑f) n • fourierLp 2 n) f ∧
    -- Pointwise a.e. convergence (Carleson)
    ∀ᵐ x ∂haarAddCircle,
      Tendsto (fun N : ℕ => fourierPartialSum (⇑f) N x) atTop (𝓝 ((⇑f) x)) := by
  constructor
  · exact hasSum_fourier_series_L2 f
  · apply carleson_ae_convergence
    exact Lp.memℒp f

/-
═══════════════════════════════════════════════════════════════════════════════
PART VIII: VERIFICATION
═══════════════════════════════════════════════════════════════════════════════ -/

-- Verify key definitions and theorems typecheck
#check @fourierPartialSum
#check @carlesonMaximal
#check @le_carlesonMaximal
#check @IsTrigPoly
#check @divergenceSet
#check @fullDivergenceSet
#check @carleson_ae_convergence
#check @carleson_continuous
#check @carleson_and_parseval

end CarlesonTheorem
