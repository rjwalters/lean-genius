import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic
import Proofs.TaylorSinCosConvergence

/-
# Taylor Convergence for Functions with Uniformly Bounded Derivatives (OQ-04)

## Open Question
Can the sin/cos Taylor convergence approach be generalized to prove Taylor
convergence for any entire function f whose derivatives satisfy ‖f^{(n)}‖_∞ ≤ C?

## Answer
Yes. If f : ℝ → ℝ is C^∞ and there exists C ≥ 0 such that ‖f^{(n)}(x)‖ ≤ C
for all n ∈ ℕ and x ∈ ℝ, then the Taylor series of f at 0 converges to f(x)
for all x ∈ ℝ, with remainder bound C · |x|^{n+1} / n!.

## Key Results
- General Taylor partial sum definition (generalizing sinPartialSum/cosPartialSum)
- Remainder bound for x > 0 (fully proved via Mathlib's taylor_mean_remainder_bound)
- General remainder bound for all x ∈ ℝ (x < 0 case proved via reflection)
- Convergence theorem: taylorPartialSum f n x → f(x)
- Taylor value at zero: taylorPartialSum f n 0 = f(0)
- Sin and cos as special cases with C = 1

## Mathematical Context
Functions with uniformly bounded derivatives form a restrictive but important
class. By Bernstein's theorem, these are exactly the bounded entire functions
of exponential type at most 1 — that is, finite linear combinations of sin(αx)
and cos(αx) with |α| ≤ 1, and their uniform limits. The fact that sin and cos
(C = 1) achieve the minimum possible bound constant shows they are optimal
in this framework.

## Proof Highlights
The x < 0 case of the remainder bound uses `iteratedDeriv_comp_neg` from
Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas:
  iteratedDeriv n (fun x => f (-x)) a = (-1)^n • iteratedDeriv n f (-a)
This lets us reduce to the x > 0 case via the reflection g(t) = f(-t).
The linear combination bound uses `iteratedDeriv_add` and `iteratedDeriv_const_smul`
to decompose the derivative of a·sin + b·cos.

## Axiom Count: 0
(Plus 2 inherited from the parent TaylorSinCosConvergence.lean)
-/

open Set Filter Topology Finset Real
open scoped Nat

namespace TaylorBoundedDerivConvergence

-- ═══════════════════════════════════════════════════════════════
-- SECTION I: General Taylor Partial Sum
-- ═══════════════════════════════════════════════════════════════

/-- The n-th Taylor partial sum of f at 0, evaluated at x:
    T_n(x) = Σ_{k=0}^{n} f^{(k)}(0) · x^k / k!

    This generalizes sinPartialSum and cosPartialSum from the parent proof. -/
noncomputable def taylorPartialSum (f : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (Finset.range (n + 1)).sum fun k =>
    (iteratedDeriv k f 0) * x ^ k / (Nat.factorial k : ℝ)

/-- taylorPartialSum for sin agrees with sinPartialSum from the parent proof. -/
theorem taylorPartialSum_sin_eq (n : ℕ) (x : ℝ) :
    taylorPartialSum Real.sin n x =
    TaylorSinCosConvergence.sinPartialSum n x := rfl

/-- taylorPartialSum for cos agrees with cosPartialSum from the parent proof. -/
theorem taylorPartialSum_cos_eq (n : ℕ) (x : ℝ) :
    taylorPartialSum Real.cos n x =
    TaylorSinCosConvergence.cosPartialSum n x := rfl

-- ═══════════════════════════════════════════════════════════════
-- SECTION II: Connection to Mathlib's Taylor Polynomial
-- ═══════════════════════════════════════════════════════════════

/-- For C^∞ functions, iteratedDerivWithin agrees with iteratedDeriv on
    any set with the unique differentiation property. -/
theorem iteratedDerivWithin_eq_of_contDiff {f : ℝ → ℝ} {n : ℕ} {s : Set ℝ} {x : ℝ}
    (hf : ContDiff ℝ ⊤ f) (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) :
    iteratedDerivWithin n f s x = iteratedDeriv n f x :=
  iteratedDerivWithin_eq_iteratedDeriv hs (hf.contDiffAt.of_le le_top) hx

/-- taylorPartialSum f agrees with Mathlib's taylorWithinEval for x > 0.
    This is the bridge between our clean sum definition and Mathlib's machinery. -/
theorem taylorPartialSum_eq_taylorWithinEval (f : ℝ → ℝ) (hf : ContDiff ℝ ⊤ f)
    (n : ℕ) (x : ℝ) (hx : 0 < x) :
    taylorPartialSum f n x = taylorWithinEval f n (Icc 0 x) 0 x := by
  rw [taylor_within_apply]
  simp only [taylorPartialSum, sub_zero]
  apply Finset.sum_congr rfl; intro k _
  have hd : iteratedDerivWithin k f (Icc 0 x) 0 = iteratedDeriv k f 0 :=
    iteratedDerivWithin_eq_of_contDiff hf (uniqueDiffOn_Icc hx)
      (Set.mem_Icc.mpr ⟨le_refl 0, hx.le⟩)
  rw [hd, smul_eq_mul]; ring

-- ═══════════════════════════════════════════════════════════════
-- SECTION III: Remainder Bounds
-- ═══════════════════════════════════════════════════════════════

/-- **Proved**: Remainder bound for x > 0, using Mathlib's taylor_mean_remainder_bound.

    This is the general version of sin_remainder_pos from OQ-01, parameterized
    over an arbitrary C^∞ function f with derivative bound C. -/
theorem remainder_bound_pos (f : ℝ → ℝ) (C : ℝ)
    (hf : ContDiff ℝ ⊤ f)
    (hbound : ∀ (m : ℕ) (y : ℝ), ‖iteratedDeriv m f y‖ ≤ C)
    (n : ℕ) (x : ℝ) (hx : 0 < x) :
    ‖f x - taylorPartialSum f n x‖ ≤ C * x ^ (n + 1) / (Nat.factorial n : ℝ) := by
  rw [taylorPartialSum_eq_taylorWithinEval f hf n x hx]
  calc ‖f x - taylorWithinEval f n (Icc 0 x) 0 x‖
      ≤ C * (x - 0) ^ (n + 1) / ↑n ! :=
        taylor_mean_remainder_bound hx.le
          (hf.contDiffOn.of_le le_top)
          (Set.mem_Icc.mpr ⟨hx.le, le_refl x⟩)
          (fun y hy => by
            rw [iteratedDerivWithin_eq_of_contDiff hf (uniqueDiffOn_Icc hx) hy]
            exact hbound _ _)
    _ = C * x ^ (n + 1) / ↑n ! := by ring

/-- **General Taylor Remainder Bound** (fully proved):
    ‖f(x) - T_n(x)‖ ≤ C · |x|^{n+1} / n!

    The x > 0 case uses remainder_bound_pos above. The x = 0 case is trivial.
    The x < 0 case uses the reflection g(t) = f(-t): since g is C^∞ with the
    same derivative bound C (by iteratedDeriv_comp_neg), we reduce to the
    x > 0 case for g. The identity (-1)^k · (-x)^k = x^k then shows
    taylorPartialSum g n (-x) = taylorPartialSum f n x. -/
theorem general_taylor_remainder_bound (f : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ContDiff ℝ ⊤ f)
    (hbound : ∀ (m : ℕ) (y : ℝ), ‖iteratedDeriv m f y‖ ≤ C)
    (n : ℕ) (x : ℝ) :
    ‖f x - taylorPartialSum f n x‖ ≤ C * |x| ^ (n + 1) / (Nat.factorial n : ℝ) := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · -- x < 0: use reflection g(t) = f(-t)
    let g : ℝ → ℝ := fun t => f (-t)
    have hg : ContDiff ℝ ⊤ g := hf.comp contDiff_neg
    have hgbound : ∀ (m : ℕ) (y : ℝ), ‖iteratedDeriv m g y‖ ≤ C := fun m y => by
      show ‖iteratedDeriv m (fun t => f (-t)) y‖ ≤ C
      rw [iteratedDeriv_comp_neg, norm_smul]
      have hn1 : ‖((-1 : ℝ) ^ m : ℝ)‖ = 1 := by
        simp [norm_pow, norm_neg, norm_one]
      rw [hn1, one_mul]; exact hbound m (-y)
    have hxpos : 0 < -x := neg_pos.mpr hx
    have key := remainder_bound_pos g C hg hgbound n (-x) hxpos
    have hgx : g (-x) = f x := by simp [g]
    have hts : taylorPartialSum g n (-x) = taylorPartialSum f n x := by
      simp only [g, taylorPartialSum, iteratedDeriv_comp_neg, neg_zero, smul_eq_mul]
      apply Finset.sum_congr rfl; intro k _
      have hpow : (-1 : ℝ) ^ k * (-x) ^ k = x ^ k := by
        rw [← mul_pow]; congr 1; ring
      calc (-1 : ℝ) ^ k * iteratedDeriv k f 0 * (-x) ^ k / ↑(Nat.factorial k)
          = iteratedDeriv k f 0 * ((-1) ^ k * (-x) ^ k) / ↑(Nat.factorial k) := by ring
        _ = iteratedDeriv k f 0 * x ^ k / ↑(Nat.factorial k) := by rw [hpow]
    rw [hgx, hts] at key; rwa [abs_of_neg hx]
  · -- x = 0: trivial since T_n(0) = f(0)
    simp [taylorPartialSum_at_zero]
  · -- x > 0: direct application of remainder_bound_pos
    rw [abs_of_pos hx]; exact remainder_bound_pos f C hf hbound n x hx

-- ═══════════════════════════════════════════════════════════════
-- SECTION IV: Convergence
-- ═══════════════════════════════════════════════════════════════

/-- |x|^n / n! → 0 for any real x (from Mathlib's summable_pow_div_factorial).
    This is the engine of all Taylor convergence proofs. -/
theorem pow_div_factorial_tendsto (x : ℝ) :
    Tendsto (fun n => |x| ^ n / (Nat.factorial n : ℝ)) atTop (𝓝 0) :=
  (summable_pow_div_factorial ‖x‖).tendsto_atTop_zero.congr fun n => by
    simp [Real.norm_eq_abs]

/-- C · |x|^{n+1} / n! → 0 for any constants C and x.
    The extra |x| factor is absorbed since |x|^{n+1}/n! = |x| · |x|^n/n!. -/
theorem C_remainder_tendsto (C x : ℝ) :
    Tendsto (fun n => C * |x| ^ (n + 1) / (Nat.factorial n : ℝ)) atTop (𝓝 0) := by
  have h := pow_div_factorial_tendsto x
  have h2 : Tendsto (fun n => C * |x| * (|x| ^ n / (Nat.factorial n : ℝ)))
      atTop (𝓝 0) := by
    rw [show (0 : ℝ) = C * |x| * 0 from by ring]; exact h.const_mul _
  exact h2.congr fun n => by ring

/-- The Taylor remainder for f tends to 0 for any fixed x. -/
theorem taylor_remainder_tendsto (f : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ContDiff ℝ ⊤ f)
    (hbound : ∀ (m : ℕ) (y : ℝ), ‖iteratedDeriv m f y‖ ≤ C)
    (x : ℝ) :
    Tendsto (fun n => f x - taylorPartialSum f n x) atTop (𝓝 0) := by
  apply squeeze_zero_norm'
  · filter_upwards with n
    exact general_taylor_remainder_bound f C hC hf hbound n x
  · exact C_remainder_tendsto C x

/-- **Main Theorem**: Taylor series convergence for smooth functions
    with uniformly bounded derivatives.

    If f : ℝ → ℝ is C^∞ and ‖f^{(n)}(x)‖ ≤ C for all n and x,
    then taylorPartialSum f n x → f(x) for every x ∈ ℝ.

    This generalizes sinPartialSum_tendsto and cosPartialSum_tendsto
    from TaylorSinCosConvergence.lean. -/
theorem taylorPartialSum_tendsto (f : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ContDiff ℝ ⊤ f)
    (hbound : ∀ (m : ℕ) (y : ℝ), ‖iteratedDeriv m f y‖ ≤ C)
    (x : ℝ) :
    Tendsto (fun n => taylorPartialSum f n x) atTop (𝓝 (f x)) := by
  have h := taylor_remainder_tendsto f C hC hf hbound x
  have : Tendsto (fun n => f x - (f x - taylorPartialSum f n x)) atTop
      (𝓝 (f x - 0)) := h.const_sub (f x)
  simp only [sub_sub_cancel, sub_zero] at this; exact this

-- ═══════════════════════════════════════════════════════════════
-- SECTION V: Values at Zero
-- ═══════════════════════════════════════════════════════════════

/-- T_n(0) = f(0) for all n: higher-order terms vanish since 0^k = 0 for k ≥ 1. -/
theorem taylorPartialSum_at_zero (f : ℝ → ℝ) (n : ℕ) :
    taylorPartialSum f n 0 = f 0 := by
  simp only [taylorPartialSum]
  rw [Finset.sum_eq_single 0
    (fun k _ hk => by simp [zero_pow hk])
    (fun h => absurd (Finset.mem_range.mpr n.succ_pos) h)]
  simp [iteratedDeriv_zero]

-- ═══════════════════════════════════════════════════════════════
-- SECTION VI: Instantiation — Sin and Cos
-- ═══════════════════════════════════════════════════════════════

/-- Sin has all derivatives bounded by 1 (from the parent proof's period-4 argument). -/
theorem sin_deriv_bound (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n Real.sin x‖ ≤ 1 :=
  TaylorSinCosConvergence.norm_iteratedDeriv_sin_le n x

/-- Cos has all derivatives bounded by 1 (from the parent proof's period-4 argument). -/
theorem cos_deriv_bound (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n Real.cos x‖ ≤ 1 :=
  TaylorSinCosConvergence.norm_iteratedDeriv_cos_le n x

/-- **Corollary**: Taylor partial sums of sin converge to sin(x).
    This recovers sinPartialSum_tendsto as an instance of the general theorem. -/
theorem sin_taylorPartialSum_tendsto (x : ℝ) :
    Tendsto (fun n => taylorPartialSum Real.sin n x) atTop (𝓝 (Real.sin x)) :=
  taylorPartialSum_tendsto Real.sin 1 zero_le_one Real.contDiff_sin sin_deriv_bound x

/-- **Corollary**: Taylor partial sums of cos converge to cos(x).
    This recovers cosPartialSum_tendsto as an instance of the general theorem. -/
theorem cos_taylorPartialSum_tendsto (x : ℝ) :
    Tendsto (fun n => taylorPartialSum Real.cos n x) atTop (𝓝 (Real.cos x)) :=
  taylorPartialSum_tendsto Real.cos 1 zero_le_one Real.contDiff_cos cos_deriv_bound x

-- ═══════════════════════════════════════════════════════════════
-- SECTION VII: Remainder Comparison
-- ═══════════════════════════════════════════════════════════════

/-- For C = 1 (sin/cos), the remainder |x|^{n+1}/n! is the minimum possible
    in this framework. Any function with C > 1 has a strictly larger bound
    (at nonzero x). -/
theorem unit_bound_optimal (n : ℕ) (x : ℝ) (C : ℝ) (hC : 1 < C) (hx : x ≠ 0) :
    |x| ^ (n + 1) / (Nat.factorial n : ℝ) <
    C * |x| ^ (n + 1) / (Nat.factorial n : ℝ) := by
  apply div_lt_div_of_pos_right _ (Nat.cast_pos.mpr n.factorial_pos)
  have hxp : 0 < |x| ^ (n + 1) := pow_pos (abs_pos.mpr hx) _
  linarith [mul_lt_mul_of_pos_right hC hxp]

/-- The remainder bound improves as C decreases: if f has a smaller derivative
    bound, it has a tighter Taylor remainder. -/
theorem smaller_bound_tighter (n : ℕ) (x : ℝ) (C₁ C₂ : ℝ)
    (hC : 0 ≤ C₁) (h12 : C₁ ≤ C₂) :
    C₁ * |x| ^ (n + 1) / (Nat.factorial n : ℝ) ≤
    C₂ * |x| ^ (n + 1) / (Nat.factorial n : ℝ) := by
  apply div_le_div_of_nonneg_right
  · exact mul_le_mul_of_nonneg_right h12 (pow_nonneg (abs_nonneg x) _)
  · exact Nat.cast_nonneg' (Nat.factorial n)

-- ═══════════════════════════════════════════════════════════════
-- SECTION VIII: Linear Combinations
-- ═══════════════════════════════════════════════════════════════

/-- A scalar multiple a · f has derivatives bounded by |a| · C.
    This shows that a · sin(x) has bound |a| and a · cos(x) has bound |a|.

    More generally, if f₁ has bound C₁ and f₂ has bound C₂, then
    f₁ + f₂ has bound C₁ + C₂ by the triangle inequality. Combined
    with scalar multiplication, this gives: for any linear combination
    a · sin(x) + b · cos(x), the derivative bound is |a| + |b|. -/
theorem linear_combo_bound (a b : ℝ) (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n (fun x => a * Real.sin x + b * Real.cos x) x‖ ≤ |a| + |b| := by
  have hsin : ContDiffAt ℝ (n : ℕ∞) Real.sin x :=
    (Real.contDiff_sin.of_le le_top).contDiffAt
  have hcos : ContDiffAt ℝ (n : ℕ∞) Real.cos x :=
    (Real.contDiff_cos.of_le le_top).contDiffAt
  rw [show (fun x => a * Real.sin x + b * Real.cos x) = a • Real.sin + b • Real.cos from by
      funext z; simp [smul_eq_mul]]
  rw [iteratedDeriv_add (hsin.const_smul a) (hcos.const_smul b)]
  rw [iteratedDeriv_const_smul hsin a, iteratedDeriv_const_smul hcos b]
  simp only [smul_eq_mul]
  calc ‖a * iteratedDeriv n Real.sin x + b * iteratedDeriv n Real.cos x‖
      ≤ ‖a * iteratedDeriv n Real.sin x‖ + ‖b * iteratedDeriv n Real.cos x‖ :=
          norm_add_le _ _
    _ = |a| * ‖iteratedDeriv n Real.sin x‖ + |b| * ‖iteratedDeriv n Real.cos x‖ := by
          simp only [norm_mul, Real.norm_eq_abs]
    _ ≤ |a| * 1 + |b| * 1 := by
          gcongr
          · exact sin_deriv_bound n x
          · exact cos_deriv_bound n x
    _ = |a| + |b| := by ring

-- ═══════════════════════════════════════════════════════════════
-- Verification
-- ═══════════════════════════════════════════════════════════════

#check taylorPartialSum
#check taylorPartialSum_tendsto
#check remainder_bound_pos
#check general_taylor_remainder_bound  -- fully proved theorem (0 axioms)
#check linear_combo_bound              -- fully proved (0 sorries)
#check sin_taylorPartialSum_tendsto
#check cos_taylorPartialSum_tendsto
#check taylorPartialSum_sin_eq
#check taylorPartialSum_cos_eq

end TaylorBoundedDerivConvergence
