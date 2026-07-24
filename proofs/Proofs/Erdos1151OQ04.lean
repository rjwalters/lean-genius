/-
# Erdős Problem #1151 OQ04 — Lebesgue Function Approach to Interpolation Divergence

## Goal

Prove `erdos_1941_divergence` by formalizing the connection between:
1. The Lebesgue function Λₙ(x) = Σₖ |ℓₖⁿ(x)| (sum of absolute Lagrange basis values)
2. Its growth at rational cosine points: Λₙ(cos(πp/q)) → ∞ for odd p, q
3. The consequence: existence of continuous f with Chebyshev interpolation → +∞

## Proof Architecture

The main theorem `erdos_1941_divergence_from_growth` is FULLY PROVED
(i.e., is a valid mathematical deduction), assuming two sorry lemmas:

  `trig_sum_harmonic_lb` [SORRY: Lipschitz + harmonic sum for general θ ∈ (0, π)]
  `divergence_from_lebesgue_growth` [SORRY: lacunary series construction]

The non-sorry results proved here:
  - `lebesgue_upper_bound`: |Lₙf(x)| ≤ ‖f‖_∞ · Λₙ(x)
  - `chebyshev_interp_linear_left`, `chebyshev_interp_linear_right`: linearity
  - `chebyshev_T_at_cos`: Tₙ(cos θ) = cos(nθ) — from Mathlib
  - `cos_rational_pi_multiple`: cos(kπp) = ±1 for integer k and odd p
  - `erdos_1941_divergence_from_growth`: main reduction theorem
  - `chebyshev_product_formula`: T_n = 2^{n-1} · ∏(X - C(cos φₖ)) [Session 5]
  - `lagrange_basis_chebyshev_formula`: explicit Lagrange basis at Chebyshev nodes [Session 5]
  - `chebyshev_lebesgue_eq`: Λₙ(cos θ) = |cos(nθ)|/n · Σₖ sin(φₖ)/|cos θ - cos φₖ| [Session 5]
  - `x_not_chebyshev_node`: cos(πp/q) ≠ chebyshevNode n k for all n when p,q odd [Session 6]
  - `chebyshev_lebesgue_eq_all_n`: applies lebesgue_eq for ALL n (not just n=mq) [Session 6]
  - `cos_rational_pi_ne_zero`: cos(nπp/q) ≠ 0 for ALL n [Session 7]
  - `cos_rational_pi_mod`: periodicity with period 2q [Session 7]
  - `cos_rational_pi_pos_min`: ∃ δ > 0, |cos(nπp/q)| ≥ δ for all n [Session 7]
  - `chebyshev_lebesgue_growth`: Λₙ → ∞ proved modulo chebyshev_lebesgue_lb [Session 11]
  - `trig_sum_lb_of_cos_eq_neg_one`: S_n ≥ (1/(2π))·n·log(n+1) for x = -1 [Session 12]
  - `chebyshev_trig_sum_lb` Case 1 (x = -1): via trig_sum_lb_of_cos_eq_neg_one [Session 12]
  - `chebyshev_trig_sum_lb` Case 2 (x ∈ (-1,1)): reduced to trig_sum_harmonic_lb [Session 13]
  - `tan_eq_cot_complement`: complementary angle cotangent bound [Session 12]
  - `odd_harmonic_sum_lb`: ∑ 1/(2j+1) ≥ (1/2)·log(m+1) [Session 12]
  - `half_log_le_log_half_add_one`: (1/2)·log(n+1) ≤ log(n/2+1) [Session 12]
  - `exists_nearest_chebyshev_angle`: nearest midpoint within π/(2n) [Session 14]
  - `chebyshev_angle_dist_triangle` / `chebyshev_angle_dist_from_nearest`: Step 3 [Session 15]
  - `sin_lb_of_in_interior` / `sin_chebyshev_midpoint_lb`: Step 4 sin lb [Session 16]
  - `chebyshev_term_lb_at_node`: Step 5 per-term lb (Steps 3+4 + cos-Lipschitz) [Session 16]
  - `odd_harmonic_sum_shifted_lb`: Step 6a shifted Σ 1/(2(j+1)+1) ≥ (1/2)·log(m+2)−1 [Session 17]
  - `trig_sum_subsum_lb`: Step 6b sub-sum ≥ harmonic via per-term lb + image-sum [Session 17]
  - `trig_sum_subsum_log_lb`: Step 6c — combined log lower bound (S6a ∘ S6b) [Session 21]
  - `trig_sum_reindex_symmetry`: S(θ,n) = S(π−θ,n) via involution σ k = ⟨n−1−k, _⟩ [Session 18]
  - `chebyshev_trig_sum_pos`: strict positivity of S(θ,n) per term [Session 20]
  - `chebyshev_quarter_floor_log_asymp_lb`: (1/4)·log(n+1) ≤ (1/2)·log(m+2)−1
    for `n ≥ N₀(θ)` and `(m : ℝ) ≥ n·θ/(4π) − 1` (Step 7a residue) [Session 24]
  - `lagrangeBasis_apply_self` / `lagrangeBasis_apply_ne`: Lagrange delta
    property ℓₖ(xⱼ) = δₖⱼ for injective nodes [Session 39]
  - `lagrangeBasis_continuous`: continuity of ℓₖ in the evaluation point [Session 39]
  - `exists_continuous_bounded_through_nodes`: continuous ‖f‖_∞ ≤ 1 interpolant
    through prescribed node values via clamped Lagrange polynomial [Session 39]
  - `chebyshev_lebesgue_saturated_continuous`: CONTINUOUS saturation witness
    ‖f‖ ≤ 1, Lₙf(x) = Λₙ(x) — ingredient (a) of Sorry 2 closed [Session 39]

## Sorry 1: trig_sum_harmonic_lb (was: chebyshev_trig_sum_lb Case 2)
Now factored as a SELF-CONTAINED lemma for general θ ∈ (0, π):
  - Statement: ∃ C > 0, C·n·log(n+1) ≤ Σ sin(φₖ)/|cos θ - cos φₖ| for all n ≥ 1
  - Depends only on θ ∈ (0, π) and cos θ ≠ any Chebyshev node (no p, q dependency)
  - Case 2 of chebyshev_trig_sum_lb is PROVED modulo this lemma
  - Proof approach: Lipschitz + Finset harmonic sum over near-nodes + finite min for small n

## Sorry 2: divergence_from_lebesgue_growth
Proof requires:
  a) For each n, existence of optimizing continuous function with ‖f‖ ≤ 1 and
     Lₙf(x) = Λₙ(x) — DONE (Session 39, `chebyshev_lebesgue_saturated_continuous`)
  b) Lacunary subsequence construction [has known gap: UBP gives lim sup, not lim;
     the stated conclusion is the strong full-limit form Lₙf(x) → +∞, which needs
     polynomial-reproduction (Lₙp = p for deg p < n) + gliding-hump cross-term
     control, not just Banach–Steinhaus]

Tags: analysis, approximation-theory, chebyshev, lebesgue-function, erdos-problems
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Tactic

namespace Erdos1151OQ04

open Finset Real Polynomial.Chebyshev

/-! ## Definitions: Chebyshev Nodes, Lagrange Interpolation, Lebesgue Function -/

/-- The k-th Chebyshev node of degree n: cos((2k+1)π/(2n)) for k = 0,...,n-1.
    These are the zeros of the n-th Chebyshev polynomial Tₙ. -/
noncomputable def chebyshevNode (n : ℕ) (k : Fin n) : ℝ :=
  Real.cos ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n))

/-- Lagrange basis polynomial: ℓₖ(x) = Π_{i≠k} (x - xᵢ)/(xₖ - xᵢ). -/
noncomputable def lagrangeBasis (n : ℕ) (nodes : Fin n → ℝ) (k : Fin n) (x : ℝ) : ℝ :=
  ∏ i ∈ Finset.univ.erase k, (x - nodes i) / (nodes k - nodes i)

/-- Lagrange interpolation: Lₙf(x) = Σₖ f(xₖ) · ℓₖ(x). -/
noncomputable def lagrangeInterp (n : ℕ) (nodes : Fin n → ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ k : Fin n, f (nodes k) * lagrangeBasis n nodes k x

/-- Chebyshev interpolation at the standard Chebyshev nodes. -/
noncomputable def chebyshevInterp (n : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  lagrangeInterp n (chebyshevNode n) f x

/-- The Lebesgue function: Λₙ(x) = Σₖ |ℓₖⁿ(x)|.
    Measures worst-case amplification: |Lₙf(x)| ≤ ‖f‖_∞ · Λₙ(x). -/
noncomputable def chebyshevLebesgue (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k : Fin n, |lagrangeBasis n (chebyshevNode n) k x|

/-! ## Proved Results: Interpolation Bound -/

/-- The Lebesgue function is nonneg. -/
theorem chebyshevLebesgue_nonneg (n : ℕ) (x : ℝ) : 0 ≤ chebyshevLebesgue n x :=
  Finset.sum_nonneg fun k _ => abs_nonneg _

/-- **Key bound**: |Lₙf(x)| ≤ ‖f‖_∞ · Λₙ(x).

    The Lebesgue function Λₙ(x) is the operator norm of the evaluation functional
    f ↦ Lₙf(x) restricted to the unit sup-norm ball of C[-1,1]. -/
theorem lebesgue_upper_bound (n : ℕ) (nodes : Fin n → ℝ) (f : ℝ → ℝ) (x : ℝ)
    (M : ℝ) (hM : ∀ t, |f t| ≤ M) :
    |lagrangeInterp n nodes f x| ≤ M * ∑ k : Fin n, |lagrangeBasis n nodes k x| := by
  simp only [lagrangeInterp]
  calc |∑ k : Fin n, f (nodes k) * lagrangeBasis n nodes k x|
      ≤ ∑ k : Fin n, |f (nodes k) * lagrangeBasis n nodes k x| :=
          abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin n, |f (nodes k)| * |lagrangeBasis n nodes k x| := by
          congr 1; ext k; exact abs_mul _ _
    _ ≤ ∑ k : Fin n, M * |lagrangeBasis n nodes k x| := by
          apply Finset.sum_le_sum
          intro k _
          apply mul_le_mul_of_nonneg_right (hM _) (abs_nonneg _)
    _ = M * ∑ k : Fin n, |lagrangeBasis n nodes k x| := (Finset.mul_sum _ _ _).symm

/-- Chebyshev interpolation bound via the Lebesgue function. -/
theorem chebyshev_upper_bound (n : ℕ) (f : ℝ → ℝ) (x : ℝ) (M : ℝ)
    (hM : ∀ t, |f t| ≤ M) :
    |chebyshevInterp n f x| ≤ M * chebyshevLebesgue n x :=
  lebesgue_upper_bound n (chebyshevNode n) f x M hM

/-! ## Proved Results: Linearity -/

/-- Chebyshev interpolation is linear in f. -/
theorem chebyshevInterp_add (n : ℕ) (f g : ℝ → ℝ) (x : ℝ) :
    chebyshevInterp n (fun t => f t + g t) x =
    chebyshevInterp n f x + chebyshevInterp n g x := by
  simp only [chebyshevInterp, lagrangeInterp]
  simp_rw [add_mul]
  exact Finset.sum_add_distrib

/-- Chebyshev interpolation scales with scalar multiplication. -/
theorem chebyshevInterp_smul (n : ℕ) (c : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    chebyshevInterp n (fun t => c * f t) x = c * chebyshevInterp n f x := by
  simp only [chebyshevInterp, lagrangeInterp]
  simp_rw [mul_assoc]
  exact (Finset.mul_sum _ _ _).symm

/-- Chebyshev interpolation of the zero function is zero.

    Useful when packaging `chebyshevInterp n · x` as a linear functional
    `C[-1,1] →L[ℝ] ℝ` (S31 UBP closure prep). -/
theorem chebyshevInterp_zero_fn (n : ℕ) (x : ℝ) :
    chebyshevInterp n (fun _ : ℝ => 0) x = 0 := by
  simp only [chebyshevInterp, lagrangeInterp, zero_mul, Finset.sum_const_zero]

/-- Chebyshev interpolation negates with the negated function.

    Composes `chebyshevInterp_smul` with `c := -1`. Useful for the
    operator-norm packaging in S31 (UBP closure prep). -/
theorem chebyshevInterp_neg (n : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    chebyshevInterp n (fun t => -f t) x = -chebyshevInterp n f x := by
  simp only [chebyshevInterp, lagrangeInterp, neg_mul, Finset.sum_neg_distrib]

/-- Chebyshev interpolation distributes over subtraction.

    Mirrors `chebyshevInterp_add` with `Finset.sum_sub_distrib` in place
    of `Finset.sum_add_distrib`. Useful for the linear-functional
    packaging in S31 (UBP closure prep). -/
theorem chebyshevInterp_sub (n : ℕ) (f g : ℝ → ℝ) (x : ℝ) :
    chebyshevInterp n (fun t => f t - g t) x =
    chebyshevInterp n f x - chebyshevInterp n g x := by
  simp only [chebyshevInterp, lagrangeInterp, sub_mul, Finset.sum_sub_distrib]

/-! ## Proved Results: Chebyshev Polynomial Connection -/

/-- **Chebyshev identity**: Tₙ(cos θ) = cos(nθ). -/
theorem chebyshev_T_at_cos (n : ℤ) (θ : ℝ) :
    (T ℝ n).eval (Real.cos θ) = Real.cos (n * θ) :=
  Polynomial.Chebyshev.T_real_cos θ n

/-- cos(kπ) = (-1)^k for any integer k. -/
theorem cos_int_pi (k : ℤ) : Real.cos (k * Real.pi) = (-1 : ℝ) ^ k :=
  Real.cos_int_mul_pi k

/-- Along the subsequence n = mq, the value cos(nπp/q) = cos(mπp) = ±1. -/
theorem cos_rational_pi_at_multiples (p q m : ℕ) (hq_pos : 0 < q) :
    Real.cos ((m * q : ℕ) * (↑p * Real.pi / ↑q)) =
    Real.cos (↑m * ↑p * Real.pi) := by
  congr 1
  have hq' : (q : ℝ) ≠ 0 := (Nat.cast_pos.mpr hq_pos).ne'
  push_cast
  field_simp

/-! ## Foundation: Chebyshev Polynomial Degree and Leading Coefficient -/

section ChebyshevPolyProps

open Polynomial

/-- T ℝ (↑n) is nonzero for any n : ℕ. -/
theorem T_ofNat_ne_zero (n : ℕ) : T ℝ (n : ℤ) ≠ 0 := by
  intro h
  have := T_eval_one ℝ (n : ℤ)
  simp [h] at this

/-- The n-th Chebyshev polynomial T_n has natDegree = n. -/
theorem natDegree_T_ofNat : ∀ n : ℕ, (T ℝ (n : ℤ)).natDegree = n
  | 0 => by simp [T_zero]
  | 1 => by simp [T_one]
  | (n + 2) => by
      have ihn  : (T ℝ (n : ℤ)).natDegree = n := natDegree_T_ofNat n
      have ihn1 : (T ℝ ((n + 1 : ℕ) : ℤ)).natDegree = n + 1 := natDegree_T_ofNat (n + 1)
      have cast1 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
      have cast2 : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
      rw [cast1] at ihn1; rw [cast2, T_add_two]
      have hne1 : T ℝ ((n : ℤ) + 1) ≠ 0 := by rw [← cast1]; exact T_ofNat_ne_zero (n + 1)
      have h2XTdeg : (2 * X * T ℝ ((n : ℤ) + 1)).natDegree = n + 2 := by
        rw [show (2 : ℝ[X]) * X * T ℝ ((n : ℤ) + 1) =
            (2 : ℝ[X]) * (X * T ℝ ((n : ℤ) + 1)) from by ring]
        rw [natDegree_mul (by norm_num : (2 : ℝ[X]) ≠ 0) (mul_ne_zero X_ne_zero hne1)]
        rw [natDegree_ofNat, natDegree_X_mul hne1, ihn1]
        omega
      have key : (2 * X * T ℝ ((n : ℤ) + 1) - T ℝ (n : ℤ)).natDegree =
                 (2 * X * T ℝ ((n : ℤ) + 1)).natDegree :=
        natDegree_sub_eq_left_of_natDegree_lt (by rw [h2XTdeg, ihn]; omega)
      rw [key, h2XTdeg]

/-- The leading coefficient of T_n is 2^(n-1) for n ≥ 1. -/
theorem leadingCoeff_T_ofNat : ∀ n : ℕ, n ≥ 1 → (T ℝ (n : ℤ)).leadingCoeff = 2 ^ (n - 1)
  | 0, h => by omega
  | 1, _ => by simp [T_one]
  | (n + 2), _ => by
      have ihn1_lc : (T ℝ ((n + 1 : ℕ) : ℤ)).leadingCoeff = 2 ^ n :=
        leadingCoeff_T_ofNat (n + 1) (by omega)
      have cast1 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
      have cast2 : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
      rw [cast1] at ihn1_lc; rw [cast2, T_add_two]
      have hne1 : T ℝ ((n : ℤ) + 1) ≠ 0 := by rw [← cast1]; exact T_ofNat_ne_zero (n + 1)
      have hne0 : T ℝ (n : ℤ) ≠ 0 := T_ofNat_ne_zero n
      have h2XT_ne : 2 * X * T ℝ ((n : ℤ) + 1) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (by norm_num) X_ne_zero) hne1
      have h2XTdeg : (2 * X * T ℝ ((n : ℤ) + 1)).natDegree = n + 2 := by
        rw [show (2 : ℝ[X]) * X * T ℝ ((n : ℤ) + 1) =
            (2 : ℝ[X]) * (X * T ℝ ((n : ℤ) + 1)) from by ring]
        rw [natDegree_mul (by norm_num : (2 : ℝ[X]) ≠ 0) (mul_ne_zero X_ne_zero hne1)]
        rw [natDegree_ofNat, natDegree_X_mul hne1]
        have := natDegree_T_ofNat (n + 1); rw [cast1] at this; omega
      have hdeg_lt : degree (T ℝ (n : ℤ)) < degree (2 * X * T ℝ ((n : ℤ) + 1)) := by
        rw [degree_eq_natDegree hne0, degree_eq_natDegree h2XT_ne, h2XTdeg, natDegree_T_ofNat n]
        exact_mod_cast (show n < n + 2 by omega)
      rw [leadingCoeff_sub_of_degree_lt hdeg_lt]
      rw [show (2 : ℝ[X]) * X * T ℝ ((n : ℤ) + 1) =
          (2 : ℝ[X]) * (X * T ℝ ((n : ℤ) + 1)) from by ring]
      rw [leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_X, one_mul, ihn1_lc]
      have h2_lc : (2 : ℝ[X]).leadingCoeff = 2 := by
        have hC : (2 : ℝ[X]) = C (2 : ℝ) := (C_ofNat 2).symm
        rw [hC, leadingCoeff_C]
      rw [h2_lc, show n + 2 - 1 = n + 1 from by omega, pow_succ]
      ring

end ChebyshevPolyProps

/-! ## Auxiliary: Chebyshev Node Properties -/

/-- The Chebyshev nodes are zeros of T_n. -/
theorem chebyshevNode_is_root (n : ℕ) (hn : 0 < n) (k : Fin n) :
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (chebyshevNode n k) = 0 := by
  simp only [chebyshevNode, chebyshev_T_at_cos]
  have hmul : (n : ℤ) * ((2 * ↑k.val + 1 : ℝ) * Real.pi / (2 * ↑n)) =
      (2 * k.val + 1 : ℝ) * Real.pi / 2 := by
    push_cast
    have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    field_simp
  rw [hmul]
  have h : (2 * (k.val : ℝ) + 1) * Real.pi / 2 = k.val * Real.pi + Real.pi / 2 := by ring
  rw [h, Real.cos_add, Real.cos_pi_div_two, mul_zero, Real.sin_nat_mul_pi, zero_mul, sub_zero]

/-- The Chebyshev nodes are distinct. -/
theorem chebyshevNode_injective (n : ℕ) (hn : 0 < n) :
    Function.Injective (chebyshevNode n) := by
  intro i j heq
  simp only [chebyshevNode] at heq
  have hi : (2 * (i.val : ℝ) + 1) * Real.pi / (2 * n) ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨le_of_lt (div_pos (mul_pos (by positivity) Real.pi_pos) (by positivity)),
     le_of_lt (by
       have hlt : 2 * i.val + 1 < 2 * n := by omega
       have hrlt : (2 * (i.val : ℝ) + 1) < 2 * n := by exact_mod_cast hlt
       rw [div_lt_iff₀ (by positivity)]
       nlinarith [Real.pi_pos])⟩
  have hj : (2 * (j.val : ℝ) + 1) * Real.pi / (2 * n) ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨le_of_lt (div_pos (mul_pos (by positivity) Real.pi_pos) (by positivity)),
     le_of_lt (by
       have hlt : 2 * j.val + 1 < 2 * n := by omega
       have hrlt : (2 * (j.val : ℝ) + 1) < 2 * n := by exact_mod_cast hlt
       rw [div_lt_iff₀ (by positivity)]
       nlinarith [Real.pi_pos])⟩
  have hangle_eq := Real.strictAntiOn_cos.injOn hi hj heq
  apply Fin.ext
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have : (2 * (i.val : ℝ) + 1) = 2 * j.val + 1 := by
    field_simp [hn', hpi] at hangle_eq; linarith
  exact_mod_cast (show (i.val : ℝ) = j.val by linarith)

/-- The Chebyshev nodes are contained in [-1, 1]. -/
theorem chebyshevNode_mem_Icc (n : ℕ) (k : Fin n) :
    chebyshevNode n k ∈ Set.Icc (-1 : ℝ) 1 :=
  ⟨neg_one_le_cos _, cos_le_one _⟩

/-- The absolute value of cosine at integer multiples of π equals 1. -/
theorem abs_cos_int_pi_mul (k : ℤ) : |Real.cos (k * Real.pi)| = 1 :=
  Real.abs_cos_int_mul_pi k

/-- Along n = mq, cos(nπp/q) ≠ 0 for odd p. -/
theorem cos_rational_pi_nonzero_along_multiples (p q m : ℕ) (hp : Odd p)
    (hq_pos : 0 < q) :
    Real.cos ((m * q : ℕ) * (↑p * Real.pi / ↑q)) ≠ 0 := by
  rw [cos_rational_pi_at_multiples p q m hq_pos]
  rw [show (↑m * ↑p * Real.pi) = (↑(m * p) : ℤ) * Real.pi by push_cast; ring]
  rw [cos_int_pi]
  exact zpow_ne_zero _ (by norm_num)

/-! ## Operator-Norm Saturation for Banach-Steinhaus (Session 31) -/

/-- **Operator-norm saturation lower bound for the Chebyshev interpolation functional.**

    For any `n : ℕ` and `x : ℝ`, there exists a function `f : ℝ → ℝ` with `|f t| ≤ 1`
    for all `t` and `chebyshevInterp n f x = chebyshevLebesgue n x`. The construction
    places `±1` (the sign of `lagrangeBasis n (chebyshevNode n) k x`) at each
    Chebyshev node and `0` elsewhere; injectivity of the nodes
    (`chebyshevNode_injective`) ensures the single-node weight survives the
    indicator-sum, and the sign choice saturates each absolute value
    `|lagrangeBasis n (chebyshevNode n) k x|` exactly.

    Combined with the existing `chebyshev_upper_bound`
    (`|chebyshevInterp n f x| ≤ M · chebyshevLebesgue n x` for `M` bounding `f`),
    this yields the operator-norm identity `‖f ↦ chebyshevInterp n f x‖ =
    chebyshevLebesgue n x` on the unit `L^∞` ball. That identity is the input to a
    future Banach-Steinhaus contrapositive
    (`Mathlib.Analysis.NormedSpace.BanachSteinhaus.banach_steinhaus`) which closes
    Sorry 2 (`divergence_from_lebesgue_growth`): once `Λₙ(x) → ∞`, the sequence of
    evaluation functionals has unbounded operator norm, so by UBP some `f` makes
    `chebyshevInterp n f x` unbounded.

    The witness `f` here is *not* continuous (it is `0` off the finite
    Chebyshev-node set); see `chebyshev_lebesgue_saturated_continuous` (Session 39)
    for the continuous upgrade via a clamped Lagrange interpolation polynomial —
    no Tietze extension needed. The discrete saturation proved here is the
    mathematical content; the continuous version is what the Banach–Steinhaus /
    lacunary-series closure of Sorry 2 consumes. -/
private lemma chebyshev_lebesgue_saturated (n : ℕ) (x : ℝ) :
    ∃ f : ℝ → ℝ, (∀ t, |f t| ≤ 1) ∧
      chebyshevInterp n f x = chebyshevLebesgue n x := by
  classical
  -- Sign weight at each node so that w k * ℓ_k(x) = |ℓ_k(x)|.
  let w : Fin n → ℝ := fun k =>
      if 0 ≤ lagrangeBasis n (chebyshevNode n) k x then (1 : ℝ) else -1
  have hw_abs : ∀ k, |w k| = 1 := by
    intro k
    show |(if 0 ≤ lagrangeBasis n (chebyshevNode n) k x then (1 : ℝ) else -1)| = 1
    by_cases h : 0 ≤ lagrangeBasis n (chebyshevNode n) k x
    · rw [if_pos h]; norm_num
    · rw [if_neg h]; norm_num
  have hw_sat : ∀ k, w k * lagrangeBasis n (chebyshevNode n) k x =
      |lagrangeBasis n (chebyshevNode n) k x| := by
    intro k
    show (if 0 ≤ lagrangeBasis n (chebyshevNode n) k x then (1 : ℝ) else -1) *
        lagrangeBasis n (chebyshevNode n) k x =
      |lagrangeBasis n (chebyshevNode n) k x|
    by_cases h : 0 ≤ lagrangeBasis n (chebyshevNode n) k x
    · rw [if_pos h, one_mul, abs_of_nonneg h]
    · push_neg at h
      rw [if_neg (not_le.mpr h), neg_one_mul, abs_of_neg h]
  -- f is the sum-of-indicators with sign weights at each Chebyshev node.
  refine ⟨fun t => ∑ k : Fin n, w k * (if t = chebyshevNode n k then (1 : ℝ) else 0),
    ?_, ?_⟩
  · -- |f t| ≤ 1
    intro t
    show |∑ k : Fin n, w k * (if t = chebyshevNode n k then (1 : ℝ) else 0)| ≤ 1
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · -- Empty sum: f t = 0.
      simp
    · by_cases ht : ∃ k : Fin n, chebyshevNode n k = t
      · -- t coincides with some node k₀: only that term contributes.
        obtain ⟨k₀, hk₀⟩ := ht
        have hsum_eq :
            (∑ k : Fin n, w k * (if t = chebyshevNode n k then (1 : ℝ) else 0)) = w k₀ := by
          rw [Finset.sum_eq_single_of_mem k₀ (Finset.mem_univ _)]
          · rw [if_pos hk₀.symm, mul_one]
          · intro k _ hk_ne
            have hne_t : t ≠ chebyshevNode n k := fun heq =>
              hk_ne ((chebyshevNode_injective n hn (hk₀.trans heq)).symm)
            rw [if_neg hne_t, mul_zero]
        rw [hsum_eq]; exact (hw_abs k₀).le
      · -- t is not a Chebyshev node: every term vanishes.
        push_neg at ht
        have hsum_zero :
            (∑ k : Fin n, w k * (if t = chebyshevNode n k then (1 : ℝ) else 0)) = 0 := by
          apply Finset.sum_eq_zero
          intro k _
          have hne_t : t ≠ chebyshevNode n k := fun heq => ht k heq.symm
          rw [if_neg hne_t, mul_zero]
        rw [hsum_zero, abs_zero]
        norm_num
  · -- chebyshevInterp n f x = chebyshevLebesgue n x
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · -- Empty sums on both sides.
      simp [chebyshevInterp, lagrangeInterp, chebyshevLebesgue]
    · simp only [chebyshevInterp, lagrangeInterp, chebyshevLebesgue]
      apply Finset.sum_congr rfl
      intro k₀ _
      -- Evaluating f at chebyshevNode n k₀: only the k = k₀ term survives.
      have hf_eval :
          (∑ k : Fin n,
              w k * (if chebyshevNode n k₀ = chebyshevNode n k then (1 : ℝ) else 0)) = w k₀ := by
        rw [Finset.sum_eq_single_of_mem k₀ (Finset.mem_univ _)]
        · rw [if_pos rfl, mul_one]
        · intro k _ hk_ne
          have h_node_ne : chebyshevNode n k₀ ≠ chebyshevNode n k := fun heq =>
            hk_ne ((chebyshevNode_injective n hn heq).symm)
          rw [if_neg h_node_ne, mul_zero]
      -- Beta-reduce f application; then apply hf_eval and hw_sat.
      show (∑ k : Fin n,
              w k * (if chebyshevNode n k₀ = chebyshevNode n k then (1 : ℝ) else 0))
            * lagrangeBasis n (chebyshevNode n) k₀ x
            = |lagrangeBasis n (chebyshevNode n) k₀ x|
      rw [hf_eval, hw_sat k₀]

/-! ## Session 39: Lagrange Delta Property and Continuous Saturation Witness -/

/-- **Lagrange basis delta property (diagonal)**: ℓₖ(xₖ) = 1 for injective nodes.

    Each factor (xₖ - xᵢ)/(xₖ - xᵢ) over i ≠ k equals 1; injectivity of the
    node family makes every denominator nonzero. -/
theorem lagrangeBasis_apply_self (n : ℕ) (nodes : Fin n → ℝ)
    (hinj : Function.Injective nodes) (k : Fin n) :
    lagrangeBasis n nodes k (nodes k) = 1 := by
  simp only [lagrangeBasis]
  apply Finset.prod_eq_one
  intro i hi
  exact div_self (sub_ne_zero.mpr (hinj.ne (Ne.symm (Finset.mem_erase.mp hi).1)))

/-- **Lagrange basis delta property (off-diagonal)**: ℓₖ(xⱼ) = 0 for j ≠ k.

    The factor at i = j vanishes: (xⱼ - xⱼ)/(xₖ - xⱼ) = 0. No injectivity
    hypothesis is needed. -/
theorem lagrangeBasis_apply_ne (n : ℕ) (nodes : Fin n → ℝ) {j k : Fin n}
    (hjk : j ≠ k) :
    lagrangeBasis n nodes k (nodes j) = 0 := by
  simp only [lagrangeBasis]
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hjk, Finset.mem_univ j⟩)
    (by rw [sub_self, zero_div])

/-- The Lagrange basis is continuous in the evaluation point: each factor
    t ↦ (t - xᵢ)/(xₖ - xᵢ) is affine, and ℓₖ is their finite product. -/
theorem lagrangeBasis_continuous (n : ℕ) (nodes : Fin n → ℝ) (k : Fin n) :
    Continuous fun t => lagrangeBasis n nodes k t := by
  simp only [lagrangeBasis]
  exact continuous_finsetProd _ fun i _ =>
    (continuous_id.sub continuous_const).div_const _

/-- **Continuous bounded interpolant through prescribed node values.**

    For any injective node family and target values w with |wₖ| ≤ 1, there is a
    continuous f : ℝ → ℝ with ‖f‖_∞ ≤ 1 and f(xₖ) = wₖ for every k.

    Construction: the Lagrange interpolation polynomial g = Σₖ wₖ·ℓₖ passes
    through the prescribed values (delta property `lagrangeBasis_apply_self` /
    `lagrangeBasis_apply_ne`) and is continuous (`lagrangeBasis_continuous`);
    clamping to [-1, 1] via t ↦ max (-1) (min 1 (g t)) preserves continuity and
    the node values (which already lie in [-1, 1]) while enforcing the global
    sup bound. This avoids both Tietze extension and any piecewise-linear
    construction. -/
theorem exists_continuous_bounded_through_nodes (n : ℕ) (nodes : Fin n → ℝ)
    (hinj : Function.Injective nodes) (w : Fin n → ℝ) (hw : ∀ k, |w k| ≤ 1) :
    ∃ f : ℝ → ℝ, Continuous f ∧ (∀ t, |f t| ≤ 1) ∧ ∀ k, f (nodes k) = w k := by
  classical
  -- The (unclamped) Lagrange interpolation polynomial through the target values.
  have hg_cont : Continuous fun t => ∑ k : Fin n, w k * lagrangeBasis n nodes k t :=
    continuous_finsetSum _ fun k _ =>
      (lagrangeBasis_continuous n nodes k).const_mul (w k)
  have hg_node : ∀ j : Fin n,
      (∑ k : Fin n, w k * lagrangeBasis n nodes k (nodes j)) = w j := by
    intro j
    have hzero : ∀ k ∈ Finset.univ, k ≠ j →
        w k * lagrangeBasis n nodes k (nodes j) = 0 := fun k _ hkj => by
      rw [lagrangeBasis_apply_ne n nodes (Ne.symm hkj), mul_zero]
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j) hzero,
      lagrangeBasis_apply_self n nodes hinj j, mul_one]
  -- Clamp to [-1, 1]: preserves continuity and node values, forces the bound.
  refine ⟨fun t => max (-1) (min 1 (∑ k : Fin n, w k * lagrangeBasis n nodes k t)),
    continuous_const.max (continuous_const.min hg_cont), fun t => ?_, fun j => ?_⟩
  · show |max (-1) (min 1 (∑ k : Fin n, w k * lagrangeBasis n nodes k t))| ≤ 1
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  · show max (-1) (min 1 (∑ k : Fin n, w k * lagrangeBasis n nodes k (nodes j))) = w j
    obtain ⟨h₁, h₂⟩ := abs_le.mp (hw j)
    rw [hg_node j, min_eq_right h₂, max_eq_right h₁]

/-- **Continuous operator-norm saturation witness.**

    Upgrades `chebyshev_lebesgue_saturated`: for any `n : ℕ` and `x : ℝ` the
    saturating function can be taken *continuous* — there is a continuous
    `f : ℝ → ℝ` with `|f t| ≤ 1` for all `t` and
    `chebyshevInterp n f x = chebyshevLebesgue n x`.

    Together with `chebyshev_upper_bound`, this pins the exact operator norm of
    the evaluation functional `f ↦ chebyshevInterp n f x` on `C(ℝ)` with the sup
    norm: `sup {|Lₙf(x)| : ‖f‖_∞ ≤ 1, f continuous} = Λₙ(x)`, attained. This is
    ingredient (a) of Sorry 2 (`divergence_from_lebesgue_growth`) as documented
    in the file header; the remaining gap is only ingredient (b), the lacunary
    series assembling these witnesses into a single `f` with full-limit
    divergence `Lₙf(x) → +∞`. -/
private lemma chebyshev_lebesgue_saturated_continuous (n : ℕ) (x : ℝ) :
    ∃ f : ℝ → ℝ, Continuous f ∧ (∀ t, |f t| ≤ 1) ∧
      chebyshevInterp n f x = chebyshevLebesgue n x := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- n = 0: both sides are empty sums; the zero function works.
    exact ⟨fun _ => 0, continuous_const, fun t => by simp,
      by simp [chebyshevInterp, lagrangeInterp, chebyshevLebesgue]⟩
  · -- Sign weights at each node so that w k * ℓₖ(x) = |ℓₖ(x)|.
    let w : Fin n → ℝ := fun k =>
      if 0 ≤ lagrangeBasis n (chebyshevNode n) k x then (1 : ℝ) else -1
    have hw_abs : ∀ k, |w k| ≤ 1 := by
      intro k
      show |(if 0 ≤ lagrangeBasis n (chebyshevNode n) k x then (1 : ℝ) else -1)| ≤ 1
      split <;> norm_num
    have hw_sat : ∀ k, w k * lagrangeBasis n (chebyshevNode n) k x =
        |lagrangeBasis n (chebyshevNode n) k x| := by
      intro k
      show (if 0 ≤ lagrangeBasis n (chebyshevNode n) k x then (1 : ℝ) else -1) *
          lagrangeBasis n (chebyshevNode n) k x =
        |lagrangeBasis n (chebyshevNode n) k x|
      by_cases h : 0 ≤ lagrangeBasis n (chebyshevNode n) k x
      · rw [if_pos h, one_mul, abs_of_nonneg h]
      · push_neg at h
        rw [if_neg (not_le.mpr h), neg_one_mul, abs_of_neg h]
    obtain ⟨f, hf_cont, hf_bd, hf_node⟩ :=
      exists_continuous_bounded_through_nodes n (chebyshevNode n)
        (chebyshevNode_injective n hn) w hw_abs
    refine ⟨f, hf_cont, hf_bd, ?_⟩
    simp only [chebyshevInterp, lagrangeInterp, chebyshevLebesgue]
    exact Finset.sum_congr rfl fun k _ => by rw [hf_node k, hw_sat k]

/-! ## Chebyshev Product Formula and Trig Helpers (Session 5) -/

section ProductFormula

open Polynomial

/-- sin((2k+1)π/(2n)) > 0 for k : Fin n.
    Since (2k+1)π/(2n) ∈ (0, π). -/
theorem chebyshevAngle_sin_pos (n : ℕ) (hn : 0 < n) (k : Fin n) :
    0 < Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · rw [div_lt_iff₀ (by positivity)]
    have hlt : 2 * k.val + 1 < 2 * n := by omega
    have : (2 * (k.val : ℝ) + 1) < 2 * n := by exact_mod_cast hlt
    nlinarith [Real.pi_pos]

/-- sin(n · φₖ) = (-1)^k where φₖ = (2k+1)π/(2n). -/
theorem sin_n_chebyshevAngle (n : ℕ) (hn : 0 < n) (k : Fin n) :
    Real.sin ((n : ℝ) * ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n))) = (-1 : ℝ) ^ k.val := by
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hsimp : (n : ℝ) * ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) =
      (k.val : ℝ) * Real.pi + Real.pi / 2 := by
    field_simp
  rw [hsimp, Real.sin_add, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi,
      Real.sin_pi_div_two, Real.cos_pi_div_two]
  ring

/-- **Chebyshev Product Formula**: T_n(x) = 2^{n-1} · ∏_{k=0}^{n-1}(X - C(cos φₖ)).

    Proof: Let D = T_n - Q where Q = 2^{n-1} · ∏(X - C(nodes k)).
    - D has degree < n (leading coefficients both equal 2^{n-1}, they cancel)
    - D has n distinct roots: each chebyshevNode n k is a root
    - card_le_degree_of_subset_roots → n ≤ natDegree D < n: contradiction → D = 0. -/
theorem chebyshev_product_formula (n : ℕ) (hn : 0 < n) :
    T ℝ (n : ℤ) = Polynomial.C ((2 : ℝ) ^ (n - 1)) *
      ∏ k : Fin n, (Polynomial.X - Polynomial.C (chebyshevNode n k)) := by
  set Q := Polynomial.C ((2 : ℝ) ^ (n - 1)) *
      ∏ k : Fin n, (Polynomial.X - Polynomial.C (chebyshevNode n k)) with hQ_def
  suffices h : T ℝ (n : ℤ) - Q = 0 from sub_eq_zero.mp h
  by_contra hD
  have h2_ne : (2 : ℝ) ^ (n - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hP_monic : (∏ k : Fin n, (Polynomial.X - Polynomial.C (chebyshevNode n k) : ℝ[X])).Monic :=
    monic_prod_X_sub_C (chebyshevNode n) Finset.univ
  have hP_ne : ∏ k : Fin n, (Polynomial.X - Polynomial.C (chebyshevNode n k) : ℝ[X]) ≠ 0 :=
    hP_monic.ne_zero
  have hQ_ne : Q ≠ 0 := mul_ne_zero (Polynomial.C_ne_zero.mpr h2_ne) hP_ne
  have hT_ne : T ℝ (n : ℤ) ≠ 0 := T_ofNat_ne_zero n
  have hP_deg : (∏ k : Fin n, (Polynomial.X - Polynomial.C (chebyshevNode n k) : ℝ[X])).natDegree = n := by
    rw [Polynomial.natDegree_prod Finset.univ _ (fun k _ => Polynomial.X_sub_C_ne_zero _)]
    simp [Polynomial.natDegree_X_sub_C]
  have hQ_natdeg : Q.natDegree = n := by
    rw [hQ_def, Polynomial.natDegree_C_mul h2_ne, hP_deg]
  have hQ_lc : Q.leadingCoeff = (2 : ℝ) ^ (n - 1) := by
    rw [hQ_def, leadingCoeff_mul, Polynomial.leadingCoeff_C, hP_monic.leadingCoeff, mul_one]
  have hT_deg : (T ℝ (n : ℤ)).degree = ↑n := by
    rw [Polynomial.degree_eq_natDegree hT_ne, natDegree_T_ofNat]
  have hQ_deg : Q.degree = ↑n := by
    rw [Polynomial.degree_eq_natDegree hQ_ne, hQ_natdeg]
  have hT_lc : (T ℝ (n : ℤ)).leadingCoeff = (2 : ℝ) ^ (n - 1) := leadingCoeff_T_ofNat n hn
  -- degree(D) < n via leading coefficient cancellation
  have hD_deg : (T ℝ (n : ℤ) - Q).degree < ↑n := by
    calc (T ℝ (n : ℤ) - Q).degree
        < (T ℝ (n : ℤ)).degree :=
            Polynomial.degree_sub_lt (hT_deg.trans hQ_deg.symm) hT_ne (hT_lc.trans hQ_lc.symm)
      _ = ↑n := hT_deg
  -- natDegree(D) < n
  have hD_natdeg : (T ℝ (n : ℤ) - Q).natDegree < n := by
    rw [Polynomial.natDegree_lt_iff_degree_lt hD]
    exact_mod_cast hD_deg
  -- Each Chebyshev node is a root of D
  have hQ_zero : ∀ k : Fin n, Q.eval (chebyshevNode n k) = 0 := fun k => by
    rw [hQ_def, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
    apply mul_eq_zero.mpr; right
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
  have hD_roots : ∀ k : Fin n, (T ℝ (n : ℤ) - Q).eval (chebyshevNode n k) = 0 := fun k => by
    rw [Polynomial.eval_sub, chebyshevNode_is_root n hn k, hQ_zero k, sub_self]
  -- Finset of n distinct roots
  let Z := Finset.image (chebyshevNode n) Finset.univ
  have hZ_card : Z.card = n := by
    simp [Z, Finset.card_image_of_injective _ (chebyshevNode_injective n hn)]
  have hZ_subset : Z.val ⊆ (T ℝ (n : ℤ) - Q).roots := by
    intro x hx
    have hxZ : x ∈ Z := hx
    simp only [Z, Finset.mem_image, Finset.mem_univ, true_and] at hxZ
    obtain ⟨k, rfl⟩ := hxZ
    rw [Polynomial.mem_roots hD]
    exact hD_roots k
  -- n ≤ natDegree D, contradicting natDegree D < n
  have h_card_le : n ≤ (T ℝ (n : ℤ) - Q).natDegree := by
    have := Polynomial.card_le_degree_of_subset_roots hZ_subset
    rwa [hZ_card] at this
  exact absurd hD_natdeg (not_lt.mpr h_card_le)

end ProductFormula

/-! ## Lagrange Basis Formula (Session 5) -/

section ChebLagrangeFormula

open Polynomial

/-- **[Key Step] Lagrange basis explicit formula at Chebyshev nodes.**

    For x = cos θ ≠ cos φₖ, the k-th Lagrange basis polynomial satisfies:
      ℓₖⁿ(cos θ) = cos(nθ) · sin(φₖ) / (n · (cos θ - cos φₖ) · (-1)^k)

    Proof via Chebyshev polynomial theory, using:
    1. chebyshev_product_formula: T_n = C(2^{n-1}) · ∏_i (X - C(nodes i))
    2. Split at k + T_real_cos gives: ∏_{i≠k} (cos θ - nodes i) = cos(nθ)/(2^{n-1}·(cos θ-nodes k))
    3. T_derivative_eq_U + U_real_cos + split product at k gives:
       ∏_{i≠k} (nodes k - nodes i) = n·(-1)^k/(2^{n-1}·sin φₖ)
    4. Combine: lagrangeBasis = numerator/denominator = formula above -/
theorem lagrange_basis_chebyshev_formula (n : ℕ) (hn : 0 < n) (k : Fin n) (θ : ℝ)
    (hne : Real.cos θ ≠ chebyshevNode n k) :
    lagrangeBasis n (chebyshevNode n) k (Real.cos θ) =
    Real.cos (n * θ) * Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) /
    (n * (Real.cos θ - chebyshevNode n k) * (-1 : ℝ)^k.val) := by
  -- Basic nonzero facts
  have h2_ne : (2 : ℝ) ^ (n - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hn_real : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hne' : Real.cos θ - chebyshevNode n k ≠ 0 := sub_ne_zero.mpr hne
  have hsin_ne : Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) ≠ 0 :=
    (chebyshevAngle_sin_pos n hn k).ne'
  -- Step 1: Product formula evaluation at cos θ
  -- T_n(cos θ) = 2^{n-1} · ∏_i (cos θ - nodes i)  [from chebyshev_product_formula]
  have hprod_eval : (2 : ℝ)^(n-1) * ∏ i : Fin n, (Real.cos θ - chebyshevNode n i) =
      Real.cos ((n : ℝ) * θ) := by
    have hprod := chebyshev_product_formula n hn
    have heval := congr_arg (Polynomial.eval (Real.cos θ)) hprod
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
               Polynomial.eval_sub, Polynomial.eval_X] at heval
    rw [chebyshev_T_at_cos] at heval
    push_cast at heval ⊢
    exact heval.symm
  -- Step 2: Split the product ∏_i (cos θ - nodes i) at index k
  have hprod_split : ∏ i : Fin n, (Real.cos θ - chebyshevNode n i) =
      (Real.cos θ - chebyshevNode n k) *
      ∏ i ∈ Finset.univ.erase k, (Real.cos θ - chebyshevNode n i) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
  -- Step 3: Compute the numerator ∏_{i≠k} (cos θ - nodes i)
  have hnum_eq : ∏ i ∈ Finset.univ.erase k, (Real.cos θ - chebyshevNode n i) =
      Real.cos ((n : ℝ) * θ) / ((2 : ℝ)^(n-1) * (Real.cos θ - chebyshevNode n k)) := by
    have := hprod_eval
    rw [hprod_split] at this
    have h_ne : (2 : ℝ)^(n-1) * (Real.cos θ - chebyshevNode n k) ≠ 0 :=
      mul_ne_zero h2_ne hne'
    field_simp [h_ne] at this ⊢
    linarith
  -- Step 4: Compute the denominator using T_n' = n·U_{n-1} and U_real_cos
  -- Step 4a: T_n' = n · U_{n-1} (T_derivative_eq_U gives multiplication in R[X])
  have hderiv_eq : Polynomial.derivative (T ℝ (n : ℤ)) = (n : ℤ) * U ℝ ((n : ℤ) - 1) :=
    T_derivative_eq_U (n : ℤ)
  -- Step 4b: U_{n-1}(nodes k) · sin(φₖ) = sin(n · φₖ) = (-1)^k
  -- U_real_cos takes (θ : ℝ) (n : ℤ) in that order (variable order in Mathlib)
  have hU_sin : (U ℝ ((n : ℤ) - 1)).eval (chebyshevNode n k) *
      Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) = (-1 : ℝ)^k.val := by
    have hU := Polynomial.Chebyshev.U_real_cos
        ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n))
        ((n : ℤ) - 1)
    simp only [chebyshevNode]
    rw [hU, show (↑(↑n - 1 : ℤ) + 1 : ℝ) = (n : ℝ) from by push_cast; ring]
    exact sin_n_chebyshevAngle n hn k
  -- Step 4c: T_n'(nodes k) via product formula derivative
  -- T_n = C(2^{n-1}) * (X - C(nodes k)) * ∏_{i≠k} (X - C(nodes i))
  -- derivative at nodes k = C(2^{n-1}) * ∏_{i≠k} (nodes k - nodes i) [second term vanishes]
  -- Also T_n'(nodes k) = n · U_{n-1}(nodes k)  [from T_derivative_eq_U]
  -- Step 4d: eval T_n' at nodes k from product formula derivative
  have hderiv_prod : (Polynomial.derivative (T ℝ (n : ℤ))).eval (chebyshevNode n k) =
      (2 : ℝ)^(n-1) * ∏ i ∈ Finset.univ.erase k, (chebyshevNode n k - chebyshevNode n i) := by
    have hT := chebyshev_product_formula n hn
    have hP_split : ∏ i : Fin n, (Polynomial.X - Polynomial.C (chebyshevNode n i) : ℝ[X]) =
        (Polynomial.X - Polynomial.C (chebyshevNode n k)) *
        ∏ i ∈ Finset.univ.erase k, (Polynomial.X - Polynomial.C (chebyshevNode n i)) := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
    rw [hT, hP_split]
    set Q_k := ∏ i ∈ Finset.univ.erase k, (Polynomial.X - Polynomial.C (chebyshevNode n i) : ℝ[X])
    simp only [Polynomial.derivative_mul, Polynomial.derivative_C, Polynomial.derivative_X_sub_C,
               Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add, zero_mul,
               Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one, zero_add]
    simp only [sub_self, zero_mul, zero_add]
    simp only [Q_k, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
               Polynomial.eval_C]
    ring
  -- Step 4e: Combine to get den formula
  have hden_eq : ∏ i ∈ Finset.univ.erase k, (chebyshevNode n k - chebyshevNode n i) =
      (n : ℝ) * (-1 : ℝ)^k.val / ((2 : ℝ)^(n-1) * Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n))) := by
    have hsin_ne' : Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) ≠ 0 := hsin_ne
    have hT_deriv_eval : (Polynomial.derivative (T ℝ (n : ℤ))).eval (chebyshevNode n k) =
        (n : ℝ) * (U ℝ ((n : ℤ) - 1)).eval (chebyshevNode n k) := by
      rw [hderiv_eq, Polynomial.eval_mul, Polynomial.eval_intCast]
      push_cast; ring
    -- From hU_sin: U(nodes k) = (-1)^k / sin(φₖ)
    have hU_val : (U ℝ ((n : ℤ) - 1)).eval (chebyshevNode n k) =
        (-1 : ℝ)^k.val / Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) := by
      rw [eq_div_iff hsin_ne']
      exact hU_sin
    rw [hT_deriv_eval] at hderiv_prod
    rw [hU_val] at hderiv_prod
    -- hderiv_prod : n * ((-1)^k / sin φₖ) = 2^{n-1} * ∏ i≠k (nk - ni)
    field_simp [h2_ne, hsin_ne'] at hderiv_prod ⊢
    linarith
  -- Step 5: Combine numerator and denominator
  simp only [lagrangeBasis, Finset.prod_div_distrib, hnum_eq, hden_eq]
  have h_denom_ne : (n : ℝ) * (-1 : ℝ)^k.val /
      ((2 : ℝ)^(n-1) * Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n))) ≠ 0 := by
    apply div_ne_zero
    · apply mul_ne_zero hn_real
      exact pow_ne_zero _ (by norm_num)
    · exact mul_ne_zero h2_ne hsin_ne
  field_simp [h2_ne, hne', hn_real, hsin_ne,
              pow_ne_zero _ (show (-1 : ℝ) ≠ 0 from by norm_num), h_denom_ne]

end ChebLagrangeFormula

/-! ## Lebesgue Function Formula (Session 5) -/

/-- **[NEW] Lebesgue function explicit formula.**

    For x = cos θ with cos θ ≠ any Chebyshev node:
    Λₙ(cos θ) = |cos(nθ)| / n · Σₖ sin(φₖ) / |cos θ - cos φₖ|

    Follows from lagrange_basis_chebyshev_formula by taking absolute values. -/
theorem chebyshev_lebesgue_eq (n : ℕ) (hn : 0 < n) (θ : ℝ)
    (hne : ∀ k : Fin n, Real.cos θ ≠ chebyshevNode n k) :
    chebyshevLebesgue n (Real.cos θ) =
    |Real.cos (n * θ)| / n *
    ∑ k : Fin n, Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) /
                 |Real.cos θ - chebyshevNode n k| := by
  simp only [chebyshevLebesgue, Finset.mul_sum]
  congr 1
  ext k
  rw [lagrange_basis_chebyshev_formula n hn k θ (hne k)]
  have hsin_pos : 0 < Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) :=
    chebyshevAngle_sin_pos n hn k
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hne' : Real.cos θ - chebyshevNode n k ≠ 0 := sub_ne_zero.mpr (hne k)
  -- |cos(nθ) · sin(φₖ) / (n · (cos θ - nodes k) · (-1)^k)|
  -- = |cos(nθ)| · sin(φₖ) / (n · |cos θ - nodes k|)
  rw [abs_div, abs_mul, abs_mul, abs_mul,
      abs_of_pos hsin_pos, abs_of_pos hn_pos]
  simp only [abs_pow, abs_neg, abs_one, one_pow, mul_one]
  -- Now: |cos(nθ)|/n · sin(φₖ)/|cos θ - nodes k| = |cos(nθ)|/n · sin(φₖ)/|cos θ - nodes k|
  field_simp

/-! ## Rational Cosine Not a Node (Session 6) -/

/-- **Key helper**: For odd p and odd q, cos(πp/q) is never a Chebyshev node of any degree n.

    Proof: By `Real.cos_eq_cos_iff`, the equation cos(πp/q) = cos((2k+1)π/(2n)) requires
    either (2k+1)π/(2n) = 2jπ + πp/q or (2k+1)π/(2n) = 2jπ − πp/q for some j : ℤ.

    Dividing by π and multiplying by 2nq:
    - Case 1: q(2k+1) = 4jnq + 2np. LHS is odd (product of two odd numbers q, 2k+1).
      RHS is even. Contradiction.
    - Case 2: q(2k+1) + 2np = 4jnq. LHS is odd + even = odd. RHS is even. Contradiction.

    This allows `chebyshev_lebesgue_eq` to be applied for ALL n (not just n = mq). -/
lemma x_not_chebyshev_node (p q : ℕ) (hp : Odd p) (hq : Odd q) (hq_pos : 0 < q)
    (n : ℕ) (hn : 0 < n) (k : Fin n) :
    Real.cos (↑p * Real.pi / ↑q) ≠ chebyshevNode n k := by
  simp only [chebyshevNode]
  intro heq
  rw [Real.cos_eq_cos_iff] at heq
  obtain ⟨j, hj | hj⟩ := heq
  · -- Case 1: (2k+1)π/(2n) = 2jπ + πp/q
    -- → q(2k+1) = 4jnq + 2np (after ×2nq/π)
    -- LHS is odd, RHS is even → contradiction
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hq_ne : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq_pos.ne'
    have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    -- Extract the angle equation (divide by π)
    have hangle : (2 * (k.val : ℝ) + 1) / (2 * n) = 2 * j + p / q := by
      have h := hj
      rw [show (2 * (k.val : ℝ) + 1) * Real.pi / (2 * ↑n) =
            Real.pi * ((2 * k.val + 1) / (2 * n)) from by ring,
          show 2 * (j : ℝ) * Real.pi + ↑p * Real.pi / ↑q =
            Real.pi * (2 * j + ↑p / ↑q) from by ring] at h
      exact mul_left_cancel₀ hpi h
    -- Multiply by 2nq to get integer equation in ℝ
    have hR : (q : ℝ) * (2 * k.val + 1) = 4 * j * n * q + 2 * n * p := by
      have h := congr_arg (· * (2 * (n : ℝ) * ↑q)) hangle
      field_simp [hn_ne, hq_ne] at h ⊢
      linarith
    -- Cast to ℤ
    have hint : (q : ℤ) * (2 * ↑k.val + 1) = 4 * j * ↑n * ↑q + 2 * ↑n * ↑p := by
      exact_mod_cast hR
    -- LHS q*(2k+1) is odd (product of two odd numbers)
    have hodd : Odd ((q : ℤ) * (2 * ↑k.val + 1)) :=
      (by exact_mod_cast hq : Odd (q : ℤ)).mul ⟨↑k.val, by ring⟩
    -- RHS 4jnq + 2np is even (= 2*(2jnq + np))
    have heven : Even (4 * j * (↑n : ℤ) * ↑q + 2 * ↑n * ↑p) :=
      ⟨2 * j * ↑n * ↑q + ↑n * ↑p, by ring⟩
    -- hint rewrites hodd: Odd (4jnq + 2np), contradicting heven
    obtain ⟨r, hr⟩ := heven
    obtain ⟨s, hs⟩ := hint ▸ hodd
    omega
  · -- Case 2: (2k+1)π/(2n) = 2jπ - πp/q
    -- → q(2k+1) + 2np = 4jnq (after ×2nq/π)
    -- LHS is odd + even = odd, RHS is even → contradiction
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hq_ne : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq_pos.ne'
    have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have hangle : (2 * (k.val : ℝ) + 1) / (2 * n) = 2 * j - p / q := by
      have h := hj
      rw [show (2 * (k.val : ℝ) + 1) * Real.pi / (2 * ↑n) =
            Real.pi * ((2 * k.val + 1) / (2 * n)) from by ring,
          show 2 * (j : ℝ) * Real.pi - ↑p * Real.pi / ↑q =
            Real.pi * (2 * j - ↑p / ↑q) from by ring] at h
      exact mul_left_cancel₀ hpi h
    have hR : (q : ℝ) * (2 * k.val + 1) + 2 * n * p = 4 * j * n * q := by
      have h := congr_arg (· * (2 * (n : ℝ) * ↑q)) hangle
      field_simp [hn_ne, hq_ne] at h ⊢
      linarith
    have hint : (q : ℤ) * (2 * ↑k.val + 1) + 2 * ↑n * ↑p = 4 * j * ↑n * ↑q := by
      exact_mod_cast hR
    -- LHS: q*(2k+1) is odd (odd × odd), 2np is even → sum is odd
    have hodd_sum : Odd ((q : ℤ) * (2 * ↑k.val + 1) + 2 * ↑n * ↑p) := by
      apply Odd.add_even
      · exact (by exact_mod_cast hq : Odd (q : ℤ)).mul ⟨↑k.val, by ring⟩
      · exact ⟨↑n * ↑p, by ring⟩
    -- RHS 4jnq is even
    have heven_rhs : Even (4 * j * (↑n : ℤ) * ↑q) := ⟨2 * j * ↑n * ↑q, by ring⟩
    obtain ⟨r, hr⟩ := heven_rhs
    obtain ⟨s, hs⟩ := hint ▸ hodd_sum
    omega

set_option maxHeartbeats 800000 in
/-- The Lebesgue formula applies for ALL n when p, q are odd (not just along n = mq
    multiples), since cos(πp/q) is never a Chebyshev node. -/
lemma chebyshev_lebesgue_eq_all_n (p q : ℕ) (hp : Odd p) (hq : Odd q)
    (hq_pos : 0 < q) (n : ℕ) (hn : 0 < n) :
    chebyshevLebesgue n (Real.cos (↑p * Real.pi / ↑q)) =
    |Real.cos (↑n * (↑p * Real.pi / ↑q))| / ↑n *
    ∑ k : Fin n, Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) /
                 |Real.cos (↑p * Real.pi / ↑q) - chebyshevNode n k| := by
  -- Direct proof mirroring chebyshev_lebesgue_eq, specialised to θ = ↑p * π / ↑q.
  -- Avoids the expensive isDefEq triggered by applying chebyshev_lebesgue_eq.
  -- push_cast normalizes implicit n-coercions from lagrange_basis_chebyshev_formula
  -- against the explicit ↑n coercions in the annotation.
  set θ := (↑p : ℝ) * Real.pi / ↑q with hθ
  simp only [chebyshevLebesgue, Finset.mul_sum]
  congr 1
  ext k
  have hne : Real.cos θ ≠ chebyshevNode n k :=
    x_not_chebyshev_node p q hp hq hq_pos n hn k
  rw [lagrange_basis_chebyshev_formula n hn k θ hne]
  have hsin_pos : 0 < Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) :=
    chebyshevAngle_sin_pos n hn k
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hne' : Real.cos θ - chebyshevNode n k ≠ 0 := sub_ne_zero.mpr hne
  rw [abs_div, abs_mul, abs_mul, abs_mul,
      abs_of_pos hsin_pos, abs_of_pos hn_pos]
  simp only [abs_pow, abs_neg, abs_one, one_pow, mul_one]
  push_cast
  field_simp

/-! ## Session 7: Cosine Nonvanishing at ALL n for Rational Multiples of π -/

/-- **cos(nπp/q) ≠ 0 for ALL n ∈ ℕ** when p and q are both odd.

    This uses a parity argument: if cos(nπp/q) = 0 then (2*k+1)*π/2 = n*p*π/q
    for some k : ℤ, giving 2*n*p = (2k+1)*q. But 2np is even and (2k+1)*q is
    odd*odd = odd (since q odd), a contradiction.

    This strengthens `cos_rational_pi_nonzero_along_multiples` which only covers
    the subsequence n = mq. Used in `cos_rational_pi_pos_min` to obtain a
    uniform lower bound δ > 0 over all n. -/
lemma cos_rational_pi_ne_zero (p q n : ℕ) (hp : Odd p) (hq : Odd q) (hq_pos : 0 < q) :
    Real.cos ((n : ℝ) * (↑p * Real.pi / ↑q)) ≠ 0 := by
  intro h
  rw [Real.cos_eq_zero_iff] at h
  obtain ⟨k, heq⟩ := h
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hq_ne : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq_pos.ne'
  -- Derive: (n : ℝ) * p / q = (2k+1)/2
  have hangle : (n : ℝ) * ↑p / ↑q = (2 * (k : ℝ) + 1) / 2 := by
    have heq' := heq
    rw [show (↑n : ℝ) * (↑p * Real.pi / ↑q) = Real.pi * ((↑n * ↑p) / ↑q) from by ring,
        show (2 * (↑k : ℝ) + 1) * Real.pi / 2 = Real.pi * ((2 * ↑k + 1) / 2) from by ring] at heq'
    exact mul_left_cancel₀ hpi heq'
  -- Cross-multiply: 2np = (2k+1)q  (over ℝ, then cast to ℤ)
  have hR : 2 * (n : ℝ) * (p : ℝ) = (2 * (k : ℝ) + 1) * (q : ℝ) := by
    have h' := hangle
    field_simp [hq_ne] at h'
    linarith
  have hint : 2 * (n : ℤ) * (p : ℤ) = (2 * k + 1) * (q : ℤ) := by exact_mod_cast hR
  -- Parity contradiction: LHS even, RHS = odd * odd = odd (since q odd)
  obtain ⟨qm, hqm⟩ := hq
  have hq_int : (q : ℤ) = 2 * ↑qm + 1 := by exact_mod_cast hqm
  have hint2 : 2 * (n : ℤ) * ↑p = (2 * k + 1) * (2 * ↑qm + 1) := by
    rw [← hq_int]; exact hint
  have heven : Even (2 * (n : ℤ) * ↑p) := ⟨↑n * ↑p, by ring⟩
  have hodd : Odd ((2 * k + 1) * (2 * ↑qm + 1) : ℤ) :=
    ⟨2 * k * ↑qm + k + ↑qm, by ring⟩
  rw [hint2] at heven
  obtain ⟨r, hr⟩ := heven
  obtain ⟨s, hs⟩ := hodd
  omega

set_option maxHeartbeats 800000 in
/-- **cos(nπp/q) has period 2q in n**: cos(nπp/q) = cos((n mod 2q)·πp/q).

    This follows because cos(nπp/q) = cos((n mod 2q)·πp/q + (n/2q)·p · 2π),
    and cos is 2π-periodic. -/
lemma cos_rational_pi_mod (p q n : ℕ) (hq_pos : 0 < q) :
    Real.cos ((n : ℝ) * (↑p * Real.pi / ↑q)) =
    Real.cos ((↑(n % (2 * q)) : ℝ) * (↑p * Real.pi / ↑q)) := by
  have hq_ne : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq_pos.ne'
  -- ℕ floor division: n = n%(2q) + n/(2q) * (2q)
  have hdiv : n = n % (2 * q) + n / (2 * q) * (2 * q) := by
    have h := Nat.mod_add_div n (2 * q)
    linarith [Nat.mul_comm (2 * q) (n / (2 * q))]
  -- The shift (n/(2q)*p * 2π) can be absorbed via cos periodicity
  have hshift : (↑(n / (2 * q) * (2 * q) : ℕ) : ℝ) * (↑p * Real.pi / ↑q) =
                (↑(n / (2 * q) * p : ℕ) : ℝ) * (2 * Real.pi) := by
    have lhs_eq : (↑(n / (2 * q) * (2 * q) : ℕ) : ℝ) = ↑(n / (2 * q)) * (2 * ↑q) := by
      push_cast; ring
    have rhs_eq : (↑(n / (2 * q) * p : ℕ) : ℝ) = ↑(n / (2 * q)) * ↑p := Nat.cast_mul _ _
    rw [lhs_eq, rhs_eq]
    field_simp [hq_ne]
  -- Rewrite n as sum, then apply cos_add_nat_mul_two_pi
  have hn_cast : (n : ℝ) = ↑(n % (2 * q)) + ↑(n / (2 * q) * (2 * q)) := by exact_mod_cast hdiv
  rw [hn_cast, add_mul, hshift]
  exact Real.cos_add_nat_mul_two_pi
    (↑(n % (2 * q)) * (↑p * Real.pi / ↑q)) (n / (2 * q) * p)

set_option maxHeartbeats 4000000 in
/-- **Uniform lower bound**: ∃ δ > 0 such that |cos(nπp/q)| ≥ δ for ALL n ∈ ℕ.

    Proof: since cos(nπp/q) is periodic with period 2q in n (by `cos_rational_pi_mod`)
    and nonzero everywhere (by `cos_rational_pi_ne_zero`), the minimum over one
    full period is positive. -/
lemma cos_rational_pi_pos_min (p q : ℕ) (hp : Odd p) (hq : Odd q) (hq_pos : 0 < q) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, δ ≤ |Real.cos ((n : ℝ) * (↑p * Real.pi / ↑q))| := by
  have h2q_pos : 0 < 2 * q := by omega
  -- Take the minimum of |cos(kπp/q)| over k = 0,...,2q-1
  let vals := Finset.image
    (fun k : Fin (2 * q) => |Real.cos ((k.val : ℝ) * (↑p * Real.pi / ↑q))|)
    Finset.univ
  have hvals_nonempty : vals.Nonempty :=
    ⟨|Real.cos (0 * (↑p * Real.pi / ↑q))|,
     Finset.mem_image.mpr ⟨⟨0, h2q_pos⟩, Finset.mem_univ _, by simp⟩⟩
  refine ⟨vals.min' hvals_nonempty, ?_, fun n => ?_⟩
  · -- min is positive since all values are positive
    have hall : ∀ x ∈ vals, (0 : ℝ) < x := fun x hx => by
      simp only [vals, Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨k, rfl⟩ := hx
      exact abs_pos.mpr (cos_rational_pi_ne_zero p q k.val hp hq hq_pos)
    exact hall _ (Finset.min'_mem vals hvals_nonempty)
  · -- |cos(nπp/q)| = |cos((n%2q)πp/q)| ≥ min
    rw [cos_rational_pi_mod p q n hq_pos]
    apply Finset.min'_le
    exact Finset.mem_image.mpr
      ⟨⟨n % (2 * q), Nat.mod_lt _ h2q_pos⟩, Finset.mem_univ _, rfl⟩

/-! ## Auxiliary Lemmas for Trig Sum Bound -/

/-- cos(t) ≥ 1/2 for t ∈ [0, π/3].
    Proof: cos is antimonotone on [0,π] and cos(π/3) = 1/2. -/
private lemma cos_ge_half_of_le_pi_div_three {t : ℝ} (ht : 0 ≤ t) (ht_le : t ≤ Real.pi / 3) :
    (1 : ℝ) / 2 ≤ Real.cos t := by
  have hpi_pos := Real.pi_pos
  have hpi3_le_pi : Real.pi / 3 ≤ Real.pi := by linarith
  have h := Real.antitoneOn_cos
    ⟨ht, le_trans ht_le hpi3_le_pi⟩          -- t ∈ [0, π]
    ⟨by linarith, hpi3_le_pi⟩                 -- π/3 ∈ [0, π]
    ht_le                                       -- t ≤ π/3 → cos(π/3) ≤ cos(t)
  rw [Real.cos_pi_div_three] at h
  linarith

/-- For t ∈ (0, π/3], cos(t)/sin(t) ≥ 1/(2t).
    Proof: sin(t) ≤ t and cos(t) ≥ 1/2, so sin(t) ≤ 2t·cos(t), i.e., 1/(2t) ≤ cos(t)/sin(t). -/
private lemma cot_ge_inv_two_mul {t : ℝ} (ht : 0 < t) (ht_le : t ≤ Real.pi / 3) :
    1 / (2 * t) ≤ Real.cos t / Real.sin t := by
  have hpi_pos := Real.pi_pos
  have hsin_pos : 0 < Real.sin t :=
    Real.sin_pos_of_pos_of_lt_pi ht (by linarith)
  rw [div_le_div_iff₀ (by positivity) hsin_pos]
  -- Goal: 1 * Real.sin t ≤ Real.cos t * (2 * t)
  have hsin_le : Real.sin t ≤ t := (Real.sin_lt ht).le
  have hcos_ge : (1 : ℝ) / 2 ≤ Real.cos t :=
    cos_ge_half_of_le_pi_div_three ht.le ht_le
  nlinarith

/-- sin(φ)/(1 + cos φ) = tan(φ/2) = sin(φ/2)/cos(φ/2) for φ ∈ (0, 2π).

    For x = -1: |x - cos φ| = |(-1) - cos φ| = 1 + cos φ (since cos φ > -1 for φ ∈ (0, π)).
    So the Lebesgue sum term sin(φₖ)/|(-1) - cos φₖ| = sin(φₖ)/(1 + cos φₖ) = tan(φₖ/2).

    Half-angle identities:
      sin(φ) = 2 sin(φ/2) cos(φ/2)
      1 + cos(φ) = 2 cos²(φ/2)  [from cos(2t) = 2cos²t - 1]
    So: sin(φ)/(1 + cos φ) = 2sin(φ/2)cos(φ/2) / (2cos²(φ/2)) = sin(φ/2)/cos(φ/2) = tan(φ/2). -/
private lemma sin_div_one_add_cos {φ : ℝ} (hφ : 0 < φ) (hφ_lt : φ < Real.pi) :
    Real.sin φ / (1 + Real.cos φ) = Real.sin (φ / 2) / Real.cos (φ / 2) := by
  have hpi_pos := Real.pi_pos
  -- φ/2 ∈ (-π/2, π/2) since φ ∈ (0, π)
  have hcos_half_pos : 0 < Real.cos (φ / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  -- 1 + cos(φ) = 2cos²(φ/2): from cos(2t) = 2cos²t - 1
  have h1cos : 1 + Real.cos φ = 2 * Real.cos (φ / 2) ^ 2 := by
    have hcos2 := Real.cos_two_mul (φ / 2)
    have hsimp : (2 : ℝ) * (φ / 2) = φ := by ring
    rw [hsimp] at hcos2
    linarith
  -- sin(φ) = 2sin(φ/2)cos(φ/2): from sin(2t) = 2sin(t)cos(t)
  have hsin : Real.sin φ = 2 * Real.sin (φ / 2) * Real.cos (φ / 2) := by
    have key := Real.sin_two_mul (φ / 2)
    have hsimp : (2 : ℝ) * (φ / 2) = φ := by ring
    rw [hsimp] at key
    exact key
  rw [hsin, h1cos]
  have h2cos_ne : 2 * Real.cos (φ / 2) ^ 2 ≠ 0 := by positivity
  field_simp [h2cos_ne, hcos_half_pos.ne']

/-- The Chebyshev node angle φₖ = (2k+1)π/(2n) ∈ (0, π) for k < n. -/
private lemma chebyshevAngle_pos_lt_pi (n : ℕ) (hn : 0 < n) (k : Fin n) :
    0 < (2 * k.val + 1 : ℝ) * Real.pi / (2 * n) ∧
    (2 * k.val + 1 : ℝ) * Real.pi / (2 * n) < Real.pi := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  constructor
  · positivity
  · rw [div_lt_iff₀ (by positivity)]
    have hlt : 2 * k.val + 1 < 2 * n := by omega
    have hlt' : (2 * k.val + 1 : ℝ) < 2 * n := by exact_mod_cast hlt
    nlinarith [mul_lt_mul_of_pos_right hlt' Real.pi_pos]

/-- For x = -1 (e.g., p = q = 1) and the Chebyshev node formula:
    sin(φₖ) / |(-1) - cos φₖ| = sin(φₖ) / (1 + cos φₖ) = tan(φₖ/2) = sin(φₖ/2)/cos(φₖ/2).

    Here |(-1) - cos φₖ| = 1 + cos φₖ since cos φₖ > -1 (as φₖ ∈ (0, π)). -/
private lemma sum_term_eq_tan_half_angle (n : ℕ) (hn : 0 < n) (k : Fin n) :
    Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) /
    |(-1 : ℝ) - Real.cos ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n))| =
    Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (4 * n)) /
    Real.cos ((2 * k.val + 1 : ℝ) * Real.pi / (4 * n)) := by
  have ⟨hφ_pos, hφ_lt_pi⟩ := chebyshevAngle_pos_lt_pi n hn k
  have hcos_gt : -1 < Real.cos ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) := by
    -- cos(π) = -1 < cos(φ) since 0 < φ < π and cos is strictly decreasing on [0,π]
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi hφ_pos.le (le_refl Real.pi) hφ_lt_pi
    simp only [Real.cos_pi] at h; linarith
  -- |(-1) - cos φ| = 1 + cos φ since -1 - cos φ < 0
  have h_abs : |(-1 : ℝ) - Real.cos ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n))| =
               1 + Real.cos ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) := by
    have hneg : (-1 : ℝ) - Real.cos ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) < 0 :=
      by linarith [hcos_gt]
    rw [abs_of_neg hneg]; ring
  rw [h_abs, sin_div_one_add_cos hφ_pos hφ_lt_pi]
  -- After rewrite: sin(φ/2)/cos(φ/2) = sin((2k+1)π/(4n))/cos((2k+1)π/(4n))
  -- where φ = (2k+1)π/(2n), so φ/2 = (2k+1)π/(4n)
  have harg : (2 * k.val + 1 : ℝ) * Real.pi / (2 * n) / 2 =
              (2 * k.val + 1 : ℝ) * Real.pi / (4 * n) := by ring
  rw [harg]

/-- Complementary angle: for k + j = n - 1, the half-angles (2k+1)π/(4n) and (2j+1)π/(4n)
    sum to π/2, so sin(A)/cos(A) = cos(B)/sin(B) where A = (2k+1)π/(4n), B = (2j+1)π/(4n). -/
private lemma tan_eq_cot_complement (n : ℕ) (hn : 0 < n) (k : Fin n)
    (hk : n / 2 ≤ k.val) :
    Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (4 * n)) /
    Real.cos ((2 * k.val + 1 : ℝ) * Real.pi / (4 * n)) ≥
    1 / (2 * ((2 * (↑(n - 1 - k.val) : ℝ) + 1) * Real.pi / (4 * ↑n))) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  -- The complementary angle
  set j := n - 1 - k.val with hj_def
  have hj_lt : j < n := by omega
  have hkj : k.val + j = n - 1 := by omega
  -- Angles sum to π/2: (2k+1)/(4n) + (2j+1)/(4n) = (2n)/(4n) = 1/2
  have hangle_sum : (2 * k.val + 1 : ℝ) * Real.pi / (4 * n) +
                    (2 * (j : ℝ) + 1) * Real.pi / (4 * n) = Real.pi / 2 := by
    have : (2 * (k.val : ℝ) + 1) + (2 * (j : ℝ) + 1) = 2 * (n : ℝ) := by
      have h0 : ((k.val + j : ℕ) : ℝ) = ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hkj
      rw [Nat.cast_add] at h0
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] at h0
      linarith
    field_simp; linarith [this]
  -- So (2k+1)π/(4n) = π/2 - (2j+1)π/(4n)
  have hA_eq : (2 * k.val + 1 : ℝ) * Real.pi / (4 * n) =
               Real.pi / 2 - (2 * (j : ℝ) + 1) * Real.pi / (4 * n) := by linarith [hangle_sum]
  -- sin(π/2 - u) = cos(u) and cos(π/2 - u) = sin(u)
  set u := (2 * (j : ℝ) + 1) * Real.pi / (4 * n) with hu_def
  have hu_pos : 0 < u := by rw [hu_def]; positivity
  have hu_le : u ≤ Real.pi / 3 := by
    rw [hu_def]
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * ↑n) (by positivity : (0 : ℝ) < 3)]
    -- Need (2j+1)·π·3 ≤ π·(4n), i.e., 3(2j+1) ≤ 4n
    have hj_bound : 3 * (2 * j + 1) ≤ 4 * n := by omega
    have hj_boundR : (3 : ℝ) * (2 * ↑j + 1) ≤ 4 * ↑n := by exact_mod_cast hj_bound
    nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_right hj_boundR Real.pi_pos.le]
  rw [hA_eq, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  -- Now goal: cos(u)/sin(u) ≥ 1/(2u)
  exact cot_ge_inv_two_mul hu_pos hu_le

/-- The angle (2k+1)π/(4n) is in (0, π/2) for k < n, so tan is positive. -/
private lemma tan_half_chebyshev_pos (n : ℕ) (hn : 0 < n) (k : Fin n) :
    0 < Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (4 * n)) /
        Real.cos ((2 * k.val + 1 : ℝ) * Real.pi / (4 * n)) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hangle_pos : 0 < (2 * k.val + 1 : ℝ) * Real.pi / (4 * n) := by positivity
  have hangle_lt : (2 * k.val + 1 : ℝ) * Real.pi / (4 * n) < Real.pi / 2 := by
    rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * n) (by positivity : (0 : ℝ) < 2)]
    have hlt : 2 * k.val + 1 < 2 * n := by omega
    nlinarith [Real.pi_pos, (show (2 * k.val + 1 : ℝ) < 2 * n from by exact_mod_cast hlt)]
  apply div_pos
  · exact Real.sin_pos_of_pos_of_lt_pi hangle_pos (by linarith [Real.pi_pos])
  · exact Real.cos_pos_of_mem_Ioo ⟨by linarith, hangle_lt⟩

/-- Cosine is 1-Lipschitz: |cos α - cos β| ≤ |α - β|.
    Used to upper-bound |cos θ - chebyshevNode n k| by the angular distance. -/
private lemma cos_dist_le (α β : ℝ) : |Real.cos α - Real.cos β| ≤ |α - β| := by
  have h := Real.lipschitzWith_cos.dist_le_mul α β
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
  exact h

/-- For d ∈ (0, π/2] and θ ∈ [d, π-d]: sin d ≤ sin θ.
    Proof: sin is increasing on [0, π/2] (for θ ≤ π/2) and by symmetry sin(π-θ) = sin θ
    (for θ > π/2, use π - θ ∈ [d, π/2] so sin(π-θ) ≥ sin d). -/
private lemma sin_ge_sin_of_mem_Icc {d θ : ℝ} (hd_pos : 0 < d) (hd_le : d ≤ Real.pi / 2)
    (hθ_ge : d ≤ θ) (hθ_le : θ ≤ Real.pi - d) :
    Real.sin d ≤ Real.sin θ := by
  have hpi := Real.pi_pos
  have hθ_nonneg : 0 ≤ θ := le_trans hd_pos.le hθ_ge
  by_cases hθ_le_half : θ ≤ Real.pi / 2
  · -- θ ∈ [d, π/2] ⊆ [-π/2, π/2]: use monotonicity of sin
    apply Real.strictMonoOn_sin.monotoneOn
    · exact Set.mem_Icc.mpr ⟨by linarith, hd_le⟩
    · exact Set.mem_Icc.mpr ⟨by linarith, hθ_le_half⟩
    · exact hθ_ge
  · -- θ ∈ (π/2, π-d]: sin θ = sin(π-θ) and π-θ ∈ [d, π/2]
    push_neg at hθ_le_half
    have hπθ_le : Real.pi - θ ≤ Real.pi / 2 := by linarith
    have hπθ_nonneg : 0 ≤ Real.pi - θ := by linarith [hθ_le]
    rw [← Real.sin_pi_sub θ]
    apply Real.strictMonoOn_sin.monotoneOn
    · exact Set.mem_Icc.mpr ⟨by linarith, hd_le⟩
    · exact Set.mem_Icc.mpr ⟨by linarith, hπθ_le⟩
    · linarith

/-- Odd harmonic partial sum bound: ∑_{j=0}^{m-1} 1/(2j+1) ≥ (1/2)·log(m+1).
    Uses 1/(2j+1) ≥ 1/(2(j+1)) and Mathlib's harmonic bound. -/
private lemma odd_harmonic_sum_lb (m : ℕ) (hm : 0 < m) :
    (1 : ℝ) / 2 * Real.log (↑m + 1) ≤
      ∑ j ∈ Finset.range m, (1 : ℝ) / (2 * ↑j + 1) := by
  -- Step 1: 1/(2j+1) ≥ 1/(2(j+1)) = (1/2) · 1/(j+1)
  have h_compare : ∀ j ∈ Finset.range m,
      (1 : ℝ) / (2 * (↑j + 1)) ≤ 1 / (2 * ↑j + 1) := by
    intro j _
    rw [div_le_div_iff₀ (by positivity) (by positivity : (0 : ℝ) < 2 * ↑j + 1)]
    nlinarith [Nat.cast_nonneg (α := ℝ) j]
  -- Step 2: ∑ 1/(2(j+1)) = (1/2) · ∑ 1/(j+1) = (1/2) · H_m
  have hsum_half : ∑ j ∈ Finset.range m, (1 : ℝ) / (2 * (↑j + 1)) =
      (1 : ℝ) / 2 * ∑ j ∈ Finset.range m, (1 : ℝ) / (↑j + 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [mul_one_div, div_div]
  -- Step 3: ∑_{j=0}^{m-1} 1/(j+1) = H_m (harmonic number)
  have hharmonic : ∀ M : ℕ, ∑ j ∈ Finset.range M, (1 : ℝ) / (↑j + 1) = ((harmonic M : ℚ) : ℝ) := by
    intro M
    induction M with
    | zero => simp [harmonic]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, harmonic_succ]
      push_cast
      ring
  -- Step 4: log(m+1) ≤ H_m
  have hlog_harmonic : Real.log (↑m + 1) ≤ ((harmonic m : ℚ) : ℝ) := by
    have := log_add_one_le_harmonic m
    exact_mod_cast this
  -- Combine: (1/2)·log(m+1) ≤ (1/2)·H_m = ∑ 1/(2(j+1)) ≤ ∑ 1/(2j+1)
  calc (1 : ℝ) / 2 * Real.log (↑m + 1)
      ≤ 1 / 2 * ((harmonic m : ℚ) : ℝ) := by
          apply mul_le_mul_of_nonneg_left hlog_harmonic (by norm_num)
    _ = ∑ j ∈ Finset.range m, 1 / (2 * (↑j + 1)) := by rw [hsum_half, hharmonic m]
    _ ≤ ∑ j ∈ Finset.range m, 1 / (2 * ↑j + 1) := Finset.sum_le_sum h_compare

/-- For n ≥ 2: (n/2 + 1)² ≥ n + 1, which gives √(n+1) ≤ n/2 + 1,
    hence (1/2)·log(n+1) ≤ log(n/2+1). -/
private lemma half_log_le_log_half_add_one (n : ℕ) (hn : 2 ≤ n) :
    (1 : ℝ) / 2 * Real.log ((↑n : ℝ) + 1) ≤ Real.log ((↑(n / 2) : ℝ) + 1) := by
  have hn1_pos : (0 : ℝ) < (↑n : ℝ) + 1 := by positivity
  have hndiv1_pos : (0 : ℝ) < (↑(n / 2) : ℝ) + 1 := by positivity
  -- Key arithmetic: n+1 ≤ (n/2+1)²
  have key : (↑n : ℝ) + 1 ≤ ((↑(n / 2) : ℝ) + 1) ^ 2 := by
    have h1 : n ≤ 2 * (n / 2) + 1 := by omega
    have h2 : 1 ≤ n / 2 := Nat.div_pos hn (by norm_num)
    have h1R : (↑n : ℝ) ≤ 2 * (↑(n / 2) : ℝ) + 1 := by exact_mod_cast h1
    have h2R : (1 : ℝ) ≤ (↑(n / 2) : ℝ) := by exact_mod_cast h2
    nlinarith [h1R, h2R, sq_nonneg ((↑(n / 2) : ℝ) - 1)]
  -- (1/2)·log(n+1) ≤ log(n/2+1) via: log(n+1) ≤ 2·log(n/2+1) = log((n/2+1)²)
  have h2log : Real.log ((↑n : ℝ) + 1) ≤ 2 * Real.log ((↑(n / 2) : ℝ) + 1) := by
    have hpow : Real.log (((↑(n / 2) : ℝ) + 1) ^ 2) = 2 * Real.log ((↑(n / 2) : ℝ) + 1) := by
      rw [Real.log_pow]
      ring
    rw [← hpow]
    -- Mathlib v4.26.0: Real.log_le_log expects strict positivity (0 < x), not 0 ≤ x.
    exact Real.log_le_log hn1_pos key
  linarith

/-- For the x = -1 case: the trigonometric Lebesgue sum S_n = Σ tan(φₖ/2) grows like n log n.

    Strategy: bound the sum from below using the sub-sum over the last n/2 terms,
    apply the cotangent lower bound, and compare with the harmonic series. -/
private lemma trig_sum_lb_of_cos_eq_neg_one (n : ℕ) (hn : 0 < n) :
    (1 : ℝ) / (2 * Real.pi) * ((↑n : ℝ) * Real.log ((↑n : ℝ) + 1)) ≤
      ∑ k : Fin n, Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) /
                   |(-1 : ℝ) - Real.cos ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n))| := by
  -- Step 1: Rewrite each term using the half-angle formula
  have hS_eq : ∑ k : Fin n, Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) /
                   |(-1 : ℝ) - Real.cos ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n))| =
               ∑ k : Fin n, Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (4 * n)) /
                   Real.cos ((2 * k.val + 1 : ℝ) * Real.pi / (4 * n)) :=
    Finset.sum_congr rfl (fun k _ => sum_term_eq_tan_half_angle n hn k)
  rw [hS_eq]
  -- Step 2: Handle n = 1 separately (sum = tan(π/4) = 1, target < 1).
  -- For ℕ, `0 < n` is `1 ≤ n`; rewrite via `Nat.one_le_iff_ne_zero` to get a `≤`-shaped
  -- term that `eq_or_lt_of_le` accepts (Mathlib unification quirk in v4.26.0).
  have hn_ge1 : 1 ≤ n := hn
  rcases eq_or_lt_of_le hn_ge1 with rfl | hn_ge_2
  · -- n = 1: target = (1/(2π))·log(2) ≤ 1 = sum
    simp only [Fin.sum_univ_one, Fin.val_zero, Nat.cast_zero, Nat.cast_one,
      mul_zero, zero_add, one_mul, mul_one]
    have hlog2_le : Real.log 2 ≤ 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      have hexp1 : Real.exp 1 ≥ 2 := by linarith
      linarith [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2) |>.mpr (by linarith)]
    have hpi_pos := Real.pi_pos
    -- sin(π/4)/cos(π/4) = 1
    have htan : Real.sin (Real.pi / 4) / Real.cos (Real.pi / 4) = 1 := by
      rw [Real.sin_pi_div_four, Real.cos_pi_div_four, div_self]
      exact ne_of_gt (by positivity)
    rw [htan]
    -- (1/(2π))·log(2) ≤ 1
    have hbound : 1 / (2 * Real.pi) * Real.log (1 + 1) ≤ 1 := by
      have hpi_gt_two : (2 : ℝ) < Real.pi := by
        have h := Real.sin_lt Real.pi_div_two_pos
        rw [Real.sin_pi_div_two] at h
        linarith
      have hinv : 1 / (2 * Real.pi) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [hpi_gt_two]
      have hlog_nonneg : 0 ≤ Real.log (1 + 1) := Real.log_nonneg (by norm_num)
      calc 1 / (2 * Real.pi) * Real.log (1 + 1)
          ≤ 1 * Real.log (1 + 1) := mul_le_mul_of_nonneg_right hinv hlog_nonneg
        _ = Real.log (1 + 1) := one_mul _
        _ ≤ 1 := by rw [show (1 : ℝ) + 1 = 2 by norm_num]; exact hlog2_le
    linarith [hbound]
  · -- Step 3: n ≥ 2. Bound sum from below by sub-sum over last n/2 terms.
    -- Each term is positive
    have hterms_nonneg : ∀ k : Fin n, 0 ≤ Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (4 * n)) /
        Real.cos ((2 * k.val + 1 : ℝ) * Real.pi / (4 * n)) :=
      fun k => le_of_lt (tan_half_chebyshev_pos n hn k)
    -- Define the sub-sum over k ≥ n/2
    set S := Finset.filter (fun k : Fin n => n / 2 ≤ k.val) Finset.univ
    -- Sub-sum ≤ full sum (since terms are nonneg)
    have hsub_le_full : ∑ k ∈ S, Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (4 * n)) /
        Real.cos ((2 * k.val + 1 : ℝ) * Real.pi / (4 * n)) ≤
        ∑ k : Fin n, Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (4 * n)) /
        Real.cos ((2 * k.val + 1 : ℝ) * Real.pi / (4 * n)) :=
      Finset.sum_le_univ_sum_of_nonneg hterms_nonneg
    -- Step 4: Bound each sub-sum term using cot_ge_inv_two_mul
    have hcot_bound : ∀ k ∈ S,
        (2 * ↑n : ℝ) / (Real.pi * (2 * ↑(n - 1 - k.val) + 1)) ≤
        Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (4 * n)) /
        Real.cos ((2 * k.val + 1 : ℝ) * Real.pi / (4 * n)) := by
      intro k hk
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      have hge := tan_eq_cot_complement n hn k hk
      -- Rewrite 1/(2·u) = 2n/(π(2j+1)) where u = (2j+1)π/(4n) and j = n-1-k
      have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      have hj_cast : (0 : ℝ) < 2 * ↑(n - 1 - k.val) + 1 := by positivity
      rw [show 1 / (2 * ((2 * (↑(n - 1 - k.val) : ℝ) + 1) * Real.pi / (4 * ↑n))) =
          (2 * ↑n) / (Real.pi * (2 * ↑(n - 1 - k.val) + 1)) from by
        field_simp; ring] at hge
      exact hge
    -- Step 5: Sum of 2n/(π(2j+1)) over j = 0,...,n/2-1 via reindexing
    -- The sub-sum ≥ (2n/π) · ∑_{j ∈ range(n/2)} 1/(2j+1) ≥ (n/π)·log(n/2+1)
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have hpi_pos := Real.pi_pos
    have hndiv_pos : 0 < n / 2 := Nat.div_pos (by omega : 2 ≤ n) (by norm_num)
    -- Step 6: Use the target chain
    calc (1 : ℝ) / (2 * Real.pi) * (↑n * Real.log (↑n + 1))
        = ↑n / Real.pi * ((1 : ℝ) / 2 * Real.log (↑n + 1)) := by ring
      _ ≤ ↑n / Real.pi * Real.log (↑(n / 2) + 1) := by
          apply mul_le_mul_of_nonneg_left
            (half_log_le_log_half_add_one n (by omega))
            (div_nonneg hn_pos.le hpi_pos.le)
      _ ≤ ∑ k ∈ S, Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (4 * n)) /
            Real.cos ((2 * k.val + 1 : ℝ) * Real.pi / (4 * n)) := by
          -- Chain: n/π·log(n/2+1) = (2n/π)·(1/2)·log(n/2+1) ≤ (2n/π)·∑ 1/(2j+1)
          --        = ∑_{k∈S} 2n/(π(2(n-1-k)+1)) ≤ ∑_{k∈S} sin/cos
          calc ↑n / Real.pi * Real.log (↑(n / 2) + 1)
              = 2 * ↑n / Real.pi * ((1 : ℝ) / 2 * Real.log (↑(n / 2) + 1)) := by ring
            _ ≤ 2 * ↑n / Real.pi * ∑ j ∈ Finset.range (n / 2), (1 : ℝ) / (2 * ↑j + 1) := by
                apply mul_le_mul_of_nonneg_left (odd_harmonic_sum_lb (n / 2) hndiv_pos)
                  (by positivity)
            _ = ∑ j ∈ Finset.range (n / 2), 2 * ↑n / (Real.pi * (2 * ↑j + 1)) := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl (fun j _ => ?_)
                rw [div_mul_div_comm, mul_one]
            _ ≤ ∑ k ∈ S, 2 * ↑n / (Real.pi * (2 * ↑(n - 1 - k.val) + 1)) := by
                -- Reindex: range(n/2) → S via j ↦ ⟨n-1-j, _⟩
                -- Then n-1-(n-1-j) = j, so terms match
                let φ : ℕ → Fin n := fun j => ⟨n - 1 - j, by omega⟩
                have hinj : Set.InjOn φ ↑(Finset.range (n / 2)) := by
                  intro j₁ hj₁ j₂ hj₂ heq
                  simp only [Finset.coe_range, Set.mem_Iio] at hj₁ hj₂
                  simp only [φ, Fin.mk.injEq] at heq
                  omega
                have himg_sub : (Finset.range (n / 2)).image φ ⊆ S := by
                  intro k hk
                  simp only [φ, Finset.mem_image, Finset.mem_range] at hk
                  obtain ⟨j, hj_lt, hk_eq⟩ := hk
                  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
                  have := Fin.mk.injEq _ _ _ _ ▸ hk_eq
                  omega
                have hvals : ∀ j ∈ Finset.range (n / 2),
                    2 * ↑n / (Real.pi * (2 * (↑j : ℝ) + 1)) =
                    2 * ↑n / (Real.pi * (2 * ↑(n - 1 - (φ j).val) + 1)) := by
                  intro j hj
                  have hj_lt : j < n / 2 := Finset.mem_range.mp hj
                  simp only [φ, Fin.val_mk]
                  have hjj : n - 1 - (n - 1 - j) = j := by omega
                  rw [hjj]
                -- ∑ range(n/2) f(j) = ∑ image(φ) g(k) ≤ ∑ S g(k)
                rw [show ∑ j ∈ Finset.range (n / 2), 2 * ↑n / (Real.pi * (2 * (↑j : ℝ) + 1)) =
                    ∑ j ∈ Finset.range (n / 2),
                      2 * ↑n / (Real.pi * (2 * ↑(n - 1 - (φ j).val) + 1)) from
                  Finset.sum_congr rfl hvals]
                calc ∑ j ∈ Finset.range (n / 2),
                        2 * ↑n / (Real.pi * (2 * ↑(n - 1 - (φ j).val) + 1))
                    = ∑ k ∈ (Finset.range (n / 2)).image φ,
                        2 * ↑n / (Real.pi * (2 * ↑(n - 1 - k.val) + 1)) := by
                      rw [Finset.sum_image hinj]
                  _ ≤ ∑ k ∈ S, 2 * ↑n / (Real.pi * (2 * ↑(n - 1 - k.val) + 1)) :=
                      Finset.sum_le_sum_of_subset_of_nonneg himg_sub
                        (fun k _ _ => by positivity)
            _ ≤ ∑ k ∈ S, Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (4 * n)) /
                  Real.cos ((2 * k.val + 1 : ℝ) * Real.pi / (4 * n)) :=
                Finset.sum_le_sum hcot_bound
      _ ≤ ∑ k : Fin n, Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (4 * n)) /
            Real.cos ((2 * k.val + 1 : ℝ) * Real.pi / (4 * n)) := hsub_le_full

/-! ## Harmonic Trig Sum Lower Bound (General x ∈ (-1, 1)) -/

/-- **Nearest Chebyshev angle within π/(2n) of θ.**

    For any θ ∈ (0, π) and n ≥ 1, there exists a Chebyshev angle
    `φ_{k₀} = (2k₀+1)π/(2n)` within distance `π/(2n)` of θ.

    Reason: the n angles φₖ (k = 0,…,n-1) are equispaced at distance π/n
    and tile (0, π) so that each θ ∈ (0, π) lies within π/(2n) of the
    nearest midpoint φ_{k₀}.

    The witness is k₀ = ⌊nθ/π⌋, which lies in {0, …, n-1} since 0 < nθ/π < n,
    and satisfies (k₀)π/n ≤ θ < (k₀+1)π/n by definition of floor; the
    midpoint φ_{k₀} = (2k₀+1)π/(2n) is then within π/(2n) of θ.

    Formalizes Step 2 of the proof sketch in `trig_sum_harmonic_lb`. -/
private lemma exists_nearest_chebyshev_angle (n : ℕ) (hn : 0 < n)
    {θ : ℝ} (hθ_pos : 0 < θ) (hθ_lt : θ < Real.pi) :
    ∃ k₀ : Fin n,
      |θ - (2 * (k₀.val : ℝ) + 1) * Real.pi / (2 * n)| ≤ Real.pi / (2 * n) := by
  have hpi_pos := Real.pi_pos
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
  -- y := nθ/π lies in (0, n).
  have hy_pos : 0 < (n : ℝ) * θ / Real.pi := by positivity
  have hy_lt : (n : ℝ) * θ / Real.pi < n := by
    rw [div_lt_iff₀ hpi_pos]; nlinarith
  -- Set m := ⌊y⌋ : ℕ via Int.toNat (well-defined since y ≥ 0).
  set m : ℕ := ⌊(n : ℝ) * θ / Real.pi⌋.toNat with hm_def
  have hfloor_nn : (0 : ℤ) ≤ ⌊(n : ℝ) * θ / Real.pi⌋ :=
    Int.floor_nonneg.mpr hy_pos.le
  have hm_int : (m : ℤ) = ⌊(n : ℝ) * θ / Real.pi⌋ := by
    rw [hm_def, Int.toNat_of_nonneg hfloor_nn]
  have hm_floor_eq : (m : ℝ) = (⌊(n : ℝ) * θ / Real.pi⌋ : ℝ) := by exact_mod_cast hm_int
  -- m < n.
  have hm_lt : m < n := by
    have h1 : (⌊(n : ℝ) * θ / Real.pi⌋ : ℝ) ≤ (n : ℝ) * θ / Real.pi := Int.floor_le _
    have h2 : (m : ℝ) < (n : ℝ) := by rw [hm_floor_eq]; linarith
    exact_mod_cast h2
  -- Floor sandwich: m ≤ y < m + 1.
  have hm_le_y : (m : ℝ) ≤ (n : ℝ) * θ / Real.pi := by
    rw [hm_floor_eq]; exact Int.floor_le _
  have hy_lt_succ : (n : ℝ) * θ / Real.pi < (m : ℝ) + 1 := by
    rw [hm_floor_eq]; exact Int.lt_floor_add_one _
  refine ⟨⟨m, hm_lt⟩, ?_⟩
  -- Two-sided bound on θ: m·π/n ≤ θ ≤ (m+1)·π/n.
  have hL : (m : ℝ) * Real.pi / n ≤ θ := by
    have h1 : (m : ℝ) * Real.pi ≤ (n : ℝ) * θ := by
      rw [le_div_iff₀ hpi_pos] at hm_le_y; exact hm_le_y
    rw [div_le_iff₀ hn_pos]; linarith
  have hR : θ ≤ ((m : ℝ) + 1) * Real.pi / n := by
    have h1 : (n : ℝ) * θ < ((m : ℝ) + 1) * Real.pi := by
      rw [div_lt_iff₀ hpi_pos] at hy_lt_succ; exact hy_lt_succ
    rw [le_div_iff₀ hn_pos]; linarith
  -- |θ - midpoint| ≤ half-width π/(2n) via abs_le.
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · -- Lower: (2m+1)π/(2n) - π/(2n) = m·π/n, and m·π/n ≤ θ.
    have hmid_lo : (2 * (m : ℝ) + 1) * Real.pi / (2 * n) - Real.pi / (2 * n) =
                   (m : ℝ) * Real.pi / n := by
      field_simp [hn_ne]
      ring
    linarith
  · -- Upper: (2m+1)π/(2n) + π/(2n) = (m+1)·π/n, and θ ≤ (m+1)·π/n.
    have hmid_hi : (2 * (m : ℝ) + 1) * Real.pi / (2 * n) + Real.pi / (2 * n) =
                   ((m : ℝ) + 1) * Real.pi / n := by
      field_simp [hn_ne]
      ring
    linarith

/-- **Step 3 of trig_sum_harmonic_lb (triangle bound).**

    For any two indices k₀, k : Fin n, the distance between θ and the chebyshev angle
    φ_k = (2k+1)π/(2n) is bounded by the distance from θ to φ_{k₀} plus the
    inter-node distance |k.val - k₀.val|·π/n.

    Combined with `exists_nearest_chebyshev_angle` (giving |θ - φ_{k₀}| ≤ π/(2n)),
    this yields the bound |θ - φ_k| ≤ (2|k.val - k₀.val| + 1)·π/(2n). -/
private lemma chebyshev_angle_dist_triangle (n : ℕ) (hn : 0 < n) (θ : ℝ) (k₀ k : Fin n) :
    |θ - (2 * (k.val : ℝ) + 1) * Real.pi / (2 * n)| ≤
      |θ - (2 * (k₀.val : ℝ) + 1) * Real.pi / (2 * n)| +
        |((k.val : ℝ) - k₀.val)| * Real.pi / n := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
  have hpi_pos := Real.pi_pos
  -- Algebraic identity: φ_k = φ_{k₀} + (k - k₀)·π/n, so
  -- θ - φ_k = (θ - φ_{k₀}) + (k₀ - k)·π/n
  have key : θ - (2 * (k.val : ℝ) + 1) * Real.pi / (2 * n) =
             (θ - (2 * (k₀.val : ℝ) + 1) * Real.pi / (2 * n)) +
             (((k₀.val : ℝ) - k.val) * Real.pi / n) := by
    field_simp
    ring
  -- |k₀ - k|·π/n = |k - k₀|·π/n
  have habs_eq : |((k₀.val : ℝ) - k.val) * Real.pi / n| =
                 |((k.val : ℝ) - k₀.val)| * Real.pi / n := by
    rw [abs_div, abs_mul, abs_of_pos hpi_pos, abs_of_pos hn_pos, abs_sub_comm]
  calc |θ - (2 * (k.val : ℝ) + 1) * Real.pi / (2 * n)|
      = |(θ - (2 * (k₀.val : ℝ) + 1) * Real.pi / (2 * n)) +
          (((k₀.val : ℝ) - k.val) * Real.pi / n)| := by rw [key]
    _ ≤ |θ - (2 * (k₀.val : ℝ) + 1) * Real.pi / (2 * n)| +
        |((k₀.val : ℝ) - k.val) * Real.pi / n| := abs_add_le _ _
    _ = |θ - (2 * (k₀.val : ℝ) + 1) * Real.pi / (2 * n)| +
        |((k.val : ℝ) - k₀.val)| * Real.pi / n := by rw [habs_eq]

/-- **Step 3 corollary**: when k₀ is within π/(2n) of θ (the nearest node), then
    for any other k : Fin n, the distance |θ - φ_k| ≤ (2|k - k₀| + 1)·π/(2n). -/
private lemma chebyshev_angle_dist_from_nearest (n : ℕ) (hn : 0 < n) (θ : ℝ) (k₀ k : Fin n)
    (hk₀ : |θ - (2 * (k₀.val : ℝ) + 1) * Real.pi / (2 * n)| ≤ Real.pi / (2 * n)) :
    |θ - (2 * (k.val : ℝ) + 1) * Real.pi / (2 * n)| ≤
      (2 * |((k.val : ℝ) - k₀.val)| + 1) * Real.pi / (2 * n) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
  have hpi_pos := Real.pi_pos
  -- Triangle bound
  have htri := chebyshev_angle_dist_triangle n hn θ k₀ k
  -- Combine: |θ - φ_k| ≤ π/(2n) + |k - k₀|·π/n = (2|k-k₀|+1)·π/(2n)
  have hsimp : Real.pi / (2 * n) + |((k.val : ℝ) - k₀.val)| * Real.pi / n =
               (2 * |((k.val : ℝ) - k₀.val)| + 1) * Real.pi / (2 * n) := by
    field_simp
    ring
  linarith [htri, hk₀]

/-- **Step 4 of trig_sum_harmonic_lb (sin lower bound on the interior).**

    On the interval [d/2, π - d/2] with d > 0 (and necessarily d ≤ π for the interval
    to be non-empty), the function sin attains its minimum at the boundary, namely
    sin(d/2). This is because sin is symmetric about π/2 (sin(π - x) = sin x),
    sin(d/2) = sin(π - d/2), and sin is monotone on each side of π/2.

    The proof splits on whether x ≤ π/2 (use monotonicity of sin on [-π/2, π/2])
    or x > π/2 (apply monotonicity to π - x ∈ [d/2, π/2) and use sin(π - x) = sin x). -/
private lemma sin_lb_of_in_interior
    (d : ℝ) (hd_pos : 0 < d)
    (x : ℝ) (h_lower : d / 2 ≤ x) (h_upper : x ≤ Real.pi - d / 2) :
    Real.sin (d / 2) ≤ Real.sin x := by
  have hpi_pos := Real.pi_pos
  have hd_half_pos : 0 < d / 2 := by linarith
  have hneg_pi_half_le : -(Real.pi / 2) ≤ d / 2 := by linarith
  by_cases hx : x ≤ Real.pi / 2
  · -- Case: d/2 ≤ x ≤ π/2 — use monotonicity of sin on [-π/2, π/2]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two hneg_pi_half_le hx h_lower
  · push_neg at hx
    -- Case: x > π/2. Use sin(x) = sin(π - x) with π - x ∈ [d/2, π/2)
    have h_pi_x_lower : d / 2 ≤ Real.pi - x := by linarith
    have h_pi_x_upper : Real.pi - x ≤ Real.pi / 2 := by linarith
    have hsin_le : Real.sin (d / 2) ≤ Real.sin (Real.pi - x) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two hneg_pi_half_le h_pi_x_upper h_pi_x_lower
    rwa [Real.sin_pi_sub] at hsin_le

/-- **Step 4 corollary (sin lower bound at chebyshev midpoints).**

    For a chebyshev midpoint φ_k = (2k+1)π/(2n) lying in [d/2, π - d/2] with d > 0,
    we have sin(φ_k) ≥ sin(d/2). -/
private lemma sin_chebyshev_midpoint_lb
    (n : ℕ) (hn : 0 < n) (k : Fin n)
    (d : ℝ) (hd_pos : 0 < d)
    (h_lower : d / 2 ≤ (2 * (k.val : ℝ) + 1) * Real.pi / (2 * n))
    (h_upper : (2 * (k.val : ℝ) + 1) * Real.pi / (2 * n) ≤ Real.pi - d / 2) :
    Real.sin (d / 2) ≤
      Real.sin ((2 * (k.val : ℝ) + 1) * Real.pi / (2 * n)) :=
  sin_lb_of_in_interior d hd_pos _ h_lower h_upper

/-- **Step 5 of trig_sum_harmonic_lb (per-term lower bound).**

    For a chebyshev midpoint φ_k whose midpoint lies in [d/2, π - d/2] (so
    `sin(φ_k) ≥ sin(d/2)`), the per-term lower bound combines:

      • Step 3:    |θ - φ_k| ≤ (2|k - k₀| + 1) · π / (2n)
      • Step 4:    sin(φ_k) ≥ sin(d/2) ≥ 0
      • Lipschitz: |cos θ - cos φ_k| ≤ |θ - φ_k|

    so that

      sin(φ_k) / |cos θ - cos φ_k|
        ≥ sin(d/2) · (2n) / ((2|k - k₀| + 1) · π).

    The denominator on the LHS is positive because `cos θ ≠ chebyshevNode n k`.
    The denominator on the RHS is positive because n ≥ 1 and π > 0. -/
private lemma chebyshev_term_lb_at_node
    (n : ℕ) (hn : 0 < n) (k₀ k : Fin n)
    (θ : ℝ)
    (d : ℝ) (hd_pos : 0 < d)
    (hk₀_close : |θ - (2 * (k₀.val : ℝ) + 1) * Real.pi / (2 * n)| ≤ Real.pi / (2 * n))
    (h_lower : d / 2 ≤ (2 * (k.val : ℝ) + 1) * Real.pi / (2 * n))
    (h_upper : (2 * (k.val : ℝ) + 1) * Real.pi / (2 * n) ≤ Real.pi - d / 2)
    (hne : Real.cos θ ≠ chebyshevNode n k) :
    Real.sin (d / 2) * (2 * (n : ℝ)) /
        ((2 * |((k.val : ℝ) - k₀.val)| + 1) * Real.pi) ≤
      Real.sin ((2 * (k.val : ℝ) + 1) * Real.pi / (2 * n)) /
        |Real.cos θ - chebyshevNode n k| := by
  set φ : ℝ := (2 * (k.val : ℝ) + 1) * Real.pi / (2 * n) with hφ_def
  -- Positivity facts
  have hpi_pos := Real.pi_pos
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have h_abs_kk₀_nn : 0 ≤ |((k.val : ℝ) - k₀.val)| := abs_nonneg _
  -- Step 4: sin(φ) ≥ sin(d/2) ≥ 0
  have hsin_lb : Real.sin (d / 2) ≤ Real.sin φ :=
    sin_chebyshev_midpoint_lb n hn k d hd_pos h_lower h_upper
  have hsin_d_half_pos : 0 < Real.sin (d / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi (by linarith)
    -- From h_lower ≤ h_upper: d/2 ≤ π - d/2, so d ≤ π
    have hd_le_pi : d ≤ Real.pi := by linarith
    linarith
  have hsin_φ_nn : 0 ≤ Real.sin φ := le_trans (le_of_lt hsin_d_half_pos) hsin_lb
  -- Step 3 + Lipschitz: |cos θ - cos φ| ≤ |θ - φ| ≤ (2|k-k₀|+1)π/(2n) =: B
  set B : ℝ := (2 * |((k.val : ℝ) - k₀.val)| + 1) * Real.pi / (2 * (n : ℝ)) with hB_def
  have h_num_pos : 0 < 2 * |((k.val : ℝ) - k₀.val)| + 1 := by positivity
  have h_num_pi_pos : 0 < (2 * |((k.val : ℝ) - k₀.val)| + 1) * Real.pi := by positivity
  have h_2n_pos : 0 < 2 * (n : ℝ) := by positivity
  have hB_pos : 0 < B := by
    rw [hB_def]; exact div_pos h_num_pi_pos h_2n_pos
  -- Lipschitz: |cos θ - cos φ| ≤ |θ - φ|
  have h_lip : |Real.cos θ - Real.cos φ| ≤ |θ - φ| :=
    Real.abs_cos_sub_cos_le θ φ
  -- Step 3 corollary: |θ - φ| ≤ B
  have h_step3 : |θ - φ| ≤ B := chebyshev_angle_dist_from_nearest n hn θ k₀ k hk₀_close
  -- Combine: |cos θ - cos φ| ≤ B
  have h_cos_le_B : |Real.cos θ - Real.cos φ| ≤ B := le_trans h_lip h_step3
  -- |cos θ - chebyshevNode n k| = |cos θ - cos φ|
  have hnode : chebyshevNode n k = Real.cos φ := by
    simp only [chebyshevNode, hφ_def]
  -- The denominator on LHS is positive (from hne)
  have h_denom_pos : 0 < |Real.cos θ - chebyshevNode n k| := by
    rw [abs_pos, sub_ne_zero]; exact hne
  have h_denom_pos' : 0 < |Real.cos θ - Real.cos φ| := by
    rw [hnode] at h_denom_pos; exact h_denom_pos
  have hsin_d_half_nn : 0 ≤ Real.sin (d / 2) := le_of_lt hsin_d_half_pos
  -- Convert sin(d/2)/B to the target form via div_div_eq_mul_div
  have h_target_eq : Real.sin (d / 2) / B =
      Real.sin (d / 2) * (2 * (n : ℝ)) /
        ((2 * |((k.val : ℝ) - k₀.val)| + 1) * Real.pi) := by
    rw [hB_def]
    exact div_div_eq_mul_div _ _ _
  rw [hnode]
  -- Two-step monotone descent:
  --   sin(d/2)/B  ≤  sin(d/2)/|cos θ - cos φ|   (denom shrinks: |cos θ - cos φ| ≤ B)
  --             ≤  sin φ /|cos θ - cos φ|       (numer grows: sin(d/2) ≤ sin φ)
  calc Real.sin (d / 2) * (2 * (n : ℝ)) /
          ((2 * |((k.val : ℝ) - k₀.val)| + 1) * Real.pi)
      = Real.sin (d / 2) / B := h_target_eq.symm
    _ ≤ Real.sin (d / 2) / |Real.cos θ - Real.cos φ| := by
        gcongr
    _ ≤ Real.sin φ / |Real.cos θ - Real.cos φ| := by
        gcongr

/-- **Step 6a (shifted odd harmonic sum lower bound).**

    The shifted sub-harmonic sum `∑ⱼ₌₀^{m-1} 1/(2(j+1)+1) = ∑ⱼ₌₀^{m-1} 1/(2j+3)` is
    bounded below by `(1/2)·log(m+2) - 1`.

    Derivation: applying `odd_harmonic_sum_lb` at `m+1` gives
    `(1/2)·log(m+2) ≤ ∑ⱼ₌₀^m 1/(2j+1)`. Splitting off the `j=0` term
    (`1/(2·0+1) = 1`) leaves `∑ⱼ₌₀^{m-1} 1/(2(j+1)+1) ≥ (1/2)·log(m+2) - 1`. -/
private lemma odd_harmonic_sum_shifted_lb (m : ℕ) :
    (1 : ℝ) / 2 * Real.log ((↑m : ℝ) + 2) - 1 ≤
      ∑ j ∈ Finset.range m, (1 : ℝ) / (2 * ((↑j : ℝ) + 1) + 1) := by
  -- Split ∑_{j=0}^{m} 1/(2j+1) = 1 + ∑_{j=0}^{m-1} 1/(2(j+1)+1)
  have hsplit : ∑ j ∈ Finset.range (m + 1), (1 : ℝ) / (2 * (↑j : ℝ) + 1) =
      1 + ∑ j ∈ Finset.range m, (1 : ℝ) / (2 * ((↑j : ℝ) + 1) + 1) := by
    rw [Finset.sum_range_succ' (fun k => (1 : ℝ) / (2 * (↑k : ℝ) + 1)) m]
    push_cast
    ring
  -- Apply odd_harmonic_sum_lb at m+1
  have hle : (1 : ℝ) / 2 * Real.log (((m + 1 : ℕ) : ℝ) + 1) ≤
      ∑ j ∈ Finset.range (m + 1), (1 : ℝ) / (2 * (↑j : ℝ) + 1) :=
    odd_harmonic_sum_lb (m + 1) (Nat.succ_pos m)
  have hcast : ((m + 1 : ℕ) : ℝ) + 1 = (↑m : ℝ) + 2 := by push_cast; ring
  rw [hcast] at hle
  linarith

/-- **Step 6b (sub-sum lower bound via per-term bound).**

    Summing the per-term lower bound `chebyshev_term_lb_at_node` over indices
    `k = k₀ + j + 1` for `j ∈ Fin m` produces a harmonic-style sub-sum lower
    bound for the full chebyshev Lebesgue trig sum.

    Hypotheses:
    - `k₀.val + m + 1 ≤ n`: the range `[k₀+1, k₀+m]` fits inside `Fin n`
    - For each `j : Fin m`, the midpoint `φ_{k₀+j+1} ∈ [d/2, π - d/2]`

    Result: `sin(d/2) · (2n / π) · ∑ⱼ 1/(2(j+1)+1) ≤ Σ_k sin(φ_k)/|cos θ - cos φ_k|`.

    Combined with `odd_harmonic_sum_shifted_lb` this yields a `n · log(m)`-style
    lower bound on the full trig sum (when `m` grows linearly with `n`). -/
private lemma trig_sum_subsum_lb (n : ℕ) (hn : 0 < n)
    (θ : ℝ)
    (d : ℝ) (hd_pos : 0 < d)
    (hne : ∀ k : Fin n, Real.cos θ ≠ chebyshevNode n k)
    (k₀ : Fin n)
    (hk₀_close : |θ - (2 * (k₀.val : ℝ) + 1) * Real.pi / (2 * n)| ≤ Real.pi / (2 * n))
    (m : ℕ) (hm_le : k₀.val + m + 1 ≤ n)
    (h_interior : ∀ j : Fin m,
      d / 2 ≤ (2 * ((k₀.val + j.val + 1 : ℕ) : ℝ) + 1) * Real.pi / (2 * n) ∧
      (2 * ((k₀.val + j.val + 1 : ℕ) : ℝ) + 1) * Real.pi / (2 * n) ≤ Real.pi - d / 2) :
    Real.sin (d / 2) * (2 * (n : ℝ)) / Real.pi *
        ∑ j ∈ Finset.range m, (1 : ℝ) / (2 * ((↑j : ℝ) + 1) + 1) ≤
      ∑ k : Fin n, Real.sin ((2 * (k.val : ℝ) + 1) * Real.pi / (2 * n)) /
                   |Real.cos θ - chebyshevNode n k| := by
  have hpi_pos := Real.pi_pos
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  -- Index injection φ : Fin m → Fin n via j ↦ k₀ + j + 1
  let φ : Fin m → Fin n := fun j => ⟨k₀.val + j.val + 1, by
    have := j.isLt; omega⟩
  -- Each chebyshev term is nonneg
  have hterm_nn : ∀ k : Fin n,
      0 ≤ Real.sin ((2 * (k.val : ℝ) + 1) * Real.pi / (2 * n)) /
          |Real.cos θ - chebyshevNode n k| :=
    fun k => div_nonneg (le_of_lt (chebyshevAngle_sin_pos n hn k)) (abs_nonneg _)
  -- φ is injective
  have hφ_inj : Function.Injective φ := by
    intro j₁ j₂ heq
    simp only [φ, Fin.mk.injEq] at heq
    exact Fin.ext (by omega)
  -- The image is a subset of Finset.univ
  have himg_sub :
      (Finset.univ : Finset (Fin m)).image φ ⊆ (Finset.univ : Finset (Fin n)) :=
    fun k _ => Finset.mem_univ k
  -- (φ j).val = k₀.val + j.val + 1 (definitional)
  have hφ_val : ∀ j : Fin m, (φ j).val = k₀.val + j.val + 1 := fun j => rfl
  -- Per-term lower bound at each j : Fin m
  have hsubterm : ∀ j : Fin m,
      Real.sin (d / 2) * (2 * (n : ℝ)) /
          ((2 * ((↑j.val : ℝ) + 1) + 1) * Real.pi) ≤
        Real.sin ((2 * ((φ j).val : ℝ) + 1) * Real.pi / (2 * n)) /
          |Real.cos θ - chebyshevNode n (φ j)| := by
    intro j
    obtain ⟨h_lower, h_upper⟩ := h_interior j
    have hne_φ : Real.cos θ ≠ chebyshevNode n (φ j) := hne _
    -- Convert the cast `((k₀.val + j.val + 1 : ℕ) : ℝ)` to `((φ j).val : ℝ)`
    have hval_eq : ((φ j).val : ℝ) = ((k₀.val + j.val + 1 : ℕ) : ℝ) := by
      rw [hφ_val]
    have h_lower' : d / 2 ≤ (2 * ((φ j).val : ℝ) + 1) * Real.pi / (2 * n) := by
      rw [hval_eq]; exact h_lower
    have h_upper' : (2 * ((φ j).val : ℝ) + 1) * Real.pi / (2 * n) ≤ Real.pi - d / 2 := by
      rw [hval_eq]; exact h_upper
    have hbound := chebyshev_term_lb_at_node n hn k₀ (φ j) θ d hd_pos
      hk₀_close h_lower' h_upper' hne_φ
    -- Translate |(φ j).val - k₀.val| = j.val + 1
    have hkk₀ : (((φ j).val : ℝ) - (k₀.val : ℝ)) = (↑j.val : ℝ) + 1 := by
      rw [hφ_val]
      push_cast
      ring
    have hkk₀_abs : |((φ j).val : ℝ) - (k₀.val : ℝ)| = (↑j.val : ℝ) + 1 := by
      rw [hkk₀]; exact abs_of_nonneg (by positivity)
    rw [hkk₀_abs] at hbound
    exact hbound
  -- Sub-sum (over Fin m) lower bound
  have hsub_sum_lb :
      ∑ j : Fin m,
          Real.sin (d / 2) * (2 * (n : ℝ)) /
              ((2 * ((↑j.val : ℝ) + 1) + 1) * Real.pi) ≤
        ∑ j : Fin m,
          Real.sin ((2 * ((φ j).val : ℝ) + 1) * Real.pi / (2 * n)) /
            |Real.cos θ - chebyshevNode n (φ j)| :=
    Finset.sum_le_sum (fun j _ => hsubterm j)
  -- Convert sub-sum to image-set sum
  have hsub_eq_image :
      ∑ j : Fin m,
          Real.sin ((2 * ((φ j).val : ℝ) + 1) * Real.pi / (2 * n)) /
            |Real.cos θ - chebyshevNode n (φ j)| =
        ∑ k ∈ (Finset.univ : Finset (Fin m)).image φ,
          Real.sin ((2 * (k.val : ℝ) + 1) * Real.pi / (2 * n)) /
            |Real.cos θ - chebyshevNode n k| := by
    rw [Finset.sum_image (fun j₁ _ j₂ _ heq => hφ_inj heq)]
  -- Image sum ≤ universe sum
  have himg_le_full :
      ∑ k ∈ (Finset.univ : Finset (Fin m)).image φ,
          Real.sin ((2 * (k.val : ℝ) + 1) * Real.pi / (2 * n)) /
            |Real.cos θ - chebyshevNode n k| ≤
        ∑ k : Fin n,
          Real.sin ((2 * (k.val : ℝ) + 1) * Real.pi / (2 * n)) /
            |Real.cos θ - chebyshevNode n k| :=
    Finset.sum_le_sum_of_subset_of_nonneg himg_sub (fun k _ _ => hterm_nn k)
  -- Convert LHS sub-sum to sub-sum form
  have hLHS_eq :
      Real.sin (d / 2) * (2 * (n : ℝ)) / Real.pi *
          ∑ j ∈ Finset.range m, (1 : ℝ) / (2 * ((↑j : ℝ) + 1) + 1) =
        ∑ j : Fin m,
          Real.sin (d / 2) * (2 * (n : ℝ)) /
              ((2 * ((↑j.val : ℝ) + 1) + 1) * Real.pi) := by
    rw [Fin.sum_univ_eq_sum_range
      (fun j => Real.sin (d / 2) * (2 * (n : ℝ)) /
        ((2 * ((↑j : ℝ) + 1) + 1) * Real.pi)) m]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    -- Per-term equality: (sin(d/2)·2n/π) · (1/(2(j+1)+1)) = sin(d/2)·2n / ((2(j+1)+1)·π)
    -- Both sides equal sin(d/2)·2n / (π·(2j+3)). `ring` cannot handle the inverse
    -- distribution `(a * b)⁻¹ = a⁻¹ * b⁻¹` directly; field_simp clears inverses
    -- and closes the goal in one step.
    have hpi_ne : (Real.pi : ℝ) ≠ 0 := Real.pi_pos.ne'
    have h_denom_pos : (0 : ℝ) < 2 * ((↑j : ℝ) + 1) + 1 := by positivity
    have h_denom_ne : 2 * ((↑j : ℝ) + 1) + 1 ≠ 0 := h_denom_pos.ne'
    field_simp
  linarith [hLHS_eq, hsub_sum_lb, hsub_eq_image, himg_le_full]

/-- **Step 6c (combined log lower bound).**

    Direct corollary of `odd_harmonic_sum_shifted_lb` (Step 6a) and
    `trig_sum_subsum_lb` (Step 6b): the trig sum is bounded below by a
    quantity of shape `sin(d/2) · (2n/π) · ((1/2)·log(m+2) − 1)`, the
    canonical `n · log(m)` growth that drives `trig_sum_harmonic_lb`.

    Hypotheses match `trig_sum_subsum_lb` plus `d ≤ π` (so `sin(d/2) ≥ 0`).
    Note: when `m` is small (e.g. `m ≤ 5`) the LHS is negative and the bound
    is vacuous — the substantive content kicks in at `m ≥ 6` where
    `(1/2)·log(8) - 1 ≈ 0.04 > 0`. -/
private lemma trig_sum_subsum_log_lb (n : ℕ) (hn : 0 < n)
    (θ : ℝ)
    (d : ℝ) (hd_pos : 0 < d) (hd_le_pi : d ≤ Real.pi)
    (hne : ∀ k : Fin n, Real.cos θ ≠ chebyshevNode n k)
    (k₀ : Fin n)
    (hk₀_close : |θ - (2 * (k₀.val : ℝ) + 1) * Real.pi / (2 * n)| ≤ Real.pi / (2 * n))
    (m : ℕ) (hm_le : k₀.val + m + 1 ≤ n)
    (h_interior : ∀ j : Fin m,
      d / 2 ≤ (2 * ((k₀.val + j.val + 1 : ℕ) : ℝ) + 1) * Real.pi / (2 * n) ∧
      (2 * ((k₀.val + j.val + 1 : ℕ) : ℝ) + 1) * Real.pi / (2 * n) ≤ Real.pi - d / 2) :
    Real.sin (d / 2) * (2 * (n : ℝ)) / Real.pi *
        ((1 : ℝ) / 2 * Real.log ((↑m : ℝ) + 2) - 1) ≤
      ∑ k : Fin n, Real.sin ((2 * (k.val : ℝ) + 1) * Real.pi / (2 * n)) /
                   |Real.cos θ - chebyshevNode n k| := by
  have hpi_pos := Real.pi_pos
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hsin_nn : 0 ≤ Real.sin (d / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hfactor_nn : 0 ≤ Real.sin (d / 2) * (2 * (n : ℝ)) / Real.pi :=
    div_nonneg (mul_nonneg hsin_nn (by linarith)) hpi_pos.le
  have h6a := odd_harmonic_sum_shifted_lb m
  have h6b := trig_sum_subsum_lb n hn θ d hd_pos hne k₀ hk₀_close m hm_le h_interior
  calc Real.sin (d / 2) * (2 * (n : ℝ)) / Real.pi *
          ((1 : ℝ) / 2 * Real.log ((↑m : ℝ) + 2) - 1)
      ≤ Real.sin (d / 2) * (2 * (n : ℝ)) / Real.pi *
          ∑ j ∈ Finset.range m, (1 : ℝ) / (2 * ((↑j : ℝ) + 1) + 1) :=
        mul_le_mul_of_nonneg_left h6a hfactor_nn
    _ ≤ ∑ k : Fin n, Real.sin ((2 * (k.val : ℝ) + 1) * Real.pi / (2 * n)) /
                     |Real.cos θ - chebyshevNode n k| := h6b

/-- **Step 7a (h_interior verifier).**

    Bridges the abstract `h_interior` hypothesis of `trig_sum_subsum_lb` and
    `trig_sum_subsum_log_lb` to a concrete pair of inputs:

      • the standard nearest-node closeness `|θ - φ_{k₀}| ≤ π/(2n)`, and
      • a single upper-cap on the largest sub-sum index, namely
        `φ_{k₀+m} ≤ π - θ/2`.

    With these, the full `h_interior` (with `d = θ`) holds for every `j : Fin m`:

      • Lower bound `θ/2 ≤ φ_{k₀+j+1}`: from `φ_{k₀} ≥ θ - π/(2n)` plus
        `(j+1)·π/n ≥ π/n = 2·(π/(2n))`, giving `φ_{k₀+j+1} ≥ θ + π/(2n) ≥ θ/2`
        (using `θ > 0`).
      • Upper bound `φ_{k₀+j+1} ≤ π - θ/2`: monotone in the index, since
        `j.val + 1 ≤ m` implies `φ_{k₀+j+1} ≤ φ_{k₀+m}`, and the cap is the
        latter.

    This packages the routine arithmetic shared by all subsequent specific
    choices of `m` (e.g. `m = ⌊nθ/(4π)⌋`-style choices used to close
    `trig_sum_harmonic_lb` in the θ ∈ (0, π/2] branch). -/
private lemma chebyshev_h_interior_of_close_and_max_index_cap
    (n : ℕ) (hn : 0 < n) (θ : ℝ) (hθ_pos : 0 < θ)
    (k₀ : Fin n)
    (hk₀_close : |θ - (2 * (k₀.val : ℝ) + 1) * Real.pi / (2 * n)| ≤ Real.pi / (2 * n))
    (m : ℕ)
    (hcap_max :
      (2 * ((k₀.val + m : ℕ) : ℝ) + 1) * Real.pi / (2 * n) ≤ Real.pi - θ / 2) :
    ∀ j : Fin m,
      θ / 2 ≤ (2 * ((k₀.val + j.val + 1 : ℕ) : ℝ) + 1) * Real.pi / (2 * n) ∧
      (2 * ((k₀.val + j.val + 1 : ℕ) : ℝ) + 1) * Real.pi / (2 * n) ≤
        Real.pi - θ / 2 := by
  intro j
  have hpi_pos := Real.pi_pos
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
  -- Casts of the natural-number index expressions
  have hcast_idx :
      ((k₀.val + j.val + 1 : ℕ) : ℝ) = (k₀.val : ℝ) + (j.val : ℝ) + 1 := by
    push_cast; ring
  have hcast_max :
      ((k₀.val + m : ℕ) : ℝ) = (k₀.val : ℝ) + (m : ℝ) := by
    push_cast; ring
  -- Algebraic decomposition: φ_{k₀+j+1} = φ_{k₀} + (j+1)·π/n
  have hφ_idx_eq :
      (2 * ((k₀.val + j.val + 1 : ℕ) : ℝ) + 1) * Real.pi / (2 * n) =
        (2 * (k₀.val : ℝ) + 1) * Real.pi / (2 * n) +
        ((j.val : ℝ) + 1) * Real.pi / n := by
    rw [hcast_idx]; field_simp; ring
  -- Algebraic decomposition: φ_{k₀+m} = φ_{k₀} + m·π/n
  have hφ_max_eq :
      (2 * ((k₀.val + m : ℕ) : ℝ) + 1) * Real.pi / (2 * n) =
        (2 * (k₀.val : ℝ) + 1) * Real.pi / (2 * n) +
        (m : ℝ) * Real.pi / n := by
    rw [hcast_max]; field_simp; ring
  -- From hk₀_close: φ_{k₀} ≥ θ - π/(2n).
  -- abs_le splits |θ - φ_{k₀}| ≤ π/(2n) into:
  --   -π/(2n) ≤ θ - φ_{k₀}  (giving φ_{k₀} ≤ θ + π/(2n))
  --   θ - φ_{k₀} ≤ π/(2n)   (giving φ_{k₀} ≥ θ - π/(2n)) — this one
  have hφk₀_ge :
      θ - Real.pi / (2 * n) ≤ (2 * (k₀.val : ℝ) + 1) * Real.pi / (2 * n) := by
    have := (abs_le.mp hk₀_close).2
    linarith
  -- π/n = 2·(π/(2n)) — used to bridge the section-spacing bound to π/(2n) units
  have hpi_n_eq : Real.pi / n = 2 * (Real.pi / (2 * n)) := by
    field_simp
  refine ⟨?_, ?_⟩
  · -- Lower bound: θ/2 ≤ φ_{k₀+j+1}
    rw [hφ_idx_eq]
    have hjval_nn : (0 : ℝ) ≤ (j.val : ℝ) := Nat.cast_nonneg _
    have hπn_nn : 0 ≤ Real.pi / n := (div_pos hpi_pos hn_pos).le
    -- (j+1)·π/n ≥ π/n (since j ≥ 0, so j+1 ≥ 1)
    have h_section_lb : Real.pi / n ≤ ((j.val : ℝ) + 1) * Real.pi / n := by
      have h1le : (1 : ℝ) ≤ (j.val : ℝ) + 1 := by linarith
      calc Real.pi / n
          = 1 * (Real.pi / n) := by ring
        _ ≤ ((j.val : ℝ) + 1) * (Real.pi / n) :=
            mul_le_mul_of_nonneg_right h1le hπn_nn
        _ = ((j.val : ℝ) + 1) * Real.pi / n := by ring
    -- Combine: φ_{k₀+j+1} ≥ (θ - π/(2n)) + π/n = θ + π/(2n) ≥ θ ≥ θ/2
    linarith
  · -- Upper bound: φ_{k₀+j+1} ≤ π - θ/2
    rw [hφ_idx_eq]
    rw [hφ_max_eq] at hcap_max
    -- (j+1)·π/n ≤ m·π/n, since j.val + 1 ≤ m (j : Fin m)
    have hj_le : (j.val : ℝ) + 1 ≤ (m : ℝ) := by
      have : j.val + 1 ≤ m := j.isLt
      exact_mod_cast this
    have hπn_nn : 0 ≤ Real.pi / n := (div_pos hpi_pos hn_pos).le
    have h_section_le :
        ((j.val : ℝ) + 1) * Real.pi / n ≤ (m : ℝ) * Real.pi / n := by
      calc ((j.val : ℝ) + 1) * Real.pi / n
          = ((j.val : ℝ) + 1) * (Real.pi / n) := by ring
        _ ≤ (m : ℝ) * (Real.pi / n) :=
            mul_le_mul_of_nonneg_right hj_le hπn_nn
        _ = (m : ℝ) * Real.pi / n := by ring
    linarith

/-- **Step 7a (m-choice + `hm_le` + `hcap_max` packager).**

    For `θ ∈ (0, π/2]`, `n ≥ 4`, the standard nearest-node closeness
    `|θ - φ_{k₀}| ≤ π/(2n)`, and any `m : ℕ` with `(m : ℝ) ≤ n·θ/(4π)`,
    both arithmetic preconditions of the trig sub-sum chain hold:

      • `hm_le`: `k₀.val + m + 1 ≤ n` (input to `trig_sum_subsum_log_lb`),
      • `hcap_max`: `φ_{k₀+m} ≤ π - θ/2` (input to
        `chebyshev_h_interior_of_close_and_max_index_cap`).

    The standard Step 7a caller-side choice `m := ⌊n·θ/(4π)⌋` satisfies the
    `(m : ℝ) ≤ n·θ/(4π)` hypothesis via `Nat.floor_le`. Combined with
    `chebyshev_h_interior_of_close_and_max_index_cap`, this closes every
    arithmetic precondition of `trig_sum_subsum_log_lb` for the asymptotic
    branch of `trig_sum_harmonic_lb`.

    **Key arithmetic** (with `θ ≤ π/2` and `n ≥ 4`):

      • From closeness: `(2k₀+1)·π/(2n) ≤ θ + π/(2n)`, hence
        `2 k₀ · π ≤ 2 n θ ≤ n π`, giving `2 k₀ ≤ n` (in ℕ).
      • From `(m : ℝ) ≤ n·θ/(4π) ≤ n/8`: `8 m ≤ n` (in ℕ).
      • Then `omega` closes `k₀.val + m + 1 ≤ n` from `2 k₀ ≤ n`,
        `8 m ≤ n`, `n ≥ 4` (since `8(k₀ + m + 1) ≤ 4n + n + 8 ≤ 8n`).
      • For the cap: `φ_{k₀+m} = φ_{k₀} + m·π/n ≤ (θ + π/(2n)) + θ/4`.
        With `θ ≤ π/2` and `n ≥ 4`: `≤ π/2 + π/8 + π/8 = 3π/4`, and
        `π - θ/2 ≥ π - π/4 = 3π/4`. -/
private lemma chebyshev_quarter_floor_hm_le_and_cap_max
    (n : ℕ) (hn : 4 ≤ n) (θ : ℝ) (hθ_pos : 0 < θ) (hθ_le : θ ≤ Real.pi / 2)
    (k₀ : Fin n)
    (hk₀_close : |θ - (2 * (k₀.val : ℝ) + 1) * Real.pi / (2 * n)| ≤ Real.pi / (2 * n))
    (m : ℕ) (hm_real_le : (m : ℝ) ≤ (n : ℝ) * θ / (4 * Real.pi)) :
    k₀.val + m + 1 ≤ n ∧
    (2 * ((k₀.val + m : ℕ) : ℝ) + 1) * Real.pi / (2 * n) ≤ Real.pi - θ / 2 := by
  have hpi_pos := Real.pi_pos
  have hπ_ne : Real.pi ≠ 0 := hpi_pos.ne'
  have hn_pos_nat : 0 < n := by omega
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos_nat
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
  have h2n_pos : (0 : ℝ) < 2 * (n : ℝ) := by linarith
  have h2n_ne : 2 * (n : ℝ) ≠ 0 := h2n_pos.ne'
  have h4_le_n : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- Step 1: m·π/n ≤ θ/4 (multiply hm_real_le by π/n > 0 and simplify)
  have hm_pi_n_le_θ4 : (m : ℝ) * Real.pi / n ≤ θ / 4 := by
    have hπn_nn : (0 : ℝ) ≤ Real.pi / n := (div_pos hpi_pos hn_pos).le
    have step :
        (m : ℝ) * (Real.pi / n) ≤ ((n : ℝ) * θ / (4 * Real.pi)) * (Real.pi / n) :=
      mul_le_mul_of_nonneg_right hm_real_le hπn_nn
    have hLHS : (m : ℝ) * (Real.pi / n) = (m : ℝ) * Real.pi / n := by ring
    have hRHS : ((n : ℝ) * θ / (4 * Real.pi)) * (Real.pi / n) = θ / 4 := by
      field_simp
    linarith
  have hθ4_le_π8 : θ / 4 ≤ Real.pi / 8 := by linarith
  have hm_pi_n_le_π8 : (m : ℝ) * Real.pi / n ≤ Real.pi / 8 :=
    le_trans hm_pi_n_le_θ4 hθ4_le_π8
  -- Step 2: φ_{k₀} ≤ θ + π/(2n) (from |θ - φ_{k₀}| ≤ π/(2n) via abs_le)
  have hφk₀_le : (2 * (k₀.val : ℝ) + 1) * Real.pi / (2 * n) ≤ θ + Real.pi / (2 * n) := by
    have := (abs_le.mp hk₀_close).1
    linarith
  -- Step 3: φ_{k₀+m} = φ_{k₀} + m·π/n (Nat-cast bridge + algebra)
  have hφ_k0m_decomp :
      (2 * ((k₀.val + m : ℕ) : ℝ) + 1) * Real.pi / (2 * n) =
        (2 * (k₀.val : ℝ) + 1) * Real.pi / (2 * n) + (m : ℝ) * Real.pi / n := by
    have hcast : ((k₀.val + m : ℕ) : ℝ) = (k₀.val : ℝ) + (m : ℝ) := by push_cast; ring
    rw [hcast]; field_simp; ring
  -- Step 4: π/(2n) ≤ π/8 (since n ≥ 4 ⟹ 2n ≥ 8)
  have hπ_2n_le_π_8 : Real.pi / (2 * n) ≤ Real.pi / 8 := by
    rw [div_le_div_iff₀ h2n_pos (by norm_num : (0 : ℝ) < 8)]
    have h_8_le_2n : (8 : ℝ) ≤ 2 * (n : ℝ) := by linarith
    nlinarith [hpi_pos]
  -- Step 5: hcap_max — assemble the cap bound.
  -- φ_{k₀+m} ≤ (θ + π/(2n)) + m·π/n ≤ (θ + π/8) + π/8 ≤ (π/2 + π/8) + π/8 = 3π/4 ≤ π - θ/2.
  have hcap_max :
      (2 * ((k₀.val + m : ℕ) : ℝ) + 1) * Real.pi / (2 * n) ≤ Real.pi - θ / 2 := by
    rw [hφ_k0m_decomp]
    have h_3π4_eq : Real.pi / 2 + Real.pi / 8 + Real.pi / 8 = 3 * Real.pi / 4 := by ring
    have h_target_ge_3π4 : 3 * Real.pi / 4 ≤ Real.pi - θ / 2 := by linarith
    linarith [hφk₀_le, hπ_2n_le_π_8, hθ_le, hm_pi_n_le_π8, h_3π4_eq, h_target_ge_3π4]
  refine ⟨?_, hcap_max⟩
  -- Step 6: hm_le — derive 2*k₀ ≤ n and 8*m ≤ n in ℕ, then `omega`.
  -- 2*k₀ ≤ n: clear (2n) from hφk₀_le, then bound by 2nθ ≤ nπ via θ ≤ π/2.
  have h2k0_real_le : 2 * (k₀.val : ℝ) ≤ (n : ℝ) := by
    have hφk₀_clear :
        (2 * (k₀.val : ℝ) + 1) * Real.pi ≤ 2 * (n : ℝ) * θ + Real.pi := by
      have step := mul_le_mul_of_nonneg_right hφk₀_le h2n_pos.le
      have hLHS :
          (2 * (k₀.val : ℝ) + 1) * Real.pi / (2 * n) * (2 * n) =
            (2 * (k₀.val : ℝ) + 1) * Real.pi := by
        field_simp
      have hRHS :
          (θ + Real.pi / (2 * n)) * (2 * n) = 2 * (n : ℝ) * θ + Real.pi := by
        field_simp
      linarith
    have h_2nθ_le_nπ : 2 * (n : ℝ) * θ ≤ (n : ℝ) * Real.pi := by
      nlinarith [hθ_le, hn_pos.le]
    have h_2k0π_le_nπ : 2 * (k₀.val : ℝ) * Real.pi ≤ (n : ℝ) * Real.pi := by linarith
    nlinarith [h_2k0π_le_nπ, hpi_pos]
  have h2k0_nat_le : 2 * k₀.val ≤ n := by exact_mod_cast h2k0_real_le
  -- 8*m ≤ n: from m·π/n ≤ π/8, clear denominators via 8n > 0.
  have h8m_real_le : 8 * (m : ℝ) ≤ (n : ℝ) := by
    have h8n_pos : (0 : ℝ) < 8 * (n : ℝ) := by linarith
    have step := mul_le_mul_of_nonneg_right hm_pi_n_le_π8 h8n_pos.le
    have hLHS :
        (m : ℝ) * Real.pi / n * (8 * (n : ℝ)) = 8 * (m : ℝ) * Real.pi := by
      field_simp
    have hRHS : Real.pi / 8 * (8 * (n : ℝ)) = (n : ℝ) * Real.pi := by
      field_simp
    have h_8mπ_le_nπ : 8 * (m : ℝ) * Real.pi ≤ (n : ℝ) * Real.pi := by linarith
    nlinarith [h_8mπ_le_nπ, hpi_pos]
  have h8m_nat_le : 8 * m ≤ n := by exact_mod_cast h8m_real_le
  -- Conclude k₀.val + m + 1 ≤ n: 8(k₀ + m + 1) ≤ 4n + n + 8 ≤ 8n iff n ≥ 8/3.
  omega

/-- **Reindex symmetry of the Chebyshev-Lebesgue trig sum: θ ↔ π - θ.**

    Under the involution `σ : Fin n ≃ Fin n`, `k ↦ n - 1 - k`:

      - The Chebyshev midpoint at the swapped index is the angle reflection:
        `φ_{σ k} = π - φ_k`, hence `sin(φ_{σ k}) = sin(φ_k)`.
      - The Chebyshev node at the swapped index is sign-flipped:
        `cos(φ_{σ k}) = -cos(φ_k)`, i.e. `chebyshevNode n (σ k) = -chebyshevNode n k`.
      - Combined with `cos(π - θ) = -cos θ`:
        `|cos(π - θ) - cos(φ_{σ k})| = |-cos θ - (-cos φ_k)| = |cos θ - cos φ_k|`.

    Therefore the Chebyshev-Lebesgue trig sum
    `S(θ, n) = Σₖ sin(φₖ)/|cos θ - cos φₖ|` is invariant under `θ ↦ π - θ`.

    This invariance reduces `trig_sum_harmonic_lb` to the case `θ ∈ (0, π/2]`:
    the going-down sub-sum (k = k₀ - j - 1) at θ ∈ (π/2, π) corresponds, via
    `σ`, to the going-up sub-sum at `π - θ ∈ (0, π/2)`. -/
private lemma trig_sum_reindex_symmetry (n : ℕ) (hn : 0 < n) (θ : ℝ) :
    ∑ k : Fin n, Real.sin ((2 * (k.val : ℝ) + 1) * Real.pi / (2 * n)) /
                 |Real.cos θ - chebyshevNode n k| =
    ∑ k : Fin n, Real.sin ((2 * (k.val : ℝ) + 1) * Real.pi / (2 * n)) /
                 |Real.cos (Real.pi - θ) - chebyshevNode n k| := by
  -- The involution σ : Fin n ≃ Fin n via k ↦ n - 1 - k
  let σ : Fin n ≃ Fin n :=
    { toFun := fun k => ⟨n - 1 - k.val, by have := k.isLt; omega⟩
      invFun := fun k => ⟨n - 1 - k.val, by have := k.isLt; omega⟩
      left_inv := fun k => by
        apply Fin.ext
        show n - 1 - (n - 1 - k.val) = k.val
        have := k.isLt; omega
      right_inv := fun k => by
        apply Fin.ext
        show n - 1 - (n - 1 - k.val) = k.val
        have := k.isLt; omega }
  -- Reindex the RHS via σ
  rw [show ∑ k : Fin n, Real.sin ((2 * (k.val : ℝ) + 1) * Real.pi / (2 * n)) /
        |Real.cos (Real.pi - θ) - chebyshevNode n k| =
      ∑ k : Fin n, Real.sin ((2 * ((σ k).val : ℝ) + 1) * Real.pi / (2 * n)) /
        |Real.cos (Real.pi - θ) - chebyshevNode n (σ k)| from
    (Equiv.sum_comp σ
      (fun k => Real.sin ((2 * ((k : Fin n).val : ℝ) + 1) * Real.pi / (2 * n)) /
                |Real.cos (Real.pi - θ) - chebyshevNode n k|)).symm]
  -- Termwise equality
  apply Finset.sum_congr rfl
  intro k _
  have hk_le : k.val ≤ n - 1 := by have := k.isLt; omega
  have hone_le : 1 ≤ n := hn
  -- σ k.val = n - 1 - k.val
  have hσ_val_nat : (σ k).val = n - 1 - k.val := rfl
  -- Cast value to ℝ
  have hσ_val : ((σ k).val : ℝ) = (n : ℝ) - 1 - (k.val : ℝ) := by
    rw [hσ_val_nat, Nat.cast_sub hk_le, Nat.cast_sub hone_le, Nat.cast_one]
  -- Angle identity: φ_{σ k} = π - φ_k
  have hangle_eq : (2 * ((σ k).val : ℝ) + 1) * Real.pi / (2 * (n : ℝ)) =
      Real.pi - (2 * (k.val : ℝ) + 1) * Real.pi / (2 * (n : ℝ)) := by
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
    rw [hσ_val]
    field_simp
    ring
  -- Sin invariance: sin(φ_{σ k}) = sin(φ_k)
  have hsin_eq : Real.sin ((2 * ((σ k).val : ℝ) + 1) * Real.pi / (2 * n)) =
      Real.sin ((2 * (k.val : ℝ) + 1) * Real.pi / (2 * n)) := by
    rw [hangle_eq, Real.sin_pi_sub]
  -- Node sign-flip: chebyshevNode n (σ k) = -chebyshevNode n k
  have hnode_eq : chebyshevNode n (σ k) = -chebyshevNode n k := by
    simp only [chebyshevNode]
    rw [hangle_eq, Real.cos_pi_sub]
  rw [hsin_eq, hnode_eq, Real.cos_pi_sub]
  -- Goal: sin(φ_k)/|cos θ - cn| = sin(φ_k)/|-cos θ - -cn|
  congr 1
  rw [show -Real.cos θ - -chebyshevNode n k =
        -(Real.cos θ - chebyshevNode n k) from by ring,
      abs_neg]

/-- **(Step 7 helper) `hne` reindex via `θ ↦ π − θ`.**

    For any `θ` whose cosine avoids all `n` Chebyshev nodes, the value
    `cos(π − θ) = −cos θ` also avoids all `n` Chebyshev nodes. This is the
    **`hne` side** of the half-π → general `θ ∈ (0, π)` WLOG bridge for
    `trig_sum_harmonic_lb`.

    Combined with `trig_sum_reindex_symmetry` (S18), which already gives
    `S(θ, n) = S(π − θ, n)`, this lets the general `θ ∈ (0, π)` asymptotic
    bound be obtained from a half-π asymptotic bound (Step 7a packaging,
    in flight as `trig_sum_harmonic_lb_asymp_le_half_pi`) by case-splitting
    on `θ ≤ π/2` vs `θ > π/2` and reindexing to `θ' := π − θ ∈ (0, π/2)`
    in the latter case.

    **Proof**: `cos(π − θ) = −cos θ` (`Real.cos_pi_sub`); the involution
    `σ : Fin n ≃ Fin n`, `k ↦ n − 1 − k` from S18 sends `chebyshevNode n k`
    to `−chebyshevNode n k` (via the angle identity
    `(2(n−1−k)+1)π/(2n) = π − (2k+1)π/(2n)`). So
    `cos(π − θ) = chebyshevNode n k`
    ⟺ `−cos θ = chebyshevNode n k`
    ⟺ `cos θ = −chebyshevNode n k = chebyshevNode n (σ k)`,
    contradicting `hne (σ k)`. -/
private lemma chebyshev_hne_pi_sub (n : ℕ) (hn : 0 < n) (θ : ℝ)
    (hne : ∀ k : Fin n, Real.cos θ ≠ chebyshevNode n k) :
    ∀ k : Fin n, Real.cos (Real.pi - θ) ≠ chebyshevNode n k := by
  intro k
  -- Reindex map (same `σ` as in `trig_sum_reindex_symmetry`).
  let σk : Fin n := ⟨n - 1 - k.val, by have := k.isLt; omega⟩
  have hk_le : k.val ≤ n - 1 := by have := k.isLt; omega
  have hone_le : 1 ≤ n := hn
  -- Cast `σk.val` from ℕ to ℝ as `n − 1 − k.val`.
  have hσ_val : (σk.val : ℝ) = (n : ℝ) - 1 - (k.val : ℝ) := by
    show ((n - 1 - k.val : ℕ) : ℝ) = _
    rw [Nat.cast_sub hk_le, Nat.cast_sub hone_le, Nat.cast_one]
  -- Angle identity in ℝ: `φ_{σ k} = π − φ_k` where `φ_j = (2j+1)π/(2n)`.
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
  have hangle_eq : (2 * (σk.val : ℝ) + 1) * Real.pi / (2 * (n : ℝ)) =
      Real.pi - (2 * (k.val : ℝ) + 1) * Real.pi / (2 * (n : ℝ)) := by
    rw [hσ_val]; field_simp; ring
  -- Sign-flip on the node: `chebyshevNode n (σ k) = − chebyshevNode n k`.
  have hnode_eq : chebyshevNode n σk = -chebyshevNode n k := by
    simp only [chebyshevNode]
    rw [hangle_eq, Real.cos_pi_sub]
  -- Goal: `cos(π − θ) ≠ chebyshevNode n k`. Rewrite LHS via `cos_pi_sub`.
  rw [Real.cos_pi_sub]
  intro h
  -- `h : -cos θ = chebyshevNode n k`. Hence
  -- `cos θ = -chebyshevNode n k = chebyshevNode n σk`, contradicting `hne σk`.
  apply hne σk
  rw [hnode_eq]; linarith

/-- **(Step 6/7 helper) Strict positivity of the Chebyshev-Lebesgue trig sum.**

    For any `θ` whose cosine avoids all `n` Chebyshev nodes, the trig sum
    `S(θ, n) = Σₖ sin(φₖ)/|cos θ − cos φₖ|` is strictly positive (every term
    has positive numerator by `chebyshevAngle_sin_pos`, positive denominator
    by `hne`).

    This is the building block for the **finite-set min'** argument in the
    `trig_sum_harmonic_lb` proof: for `1 ≤ n < N₀(d)`, the ratio
    `S(θ, n) / (n · log(n+1))` is well-defined and strictly positive, so its
    minimum over the finite set `{1, …, N₀−1}` exists and is positive,
    yielding the small-`n` constant in `trig_sum_harmonic_lb`. -/
private lemma chebyshev_trig_sum_pos (n : ℕ) (hn : 0 < n) (θ : ℝ)
    (hne : ∀ k : Fin n, Real.cos θ ≠ chebyshevNode n k) :
    0 < ∑ k : Fin n, Real.sin ((2 * (k.val : ℝ) + 1) * Real.pi / (2 * n)) /
                     |Real.cos θ - chebyshevNode n k| := by
  -- Each term is strictly positive: sin > 0 by chebyshevAngle_sin_pos, denominator
  -- > 0 by hne k. Apply Finset.sum_pos with the nonempty witness k = 0.
  apply Finset.sum_pos
  · intro k _
    exact div_pos (chebyshevAngle_sin_pos n hn k)
      (abs_pos.mpr (sub_ne_zero.mpr (hne k)))
  · exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩

/- **[SORRY-DESIGN-NOTE — orphan docstring, not attached to a declaration]
   Harmonic trig sum lower bound for general θ ∈ (0, π).

    For any θ ∈ (0, π) with cos θ not a Chebyshev node for any n, the sum
    S_n = Σₖ sin(φₖ)/|cos θ - cos φₖ| grows at least as fast as n · log(n+1).

    Proof sketch: Let d = min(θ, π-θ) > 0.
    1. By Lipschitz (|cos α - cos β| ≤ |α - β|): each term ≥ sin(φₖ)/|θ - φₖ|.
    2. Nearest node k₀ satisfies |θ - φ_{k₀}| ≤ π/(2n).
    3. For the j-th nearest node beyond k₀ (j = 0,...,m-1 with m = ⌊nd/(4π)⌋):
       - |θ - φ_{k₀+j+1}| ≤ (2j+3)π/(2n)
       - sin(φ_{k₀+j+1}) ≥ sin(d/2) ≥ d/π  (since node is in (d/2, π-d/2))
       - Term ≥ (d/π) · 2n/((2j+3)π) = 2dn/(π²(2j+3))
    4. Sub-sum ≥ (2dn/π²) · Σ_{j=0}^{m-1} 1/(2j+3) ≥ (2dn/π²) · ((1/2)·log(m+2) - 1)
    5. For n ≥ N₀(d), this gives ≥ C · n · log(n+1) where C depends on d.
    6. For 1 ≤ n < N₀, each S_n > 0 and n·log(n+1) > 0, so min ratio over
       the finite set {1,...,N₀-1} is positive (Finset.min' argument).
    7. Take C₂ = min of the large-n constant and the finite-set minimum.

    NOTE: `trig_sum_reindex_symmetry` lets the proof WLOG assume θ ∈ (0, π/2]. -/

/-- **(Step 7 helper) Small-n lower bound via finite-set minimum.**

    For any `θ` whose cosine avoids all Chebyshev nodes for every `n ≥ 1`, and
    any cutoff `N ≥ 1`, there is a positive constant `C` (depending on `θ` and
    `N`) such that for every `1 ≤ n ≤ N`,
    `C · n · log(n+1) ≤ S(θ, n)`.

    This is the **finite-set side** of `trig_sum_harmonic_lb`'s Step 7
    (combined with an asymptotic large-`n` bound from `trig_sum_subsum_log_lb`,
    the unified `n · log(n+1)` lower bound follows by taking the minimum of
    the two constants).

    Proof: The ratio `r(n) := S(θ, n) / (n · log(n+1))` is strictly positive
    for every `1 ≤ n ≤ N` because
    - the numerator `S(θ, n)` is positive by `chebyshev_trig_sum_pos`, and
    - the denominator is positive since `n ≥ 1` ⇒ `log(n+1) ≥ log 2 > 0`.
    Take `C := Finset.min'` over the finite image `(Finset.Icc 1 N).image r`
    and use `Finset.min'_le` to invert the division. -/
private lemma trig_sum_small_n_const (θ : ℝ)
    (hne : ∀ (n : ℕ) (_ : 0 < n) (k : Fin n), Real.cos θ ≠ chebyshevNode n k)
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → n ≤ N →
      C * ((↑n : ℝ) * Real.log ((↑n : ℝ) + 1)) ≤
        ∑ k : Fin n, Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) /
                     |Real.cos θ - chebyshevNode n k| := by
  -- Define r(n) = S(θ, n) / (n · log(n+1)); take the min over s = {1, …, N}.
  let r : ℕ → ℝ := fun n =>
    (∑ k : Fin n, Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) /
                  |Real.cos θ - chebyshevNode n k|) /
    ((↑n : ℝ) * Real.log ((↑n : ℝ) + 1))
  let s : Finset ℕ := Finset.Icc 1 N
  have hs_ne : s.Nonempty :=
    ⟨1, by simp only [s, Finset.mem_Icc]; exact ⟨le_refl 1, hN⟩⟩
  have him_ne : (s.image r).Nonempty := hs_ne.image r
  -- Each r(n) for n ∈ s is positive: numerator > 0 (chebyshev_trig_sum_pos),
  -- denominator > 0 (n ≥ 1 ⇒ log(n+1) ≥ log 2 > 0).
  have hr_pos : ∀ n ∈ s, 0 < r n := by
    intro n hn_in
    rw [Finset.mem_Icc] at hn_in
    obtain ⟨hn_pos, _⟩ := hn_in
    show 0 < (∑ k : Fin n, Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) /
                  |Real.cos θ - chebyshevNode n k|) /
              ((↑n : ℝ) * Real.log ((↑n : ℝ) + 1))
    apply div_pos
    · -- Numerator positivity via chebyshev_trig_sum_pos. The pointwise
      -- summand `(2 * k.val + 1 : ℝ)` (Nat-cast) and `(2 * (k.val : ℝ) + 1)`
      -- (mixed) are equal after `push_cast`/`ring`, so a `congr 2`-style
      -- bridge transports the existing positivity to the Nat-cast form.
      have hpos := chebyshev_trig_sum_pos n hn_pos θ (hne n hn_pos)
      have hcast :
          (∑ k : Fin n,
              Real.sin ((2 * (k.val : ℝ) + 1) * Real.pi / (2 * n)) /
                |Real.cos θ - chebyshevNode n k|) =
          (∑ k : Fin n,
              Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) /
                |Real.cos θ - chebyshevNode n k|) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        congr 2
      linarith
    · -- Denominator positivity: n ≥ 1 and log(n+1) ≥ log 2 > 0.
      apply mul_pos
      · exact_mod_cast hn_pos
      · apply Real.log_pos
        have hn_real : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
        linarith
  refine ⟨(s.image r).min' him_ne, ?_, ?_⟩
  · -- min' > 0: every element of the image is positive.
    rw [Finset.lt_min'_iff]
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨n, hn_in, rfl⟩ := hx
    exact hr_pos n hn_in
  · intro n hn₁ hnN
    have hn_in : n ∈ s := by rw [Finset.mem_Icc]; exact ⟨hn₁, hnN⟩
    have hr_in : r n ∈ s.image r := Finset.mem_image_of_mem r hn_in
    have hC_le : (s.image r).min' him_ne ≤ r n :=
      Finset.min'_le _ _ hr_in
    have hd_pos : 0 < (↑n : ℝ) * Real.log ((↑n : ℝ) + 1) := by
      apply mul_pos
      · exact_mod_cast hn₁
      · apply Real.log_pos
        have hn_real : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn₁
        linarith
    -- Unfold r n and invert the division: C ≤ S/D ⟺ C·D ≤ S (D > 0).
    have hr_unfold : r n =
        (∑ k : Fin n, Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) /
                      |Real.cos θ - chebyshevNode n k|) /
        ((↑n : ℝ) * Real.log ((↑n : ℝ) + 1)) := rfl
    rw [hr_unfold] at hC_le
    rwa [le_div_iff₀ hd_pos] at hC_le

/-- **(Step 7a residue) Asymptotic log lower bound for the quarter-floor input.**

    For any `θ > 0`, there exists `N₀ : ℕ` such that for every `n ≥ N₀` and
    every `m : ℕ` satisfying `(m : ℝ) ≥ n·θ/(4π) − 1`:

      `(1/4) · log((n : ℝ) + 1) ≤ (1/2) · log((m : ℝ) + 2) − 1`.

    The standard Step 7a caller-side choice `m := ⌊n·θ/(4π)⌋ : ℕ` satisfies
    the hypothesis via `Nat.lt_floor_add_one` (since
    `((⌊x⌋₊ : ℕ) : ℝ) > x − 1` for nonneg `x`). Combined with
    `trig_sum_subsum_log_lb` (whose RHS factor is exactly
    `(1/2) · log((m : ℝ) + 2) − 1`), this yields an asymptotic
    `(sin(θ/2) / (2π)) · n · log(n+1)` lower bound for the trig sum,
    which is then ready for `trig_sum_combine_small_large_const`.

    **Witness**: `N₀ = ⌈16π² · e⁴ / θ²⌉ + 2` (provided by `exists_nat_gt`),
    `c = 1/4`. The proof reduces

      `(1/2) · log(m+2) − 1 ≥ (1/4) · log(n+1)`
        ⟺  `2 · log(m+2) − 4 ≥ log(n+1)`
        ⟺  `log((m+2)²) ≥ log((n+1) · e⁴)`
        ⟺  `(m+2)² ≥ (n+1) · e⁴`.

    From `m + 2 ≥ n · θ/(4π)`, we have `(m+2)² ≥ n² · θ² / (16π²)`. The
    remaining `n² · θ² / (16π²) ≥ (n+1) · e⁴` simplifies to `n² ≥ K·(n+1)`
    where `K := 16π² · e⁴ / θ²`, which holds whenever `n ≥ K + 1`:
    `n² = n·n ≥ (K+1)·n ≥ K·n + n ≥ K·n + K = K·(n+1)`. -/
private lemma chebyshev_quarter_floor_log_asymp_lb
    (θ : ℝ) (hθ_pos : 0 < θ) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ m : ℕ,
      (n : ℝ) * θ / (4 * Real.pi) - 1 ≤ (m : ℝ) →
      (1 : ℝ) / 4 * Real.log ((n : ℝ) + 1) ≤
        (1 : ℝ) / 2 * Real.log ((m : ℝ) + 2) - 1 := by
  have hπ_pos := Real.pi_pos
  have hπ_sq_pos : (0 : ℝ) < Real.pi ^ 2 := pow_pos hπ_pos 2
  have hθ_sq_pos : (0 : ℝ) < θ ^ 2 := pow_pos hθ_pos 2
  have hexp4_pos : (0 : ℝ) < Real.exp 4 := Real.exp_pos 4
  -- K := 16π²·e⁴/θ² > 0
  set K : ℝ := (16 : ℝ) * Real.pi ^ 2 * Real.exp 4 / θ ^ 2 with hK_def
  have hK_pos : 0 < K := by
    rw [hK_def]; positivity
  -- Pick `N₀` strictly greater than `K + 1` (Archimedean).
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (K + 1)
  refine ⟨N₀, ?_⟩
  intro n hn m hm
  -- From `N₀ ≤ n`: `K + 1 < (n : ℝ)`, hence `K ≤ n − 1`, `n ≥ 1`.
  have hN₀_real : (N₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h_n_gt_K1 : K + 1 < (n : ℝ) := lt_of_lt_of_le hN₀ hN₀_real
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have h_n_ge_K : K ≤ (n : ℝ) := by linarith
  -- `m + 2 > 0` and `(m + 2) ≥ n·θ/(4π)` (the latter from `hm + 2 ≥ 1`).
  have hm_real_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hm_2_pos : (0 : ℝ) < (m : ℝ) + 2 := by linarith
  have h_4π_pos : (0 : ℝ) < 4 * Real.pi := by linarith
  have hnθ_4π_pos : (0 : ℝ) < (n : ℝ) * θ / (4 * Real.pi) :=
    div_pos (mul_pos hn_pos hθ_pos) h_4π_pos
  have hm_2_lb : (n : ℝ) * θ / (4 * Real.pi) ≤ (m : ℝ) + 2 := by linarith
  -- `(m + 2)² ≥ (n·θ/(4π))² = n²·θ²/(16π²)`.
  have hsq_lb : ((n : ℝ) * θ / (4 * Real.pi)) ^ 2 ≤ ((m : ℝ) + 2) ^ 2 := by
    have h_self := mul_self_le_mul_self hnθ_4π_pos.le hm_2_lb
    have heq1 : ((n : ℝ) * θ / (4 * Real.pi)) ^ 2 =
                ((n : ℝ) * θ / (4 * Real.pi)) * ((n : ℝ) * θ / (4 * Real.pi)) := by ring
    have heq2 : ((m : ℝ) + 2) ^ 2 = ((m : ℝ) + 2) * ((m : ℝ) + 2) := by ring
    linarith [h_self, heq1, heq2]
  have hsq_simp : ((n : ℝ) * θ / (4 * Real.pi)) ^ 2 =
      (n : ℝ) ^ 2 * θ ^ 2 / (16 * Real.pi ^ 2) := by
    field_simp
    ring
  rw [hsq_simp] at hsq_lb
  -- `n² ≥ K · (n + 1)`: from `n ≥ K + 1`, `n·n ≥ (K+1)·n = K·n + n ≥ K·n + K`.
  have h_n_sq_ge : K * ((n : ℝ) + 1) ≤ (n : ℝ) ^ 2 := by
    have h1 : K + 1 ≤ (n : ℝ) := by linarith
    have h_pow : (n : ℝ) ^ 2 = (n : ℝ) * (n : ℝ) := by ring
    rw [h_pow]
    nlinarith [h1, hn_pos, h_n_ge_K]
  -- Multiply by the positive factor `θ²/(16π²)` and simplify.
  have h_factor_nn : (0 : ℝ) ≤ θ ^ 2 / (16 * Real.pi ^ 2) := by positivity
  have h_main_step :
      K * ((n : ℝ) + 1) * (θ ^ 2 / (16 * Real.pi ^ 2)) ≤
        (n : ℝ) ^ 2 * (θ ^ 2 / (16 * Real.pi ^ 2)) :=
    mul_le_mul_of_nonneg_right h_n_sq_ge h_factor_nn
  -- `K · (θ²/(16π²)) = e⁴` (definition of `K`).
  have hK_simp : K * ((n : ℝ) + 1) * (θ ^ 2 / (16 * Real.pi ^ 2)) =
      ((n : ℝ) + 1) * Real.exp 4 := by
    rw [hK_def]
    field_simp
  have h_rhs_simp : (n : ℝ) ^ 2 * (θ ^ 2 / (16 * Real.pi ^ 2)) =
      (n : ℝ) ^ 2 * θ ^ 2 / (16 * Real.pi ^ 2) := by
    ring
  rw [hK_simp, h_rhs_simp] at h_main_step
  -- Combine: `(n + 1)·e⁴ ≤ n²·θ²/(16π²) ≤ (m + 2)²`.
  have h_combine : ((n : ℝ) + 1) * Real.exp 4 ≤ ((m : ℝ) + 2) ^ 2 :=
    le_trans h_main_step hsq_lb
  -- Take `Real.log` of both sides; both are positive.
  have hLHS_pos : (0 : ℝ) < ((n : ℝ) + 1) * Real.exp 4 := mul_pos hn1_pos hexp4_pos
  have h_log_ineq : Real.log (((n : ℝ) + 1) * Real.exp 4) ≤ Real.log (((m : ℝ) + 2) ^ 2) :=
    Real.log_le_log hLHS_pos h_combine
  rw [Real.log_mul hn1_pos.ne' hexp4_pos.ne', Real.log_exp,
      Real.log_pow] at h_log_ineq
  -- `h_log_ineq : log (n + 1) + 4 ≤ ↑(2 : ℕ) * log (m + 2)`
  -- After Nat-cast normalization, becomes `log (n + 1) + 4 ≤ 2 * log (m + 2)`.
  push_cast at h_log_ineq
  linarith

/-- **(Step 7a/asymptotic side) Large-`n` harmonic lower bound for `θ ∈ (0, π/2]`.**

    Composes the Step 7 helpers into a clean asymptotic bound: for any
    `θ ∈ (0, π/2]` whose cosine avoids all Chebyshev nodes,

      `∃ N₀, ∀ n ≥ N₀,  C₁ · n · log(n+1) ≤ S(θ, n)`

    with `C₁ = sin(θ/2) / (2π)`. This is the **`hlarge` hypothesis** consumed
    by `trig_sum_combine_small_large_const` (Step 7c, in flight as PR #17457):
    feeding this lemma to that helper yields the unified
    `C · n · log(n+1) ≤ S(θ, n)` for all `n ≥ 1`, closing the asymptotic side
    of `trig_sum_harmonic_lb`'s θ ∈ (0, π/2] branch. The general
    `θ ∈ (0, π)` branch reduces to this case via `trig_sum_reindex_symmetry`
    (S18, merged): `S(θ, n) = S(π - θ, n)`, and `π - θ ∈ (0, π/2)` when
    `θ ∈ [π/2, π)`.

    **Proof sketch** (composing already-merged helpers):

    1. `exists_nearest_chebyshev_angle` → `k₀ : Fin n` with
       `|θ - φ_{k₀}| ≤ π/(2n)`.
    2. `m := ⌊n·θ/(4π)⌋` satisfies `(m : ℝ) ≤ n·θ/(4π)` (`Nat.floor_le`)
       and `n·θ/(4π) - 1 ≤ (m : ℝ)` (`Nat.lt_floor_add_one`).
    3. `chebyshev_quarter_floor_hm_le_and_cap_max` (S23) → both `hm_le`
       and `hcap_max` simultaneously.
    4. `chebyshev_h_interior_of_close_and_max_index_cap` (S22) → `h_interior`
       (with `d := θ`) from `hk₀_close` + `hcap_max`.
    5. `trig_sum_subsum_log_lb` (S21) →
       `sin(θ/2) · (2n/π) · ((1/2)·log(m+2) − 1) ≤ S(θ, n)` (mixed-cast form).
    6. `chebyshev_quarter_floor_log_asymp_lb` (S24) →
       `(1/4)·log(n+1) ≤ (1/2)·log(m+2) − 1` for `n ≥ N₀_log`.
    7. Multiply by the nonnegative factor `sin(θ/2) · (2n/π)`:
       `sin(θ/2) · (2n/π) · (1/4)·log(n+1) ≤ S(θ, n)`.
    8. Algebra: LHS `= (sin(θ/2)/(2π)) · n · log(n+1)`. Take
       `C₁ := sin(θ/2)/(2π)` and `N₀ := max N₀_log 4` (the `4` for S23's
       `n ≥ 4` hypothesis).
    9. Cast bridge from mixed `(2 * (k.val : ℝ) + 1)` to outer
       `(2 * k.val + 1 : ℝ)` form via `Finset.sum_congr` + `push_cast` + `ring`
       (matches `trig_sum_small_n_const` (S22) and `trig_sum_harmonic_lb`
       targets exactly).

    Positivity: `sin(θ/2) > 0` since `θ/2 ∈ (0, π/4] ⊂ (0, π)`; `2π > 0`. -/
private lemma trig_sum_harmonic_lb_asymp_le_half_pi
    (θ : ℝ) (hθ_pos : 0 < θ) (hθ_le : θ ≤ Real.pi / 2)
    (hne : ∀ (n : ℕ) (_ : 0 < n) (k : Fin n), Real.cos θ ≠ chebyshevNode n k) :
    ∃ (N₀ : ℕ) (C₁ : ℝ), 0 < C₁ ∧ ∀ n : ℕ, N₀ ≤ n →
      C₁ * ((↑n : ℝ) * Real.log ((↑n : ℝ) + 1)) ≤
        ∑ k : Fin n, Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) /
                     |Real.cos θ - chebyshevNode n k| := by
  have hπ_pos := Real.pi_pos
  have hθ_lt_pi : θ < Real.pi := by linarith
  have hθ_le_pi : θ ≤ Real.pi := by linarith
  -- Positivity of `sin(θ/2)` since `θ/2 ∈ (0, π/4] ⊂ (0, π)`.
  have hsin_pos : 0 < Real.sin (θ / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith
    · linarith
  -- `C₁ := sin(θ/2) / (2π) > 0`.
  set C₁ : ℝ := Real.sin (θ / 2) / (2 * Real.pi) with hC₁_def
  have hC₁_pos : 0 < C₁ := by
    rw [hC₁_def]; exact div_pos hsin_pos (by linarith)
  -- Get `N₀_log` from S24.
  obtain ⟨N₀_log, hN₀_log⟩ := chebyshev_quarter_floor_log_asymp_lb θ hθ_pos
  -- `N₀ := max N₀_log 4` (the `4` for S23's `n ≥ 4` hypothesis).
  refine ⟨max N₀_log 4, C₁, hC₁_pos, ?_⟩
  intro n hn
  have hn_log : N₀_log ≤ n := le_of_max_le_left hn
  have hn_4 : 4 ≤ n := le_of_max_le_right hn
  have hn_pos : 0 < n := by omega
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  -- Step 1: nearest-node closeness.
  obtain ⟨k₀, hk₀_close⟩ := exists_nearest_chebyshev_angle n hn_pos hθ_pos hθ_lt_pi
  -- Step 2: `m := ⌊n·θ/(4π)⌋ : ℕ`. `Nat.floor_le` and `Nat.lt_floor_add_one`
  -- bracket `m` between `n·θ/(4π) − 1` (S24's hypothesis) and `n·θ/(4π)`
  -- (S23's hypothesis).
  have h4π_pos : (0 : ℝ) < 4 * Real.pi := by linarith
  have hy_pos : (0 : ℝ) < (n : ℝ) * θ / (4 * Real.pi) :=
    div_pos (mul_pos hn_real_pos hθ_pos) h4π_pos
  set m : ℕ := ⌊(n : ℝ) * θ / (4 * Real.pi)⌋₊ with hm_def
  have hm_real_le : (m : ℝ) ≤ (n : ℝ) * θ / (4 * Real.pi) := Nat.floor_le hy_pos.le
  have hm_lt_succ : (n : ℝ) * θ / (4 * Real.pi) < (m : ℝ) + 1 :=
    Nat.lt_floor_add_one ((n : ℝ) * θ / (4 * Real.pi))
  have hm_real_ge : (n : ℝ) * θ / (4 * Real.pi) - 1 ≤ (m : ℝ) := by linarith
  -- Step 3: apply S23 to obtain `hm_le` and `hcap_max` simultaneously.
  obtain ⟨hm_le, hcap_max⟩ :=
    chebyshev_quarter_floor_hm_le_and_cap_max n hn_4 θ hθ_pos hθ_le k₀ hk₀_close m
      hm_real_le
  -- Step 4: apply S22 to obtain `h_interior` (with `d := θ`).
  have h_interior :=
    chebyshev_h_interior_of_close_and_max_index_cap n hn_pos θ hθ_pos k₀ hk₀_close m
      hcap_max
  -- Step 5: apply S21 to obtain the log lower bound (mixed-cast sum form).
  have hbound_mixedcast :
      Real.sin (θ / 2) * (2 * (n : ℝ)) / Real.pi *
        ((1 : ℝ) / 2 * Real.log ((↑m : ℝ) + 2) - 1) ≤
      ∑ k : Fin n, Real.sin ((2 * (k.val : ℝ) + 1) * Real.pi / (2 * n)) /
                   |Real.cos θ - chebyshevNode n k| :=
    trig_sum_subsum_log_lb n hn_pos θ θ hθ_pos hθ_le_pi (hne n hn_pos) k₀ hk₀_close m
      hm_le h_interior
  -- Step 6: apply S24 to convert `(1/2)·log(m+2) − 1 ≥ (1/4)·log(n+1)`.
  have hlog_le : (1 : ℝ) / 4 * Real.log ((n : ℝ) + 1) ≤
                 (1 : ℝ) / 2 * Real.log ((↑m : ℝ) + 2) - 1 :=
    hN₀_log n hn_log m hm_real_ge
  -- Step 7: multiply by the nonneg factor `sin(θ/2)·(2n/π) ≥ 0`.
  have hpref_nn : 0 ≤ Real.sin (θ / 2) * (2 * (n : ℝ)) / Real.pi := by
    apply div_nonneg
    · exact mul_nonneg hsin_pos.le (by linarith)
    · linarith
  -- Step 8: algebraic identity `C₁ · n · log(n+1) = sin(θ/2)·(2n/π)·(1/4)·log(n+1)`.
  have hC₁_eq :
      C₁ * ((n : ℝ) * Real.log ((n : ℝ) + 1)) =
      Real.sin (θ / 2) * (2 * (n : ℝ)) / Real.pi *
        ((1 : ℝ) / 4 * Real.log ((n : ℝ) + 1)) := by
    rw [hC₁_def]
    field_simp
    ring
  -- Step 9: final calc chain. The mixed-cast form `(2 * (k.val : ℝ) + 1)`
  -- and outer-cast form `(2 * k.val + 1 : ℝ)` are definitionally equal,
  -- so no bridge is needed (Lean unifies via rfl on the calc terminus).
  calc C₁ * ((n : ℝ) * Real.log ((n : ℝ) + 1))
      = Real.sin (θ / 2) * (2 * (n : ℝ)) / Real.pi *
          ((1 : ℝ) / 4 * Real.log ((n : ℝ) + 1)) := hC₁_eq
    _ ≤ Real.sin (θ / 2) * (2 * (n : ℝ)) / Real.pi *
          ((1 : ℝ) / 2 * Real.log ((↑m : ℝ) + 2) - 1) :=
        mul_le_mul_of_nonneg_left hlog_le hpref_nn
    _ ≤ ∑ k : Fin n, Real.sin ((2 * (k.val : ℝ) + 1) * Real.pi / (2 * n)) /
                     |Real.cos θ - chebyshevNode n k| := hbound_mixedcast

/-- **(Step 7a, general θ) Asymptotic large-`n` lower bound for the trig sum.**

    Extends `trig_sum_harmonic_lb_asymp_le_half_pi` (S26) from
    `θ ∈ (0, π/2]` to the full open interval `θ ∈ (0, π)` via the WLOG
    bridge S18 (`trig_sum_reindex_symmetry`) + S27 (`chebyshev_hne_pi_sub`).

    For any `θ ∈ (0, π)` whose cosine avoids all Chebyshev nodes
    (for every `n ≥ 1`), there exist `N₀ : ℕ` and `C₁ > 0` such that
    `C₁ · n · log(n+1) ≤ S(θ, n)` for all `n ≥ N₀`.

    **Proof**: split on `θ ≤ π/2`.
      • If `θ ≤ π/2`, apply S26 directly.
      • If `θ > π/2`, set `θ' := π − θ ∈ (0, π/2)`. Use S27 to obtain
        `hne'` for `θ'`, apply S26 to `(θ', hne')` to get
        `C₁ · n · log(n+1) ≤ S(π − θ, n)`, then rewrite via S18
        (`S(θ, n) = S(π − θ, n)`) to conclude.

    **Why packaged independently of S25**: S25's combine helper
    (`trig_sum_combine_small_large_const`, in flight as PR #17457) consumes
    a `hlarge` hypothesis of exactly this shape but parameterised over the
    same `θ` it concludes for. By extending S26's reach to all `θ ∈ (0, π)`,
    this helper closes the angle-domain gap so the final `trig_sum_harmonic_lb`
    can apply S25 directly without an additional in-line WLOG case split. -/
private lemma trig_sum_harmonic_lb_asymp
    (θ : ℝ) (hθ_pos : 0 < θ) (hθ_lt : θ < Real.pi)
    (hne : ∀ (n : ℕ) (_ : 0 < n) (k : Fin n), Real.cos θ ≠ chebyshevNode n k) :
    ∃ (N₀ : ℕ) (C₁ : ℝ), 0 < C₁ ∧ ∀ n : ℕ, N₀ ≤ n →
      C₁ * ((↑n : ℝ) * Real.log ((↑n : ℝ) + 1)) ≤
        ∑ k : Fin n, Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) /
                     |Real.cos θ - chebyshevNode n k| := by
  by_cases hcase : θ ≤ Real.pi / 2
  · -- Branch 1: `θ ≤ π/2`. Direct application of S26.
    exact trig_sum_harmonic_lb_asymp_le_half_pi θ hθ_pos hcase hne
  · -- Branch 2: `θ > π/2`. WLOG bridge via `θ' := π − θ ∈ (0, π/2)`.
    push_neg at hcase
    -- Build the hypotheses for S26 at `θ' := π − θ`.
    have hθ'_pos : 0 < Real.pi - θ := by linarith
    have hθ'_le : Real.pi - θ ≤ Real.pi / 2 := by linarith
    -- S27 supplies the `hne` side of the bridge for each `n`.
    have hne' : ∀ (n : ℕ) (_ : 0 < n) (k : Fin n),
        Real.cos (Real.pi - θ) ≠ chebyshevNode n k := by
      intro n hn k
      exact chebyshev_hne_pi_sub n hn θ (hne n hn) k
    -- Apply S26 to `(π − θ)` to get `(N₀, C₁, hbound')` for the reindexed sum.
    obtain ⟨N₀, C₁, hC₁_pos, hbound'⟩ :=
      trig_sum_harmonic_lb_asymp_le_half_pi (Real.pi - θ) hθ'_pos hθ'_le hne'
    -- Bump `N₀` to `max N₀ 1` so we can apply `trig_sum_reindex_symmetry`
    -- (which requires `0 < n`). This costs nothing: at `n = 0` the sum is
    -- empty and the bound is trivially `0 ≤ 0`, so adding a 1-floor only
    -- prunes the trivial entry.
    refine ⟨max N₀ 1, C₁, hC₁_pos, ?_⟩
    intro n hn_max
    have hN₀_le : N₀ ≤ n := le_of_max_le_left hn_max
    have hn_pos : 0 < n := by
      have h1_le : 1 ≤ n := le_of_max_le_right hn_max
      omega
    -- S18: `S(θ, n) = S(π − θ, n)`. Rewrite the goal LHS sum.
    have hsym := trig_sum_reindex_symmetry n hn_pos θ
    rw [hsym]
    exact hbound' n hN₀_le

private lemma trig_sum_harmonic_lb (θ : ℝ) (hθ_pos : 0 < θ) (hθ_lt : θ < Real.pi)
    (hne : ∀ (n : ℕ) (_ : 0 < n) (k : Fin n), Real.cos θ ≠ chebyshevNode n k) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      C * ((↑n : ℝ) * Real.log ((↑n : ℝ) + 1)) ≤
        ∑ k : Fin n, Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) /
                     |Real.cos θ - chebyshevNode n k| := by
  -- **Closure (S29)**. The proof composes the asymptotic large-`n` packaging
  -- `trig_sum_harmonic_lb_asymp` (S28, general θ ∈ (0, π)) with the
  -- finite-set min' lower bound `trig_sum_small_n_const` (S22) via a
  -- min-of-two-constants split.
  --
  -- Step 1: S28 yields `(N₀, C₁ > 0, hlarge)` with
  --   `∀ n ≥ N₀, C₁ · n · log(n+1) ≤ S(θ, n)`.
  -- Step 2: S22 with cutoff `N := max N₀ 1` (`≥ 1`) yields `(C₂ > 0, hsmall)`
  --   covering `1 ≤ n ≤ N`.
  -- Step 3: take `C := min C₁ C₂ > 0`. Case on `n ≤ N`:
  --   - small branch: `min ≤ C₂` and `hsmall` gives the bound;
  --   - large branch (`n > N ≥ N₀`): `min ≤ C₁` and `hlarge` gives the bound.
  obtain ⟨N₀, C₁, hC₁_pos, hlarge⟩ :=
    trig_sum_harmonic_lb_asymp θ hθ_pos hθ_lt hne
  set N : ℕ := max N₀ 1 with hN_def
  have hN_ge : 1 ≤ N := le_max_right N₀ 1
  obtain ⟨C₂, hC₂_pos, hsmall⟩ := trig_sum_small_n_const θ hne N hN_ge
  refine ⟨min C₁ C₂, lt_min hC₁_pos hC₂_pos, fun n hn₁ => ?_⟩
  -- Denominator nonneg: `n ≥ 1 ⇒ n · log(n+1) ≥ 0` (in fact > 0; ≥ 0 suffices).
  have hg_nn : 0 ≤ (↑n : ℝ) * Real.log ((↑n : ℝ) + 1) := by
    apply mul_nonneg (by exact_mod_cast Nat.zero_le n)
    apply Real.log_nonneg
    have hn_real : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn₁
    linarith
  by_cases hcase : n ≤ N
  · -- Small-n branch: `1 ≤ n ≤ N` ⇒ apply `hsmall`; `min ≤ C₂` by `min_le_right`.
    calc min C₁ C₂ * ((↑n : ℝ) * Real.log ((↑n : ℝ) + 1))
        ≤ C₂ * ((↑n : ℝ) * Real.log ((↑n : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hg_nn
      _ ≤ _ := hsmall n hn₁ hcase
  · -- Large-n branch: `n > N ≥ N₀` ⇒ apply `hlarge`; `min ≤ C₁` by `min_le_left`.
    push_neg at hcase
    have hN₀_le_n : N₀ ≤ n := by
      have hN₀_le_N : N₀ ≤ N := le_max_left N₀ 1
      omega
    calc min C₁ C₂ * ((↑n : ℝ) * Real.log ((↑n : ℝ) + 1))
        ≤ C₁ * ((↑n : ℝ) * Real.log ((↑n : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hg_nn
      _ ≤ _ := hlarge n hN₀_le_n

/-! ## Key Lemmas with Sorry -/

/-- **[SORRY] Harmonic sum lower bound for Chebyshev trig sum.**

    For x = cos(πp/q) with p, q odd, the trigonometric Lebesgue sum
    S_n = Σₖ sin(φₖ)/|x - cos φₖ| grows at least as fast as n · log(n+1).

    **Proof strategy (2 cases)**:

    **Case 1: x = -1** (when p/q is an odd integer, e.g., p = q = 1):
    - Using sum_term_eq_tan_half_angle: S_n = Σₖ tan(φₖ/2) where φₖ = (2k+1)π/(2n)
    - For k = n-1-j (j = 0,...,⌊n/4⌋-1): φₖ/2 = π/2 - (2j+1)π/(4n)
    - tan(φₖ/2) = cot((2j+1)π/(4n)) ≥ 2n/(π(2j+1)) by cot_ge_inv_two_mul
    - Sub-sum: Σⱼ₌₀^{⌊n/4⌋-1} 2n/(π(2j+1)) ≥ (n/π)·log(⌊n/4⌋+1) ≥ C·n·log(n+1)
    - Apply: trig_sum_lb_of_cos_eq_neg_one

    **Case 2: x ∈ (-1, 1)** (when sin(πp/q) ≠ 0):
    - Let s = |sin(πp/q)| > 0 (since x ≠ ±1 means p/q ∉ ℤ)
    - For nodes k at distance j·π/n from nearest node k₀:
        sin(φₖ)/|x - cos φₖ| ≥ (s/2) / (j·π/n) = s·n/(2π·j)  by Lipschitz + sin bound
    - Summing j = 1..⌊n·s/(2π)⌋: S_n ≥ (s·n/(2π))·Hₘ ≥ (s·n/(2π))·log(⌊n·s/(2π)⌋+1)
    - Take C₂ = s²/(4π²) -/
private lemma chebyshev_trig_sum_lb (p q : ℕ) (hp : Odd p) (hq : Odd q) (hq_pos : 0 < q) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ n : ℕ, 1 ≤ n →
      C₂ * ((↑n : ℝ) * Real.log ((↑n : ℝ) + 1)) ≤
        ∑ k : Fin n, Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) /
                     |Real.cos ((↑p : ℝ) * Real.pi / ↑q) - chebyshevNode n k| := by
  -- Case split: either cos(πp/q) = -1 or cos(πp/q) ∈ (-1, 1)
  by_cases hx_neg1 : Real.cos ((↑p : ℝ) * Real.pi / ↑q) = -1
  · -- Case 1: x = -1 (e.g., p = q, or p = 3q, etc.)
    -- The sum becomes ∑ sin(φ_k)/|(-1) - cos(φ_k)| = ∑ tan(φ_k/2) by half-angle identity
    -- Apply trig_sum_lb_of_cos_eq_neg_one with C₂ = 1/(2π)
    refine ⟨1 / (2 * Real.pi), by positivity, fun n hn => ?_⟩
    have hrewrite : ∀ k : Fin n,
        Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) /
          |Real.cos ((↑p : ℝ) * Real.pi / ↑q) - chebyshevNode n k| =
        Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) /
          |(-1 : ℝ) - Real.cos ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n))| := by
      intro k
      simp only [hx_neg1, chebyshevNode]
    rw [show ∑ k : Fin n, Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) /
          |Real.cos ((↑p : ℝ) * Real.pi / ↑q) - chebyshevNode n k| =
        ∑ k : Fin n, Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) /
          |(-1 : ℝ) - Real.cos ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n))| from
      Finset.sum_congr rfl (fun k _ => hrewrite k)]
    exact trig_sum_lb_of_cos_eq_neg_one n hn
  · -- Case 2: x = cos(πp/q) ∈ (-1, 1), Lipschitz + harmonic sum
    -- Step 1: cos(πp/q) ∈ (-1, 1)
    have hx_gt : -1 < Real.cos ((↑p : ℝ) * Real.pi / ↑q) := by
      by_contra h; push_neg at h
      exact hx_neg1 (le_antisymm h (neg_one_le_cos _))
    have hx_lt : Real.cos ((↑p : ℝ) * Real.pi / ↑q) < 1 := by
      by_contra h; push_neg at h
      have heq : Real.cos ((↑p : ℝ) * Real.pi / ↑q) = 1 :=
        le_antisymm (Real.cos_le_one _) h
      rw [Real.cos_eq_one_iff] at heq
      obtain ⟨k, hk⟩ := heq
      have hq_ne : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq_pos.ne'
      have hpR : (p : ℝ) = k * (2 * q) := by field_simp at hk; linarith
      have hpZ : (p : ℤ) = k * (2 * q) := by exact_mod_cast hpR
      exact (Int.not_odd_iff_even.mpr (⟨k * q, by linarith⟩ : Even (p : ℤ))) (by exact_mod_cast hp)
    -- Step 2: arccos gives canonical angle θ₀ ∈ (0, π) with cos θ₀ = cos(πp/q)
    set x := Real.cos ((↑p : ℝ) * Real.pi / ↑q) with hx_def
    set θ₀ := Real.arccos x with hθ₀_def
    have hcos_eq : Real.cos θ₀ = x := Real.cos_arccos (neg_one_le_cos _) (Real.cos_le_one _)
    have hθ₀_pos : 0 < θ₀ := Real.arccos_pos.mpr hx_lt
    have hθ₀_lt_pi : θ₀ < Real.pi := by
      apply lt_of_le_of_ne (Real.arccos_le_pi x)
      intro heq
      -- θ₀ := arccos x and arccos x = π give θ₀ = π, so cos θ₀ = cos π = -1.
      rw [hθ₀_def, heq, Real.cos_pi] at hcos_eq
      linarith
    -- Step 3: Each sum term is positive
    have hterm_pos : ∀ (n : ℕ) (hn : 0 < n) (k : Fin n),
        0 < Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) /
            |x - chebyshevNode n k| := by
      intro n hn k
      exact div_pos (chebyshevAngle_sin_pos n hn k)
        (abs_pos.mpr (sub_ne_zero.mpr (x_not_chebyshev_node p q hp hq hq_pos n hn k)))
    -- Step 4: Reduce to cos θ₀ form
    suffices h_main : ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ n : ℕ, 1 ≤ n →
        C₂ * ((↑n : ℝ) * Real.log ((↑n : ℝ) + 1)) ≤
          ∑ k : Fin n, Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) /
                       |Real.cos θ₀ - chebyshevNode n k| by
      obtain ⟨C₂, hC₂, hbound⟩ := h_main
      refine ⟨C₂, hC₂, fun n hn => ?_⟩
      have : x = Real.cos θ₀ := hcos_eq.symm
      rw [this]; exact hbound n hn
    -- Step 5: Apply trig_sum_harmonic_lb with θ₀ and the node-avoidance property
    have hne : ∀ (n : ℕ) (_ : 0 < n) (k : Fin n), Real.cos θ₀ ≠ chebyshevNode n k := by
      intro n hn k
      rw [hcos_eq]
      exact x_not_chebyshev_node p q hp hq hq_pos n hn k
    exact trig_sum_harmonic_lb θ₀ hθ₀_pos hθ₀_lt_pi hne

/-- **Logarithmic lower bound on the Lebesgue function** (proved modulo `chebyshev_trig_sum_lb`).

    For x = cos(πp/q) with p, q odd, there exists C > 0 such that for all n ≥ 1:
      Λₙ(x) ≥ C · log(n + 1)

    Proof: Take C = δ · C₂ where:
    - δ > 0 from `cos_rational_pi_pos_min`: |cos(nπp/q)| ≥ δ uniformly in n
    - C₂ > 0 from `chebyshev_trig_sum_lb`: C₂ · n · log(n+1) ≤ S_n

    Then Λₙ = |cos(nθ)|/n · S_n ≥ (δ/n) · C₂ · n · log(n+1) = δ · C₂ · log(n+1). -/
private lemma chebyshev_lebesgue_lb (p q : ℕ) (hp : Odd p) (hq : Odd q) (hq_pos : 0 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      C * Real.log ((↑n : ℝ) + 1) ≤ chebyshevLebesgue n (Real.cos (↑p * Real.pi / ↑q)) := by
  -- Step 1: Uniform lower bound δ on |cos(nπp/q)| for all n
  obtain ⟨δ, hδ_pos, hδ_lb⟩ := cos_rational_pi_pos_min p q hp hq hq_pos
  -- Step 2: Harmonic sum lower bound C₂ · n · log(n+1) ≤ S_n
  obtain ⟨C₂, hC₂_pos, hC₂_lb⟩ := chebyshev_trig_sum_lb p q hp hq hq_pos
  -- Step 3: Take C = δ · C₂; show C · log(n+1) ≤ Λₙ(x) for all n ≥ 1
  refine ⟨δ * C₂, mul_pos hδ_pos hC₂_pos, fun n hn => ?_⟩
  have hn_pos : (0 : ℝ) < (↑n : ℝ) := Nat.cast_pos.mpr hn
  have hlog_nn : 0 ≤ Real.log ((↑n : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hcos_lb : δ ≤ |Real.cos ((↑n : ℝ) * (↑p * Real.pi / ↑q))| := hδ_lb n
  have hS_lb : C₂ * ((↑n : ℝ) * Real.log ((↑n : ℝ) + 1)) ≤
      ∑ k : Fin n, Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) /
                   |Real.cos ((↑p : ℝ) * Real.pi / ↑q) - chebyshevNode n k| :=
    hC₂_lb n hn
  -- Step 4: Apply Lebesgue formula Λₙ = |cos(nθ)|/n · S_n
  rw [chebyshev_lebesgue_eq_all_n p q hp hq hq_pos n hn]
  -- Step 5: δ · C₂ · log(n+1) = (δ/n) · (C₂ · n · log(n+1)) ≤ (|cos(nθ)|/n) · S_n
  calc δ * C₂ * Real.log ((↑n : ℝ) + 1)
      = δ / (↑n : ℝ) * (C₂ * ((↑n : ℝ) * Real.log ((↑n : ℝ) + 1))) := by
          field_simp [hn_pos.ne']
    _ ≤ |Real.cos ((↑n : ℝ) * (↑p * Real.pi / ↑q))| / (↑n : ℝ) *
        ∑ k : Fin n, Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) /
                     |Real.cos ((↑p : ℝ) * Real.pi / ↑q) - chebyshevNode n k| :=
        mul_le_mul
          ((div_le_div_iff_of_pos_right hn_pos).mpr hcos_lb)
          hS_lb
          (mul_nonneg hC₂_pos.le (mul_nonneg hn_pos.le hlog_nn))
          (div_nonneg (abs_nonneg _) hn_pos.le)

/-- **Lebesgue function growth at rational cosines** (proved modulo `chebyshev_lebesgue_lb`).

    For x = cos(πp/q) with p, q odd, the Chebyshev Lebesgue function Λₙ(x) → ∞ as n → ∞.
    The proof applies `tendsto_atTop_mono` with the logarithmic lower bound `chebyshev_lebesgue_lb`,
    combined with the fact that C · log(n+1) → ∞ (from `tendsto_log_atTop`). -/
theorem chebyshev_lebesgue_growth (p q : ℕ) (hp : Odd p) (hq : Odd q)
    (hq_pos : 0 < q) :
    Filter.Tendsto (fun n => chebyshevLebesgue n (Real.cos (↑p * Real.pi / ↑q)))
      Filter.atTop Filter.atTop := by
  -- Extract: ∃ C > 0, ∀ n ≥ 1, C · log(n+1) ≤ Λₙ(x)
  obtain ⟨C, hC_pos, hC_lb⟩ := chebyshev_lebesgue_lb p q hp hq hq_pos
  -- The lower bound C · log(n+1) tends to +∞
  have hlb_atTop : Filter.Tendsto (fun n : ℕ => C * Real.log ((↑n : ℝ) + 1))
      Filter.atTop Filter.atTop :=
    (tendsto_log_atTop.comp
      (Filter.Tendsto.atTop_add tendsto_natCast_atTop_atTop tendsto_const_nhds)).const_mul_atTop hC_pos
  -- Since Λₙ(x) ≥ C·log(n+1) and C·log(n+1) → ∞, we have Λₙ(x) → ∞
  apply Filter.tendsto_atTop_mono (f := fun n : ℕ => C * Real.log ((↑n : ℝ) + 1)) _ hlb_atTop
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- n = 0: Λ₀ = 0 (empty sum) and C · log(0+1) = C · log(1) = 0
    simp [chebyshevLebesgue, Real.log_one]
  · -- n ≥ 1: apply the analytic lower bound
    exact hC_lb n hn

/-- **[SORRY] Divergence from Lebesgue growth.**

    If Λₙ(x) → ∞, then ∃ continuous f with Lₙf(x) → +∞.

    Proof sketch has gap in cross-term estimate; lacunary series construction needed. -/
theorem divergence_from_lebesgue_growth (x : ℝ)
    (hgrowth : Filter.Tendsto (fun n => chebyshevLebesgue n x)
               Filter.atTop Filter.atTop) :
    ∃ f : ℝ → ℝ, Continuous f ∧
      ∀ M : ℝ, ∃ N : ℕ, ∀ n ≥ N, M < chebyshevInterp n f x := by
  sorry

/-! ## Main Theorem (Proof Complete Modulo Sorries) -/

/-- **Erdős's Result (1941) — Lebesgue function proof.**

    For x = cos(πp/q) with odd p, q ≥ 1, there exists a continuous f
    such that the Chebyshev interpolation sequence Lₙf(x) → +∞. -/
theorem erdos_1941_divergence_from_growth (p q : ℕ) (hp : Odd p) (hq : Odd q)
    (hq_pos : 0 < q) :
    let x := Real.cos (↑p * Real.pi / ↑q)
    ∃ f : ℝ → ℝ, Continuous f ∧
      ∀ M : ℝ, ∃ N : ℕ, ∀ n ≥ N, M < chebyshevInterp n f x :=
  divergence_from_lebesgue_growth _
    (chebyshev_lebesgue_growth p q hp hq hq_pos)

/-! ## Session 40: Polynomial reproduction — Lₙp = p for deg p < n

The missing "lacunary-assembly" ingredient of Sorry 2's strong (full-limit)
form: Chebyshev interpolation reproduces every polynomial of degree < n
exactly. Proved by bridging this file's function-level `lagrangeBasis` to
Mathlib's polynomial-level `Lagrange.basis` and invoking the interpolation
characterization `Lagrange.eq_interpolate`. The partition-of-unity corollary
`sum_lagrangeBasis_eq_one` (Σₖ ℓₖ(x) = 1) is the p = 1 instance. -/

/-- Bridge: the function-level Lagrange basis of this file is the evaluation of
    Mathlib's polynomial-level `Lagrange.basis` (no injectivity needed — both
    sides are the same formal product of affine ratios). -/
theorem lagrangeBasis_eq_eval_basis (n : ℕ) (nodes : Fin n → ℝ) (k : Fin n) (x : ℝ) :
    lagrangeBasis n nodes k x = (Lagrange.basis Finset.univ nodes k).eval x := by
  simp only [lagrangeBasis, Lagrange.basis, Lagrange.basisDivisor,
    Polynomial.eval_prod, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_X]
  exact Finset.prod_congr rfl fun i _ => div_eq_inv_mul _ _

/-- **Polynomial reproduction for Lagrange interpolation at injective nodes**:
    for a polynomial `p` with `p.degree < n`, the `n`-node Lagrange interpolant
    of `p` reproduces `p` at every point — the interpolation problem on `n`
    nodes has the unique solution `p` itself (`Lagrange.eq_interpolate`). -/
theorem lagrangeInterp_polynomial (n : ℕ) (nodes : Fin n → ℝ)
    (hinj : Function.Injective nodes) (p : Polynomial ℝ)
    (hdeg : p.degree < (n : WithBot ℕ)) (x : ℝ) :
    lagrangeInterp n nodes (fun t => p.eval t) x = p.eval x := by
  have hvs : Set.InjOn nodes ↑(Finset.univ : Finset (Fin n)) := hinj.injOn
  have hdeg' : p.degree < (Finset.univ : Finset (Fin n)).card := by simpa using hdeg
  have hrep : p = Lagrange.interpolate Finset.univ nodes fun i => p.eval (nodes i) :=
    Lagrange.eq_interpolate hvs hdeg'
  calc lagrangeInterp n nodes (fun t => p.eval t) x
      = (Lagrange.interpolate Finset.univ nodes fun i => p.eval (nodes i)).eval x := by
        rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum]
        simp only [lagrangeInterp, Polynomial.eval_mul, Polynomial.eval_C,
          lagrangeBasis_eq_eval_basis]
    _ = p.eval x := by rw [← hrep]

/-- **Chebyshev interpolation reproduces polynomials of degree < n** — the
    polynomial-reproduction ingredient of the Sorry 2 strong-form roadmap
    (state.md S39/S40): together with the S39 continuous saturation witness it
    feeds the gliding-hump construction for the full-limit divergence. -/
theorem chebyshevInterp_polynomial (n : ℕ) (hn : 0 < n) (p : Polynomial ℝ)
    (hdeg : p.degree < (n : WithBot ℕ)) (x : ℝ) :
    chebyshevInterp n (fun t => p.eval t) x = p.eval x :=
  lagrangeInterp_polynomial n (chebyshevNode n) (chebyshevNode_injective n hn) p hdeg x

/-- **Partition of unity**: the Lagrange basis functions at injective nodes sum
    to 1 pointwise (reproduction of the constant polynomial `1`). -/
theorem sum_lagrangeBasis_eq_one (n : ℕ) (hn : 0 < n) (nodes : Fin n → ℝ)
    (hinj : Function.Injective nodes) (x : ℝ) :
    ∑ k : Fin n, lagrangeBasis n nodes k x = 1 := by
  have h := lagrangeInterp_polynomial n nodes hinj 1
    (by rw [Polynomial.degree_one]; exact_mod_cast hn) x
  simpa [lagrangeInterp] using h

/-- Partition of unity at the Chebyshev nodes. -/
theorem sum_chebyshev_lagrangeBasis_eq_one (n : ℕ) (hn : 0 < n) (x : ℝ) :
    ∑ k : Fin n, lagrangeBasis n (chebyshevNode n) k x = 1 :=
  sum_lagrangeBasis_eq_one n hn (chebyshevNode n) (chebyshevNode_injective n hn) x

end Erdos1151OQ04
