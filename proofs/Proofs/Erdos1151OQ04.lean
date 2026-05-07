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

## Sorry 1: trig_sum_harmonic_lb (was: chebyshev_trig_sum_lb Case 2)
Now factored as a SELF-CONTAINED lemma for general θ ∈ (0, π):
  - Statement: ∃ C > 0, C·n·log(n+1) ≤ Σ sin(φₖ)/|cos θ - cos φₖ| for all n ≥ 1
  - Depends only on θ ∈ (0, π) and cos θ ≠ any Chebyshev node (no p, q dependency)
  - Case 2 of chebyshev_trig_sum_lb is PROVED modulo this lemma
  - Proof approach: Lipschitz + Finset harmonic sum over near-nodes + finite min for small n

## Sorry 2: divergence_from_lebesgue_growth
Proof requires:
  a) For each n, existence of optimizing continuous function with ‖f‖ ≤ 1 and Lₙf(x) = Λₙ(x)
  b) Lacunary subsequence construction [has known gap: UBP gives lim sup, not lim]

Tags: analysis, approximation-theory, chebyshev, lebesgue-function, erdos-problems
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
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
  ring

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
    nlinarith

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
      push_cast; have := hkj; linarith
    field_simp; linarith [this]
  -- So (2k+1)π/(4n) = π/2 - (2j+1)π/(4n)
  have hA_eq : (2 * k.val + 1 : ℝ) * Real.pi / (4 * n) =
               Real.pi / 2 - (2 * (j : ℝ) + 1) * Real.pi / (4 * n) := by linarith [hangle_sum]
  -- sin(π/2 - u) = cos(u) and cos(π/2 - u) = sin(u)
  set u := (2 * (j : ℝ) + 1) * Real.pi / (4 * n) with hu_def
  have hu_pos : 0 < u := by unfold_let u; positivity
  have hu_le : u ≤ Real.pi / 3 := by
    unfold_let u
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * ↑n) (by positivity : (0 : ℝ) < 3)]
    -- Need (2j+1)·π·3 ≤ π·(4n), i.e., 3(2j+1) ≤ 4n
    have hj_bound : j < n / 2 + 1 := by omega
    nlinarith [Real.pi_pos, hj_bound]
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
    rw [← Real.sin_pi_sub]
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
    nlinarith [(show (0 : ℝ) ≤ j from Nat.cast_nonneg)]
  -- Step 2: ∑ 1/(2(j+1)) = (1/2) · ∑ 1/(j+1) = (1/2) · H_m
  have hsum_half : ∑ j ∈ Finset.range m, (1 : ℝ) / (2 * (↑j + 1)) =
      (1 : ℝ) / 2 * ∑ j ∈ Finset.range m, (1 : ℝ) / (↑j + 1) := by
    rw [Finset.mul_sum]; congr 1; ext j; ring
  -- Step 3: ∑_{j=0}^{m-1} 1/(j+1) = H_m (harmonic number)
  have hharmonic : ∑ j ∈ Finset.range m, (1 : ℝ) / (↑j + 1) = ((harmonic m : ℚ) : ℝ) := by
    induction m with
    | zero => simp [harmonic]
    | succ n ih =>
      rw [Finset.sum_range_succ, harmonic_succ]
      push_cast [ih]
      ring
  -- Step 4: log(m+1) ≤ H_m
  have hlog_harmonic : Real.log (↑m + 1) ≤ ((harmonic m : ℚ) : ℝ) := by
    have := log_add_one_le_harmonic m
    exact_mod_cast this
  -- Combine: (1/2)·log(m+1) ≤ (1/2)·H_m = ∑ 1/(2(j+1)) ≤ ∑ 1/(2j+1)
  calc (1 : ℝ) / 2 * Real.log (↑m + 1)
      ≤ 1 / 2 * ((harmonic m : ℚ) : ℝ) := by
          apply mul_le_mul_of_nonneg_left hlog_harmonic (by norm_num)
    _ = ∑ j ∈ Finset.range m, 1 / (2 * (↑j + 1)) := by rw [hsum_half, hharmonic]
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
    nlinarith [show (↑(n / 2) : ℝ) ≥ 1 from by exact_mod_cast h2]
  -- (1/2)·log(n+1) ≤ log(n/2+1) via: log(n+1) ≤ 2·log(n/2+1) = log((n/2+1)²)
  have h2log : Real.log ((↑n : ℝ) + 1) ≤ 2 * Real.log ((↑(n / 2) : ℝ) + 1) := by
    have hpow : Real.log (((↑(n / 2) : ℝ) + 1) ^ 2) = 2 * Real.log ((↑(n / 2) : ℝ) + 1) := by
      rw [Real.log_pow]
      ring
    rw [← hpow]
    exact Real.log_le_log hn1_pos.le key
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
  -- Step 2: Handle n = 1 separately (sum = tan(π/4) = 1, target < 1)
  rcases eq_or_lt_of_le hn with rfl | hn_ge_2
  · -- n = 1: target = (1/(2π))·log(2) ≤ 1 = sum
    simp only [Fin.sum_univ_one, Nat.cast_one, mul_one]
    have hlog2_le : Real.log 2 ≤ 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      have hexp1 : Real.exp 1 ≥ 2 := by linarith
      linarith [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2) |>.mpr (by linarith)]
    have hpi_pos := Real.pi_pos
    -- sin(π/4)/cos(π/4) = 1
    have htan : Real.sin (1 * Real.pi / (4 * 1)) / Real.cos (1 * Real.pi / (4 * 1)) = 1 := by
      have h1 : (1 : ℝ) * Real.pi / (4 * 1) = Real.pi / 4 := by ring
      rw [h1, Real.sin_pi_div_four, Real.cos_pi_div_four, div_self]
      exact (Real.sqrt_ne_zero'.mpr (by positivity)).symm ▸ Real.sqrt_pos_of_pos (by norm_num) |>.ne'
    rw [htan]
    -- (1/(2π))·log(2) ≤ 1
    have : 1 / (2 * Real.pi) * Real.log (1 + 1) ≤ 1 := by
      have : 1 / (2 * Real.pi) ≤ 1 := div_le_one_of_le (by linarith) (by positivity)
      nlinarith [hlog2_le]
    linarith [this]
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
                rw [Finset.mul_sum]; congr 1; ext j; ring
            _ ≤ ∑ k ∈ S, 2 * ↑n / (Real.pi * (2 * ↑(n - 1 - k.val) + 1)) := by
                -- Reindex: range(n/2) → S via j ↦ ⟨n-1-j, _⟩
                -- Then n-1-(n-1-j) = j, so terms match
                let φ : ℕ → Fin n := fun j => ⟨n - 1 - j, by omega⟩
                have hinj : ∀ j₁ ∈ Finset.range (n / 2), ∀ j₂ ∈ Finset.range (n / 2),
                    φ j₁ = φ j₂ → j₁ = j₂ := by
                  intro j₁ _ j₂ _ heq
                  simp only [φ, Fin.mk.injEq] at heq; omega
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
                  congr 1; congr 1; congr 1
                  simp only [φ, Fin.val_mk]
                  have hj_lt : j < n / 2 := Finset.mem_range.mp hj
                  have : n - 1 - (n - 1 - j) = j := by omega
                  exact_mod_cast congrArg (↑· : ℕ → ℝ) this
                -- ∑ range(n/2) f(j) = ∑ image(φ) g(k) ≤ ∑ S g(k)
                rw [show ∑ j ∈ Finset.range (n / 2), 2 * ↑n / (Real.pi * (2 * (↑j : ℝ) + 1)) =
                    ∑ j ∈ Finset.range (n / 2),
                      2 * ↑n / (Real.pi * (2 * ↑(n - 1 - (φ j).val) + 1)) from
                  Finset.sum_congr rfl hvals]
                rw [← Finset.sum_image hinj]
                exact Finset.sum_le_sum_of_subset_of_nonneg himg_sub
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
        |((k₀.val : ℝ) - k.val) * Real.pi / n| := abs_add _ _
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
  -- 1/B ≤ 1/|cos θ - cos φ|
  have h_inv : 1 / B ≤ 1 / |Real.cos θ - Real.cos φ| := by
    apply one_div_le_one_div_of_le h_denom_pos'
    rw [hnode]; exact h_cos_le_B
  -- sin(d/2)/B ≤ sin(φ)/|cos θ - cos φ|
  have hsin_d_half_nn : 0 ≤ Real.sin (d / 2) := le_of_lt hsin_d_half_pos
  have h1 : Real.sin (d / 2) / B ≤ Real.sin (d / 2) / |Real.cos θ - Real.cos φ| := by
    rw [div_eq_mul_one_div, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left h_inv hsin_d_half_nn
  have h2 : Real.sin (d / 2) / |Real.cos θ - Real.cos φ| ≤
            Real.sin φ / |Real.cos θ - Real.cos φ| := by
    apply div_le_div_of_nonneg_right hsin_lb h_denom_pos'
  -- Convert sin(d/2)/B to the target form via div_div_eq_mul_div
  have h_target_eq : Real.sin (d / 2) / B =
      Real.sin (d / 2) * (2 * (n : ℝ)) /
        ((2 * |((k.val : ℝ) - k₀.val)| + 1) * Real.pi) := by
    rw [hB_def]
    exact div_div_eq_mul_div _ _ _
  rw [hnode]
  calc Real.sin (d / 2) * (2 * (n : ℝ)) /
          ((2 * |((k.val : ℝ) - k₀.val)| + 1) * Real.pi)
      = Real.sin (d / 2) / B := h_target_eq.symm
    _ ≤ Real.sin (d / 2) / |Real.cos θ - Real.cos φ| := h1
    _ ≤ Real.sin φ / |Real.cos θ - Real.cos φ| := h2

/-- **[SORRY] Harmonic trig sum lower bound for general θ ∈ (0, π).**

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
    7. Take C₂ = min of the large-n constant and the finite-set minimum. -/
private lemma trig_sum_harmonic_lb (θ : ℝ) (hθ_pos : 0 < θ) (hθ_lt : θ < Real.pi)
    (hne : ∀ (n : ℕ) (_ : 0 < n) (k : Fin n), Real.cos θ ≠ chebyshevNode n k) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      C * ((↑n : ℝ) * Real.log ((↑n : ℝ) + 1)) ≤
        ∑ k : Fin n, Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) /
                     |Real.cos θ - chebyshevNode n k| := by
  -- Core technical lemma: Lipschitz + harmonic sum over near-nodes + finite minimum.
  -- See docstring for full proof sketch.
  sorry

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
      exact (not_odd_iff_even.mpr (⟨k * q, by linarith⟩ : Even (p : ℤ))) (by exact_mod_cast hp)
    -- Step 2: arccos gives canonical angle θ₀ ∈ (0, π) with cos θ₀ = cos(πp/q)
    set x := Real.cos ((↑p : ℝ) * Real.pi / ↑q) with hx_def
    set θ₀ := Real.arccos x with hθ₀_def
    have hcos_eq : Real.cos θ₀ = x := Real.cos_arccos (neg_one_le_cos _) (Real.cos_le_one _)
    have hθ₀_pos : 0 < θ₀ := Real.arccos_pos.mpr hx_lt
    have hθ₀_lt_pi : θ₀ < Real.pi := by
      apply lt_of_le_of_ne (Real.arccos_le_pi x)
      intro heq
      rw [← heq, Real.cos_pi] at hcos_eq
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

end Erdos1151OQ04
