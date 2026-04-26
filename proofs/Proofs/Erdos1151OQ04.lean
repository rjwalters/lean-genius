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

  `chebyshev_lebesgue_lb` [SORRY: harmonic sum lower bound — key analytic step]
  `divergence_from_lebesgue_growth` [SORRY: lacunary series construction]

The non-sorry results proved here:
  - `lebesgue_upper_bound`: |Lₙf(x)| ≤ ‖f‖_∞ · Λₙ(x)
  - `chebyshev_interp_linear_left`, `chebyshev_interp_linear_right`: linearity
  - `chebyshev_T_at_cos`: Tₙ(cos θ) = cos(nθ) — from Mathlib
  - `cos_rational_pi_multiple`: cos(kπp) = ±1 for integer k and odd p
  - `erdos_1941_divergence_from_growth`: main reduction theorem
  - `chebyshev_product_formula`: T_n = 2^{n-1} · ∏(X - C(cos φₖ)) [Session 5, NEW]
  - `lagrange_basis_chebyshev_formula`: explicit Lagrange basis at Chebyshev nodes [Session 5, NEW]
  - `chebyshev_lebesgue_eq`: Λₙ(cos θ) = |cos(nθ)|/n · Σₖ sin(φₖ)/|cos θ - cos φₖ| [Session 5, NEW]
  - `x_not_chebyshev_node`: cos(πp/q) ≠ chebyshevNode n k for all n when p,q odd [Session 6, NEW]
  - `chebyshev_lebesgue_eq_all_n`: applies lebesgue_eq for ALL n (not just n=mq) [Session 6, NEW]
  - `cos_rational_pi_ne_zero`: cos(nπp/q) ≠ 0 for ALL n [Session 7, NEW]
  - `cos_rational_pi_mod`: periodicity with period 2q [Session 7, NEW]
  - `cos_rational_pi_pos_min`: ∃ δ > 0, |cos(nπp/q)| ≥ δ for all n [Session 7, NEW]
  - `chebyshev_lebesgue_growth`: Λₙ → ∞ proved modulo chebyshev_lebesgue_lb [Session 11, NEW]

## Sorry 1: chebyshev_lebesgue_lb
Proof requires:
  a) C_min = cos_rational_pi_pos_min gives ∃ δ > 0 [PROVED, Session 7]
  b) S_n = Σₖ sin(φₖ)/|cos θ - cos φₖ| ≥ C₂·n·log(n+1) via harmonic comparison [OPEN]
     — uses |cos θ - cos φ| ≤ |θ−φ| (Lipschitz), node spacing π/n, and
     — Mathlib: `NumberTheory.Harmonic.Bounds.log_add_one_le_harmonic`
  c) Λₙ = δ/n · S_n ≥ δ · C₂ · log(n+1) → ∞

## Sorry 2: divergence_from_lebesgue_growth
Proof requires:
  a) For each n, existence of optimizing continuous function with ‖f‖ ≤ 1 and Lₙf(x) = Λₙ(x)
  b) Lacunary subsequence construction [has known gap in proof sketch]

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
  rw [div_le_div_iff (by positivity) hsin_pos]
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

/-! ## Helper Lemmas for Harmonic Sum Lower Bound -/

/-- Half-angle B_k = (2k+1)π/(4n) lies strictly in (0, π/2). -/
private lemma chebyshevHalfAngle_pos_lt (n : ℕ) (hn : 0 < n) (k : Fin n) :
    0 < (2 * k.val + 1 : ℝ) * Real.pi / (4 * n) ∧
    (2 * k.val + 1 : ℝ) * Real.pi / (4 * n) < Real.pi / 2 := by
  have hpi := Real.pi_pos
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  constructor
  · positivity
  · rw [div_lt_div_iff (by positivity : (0:ℝ) < 4 * ↑n) (by positivity : (0:ℝ) < 2)]
    have hlt : 2 * k.val + 1 < 2 * n := by omega
    nlinarith [(show (2 * (k.val : ℝ) + 1) < 2 * ↑n from by exact_mod_cast hlt)]

/-- Each tan(B_k) term is nonneg since B_k ∈ (0, π/2). -/
private lemma tan_half_angle_nonneg (n : ℕ) (hn : 0 < n) (k : Fin n) :
    0 ≤ Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (4 * n)) /
        Real.cos ((2 * k.val + 1 : ℝ) * Real.pi / (4 * n)) := by
  have ⟨hpos, hlt⟩ := chebyshevHalfAngle_pos_lt n hn k
  exact div_nonneg
    (Real.sin_nonneg_of_nonneg_of_le_pi hpos.le (by linarith [Real.pi_pos]))
    (Real.cos_pos_of_mem_Ioo ⟨by linarith, hlt⟩).le

/-- **Cot lower bound for large k**: For k with k.val ≥ (n+1)/2, the complementary angle
    u = π/2 - B_k satisfies u ∈ (0, π/3], so cot(u) ≥ 1/(2u), giving:
    tan(B_k) = cot(u) ≥ 2n/(π(2(n - k.val) - 1)). -/
private lemma tan_half_angle_cot_lb (n : ℕ) (hn : 1 < n) (k : Fin n)
    (hk : (n + 1) / 2 ≤ k.val) :
    2 * ↑n / (Real.pi * (2 * ((↑n : ℝ) - ↑k.val) - 1)) ≤
    Real.sin ((2 * ↑k.val + 1 : ℝ) * Real.pi / (4 * ↑n)) /
    Real.cos ((2 * ↑k.val + 1 : ℝ) * Real.pi / (4 * ↑n)) := by
  have hpi := Real.pi_pos
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
  have hk_lt : k.val < n := k.isLt
  have hnk_pos : 0 < n - k.val := by omega
  -- In ℝ: 2(n-k) - 1 > 0
  have hR_pos : (0 : ℝ) < 2 * (↑n - ↑k.val) - 1 := by
    have : (1 : ℝ) ≤ ↑n - ↑k.val := by
      have h := Nat.cast_sub (show k.val ≤ n from by omega)
      rw [← h]; exact_mod_cast hnk_pos
    linarith
  -- Define u = complementary angle = (2(n-k)-1)π/(4n)
  set u := (2 * ((↑n : ℝ) - ↑k.val) - 1) * Real.pi / (4 * ↑n)
  -- u > 0
  have hu_pos : 0 < u := by positivity
  -- u ≤ π/3: since k ≥ (n+1)/2, n-k ≤ n/2, so 2(n-k)-1 ≤ n-1, and (n-1)/(4n) < 1/4 < 1/3
  have hu_le : u ≤ Real.pi / 3 := by
    show (2 * ((↑n : ℝ) - ↑k.val) - 1) * Real.pi / (4 * ↑n) ≤ Real.pi / 3
    rw [div_le_div_iff (by positivity : (0:ℝ) < 4 * ↑n) (by positivity : (0:ℝ) < 3)]
    -- Need: (2(n-k)-1) · π · 3 ≤ 4n · π, i.e., 3(2(n-k)-1) ≤ 4n
    -- From k ≥ (n+1)/2: n-k ≤ n/2, so 2(n-k) ≤ n, hence 2(n-k)-1 ≤ n-1
    -- 3(n-1) = 3n-3 ≤ 4n since n ≥ 0
    have hnk_le : n - k.val ≤ n / 2 := by omega
    have hcast_sub : (↑n : ℝ) - ↑k.val = ↑(n - k.val) := by
      rw [Nat.cast_sub (show k.val ≤ n from by omega)]
    have hcast_le : (↑(n - k.val) : ℝ) ≤ ↑(n / 2) := Nat.cast_le.mpr hnk_le
    have hdiv_le : (2 : ℝ) * ↑(n / 2) ≤ ↑n := by exact_mod_cast (show 2 * (n / 2) ≤ n by omega)
    rw [hcast_sub]
    nlinarith [hcast_le, hdiv_le]
  -- B_k + u = π/2, so B_k = π/2 - u
  have hB_eq : (2 * ↑k.val + 1 : ℝ) * Real.pi / (4 * ↑n) = Real.pi / 2 - u := by
    have : (2 * ↑k.val + 1 : ℝ) * Real.pi / (4 * ↑n) +
           (2 * ((↑n : ℝ) - ↑k.val) - 1) * Real.pi / (4 * ↑n) = Real.pi / 2 := by
      field_simp [hn_pos.ne']; ring
    linarith
  -- Rewrite sin(B)/cos(B) = sin(π/2 - u)/cos(π/2 - u) = cos(u)/sin(u)
  rw [hB_eq, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  -- Show 2n/(π(2(n-k)-1)) = 1/(2u) and apply cot_ge_inv_two_mul
  have h_eq : 2 * ↑n / (Real.pi * (2 * ((↑n : ℝ) - ↑k.val) - 1)) = 1 / (2 * u) := by
    show 2 * ↑n / (Real.pi * (2 * ((↑n : ℝ) - ↑k.val) - 1)) =
         1 / (2 * ((2 * ((↑n : ℝ) - ↑k.val) - 1) * Real.pi / (4 * ↑n)))
    field_simp [hpi.ne', hn_pos.ne', hR_pos.ne']
    ring
  rw [h_eq]
  exact cot_ge_inv_two_mul hu_pos hu_le

/-- **Odd harmonic sum lower bound**: Σ_{j=0}^{m-1} 1/(2j+1) ≥ (1/2)·log(m+1).

    Proof: 1/(2j+1) ≥ 1/(2(j+1)) = (1/2)·(1/(j+1)), so the sum ≥ (1/2)·H_m,
    and H_m ≥ log(m+1) by the standard harmonic bound. -/
private lemma odd_harmonic_sum_lb (m : ℕ) (hm : 0 < m) :
    (1 : ℝ) / 2 * Real.log ((↑m : ℝ) + 1) ≤
    ∑ j ∈ Finset.range m, (1 : ℝ) / (2 * (↑j : ℝ) + 1) := by
  -- Each 1/(2j+1) ≥ 1/(2(j+1))
  have hpw : ∀ j ∈ Finset.range m,
      (1 : ℝ) / (2 * (↑j + 1)) ≤ 1 / (2 * ↑j + 1) := by
    intro j _
    apply div_le_div_of_nonneg_left (by positivity : (0:ℝ) < 1)
      (by positivity : (0:ℝ) < 2 * ↑j + 1)
      (by positivity : (0:ℝ) < 2 * (↑j + 1))
    push_cast
    linarith
  -- Σ 1/(2(j+1)) ≤ Σ 1/(2j+1)
  have h1 : ∑ j ∈ Finset.range m, (1 : ℝ) / (2 * (↑j + 1)) ≤
            ∑ j ∈ Finset.range m, (1 : ℝ) / (2 * ↑j + 1) :=
    Finset.sum_le_sum hpw
  -- Σ 1/(2(j+1)) = (1/2) · Σ 1/(j+1)
  have h2 : ∑ j ∈ Finset.range m, (1 : ℝ) / (2 * (↑j + 1)) =
            (1 : ℝ) / 2 * ∑ j ∈ Finset.range m, 1 / (↑j + 1) := by
    rw [Finset.mul_sum]; congr 1; ext j; ring
  -- Σ_{j=0}^{m-1} 1/(j+1) = harmonic m, and log(m+1) ≤ harmonic m
  -- Use: Real.add_one_le_exp gives exp(t) ≥ 1+t, hence log(1+1/k) ≤ 1/k
  -- Telescoping: log(m+1) = Σ_{j=0}^{m-1} log((j+2)/(j+1)) ≤ Σ 1/(j+1) = H_m
  have h3 : Real.log ((↑m : ℝ) + 1) ≤
            ∑ j ∈ Finset.range m, (1 : ℝ) / (↑j + 1) := by
    -- log(m+1) = log(m+1) - log(1) = Σ [log(j+2) - log(j+1)]
    -- Each log(j+2) - log(j+1) = log((j+2)/(j+1)) = log(1 + 1/(j+1)) ≤ 1/(j+1)
    -- Formalized via Finset.sum_range_induction + Real.log inequality
    -- Telescoping: log(m+1) = Σ_{j=0}^{m-1} [log(j+2) - log(j+1)], each ≤ 1/(j+1)
    have htelescope := Finset.sum_range_sub (fun j : ℕ => Real.log ((↑j : ℝ) + 1)) m
    -- htelescope : Σ (log(j+2) - log(j+1)) = log(m+1) - log(1)
    simp only [Nat.cast_zero, zero_add, Real.log_one, sub_zero] at htelescope
    rw [← htelescope]
    -- Bound each term: log(j+2) - log(j+1) ≤ 1/(j+1)
    apply Finset.sum_le_sum
    intro j _
    have hj1 : (0 : ℝ) < ↑j + 1 := by positivity
    have hj2 : (0 : ℝ) < ↑j + 2 := by positivity
    -- log(j+2) - log(j+1) = log((j+2)/(j+1)) = log(1 + 1/(j+1))
    rw [show (↑(j + 1) : ℝ) + 1 = ↑j + 2 from by push_cast; ring]
    rw [← Real.log_div hj2.ne' hj1.ne']
    have hdiv_eq : (↑j + 2 : ℝ) / (↑j + 1) = 1 + 1 / (↑j + 1) := by
      field_simp; ring
    rw [hdiv_eq]
    -- log(1 + x) ≤ x for x ≥ 0, from exp(x) ≥ 1 + x
    calc Real.log (1 + 1 / (↑j + 1))
        ≤ Real.log (Real.exp (1 / (↑j + 1))) := by
          apply Real.log_le_log (by positivity) (Real.add_one_le_exp _)
      _ = 1 / (↑j + 1) := Real.log_exp _
  -- Combine: (1/2)·log(m+1) ≤ (1/2)·H_m = Σ 1/(2(j+1)) ≤ Σ 1/(2j+1)
  calc (1 : ℝ) / 2 * Real.log ((↑m : ℝ) + 1)
      ≤ 1 / 2 * ∑ j ∈ Finset.range m, 1 / (↑j + 1) := by
          exact mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = ∑ j ∈ Finset.range m, 1 / (2 * (↑j + 1)) := h2.symm
    _ ≤ ∑ j ∈ Finset.range m, 1 / (2 * ↑j + 1) := h1

/-- **Sub-sum reindexing**: The sum of 1/(2(n-k)-1) over k ≥ ⌈n/2⌉ equals the odd harmonic sum.

    Maps k ↦ n-1-k, sending {⌈n/2⌉,...,n-1} → {0,...,⌊n/2⌋-1}, with
    2(n-k)-1 = 2(n-1-k)+1, matching the odd harmonic indexing. -/
private lemma sub_sum_eq_odd_harmonic (n : ℕ) (hn : 1 < n)
    (f : ℕ → ℝ) :
    ∑ k ∈ (Finset.range n).filter (fun k => (n + 1) / 2 ≤ k),
      f (2 * (n - k) - 1) =
    ∑ j ∈ Finset.range (n / 2), f (2 * j + 1) := by
  -- Bijection k ↦ n-1-k maps {k : (n+1)/2 ≤ k < n} → {j : j < n/2}
  -- with 2*(n-k)-1 = 2*(n-1-k)+1 = 2*j+1
  apply Finset.sum_nbij (fun k => n - 1 - k)
  · -- Maps source to target
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    omega
  · -- Injective on source
    intro a ha b hb hab
    simp only [Finset.mem_filter, Finset.mem_range] at ha hb
    omega
  · -- Surjective onto target
    intro j hj
    simp only [Finset.mem_range] at hj
    exact ⟨n - 1 - j, by simp only [Finset.mem_filter, Finset.mem_range]; omega, by omega⟩
  · -- Values match: f(2*(n-k)-1) = f(2*(n-1-k)+1)
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    congr 1; omega

/-- For the x = -1 case: the trigonometric Lebesgue sum S_n = Σ tan(φₖ/2) grows like n log n.

    Proof:
    - n = 1: tan(π/4) = 1 ≥ log(2)/(2π) by direct computation
    - n ≥ 2: Sub-sum over k ≥ ⌈n/2⌉ using cot bound + odd harmonic estimate -/
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
  have hpi := Real.pi_pos
  -- Step 2: Handle n = 1 directly
  rcases Nat.eq_or_gt_of_le hn with rfl | hn2
  · -- n = 1: S₁ = tan(π/4) = sin(π/4)/cos(π/4) = 1
    simp only [Finset.univ_unique, Finset.sum_singleton, Fin.val_zero]
    -- Simplify angle: (2·0+1)·π/(4·1) = π/4
    have hangle : (2 * (0 : ℝ) + 1) * Real.pi / (4 * 1) = Real.pi / 4 := by ring
    rw [hangle]
    -- sin(π/4)/cos(π/4) = tan(π/4) = 1
    have htan1 : Real.sin (Real.pi / 4) / Real.cos (Real.pi / 4) = 1 := by
      have hcos_pos : 0 < Real.cos (Real.pi / 4) :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
      rw [div_eq_one_iff_eq hcos_pos.ne']
      exact (Real.sin_pi_div_four).trans (Real.cos_pi_div_four).symm
    rw [htan1]
    -- Need: 1/(2π) · 1 · log(2) ≤ 1, i.e., log(2) ≤ 2π
    -- log(2) ≤ 1 (since e > 2) and 1 ≤ 2π
    have hlog2_le : Real.log 2 ≤ 1 := by
      have h := Real.add_one_le_exp (Real.log 2)
      rw [Real.exp_log (by norm_num : (0:ℝ) < 2)] at h; linarith
    push_cast; nlinarith [Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num)]
  · -- n ≥ 2: Sub-sum approach using cot bound + odd harmonic estimate
    -- The sum over Fin n ≥ sub-sum over k ≥ (n+1)/2 (using nonneg of dropped terms)
    -- Each term in sub-sum ≥ 2n/(π(2(n-k)-1)) by tan_half_angle_cot_lb
    -- Sub-sum ≥ (2n/π) · odd_harmonic(n/2) ≥ (2n/π) · (1/2) · log(n/2+1)
    -- ≥ (n/π) · (1/2) · log(n+1) = (1/(2π)) · n · log(n+1)
    have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
    have hm_pos : 0 < n / 2 := by omega
    -- Step E: Log comparison: (1/2)·log(n+1) ≤ log(n/2+1) since (n/2+1)² ≥ n+1 for n ≥ 2
    have hLogComp : (1 : ℝ) / 2 * Real.log ((↑n : ℝ) + 1) ≤
                    Real.log ((↑(n / 2) : ℝ) + 1) := by
      have hsq : (↑n : ℝ) + 1 ≤ ((↑(n / 2) : ℝ) + 1) ^ 2 := by
        have : (n / 2 + 1) * (n / 2 + 1) ≥ n + 1 := by omega
        have h : (↑((n / 2 + 1) * (n / 2 + 1)) : ℝ) ≥ ↑(n + 1) := Nat.cast_le.mpr this
        push_cast at h ⊢; nlinarith
      calc (1 : ℝ) / 2 * Real.log ((↑n : ℝ) + 1)
          ≤ 1 / 2 * Real.log (((↑(n / 2) : ℝ) + 1) ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact Real.log_le_log (by positivity) hsq
        _ = 1 / 2 * (2 * Real.log ((↑(n / 2) : ℝ) + 1)) := by
            rw [Real.log_pow]; push_cast; ring
        _ = Real.log ((↑(n / 2) : ℝ) + 1) := by ring
    -- Step D: Odd harmonic bound
    have hHarmonic := odd_harmonic_sum_lb (n / 2) hm_pos
    -- Assemble via calc chain: target ≤ ... ≤ Σ_Fin tan(B_k)
    let S := (Finset.univ : Finset (Fin n)).filter (fun k => (n + 1) / 2 ≤ k.val)
    calc (1 : ℝ) / (2 * Real.pi) * ((↑n : ℝ) * Real.log ((↑n : ℝ) + 1))
        -- Step E: factor and apply log comparison
        = (↑n / Real.pi) * ((1 : ℝ) / 2 * Real.log ((↑n : ℝ) + 1)) := by ring
      _ ≤ (↑n / Real.pi) * Real.log ((↑(n / 2) : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hLogComp (by positivity)
        -- Step D: rewrite and apply harmonic bound
      _ = (2 * ↑n / Real.pi) * ((1 : ℝ) / 2 * Real.log ((↑(n / 2) : ℝ) + 1)) := by ring
      _ ≤ (2 * ↑n / Real.pi) * ∑ j ∈ Finset.range (n / 2), 1 / (2 * ↑j + 1) :=
          mul_le_mul_of_nonneg_left hHarmonic (by positivity)
        -- Factor into sum
      _ = ∑ j ∈ Finset.range (n / 2), 2 * ↑n / (Real.pi * (2 * ↑j + 1)) := by
          rw [Finset.mul_sum]; congr 1; ext j; ring
        -- Step C: Reindex j ↦ ⟨n-1-j,...⟩ mapping range(n/2) → filtered Fin n
      _ = ∑ k ∈ S, 2 * ↑n / (Real.pi * (2 * ((↑n : ℝ) - ↑k.val) - 1)) := by
          symm
          apply Finset.sum_nbij (fun (k : Fin n) => n - 1 - k.val)
          · -- Maps S → range(n/2)
            intro k hk
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hk
            simp only [Finset.mem_range]; omega
          · -- Injective on S
            intro a ha b hb hab
            exact Fin.ext (by omega)
          · -- Surjective onto range(n/2)
            intro j hj
            simp only [Finset.mem_range] at hj
            exact ⟨⟨n - 1 - j, by omega⟩,
              by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]; omega,
              by omega⟩
          · -- Values match: 2n/(π(2(n-k)-1)) at k = 2n/(π(2j+1)) at j = n-1-k
            intro k hk
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hk
            congr 1; congr 1
            have hle : k.val ≤ n := by omega
            rw [show (n - 1 - k.val : ℕ) = n - k.val - 1 from by omega,
                show (↑n : ℝ) - ↑k.val = ↑(n - k.val) from
                  (Nat.cast_sub hle).symm,
                Nat.cast_sub (show 1 ≤ n - k.val from by omega)]
            push_cast; ring
        -- Step B: Apply cot bound to each term
      _ ≤ ∑ k ∈ S,
            Real.sin ((2 * ↑k.val + 1 : ℝ) * Real.pi / (4 * ↑n)) /
            Real.cos ((2 * ↑k.val + 1 : ℝ) * Real.pi / (4 * ↑n)) := by
          apply Finset.sum_le_sum
          intro k hk
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hk
          exact tan_half_angle_cot_lb n hn2 k hk
        -- Step A: Sub-sum ≤ full sum (dropped terms are nonneg)
      _ ≤ ∑ k : Fin n,
            Real.sin ((2 * ↑k.val + 1 : ℝ) * Real.pi / (4 * ↑n)) /
            Real.cos ((2 * ↑k.val + 1 : ℝ) * Real.pi / (4 * ↑n)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun k _ _ => tan_half_angle_nonneg n (by omega) k)

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
  sorry  -- S_n ≥ C₂ · n · log(n+1) via Lipschitz bound + harmonic series

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
