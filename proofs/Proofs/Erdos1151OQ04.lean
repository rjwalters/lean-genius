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

/-- For the x = -1 case: the trigonometric Lebesgue sum S_n = Σ tan(φₖ/2) grows like n log n.

    **Proof sketch (for a future session)**:
    Step 1: Rewrite using `Finset.sum_congr` + `sum_term_eq_tan_half_angle`:
      S_n = Σₖ tan((2k+1)π/(4n)) = Σₖ sin((2k+1)π/(4n)) / cos((2k+1)π/(4n))

    Step 2: Take the sub-sum over k = n-m,...,n-1 (last m terms, where m = ⌊√(n+1)⌋):
      For j = n-1-k = 0,...,m-1: tan(φₖ/2) = cot((2j+1)π/(4n)) [since φₖ/2 = π/2-(2j+1)π/(4n)]
      The complementary angle (2j+1)π/(4n) ≤ (2m-1)π/(4n) ≤ mπ/(2n) ≤ π/3 for m ≤ 2n/3

    Step 3: Apply `cot_ge_inv_two_mul` to each sub-sum term:
      cot((2j+1)π/(4n)) ≥ 2n / (π(2j+1))

    Step 4: Bound the odd harmonic sum:
      Σⱼ₌₀^{m-1} 1/(2j+1) ≥ (1/2) Σⱼ₌₁^m 1/j = (1/2) Hₘ ≥ (1/2) log(m+1)
      [by comparison 1/(2j+1) ≥ 1/(2j+2) and `log_add_one_le_harmonic`]

    Step 5: Combine: S_n ≥ (2n/π)(1/2)log(m+1) = (n/π)log(m+1)
      With m ≥ ⌊√(n+1)⌋: log(m+1) ≥ (1/2)log(n+1) so S_n ≥ (n/(2π))log(n+1) ✓

    Main implementation challenge: index arithmetic for the sub-sum bijection k ↔ j in Finset. -/
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
  -- Shorthand for the half-angle θₖ = (2k+1)π/(4n)
  set θ : Fin n → ℝ := fun k => (2 * k.val + 1 : ℝ) * Real.pi / (4 * n)
  -- Step 2: Bijection shows ∑ tan(θₖ) = ∑ cot(θₖ)  via involution k ↦ n-1-k
  -- Key: (2*(n-1-k)+1)π/(4n) = π/2 - θₖ, so cot of that = tan(θₖ)
  have hS_cot :
      ∑ k : Fin n, Real.sin (θ k) / Real.cos (θ k) =
      ∑ k : Fin n, Real.cos (θ k) / Real.sin (θ k) := by
    -- The involution k ↦ n-1-k on Fin n
    let invol : Fin n ≃ Fin n := {
      toFun := fun k => ⟨n - 1 - k.val, by omega⟩
      invFun := fun k => ⟨n - 1 - k.val, by omega⟩
      left_inv := fun k => by ext; simp only [Fin.coe_mk]; omega
      right_inv := fun k => by ext; simp only [Fin.coe_mk]; omega }
    -- The cot-sum under invol equals itself (bijection)
    have hinvol_sum : ∑ k : Fin n, (Real.cos (θ (invol k)) / Real.sin (θ (invol k))) =
                      ∑ k : Fin n, Real.cos (θ k) / Real.sin (θ k) :=
      Equiv.sum_comp invol (fun k => Real.cos (θ k) / Real.sin (θ k))
    -- Each tan(θₖ) = cot(θ_{invol k}): complementary angle argument
    have hfg : ∀ k : Fin n,
        Real.sin (θ k) / Real.cos (θ k) =
        Real.cos (θ (invol k)) / Real.sin (θ (invol k)) := by
      intro k
      -- θ (invol k) = π/2 - θ k  [since (2(n-1-k)+1)π/(4n) = π/2 - (2k+1)π/(4n)]
      have hkle : k.val ≤ n - 1 := Nat.lt_succ_iff.mp k.isLt
      have hcast : ((n - 1 - k.val : ℕ) : ℝ) = (n : ℝ) - 1 - (k.val : ℝ) := by
        rw [Nat.cast_sub hkle, Nat.cast_sub hn]
      have hθinvol : θ (invol k) = Real.pi / 2 - θ k := by
        simp only [θ, invol, Equiv.coe_fn_mk, Fin.coe_mk]
        rw [hcast]
        have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
        field_simp
        ring
      rw [hθinvol, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
    rw [Finset.sum_congr rfl (fun k _ => hfg k), hinvol_sum]
  -- Step 3: From ∑ tan = ∑ cot, derive 2S = ∑ tan + ∑ cot = ∑ 2/sin(2θₖ)
  -- so S = ∑ 1/sin((2k+1)π/(2n))
  have hsin2_pos : ∀ k : Fin n, 0 < Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) := by
    intro k
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · have hlt : 2 * k.val + 1 < 2 * n := by omega
      have hlt' : (2 * k.val + 1 : ℝ) < 2 * n := by exact_mod_cast hlt
      have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      rw [div_lt_iff (by positivity)]
      nlinarith [Real.pi_pos]
  have hsin_pos : ∀ k : Fin n, 0 < Real.sin (θ k) := by
    intro k
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · have ⟨_, hφ_lt⟩ := chebyshevAngle_pos_lt_pi n hn k
      simp only [θ]; linarith [Real.pi_pos]
  have hcos_pos : ∀ k : Fin n, 0 < Real.cos (θ k) := by
    intro k
    apply Real.cos_pos_of_mem_Ioo
    simp only [θ]
    constructor
    · linarith [Real.pi_pos]
    · have hlt : 2 * k.val + 1 < 2 * n := by omega
      have hlt' : (2 * k.val + 1 : ℝ) < 2 * n := by exact_mod_cast hlt
      have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      rw [div_lt_div_iff (by positivity) (by positivity)]
      nlinarith [Real.pi_pos]
  -- sin(2θₖ) = (2k+1)π/(2n): the double-angle connection
  have hsin2_eq : ∀ k : Fin n,
      Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) =
      2 * Real.sin (θ k) * Real.cos (θ k) := by
    intro k
    have key := Real.sin_two_mul (θ k)
    simp only [θ] at key ⊢
    have harg : 2 * ((2 * k.val + 1 : ℝ) * Real.pi / (4 * n)) =
                (2 * k.val + 1 : ℝ) * Real.pi / (2 * n) := by ring
    rw [harg] at key; exact key
  -- S = ∑ 1/sin((2k+1)π/(2n)): from 2S = ∑ tan + ∑ cot = ∑ 2/sin(2θ)
  have hS_inv_sin :
      ∑ k : Fin n, Real.sin (θ k) / Real.cos (θ k) =
      ∑ k : Fin n, 1 / Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) := by
    -- 2S = S + S = ∑ tan + ∑ cot = ∑ (tan + cot) = ∑ 2/(sin·cos/cos·sin) ... simplified:
    -- tan(x) + cot(x) = sin/cos + cos/sin = (sin² + cos²)/(sin·cos) = 1/(sin·cos)
    -- And 1/(sin·cos) = 2/sin(2x), so 2S = ∑ 2/sin(2θ), S = ∑ 1/sin(2θ)
    have h2S : 2 * ∑ k : Fin n, Real.sin (θ k) / Real.cos (θ k) =
               ∑ k : Fin n, 2 / Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) := by
      -- For each k: tan(θk) + cot(θk) = 2/sin(2θk) by double-angle formula
      have step : ∀ k : Fin n,
          Real.sin (θ k) / Real.cos (θ k) + Real.cos (θ k) / Real.sin (θ k) =
          2 / Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) := by
        intro k
        have hs := (hsin_pos k).ne'
        have hc := (hcos_pos k).ne'
        rw [hsin2_eq k]; field_simp [hs, hc]; ring
      -- 2 * ∑ tan = ∑ tan + ∑ cot (via hS_cot) = ∑ (tan + cot)
      have heq1 : 2 * ∑ k : Fin n, Real.sin (θ k) / Real.cos (θ k) =
                  ∑ k : Fin n, Real.sin (θ k) / Real.cos (θ k) +
                  ∑ k : Fin n, Real.cos (θ k) / Real.sin (θ k) := by
        linarith [hS_cot]
      rw [heq1, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun k _ => step k)
    -- From h2S and 2*(∑ 1/sin) = ∑ 2/sin, deduce S = ∑ 1/sin by linear arithmetic
    have h2S_rw : 2 * ∑ k : Fin n, 1 / Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) =
                  ∑ k : Fin n, 2 / Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) := by
      rw [Finset.mul_sum]; congr 1; ext k; ring
    linarith [h2S, h2S_rw]
  -- Step 4: Bound 1/sin(x) ≥ 1/x ≥ 2n/(π(2k+1)) using sin(x) ≤ x
  have hS_harm :
      ∑ k : Fin n, (2 * n : ℝ) / (Real.pi * (2 * k.val + 1)) ≤
      ∑ k : Fin n, Real.sin (θ k) / Real.cos (θ k) := by
    rw [hS_inv_sin]
    apply Finset.sum_le_sum
    intro k _
    rw [div_le_div_iff (by positivity) (hsin2_pos k)]
    -- Goal: 2n * sin((2k+1)π/(2n)) ≤ π * (2k+1)
    -- Since sin(x) ≤ x: sin((2k+1)π/(2n)) ≤ (2k+1)π/(2n)
    have hx_pos : 0 < (2 * k.val + 1 : ℝ) * Real.pi / (2 * n) := by positivity
    have hsin_le : Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) ≤
                   (2 * k.val + 1 : ℝ) * Real.pi / (2 * n) :=
      (Real.sin_lt hx_pos).le
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    calc (2 * n : ℝ) * Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n))
        ≤ 2 * n * ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) :=
          mul_le_mul_of_nonneg_left hsin_le (by positivity)
      _ = Real.pi * (2 * k.val + 1 : ℝ) := by field_simp; ring
  -- Step 5: Odd harmonic sum ≥ (1/2) log(n+1) via comparison with standard harmonic
  -- and log_add_one_le_harmonic
  have hS_log_lb : 1 / (2 * Real.pi) * ((n : ℝ) * Real.log ((n : ℝ) + 1)) ≤
                   ∑ k : Fin n, (2 * n : ℝ) / (Real.pi * (2 * k.val + 1)) := by
    rw [div_mul_eq_mul_div, le_div_iff (by positivity : (0 : ℝ) < 2 * Real.pi)]
    -- Goal: n * log(n+1) ≤ (2π) * ∑ 2n/(π(2k+1))
    -- = 4n * ∑ 1/(2k+1) ≥ 4n * (1/2) * ∑ 1/(k+1) = 2n * harmonic n ≥ 2n * log(n+1)
    -- Hmm: need n * log(n+1) ≤ (2π) * ∑ 2n/(π(2k+1)) = 4n * ∑ 1/(2k+1)
    -- And ∑ 1/(2k+1) ≥ (1/2) harmonic n ≥ (1/2) log(n+1)
    -- So 4n * ∑ 1/(2k+1) ≥ 4n * (1/2) * log(n+1) = 2n * log(n+1) ≥ n * log(n+1). ✓
    have hpi_pos := Real.pi_pos
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    -- ∑ 1/(2k+1) ≥ (1/2) * harmonic n ≥ (1/2) * log(n+1)
    have hodd_harm_lb : (1 : ℝ) / 2 * (harmonic n : ℝ) ≤
                        ∑ k : Fin n, (1 : ℝ) / (2 * k.val + 1) := by
      -- Step A: expand harmonic n as ∑_{k : Fin n} 1/(k+1) in ℝ
      -- Prove in ℚ first (no cast ambiguity), then lift via exact_mod_cast
      have h_harm_eq : (harmonic n : ℝ) = ∑ k : Fin n, (1 : ℝ) / ((k.val : ℝ) + 1) := by
        have hq : harmonic n = ∑ k : Fin n, (1 : ℚ) / ((k.val : ℚ) + 1) := by
          simp only [harmonic, ← Finset.sum_fin_eq_sum_range]
          congr 1; ext k; push_cast; ring
        exact_mod_cast hq
      -- Step B: each term 1/(2k+1) ≥ (1/2)/(k+1)
      have h_term : ∀ k : Fin n,
          (1 : ℝ) / 2 * (1 / ((k.val : ℝ) + 1)) ≤ 1 / (2 * (k.val : ℝ) + 1) := by
        intro k
        rw [mul_one_div, div_le_div_iff (by positivity) (by positivity)]
        linarith
      -- Combine
      calc (1 : ℝ) / 2 * (harmonic n : ℝ)
          = 1 / 2 * ∑ k : Fin n, 1 / ((k.val : ℝ) + 1) := by rw [h_harm_eq]
        _ = ∑ k : Fin n, 1 / 2 * (1 / ((k.val : ℝ) + 1)) := by rw [Finset.mul_sum]
        _ ≤ ∑ k : Fin n, 1 / (2 * (k.val : ℝ) + 1) :=
              Finset.sum_le_sum (fun k _ => h_term k)
    have hlog_harm := log_add_one_le_harmonic n
    -- Combine: n * log(n+1) ≤ 2n * log(n+1) ≤ 4n * (1/2) * harmonic n ≤ 4n * ∑ 1/(2k+1)
    -- = (2π) * ∑ 2n/(π(2k+1))
    have hrhs : (2 * Real.pi) * ∑ k : Fin n, (2 * n : ℝ) / (Real.pi * (2 * k.val + 1)) =
                4 * n * ∑ k : Fin n, (1 : ℝ) / (2 * k.val + 1) := by
      rw [Finset.mul_sum]; congr 1; ext k; field_simp; ring
    rw [hrhs]
    have hlog_le : Real.log ((n : ℝ) + 1) ≤ (harmonic n : ℝ) := by exact_mod_cast hlog_harm
    calc (n : ℝ) * Real.log ((n : ℝ) + 1)
        ≤ n * (harmonic n : ℝ) :=
          mul_le_mul_of_nonneg_left hlog_le hn_pos.le
      _ ≤ n * (2 * ∑ k : Fin n, (1 : ℝ) / (2 * k.val + 1)) := by
          apply mul_le_mul_of_nonneg_left _ hn_pos.le
          linarith [hodd_harm_lb]
      _ ≤ 4 * n * ∑ k : Fin n, (1 : ℝ) / (2 * k.val + 1) := by
          have hsum_nn : 0 ≤ ∑ k : Fin n, (1 : ℝ) / (2 * k.val + 1) :=
            Finset.sum_nonneg fun k _ => by positivity
          nlinarith
  linarith [hS_harm]

/-! ## Key Lemmas with Sorry -/

/-- cos(πp/q) ≠ 1 when p is odd and q > 0.

    Proof: By `Real.cos_eq_one_iff`, cos(θ) = 1 iff θ = 2nπ for some n : ℤ.
    If πp/q = 2nπ then p = 2nq (clearing π and q), making p even — contradicting Odd p. -/
private lemma cos_pi_mul_odd_ne_one (p q : ℕ) (hp : Odd p) (hq_pos : 0 < q) :
    Real.cos ((↑p : ℝ) * Real.pi / (↑q : ℝ)) ≠ 1 := by
  intro heq
  rw [Real.cos_eq_one_iff] at heq
  obtain ⟨n, hn⟩ := heq
  -- hn : (↑n : ℝ) * (2 * π) = ↑p * π / ↑q
  have hpi_ne : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hq_ne : (↑q : ℝ) ≠ 0 := (Nat.cast_pos.mpr hq_pos).ne'
  -- Derive p = 2nq as reals (multiply both sides of hn by q/π)
  have hreal : (↑p : ℝ) = 2 * (↑n : ℝ) * (↑q : ℝ) := by
    field_simp [hpi_ne, hq_ne] at hn; linarith
  -- Lift to ℤ: (p : ℤ) = 2 * n * q
  have hpq_int : (↑p : ℤ) = 2 * n * (↑q : ℤ) := by exact_mod_cast hreal
  -- Odd p gives p = 2*m + 1, contradicting 2 | p
  obtain ⟨m, hm⟩ := hp
  have hmcast : (↑p : ℤ) = 2 * (↑m : ℤ) + 1 := by exact_mod_cast hm
  omega  -- 2*n*q = 2*m+1 is impossible (different parities mod 2)

/-- **[SORRY] Harmonic sum lower bound for Chebyshev trig sum.**

    For x = cos(πp/q) with p, q odd, the trigonometric Lebesgue sum
    S_n = Σₖ sin(φₖ)/|x - cos φₖ| grows at least as fast as n · log(n+1).

    **Proof by cases on x = -1 vs x ∈ (-1, 1)**:

    **Case 1: x = -1** (p/q is an odd integer, e.g., p = q = 1):
    - Delegates to `trig_sum_lb_of_cos_eq_neg_one`; C₂ = 1/(2π).

    **Case 2: x ∈ (-1, 1)** (sin(πp/q) ≠ 0, since x ≠ ±1):
    - Let s = |sin(πp/q)| > 0, θ = πp/q, and let k₀ be the nearest node to θ.
    - Lipschitz: |x - cos φₖ| = |cos θ - cos φₖ| ≤ |θ - φₖ| (cos is 1-Lipschitz)
    - For k = k₀ + j with |j| ≤ ns/(2π): sin(φₖ) ≥ s/2 (continuity) and
        |θ - φₖ| ≤ (|j|+1)·π/n, so sin(φₖ)/|x - cos φₖ| ≥ sn/(2π(|j|+1))
    - Harmonic sum: Σⱼ₌₁^m 1/(j+1) ≥ log(m+2) - 1, giving S_n ≥ (sn/(2π))·log(m+2)
    - With m = ⌊ns/(2π)⌋: log(m+2) ≥ (1/2)·log(n+1) for n ≥ N(s)
    - Take C₂ = s²/(8π²). (Note x ≠ 1 is proved by `cos_pi_mul_odd_ne_one`) -/
private lemma chebyshev_trig_sum_lb (p q : ℕ) (hp : Odd p) (hq : Odd q) (hq_pos : 0 < q) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ n : ℕ, 1 ≤ n →
      C₂ * ((↑n : ℝ) * Real.log ((↑n : ℝ) + 1)) ≤
        ∑ k : Fin n, Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) /
                     |Real.cos ((↑p : ℝ) * Real.pi / ↑q) - chebyshevNode n k| := by
  -- x ≠ 1: from Odd p (p = 2nq would be even)
  have hx_ne_one : Real.cos ((↑p : ℝ) * Real.pi / ↑q) ≠ 1 :=
    cos_pi_mul_odd_ne_one p q hp hq_pos
  -- Case split: x = -1 or x ∈ (-1, 1)
  by_cases hx : Real.cos ((↑p : ℝ) * Real.pi / ↑q) = -1
  · -- **Case x = -1**: sum equals Σₖ sin(φₖ)/(1+cos φₖ) = Σₖ tan(φₖ/2)
    refine ⟨1 / (2 * Real.pi), by positivity, fun n hn => ?_⟩
    -- Rewrite each sum term: substitute hx and unfold chebyshevNode
    have hsum_eq :
        ∑ k : Fin n, Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * ↑n)) /
          |Real.cos ((↑p : ℝ) * Real.pi / ↑q) - chebyshevNode n k| =
        ∑ k : Fin n, Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * ↑n)) /
          |(-1 : ℝ) - Real.cos ((2 * k.val + 1 : ℝ) * Real.pi / (2 * ↑n))| :=
      Finset.sum_congr rfl fun k _ => by simp only [hx, chebyshevNode]
    rw [hsum_eq]
    exact trig_sum_lb_of_cos_eq_neg_one n hn
  · -- **Case x ∈ (-1, 1)**: sin(πp/q)² > 0 since x ≠ ±1
    have hx_gt : -1 < Real.cos ((↑p : ℝ) * Real.pi / ↑q) :=
      lt_of_le_of_ne (Real.neg_one_le_cos _) (Ne.symm hx)
    have hx_lt : Real.cos ((↑p : ℝ) * Real.pi / ↑q) < 1 :=
      lt_of_le_of_ne (Real.cos_le_one _) hx_ne_one
    have hsin_sq_pos : 0 < Real.sin ((↑p : ℝ) * Real.pi / ↑q) ^ 2 := by
      have hcos_sq_lt : Real.cos ((↑p : ℝ) * Real.pi / ↑q) ^ 2 < 1 := by nlinarith
      have := Real.sin_sq_add_cos_sq ((↑p : ℝ) * Real.pi / ↑q)
      nlinarith
    -- C₂ = sin²(πp/q) / (8π²) > 0
    refine ⟨Real.sin ((↑p : ℝ) * Real.pi / ↑q) ^ 2 / (8 * Real.pi ^ 2),
            by positivity, fun n hn => ?_⟩
    -- Proof by Lipschitz + nearest-node + harmonic sum (see docstring above)
    sorry

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
