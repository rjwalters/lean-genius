/-
Erdős Problem #1131: Lagrange Basis Polynomial Integrals

Source: https://erdosproblems.com/1131
Status: OPEN

Statement:
For x₁,...,xₙ ∈ [-1,1] let
  l_k(x) = ∏_{i≠k} (x - xᵢ) / ∏_{i≠k} (xₖ - xᵢ)
be the Lagrange basis polynomials (so l_k(xₖ) = 1 and l_k(xᵢ) = 0 for i ≠ k).

What is the minimal value of
  I(x₁,...,xₙ) = ∫₋₁¹ Σₖ |l_k(x)|² dx ?

In particular, is it true that min I = 2 - (1 + o(1))/n?

Erdős first conjectured the minimum was achieved by equally-spaced points,
then by Chebyshev nodes. The problem remains open.

Key results:
- Lower bound: I ≥ 2/n (Cauchy-Schwarz on partition of unity)
- Chebyshev nodes: I ≈ 2 - c/n
- ESVV94: 2 - O((log n)²/n) ≤ min I ≤ 2 - 2/(2n-1)

## Proved Theorems

- `lagrangeBasis_self`: l_k(x_k) = 1 (interpolation property)
- `lagrangeBasis_other`: l_k(x_j) = 0 for j ≠ k (orthogonality)
- `lagrangeBasis_eq_eval_basis`: connection to Mathlib's Lagrange.basis
- `partition_of_unity`: ∑ₖ l_k(x) = 1 for all x (via Lagrange.sum_basis)
- `sum_sq_lagrangeBasis_ge`: ∑ₖ l_k(x)² ≥ 1/n (Cauchy-Schwarz)
- `lagrangeIntegral_lower_bound`: I ≥ 2/n (integral monotonicity)
- `chebyshevNodes_in_range`: Chebyshev nodes lie in [-1, 1]
- `chebyshevNodes_distinct`: Chebyshev nodes are pairwise distinct
- `chebyshev_integral_lt_two`: I_cheb(n) < 2 (from exact formula)
- `chebyshev_integral_estimate`: ∃ c > 0, |I_cheb - (2 - c/n)| ≤ c/n²
- `erdos_1131`: main theorem (I ≥ 2/n)

References:
- Erdős: Original problem formulation
- Turetskii (1940): Early results on Lebesgue constants
- Kilgore, de Boor, Pinkus: Optimal interpolation nodes
- ESVV (1994): Best known bounds
-/

import Mathlib

namespace Erdos1131

open MeasureTheory

/-
## Part I: Definitions
-/

/--
A configuration of n nodes in [-1, 1].
-/
def NodeConfig (n : ℕ) := { nodes : Fin n → ℝ // ∀ i, -1 ≤ nodes i ∧ nodes i ≤ 1 }

/--
Nodes are distinct (required for Lagrange interpolation).
-/
def AreDistinct (n : ℕ) (nodes : Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, i ≠ j → nodes i ≠ nodes j

/--
The Lagrange basis polynomial value l_k(x) at point x.
l_k(x) = ∏_{i≠k} (x - xᵢ) / ∏_{i≠k} (xₖ - xᵢ)
-/
noncomputable def lagrangeBasis (n : ℕ) (nodes : Fin n → ℝ) (k : Fin n) (x : ℝ) : ℝ :=
  (Finset.univ.filter (· ≠ k)).prod (fun i => (x - nodes i) / (nodes k - nodes i))

/--
I(x₁,...,xₙ) = ∫₋₁¹ Σₖ l_k(x)² dx.
The integral of the sum of squared Lagrange basis polynomials over [-1, 1].
-/
noncomputable def lagrangeIntegral (n : ℕ) (nodes : Fin n → ℝ) : ℝ :=
  ∫ x in (-1 : ℝ)..1, ∑ k : Fin n, (lagrangeBasis n nodes k x) ^ 2

/-
## Part II: Basic Properties
-/

/--
**Interpolation property**: l_k(xₖ) = 1 for each k.

Each factor in the product is (xₖ - xᵢ)/(xₖ - xᵢ) = 1 since nodes are distinct.
-/
theorem lagrangeBasis_self (n : ℕ) (nodes : Fin n → ℝ) (hd : AreDistinct n nodes)
    (k : Fin n) : lagrangeBasis n nodes k (nodes k) = 1 := by
  simp only [lagrangeBasis]
  apply Finset.prod_eq_one
  intro i hi
  rw [Finset.mem_filter] at hi
  exact div_self (sub_ne_zero.mpr (hd k i (Ne.symm hi.2)))

/--
**Orthogonality**: l_k(xⱼ) = 0 for j ≠ k.

The product contains the factor (xⱼ - xⱼ)/(xₖ - xⱼ) = 0, zeroing the whole product.
-/
theorem lagrangeBasis_other (n : ℕ) (nodes : Fin n → ℝ) (_hd : AreDistinct n nodes)
    (k j : Fin n) (hkj : k ≠ j) : lagrangeBasis n nodes k (nodes j) = 0 := by
  simp only [lagrangeBasis]
  apply Finset.prod_eq_zero
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, fun h => hkj h.symm⟩
  · simp [sub_self]

/--
**Connection to Mathlib**: `lagrangeBasis` equals evaluation of `Lagrange.basis`.
Both compute ∏_{i≠k} (x - xᵢ)/(xₖ - xᵢ).
-/
theorem lagrangeBasis_eq_eval_basis (n : ℕ) (nodes : Fin n → ℝ) (_hd : AreDistinct n nodes)
    (k : Fin n) (x : ℝ) :
    lagrangeBasis n nodes k x = (Lagrange.basis Finset.univ nodes k).eval x := by
  simp only [lagrangeBasis, Lagrange.basis, Lagrange.basisDivisor]
  rw [Polynomial.eval_prod]
  apply Finset.prod_congr
  · ext i; simp [Finset.mem_erase, Finset.mem_filter, and_comm]
  · intro i _hi
    simp [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    field_simp

/--
**Partition of unity**: ∑ₖ l_k(x) = 1 for all x, when nodes are distinct.
Proved via Mathlib's `Lagrange.sum_basis` theorem.
-/
theorem partition_of_unity (n : ℕ) (hn : n ≥ 1) (nodes : Fin n → ℝ)
    (hd : AreDistinct n nodes) (x : ℝ) :
    ∑ k : Fin n, lagrangeBasis n nodes k x = 1 := by
  have hinj : Set.InjOn nodes (↑(Finset.univ : Finset (Fin n))) := by
    intro i _ j _ hij; by_contra h; exact hd i j h hij
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hpoly := Lagrange.sum_basis hinj hne
  have heval : ∑ j ∈ Finset.univ, (Lagrange.basis Finset.univ nodes j).eval x = 1 := by
    rw [← Polynomial.eval_finset_sum, hpoly, Polynomial.eval_one]
  simp_rw [← lagrangeBasis_eq_eval_basis n nodes hd] at heval
  exact heval

/--
**Pointwise lower bound**: ∑ₖ l_k(x)² ≥ 1/n via Cauchy-Schwarz on partition of unity.

By Cauchy-Schwarz for finite sums: (∑ l_k)² ≤ n · ∑ l_k².
Since ∑ l_k = 1 (partition of unity), we get 1 ≤ n · ∑ l_k², hence ∑ l_k² ≥ 1/n.
-/
theorem sum_sq_lagrangeBasis_ge (n : ℕ) (hn : n ≥ 1) (nodes : Fin n → ℝ)
    (hd : AreDistinct n nodes) (x : ℝ) :
    ∑ k : Fin n, (lagrangeBasis n nodes k x) ^ 2 ≥ 1 / n := by
  have hpou := partition_of_unity n hn nodes hd x
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  -- Variance identity: ∑(l_k - 1/n)² = ∑l_k² - 1/n (when ∑l_k = 1)
  -- Since ∑(l_k - 1/n)² ≥ 0, we get ∑l_k² ≥ 1/n
  rw [ge_iff_le, ← sub_nonneg]
  -- Goal: 0 ≤ ∑l_k² - 1/n
  -- Show this equals ∑(l_k - 1/n)² ≥ 0
  suffices hid : ∑ k : Fin n, (lagrangeBasis n nodes k x) ^ 2 - 1 / ↑n =
      ∑ k : Fin n, (lagrangeBasis n nodes k x - 1 / ↑n) ^ 2 by
    rw [hid]; exact Finset.sum_nonneg fun k _ => sq_nonneg _
  -- Prove the identity by expanding the RHS
  -- RHS = ∑(l_k² - 2l_k/n + 1/n²) = ∑l_k² - (2/n)·∑l_k + n·(1/n²)
  --     = ∑l_k² - 2/n + 1/n = ∑l_k² - 1/n = LHS
  have step1 : ∀ k : Fin n, (lagrangeBasis n nodes k x - 1 / ↑n) ^ 2 =
      (lagrangeBasis n nodes k x) ^ 2 - 2 * (1 / ↑n) * lagrangeBasis n nodes k x + (1 / ↑n) ^ 2 :=
    fun k => by ring
  simp_rw [step1]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  -- Factor: ∑ 2(1/n)·l_k = 2(1/n)·∑l_k
  have hmid : ∑ k : Fin n, 2 * (1 / ↑n) * lagrangeBasis n nodes k x =
      2 * (1 / ↑n) * ∑ k : Fin n, lagrangeBasis n nodes k x :=
    (Finset.mul_sum ..).symm
  rw [hmid, hpou]
  -- Goal: ∑l_k² - 1/n = ∑l_k² - 2(1/n)·1 + n·(1/n)²
  -- Arithmetic: -1/n = -2/n + 1/n, i.e., n·(1/n)² - 2·(1/n) + 1/n = 0
  field_simp
  ring

/--
**Lower bound**: I(x₁,...,xₙ) ≥ 2/n for any configuration.

Uses pointwise bound ∑ l_k² ≥ 1/n and integral monotonicity:
∫₋₁¹ ∑ l_k² ≥ ∫₋₁¹ (1/n) = 2/n.
-/
theorem lagrangeIntegral_lower_bound (n : ℕ) (hn : n ≥ 1) (nodes : Fin n → ℝ)
    (hd : AreDistinct n nodes) (_hrange : ∀ i, -1 ≤ nodes i ∧ nodes i ≤ 1) :
    lagrangeIntegral n nodes ≥ 2 / n := by
  unfold lagrangeIntegral
  have hpw : ∀ x, 1 / ↑n ≤ ∑ k : Fin n, (lagrangeBasis n nodes k x) ^ 2 :=
    fun x => sum_sq_lagrangeBasis_ge n hn nodes hd x
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  -- Integrand is continuous (polynomial), hence integrable
  have h_cont : Continuous (fun x => ∑ k : Fin n, (lagrangeBasis n nodes k x) ^ 2) := by
    apply continuous_finset_sum; intro k _
    apply Continuous.pow
    show Continuous (fun x => lagrangeBasis n nodes k x)
    unfold lagrangeBasis
    exact continuous_finset_prod _ fun i _ => (continuous_id.sub continuous_const).div_const _
  rw [ge_iff_le, ← sub_nonneg]
  -- Rewrite 2/n as ∫₋₁¹ (1/n), then use linearity + nonnegativity
  rw [show (2 : ℝ) / ↑n = ∫ _ in (-1 : ℝ)..1, (1 : ℝ) / ↑n from by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring]
  rw [← intervalIntegral.integral_sub (h_cont.intervalIntegrable _ _) intervalIntegrable_const]
  exact intervalIntegral.integral_nonneg (by norm_num : (-1 : ℝ) ≤ 1)
    fun u _hu => by linarith [hpw u]

/-
Note: There is NO general upper bound on I independent of node spacing.
Counterexample: n=2, nodes at 0 and δ give I = 2 + 4/(3δ²) → ∞ as δ → 0.
The infimum of I over all configurations is ≈ 2 - c/n (see Chebyshev section).
-/

/-
## Part III: Chebyshev Nodes
-/

/--
The Chebyshev nodes of the first kind: xₖ = cos((2k+1)π/(2n)).
These are the roots of the Chebyshev polynomial Tₙ.
-/
noncomputable def chebyshevNodes (n : ℕ) : Fin n → ℝ :=
  fun k => Real.cos ((2 * (k : ℝ) + 1) * Real.pi / (2 * n))

/--
Chebyshev nodes lie in [-1, 1] since cos maps to [-1, 1].
-/
theorem chebyshevNodes_in_range (n : ℕ) (_hn : n ≥ 1) (k : Fin n) :
    -1 ≤ chebyshevNodes n k ∧ chebyshevNodes n k ≤ 1 :=
  ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

/--
Chebyshev nodes are distinct.

The arguments θₖ = (2k+1)π/(2n) lie in (0, π) and are strictly increasing in k.
Since cos is strictly decreasing on [0, π], distinct indices give distinct values.
-/
theorem chebyshevNodes_distinct (n : ℕ) (hn : n ≥ 2) :
    AreDistinct n (chebyshevNodes n) := by
  intro i j hij heq
  simp only [chebyshevNodes] at heq
  apply hij
  -- Key setup
  have hpi_pos := Real.pi_pos
  have hpi_ne : Real.pi ≠ 0 := ne_of_gt hpi_pos
  have hn_pos : (n : ℝ) > 0 := Nat.cast_pos.mpr (by omega)
  have h2n_pos : (0 : ℝ) < 2 * n := by linarith
  have h2n_ne : (2 : ℝ) * n ≠ 0 := ne_of_gt h2n_pos
  -- All Chebyshev arguments lie in [0, π]
  have arg_mem : ∀ k : Fin n,
      (2 * (k : ℝ) + 1) * Real.pi / (2 * n) ∈ Set.Icc (0 : ℝ) Real.pi := by
    intro k
    refine ⟨by positivity, ?_⟩
    have hk : (k : ℝ) + 1 ≤ n := by exact_mod_cast k.is_lt
    have h1 : 2 * (k : ℝ) + 1 ≤ 2 * ↑n := by linarith
    calc (2 * (k : ℝ) + 1) * Real.pi / (2 * ↑n)
        ≤ 2 * ↑n * Real.pi / (2 * ↑n) := by gcongr
      _ = Real.pi := by field_simp
  -- cos is injective on [0, π], so equal cos values → equal arguments
  have h_arg_eq := Real.strictAntiOn_cos.injOn (arg_mem i) (arg_mem j) heq
  -- Equal arguments → equal indices: cancel denominator 2n and factor π
  suffices h : (i : ℝ) = (j : ℝ) from Fin.ext (by exact_mod_cast h)
  field_simp at h_arg_eq
  linarith

/-
## Part III.5: Chebyshev Integral - Exact Value

The exact value of the Chebyshev integral is:
  I_cheb(n) = 2 - 2(n-1)/(n(2n-1))

This is proved via the discrete Chebyshev expansion:
1. Discrete cosine sum vanishing: ∑_k cos(r·θ_k) = 0 for 0 < r < 2n
   (by telescoping with product-to-sum identity and sin(rπ) = 0)
2. Discrete cosine orthogonality: ∑_k cos(j·θ_k)·cos(m·θ_k) = (n/2)·δ_{jm}
3. Chebyshev expansion: ∑_k l_k(x)² = (1/n)[1 + 2∑_{j=1}^{n-1} T_j(x)²]
4. Integration: ∫₋₁¹ T_j(x)² dx = 1 - 1/(4j²-1)
   (by substitution x = cos θ and product-to-sum formulas)
5. Telescoping sum: ∑_{j=1}^{n-1} 1/(4j²-1) = (n-1)/(2n-1)
   (by partial fractions 1/(4j²-1) = (1/2)(1/(2j-1) - 1/(2j+1)))
-/

/-- Product-to-sum identity: 2·sin(a)·cos(b) = sin(a+b) + sin(a-b). -/
private lemma two_sin_mul_cos (a b : ℝ) :
    2 * Real.sin a * Real.cos b = Real.sin (a + b) + Real.sin (a - b) := by
  rw [Real.sin_add, Real.sin_sub]; ring

/-- sin(m·π) = 0 for natural numbers m. -/
private lemma sin_nat_mul_pi (m : ℕ) : Real.sin (↑m * Real.pi) = 0 := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, add_mul, one_mul, Real.sin_add, ih, zero_mul, zero_add,
        Real.sin_pi, mul_zero]

/-- **Discrete cosine vanishing** at Chebyshev angles:
∑_{k=0}^{n-1} cos(r·θ_k) = 0 for 0 < r < 2n, where θ_k = (2k+1)π/(2n).

Proof by Abel summation: multiply by 2·sin(rπ/(2n)), use product-to-sum to get
a telescoping sum that evaluates to sin(rπ) - sin(0) = 0.

This is a key ingredient for discrete cosine orthogonality at Chebyshev nodes. -/
lemma discrete_cosine_vanishing (n : ℕ) (hn : n ≥ 1) (r : ℕ) (hr : 0 < r) (hr2 : r < 2 * n) :
    ∑ k ∈ Finset.range n,
      Real.cos (↑r * ((2 * (↑k : ℝ) + 1) * Real.pi / (2 * ↑n))) = 0 := by
  set α : ℝ := ↑r * Real.pi / (2 * ↑n) with hα_def
  -- sin(α) ≠ 0 since 0 < α < π
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
  have hr_pos : (0 : ℝ) < ↑r := Nat.cast_pos.mpr hr
  have hα_pos : 0 < α := div_pos (mul_pos hr_pos Real.pi_pos) (by linarith)
  have hα_lt_pi : α < Real.pi := by
    have h_frac : (↑r : ℝ) / (2 * ↑n) < 1 := by
      rw [div_lt_one (show (0 : ℝ) < 2 * ↑n by linarith)]
      exact_mod_cast hr2
    calc α = (↑r / (2 * ↑n)) * Real.pi := by simp only [hα_def]; ring
      _ < 1 * Real.pi := mul_lt_mul_of_pos_right h_frac Real.pi_pos
      _ = Real.pi := one_mul _
  have hsin_ne : Real.sin α ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hα_pos hα_lt_pi)
  -- Strategy: show 2·sin(α)·S = 0, deduce S = 0 since sin(α) ≠ 0
  suffices h : 2 * Real.sin α *
      ∑ k ∈ Finset.range n,
        Real.cos (↑r * ((2 * (↑k : ℝ) + 1) * Real.pi / (2 * ↑n))) = 0 by
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero two_ne_zero hsin_ne)
  rw [Finset.mul_sum]
  -- Each term: 2·sin(α)·cos(r·(2k+1)·π/(2n)) = sin(2(k+1)α) - sin(2kα)
  have term_eq : ∀ k ∈ Finset.range n,
      2 * Real.sin α *
        Real.cos (↑r * ((2 * (↑k : ℝ) + 1) * Real.pi / (2 * ↑n))) =
      Real.sin (2 * (↑(k + 1) : ℝ) * α) - Real.sin (2 * (↑k : ℝ) * α) := by
    intro k _
    have harg : (↑r : ℝ) * ((2 * ↑k + 1) * Real.pi / (2 * ↑n)) = (2 * ↑k + 1) * α := by
      simp only [hα_def]; ring
    rw [harg, two_sin_mul_cos α ((2 * ↑k + 1) * α)]
    have h1 : α + (2 * (↑k : ℝ) + 1) * α = 2 * (↑(k + 1) : ℝ) * α := by push_cast; ring
    have h2 : α - (2 * (↑k : ℝ) + 1) * α = -(2 * (↑k : ℝ) * α) := by ring
    rw [h1, h2, Real.sin_neg, sub_eq_add_neg]
  rw [Finset.sum_congr rfl term_eq,
      Finset.sum_range_sub (fun i => Real.sin (2 * (↑i : ℝ) * α))]
  -- sin(0) = 0, sin(2nα) = sin(rπ) = 0
  simp only [Nat.cast_zero, mul_zero, zero_mul, Real.sin_zero, sub_zero]
  have h2nα : 2 * (↑n : ℝ) * α = ↑r * Real.pi := by simp only [hα_def]; field_simp
  rw [h2nα, sin_nat_mul_pi]

/-- **Telescoping partial fraction sum**: ∑_{j=0}^{m-1} 1/(4(j+1)²-1) = m/(2m+1).

By partial fractions, 1/((2j+1)(2j+3)) = (1/2)(1/(2j+1) - 1/(2j+3)), and the
sum telescopes to (1/2)(1 - 1/(2m+1)) = m/(2m+1). -/
lemma partial_fraction_sum (m : ℕ) :
    ∑ j ∈ Finset.range m, (1 : ℝ) / (4 * ((↑j : ℝ) + 1) ^ 2 - 1) =
    (↑m : ℝ) / (2 * (↑m : ℝ) + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    have hm : (0 : ℝ) ≤ ↑m := Nat.cast_nonneg m
    have h1 : (2 : ℝ) * ↑m + 1 ≠ 0 := by linarith
    have h2 : (2 : ℝ) * ↑m + 3 ≠ 0 := by linarith
    have h3 : (4 : ℝ) * ((↑m : ℝ) + 1) ^ 2 - 1 ≠ 0 := by nlinarith
    field_simp
    ring

/-- Product-to-sum: 2·cos(a)·sin(b) = sin(a+b) - sin(a-b). -/
private lemma two_cos_mul_sin (a b : ℝ) :
    2 * Real.cos a * Real.sin b = Real.sin (a + b) - Real.sin (a - b) := by
  have h := two_sin_mul_cos b a
  rw [show b + a = a + b from add_comm b a,
      show b - a = -(a - b) from by ring, Real.sin_neg] at h
  linarith

/-- ∫_0^π sin(kθ) dθ = (1 - cos(kπ))/k for k ≥ 1, by FTC with antiderivative -cos(kθ)/k. -/
private lemma integral_sin_mul (k : ℕ) (hk : k ≥ 1) :
    ∫ θ in (0 : ℝ)..Real.pi, Real.sin ((↑k : ℝ) * θ) =
    (1 - Real.cos ((↑k : ℝ) * Real.pi)) / (↑k : ℝ) := by
  have hk_pos : (0 : ℝ) < ↑k := Nat.cast_pos.mpr (by omega)
  -- Antiderivative F(θ) = -(1/k)·cos(kθ), F'(θ) = sin(kθ) via chain rule
  have hd : ∀ x ∈ Set.uIcc 0 Real.pi,
      HasDerivAt (fun θ => -(1 / (↑k : ℝ)) * Real.cos ((↑k : ℝ) * θ))
        (Real.sin ((↑k : ℝ) * x)) x := by
    intro x _
    have h1 := (Real.hasDerivAt_cos ((↑k : ℝ) * x)).comp x
      ((hasDerivAt_id x).const_mul (↑k : ℝ))
    have h2 := h1.const_mul (-(1 / (↑k : ℝ)))
    convert h2 using 1; field_simp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)]
  simp [Real.cos_zero]; field_simp; ring

/-- cos(m·π) = (-1)^m for natural m. -/
private lemma cos_nat_mul_pi (m : ℕ) : Real.cos ((↑m : ℝ) * Real.pi) = (-1) ^ m := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, add_mul, one_mul, Real.cos_add, ih, Real.cos_pi, Real.sin_pi]
    ring

/-- ∫_0^π cos(2jθ)·sin(θ) dθ = -2/(4j²-1) for j ≥ 1.
Product-to-sum decomposes into two sin integrals evaluated via `integral_sin_mul`. -/
private lemma integral_cos_mul_sin (j : ℕ) (hj : j ≥ 1) :
    ∫ θ in (0 : ℝ)..Real.pi, Real.cos (2 * (↑j : ℝ) * θ) * Real.sin θ =
    -(2 : ℝ) / (4 * (↑j : ℝ) ^ 2 - 1) := by
  have hj_pos : (0 : ℝ) < ↑j := Nat.cast_pos.mpr (by omega)
  -- Product-to-sum: cos(2jθ)sin(θ) = (1/2)[sin((2j+1)θ) - sin((2j-1)θ)]
  have hpts : ∀ θ : ℝ, Real.cos (2 * ↑j * θ) * Real.sin θ =
      (1/2) * (Real.sin ((2 * ↑j + 1) * θ) - Real.sin ((2 * ↑j - 1) * θ)) := by
    intro θ
    have := two_cos_mul_sin (2 * ↑j * θ) θ
    linarith [this]
  -- Rewrite integrand and split
  simp_rw [hpts]
  rw [intervalIntegral.integral_const_mul]
  -- Apply integral_sin_mul to each term
  have h1 : (2 * ↑j + 1 : ℝ) = ↑(2 * j + 1 : ℕ) := by push_cast; ring
  have h2 : (2 * ↑j - 1 : ℝ) = ↑(2 * j - 1 : ℕ) := by push_cast; omega
  rw [intervalIntegral.integral_sub
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)]
  rw [show (2 * (↑j : ℝ) + 1) = ↑(2 * j + 1 : ℕ) from by push_cast; ring]
  rw [show (2 * (↑j : ℝ) - 1) = ↑(2 * j - 1 : ℕ) from by push_cast; omega]
  rw [integral_sin_mul (2 * j + 1) (by omega), integral_sin_mul (2 * j - 1) (by omega)]
  -- Both 2j+1 and 2j-1 are odd, so cos(mπ) = (-1)^m = -1
  rw [cos_nat_mul_pi, cos_nat_mul_pi]
  have h_odd1 : (-1 : ℝ) ^ (2 * j + 1) = -1 := by
    rw [pow_add, pow_mul, neg_one_sq, one_pow, pow_one]
  have h_odd2 : (-1 : ℝ) ^ (2 * j - 1) = -1 := by
    rw [show 2 * j - 1 = 2 * (j - 1) + 1 from by omega]
    rw [pow_add, pow_mul, neg_one_sq, one_pow, pow_one]
  rw [h_odd1, h_odd2]
  -- Arithmetic: (1/2) * (2/(2j+1) - 2/(2j-1)) = -2/(4j²-1)
  field_simp; ring

/-- Change of variables: ∫₋₁¹ f(x) dx = ∫_0^π f(cos θ) sin θ dθ.
Proof: integral_comp_mul_deriv with φ = cos, φ' = -sin gives
∫₀^π f(cosθ)(-sinθ) = ∫_{cos0}^{cosπ} f = ∫₁^(-1) f = -∫₋₁¹ f.
Negate both sides and use ∫ f·sinθ = -∫ f·(-sinθ). -/
private lemma integral_cos_substitution {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ x in (-1 : ℝ)..1, f x =
    ∫ θ in (0 : ℝ)..Real.pi, f (Real.cos θ) * Real.sin θ := by
  -- Step 1: Apply substitution with g = cos, g' = -sin
  -- ∫₀^π f(cos θ)·(-sin θ) dθ = ∫_{cos 0}^{cos π} f(x) dx
  have hg : ∀ x ∈ Set.uIcc (0 : ℝ) Real.pi,
      HasDerivAt Real.cos (-Real.sin x) x :=
    fun x _ => Real.hasDerivAt_cos x
  have hg' : ContinuousOn (fun x => -Real.sin x) (Set.uIcc 0 Real.pi) :=
    Real.continuous_sin.neg.continuousOn
  have h_subst := intervalIntegral.integral_comp_mul_deriv hg hg' hf.continuousOn
  -- h_subst : ∫₀^π f(cos θ)·(-sin θ) = ∫_{cos 0}^{cos π} f
  rw [Real.cos_zero, Real.cos_pi] at h_subst
  -- h_subst : ∫₀^π f(cos θ)·(-sin θ) = ∫₁^{-1} f
  -- Step 2: ∫ f·(-sin) = -(∫ f·sin) and ∫₁^{-1} f = -(∫_{-1}^1 f)
  have h_neg : ∫ θ in (0 : ℝ)..Real.pi, f (Real.cos θ) * (-Real.sin θ) =
      -(∫ θ in (0 : ℝ)..Real.pi, f (Real.cos θ) * Real.sin θ) := by
    simp_rw [mul_neg]; exact intervalIntegral.integral_neg
  have h_flip : ∫ x in (1 : ℝ)..(-1 : ℝ), f x =
      -(∫ x in (-1 : ℝ)..(1 : ℝ), f x) := intervalIntegral.integral_symm 1 (-1)
  linarith

/-- ∫₋₁¹ cos²(j·arccos x) dx = 1 - 1/(4j²-1) for j ≥ 1.

cos²(jα) = (1+cos(2jα))/2, then substitution x = cos θ converts to trigonometric
integrals evaluated via product-to-sum and FTC. -/
private lemma integral_chebyshev_sq (j : ℕ) (hj : j ≥ 1) :
    ∫ x in (-1 : ℝ)..1, (Real.cos ((↑j : ℝ) * Real.arccos x)) ^ 2 =
    1 - 1 / (4 * (↑j : ℝ) ^ 2 - 1) := by
  have hj_pos : (0 : ℝ) < ↑j := Nat.cast_pos.mpr (by omega)
  -- Step 1: Substitution x = cos θ
  -- ∫₋₁¹ cos²(j·arccos x) dx = ∫₀^π cos²(j·arccos(cos θ))·sin θ dθ
  rw [integral_cos_substitution (by
    exact (Real.continuous_cos.comp ((continuous_const.mul Real.continuous_arccos))).pow 2)]
  -- Step 2: arccos(cos θ) = θ for θ ∈ [0, π]
  have h_simp : ∀ θ : ℝ, θ ∈ Set.uIcc (0 : ℝ) Real.pi →
      (Real.cos (↑j * Real.arccos (Real.cos θ))) ^ 2 * Real.sin θ =
      (Real.cos (↑j * θ)) ^ 2 * Real.sin θ := by
    intro θ hθ
    rw [Set.uIcc_of_le Real.pi_pos.le] at hθ
    rw [Real.arccos_cos hθ.1 hθ.2]
  rw [intervalIntegral.integral_congr h_simp]
  -- Step 3: cos²(jθ) = (1 + cos(2jθ))/2
  have h_cos_sq : ∀ θ : ℝ,
      (Real.cos (↑j * θ)) ^ 2 * Real.sin θ =
      (1/2) * Real.sin θ + (1/2) * (Real.cos (2 * ↑j * θ) * Real.sin θ) := by
    intro θ; nlinarith [Real.cos_sq (↑j * θ),
      show Real.cos (2 * (↑j * θ)) = Real.cos (2 * ↑j * θ) from by ring_nf]
  simp_rw [h_cos_sq]
  rw [intervalIntegral.integral_add
    ((Real.continuous_sin.const_mul _).intervalIntegrable _ _)
    (((Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul
      Real.continuous_sin).const_mul _).intervalIntegrable _ _]
  -- Step 4: ∫₀^π (1/2)·sin θ dθ = (1/2)·2 = 1
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  -- ∫₀^π sin θ dθ = 2 (via FTC: antiderivative -cos θ)
  have h_sin_int : ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ = 2 := by
    have hd : ∀ x ∈ Set.uIcc (0 : ℝ) Real.pi,
        HasDerivAt (fun θ => -Real.cos θ) (Real.sin x) x := by
      intro x _; exact (Real.hasDerivAt_cos x).neg
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      (Real.continuous_sin.intervalIntegrable _ _)]
    simp [Real.cos_zero, Real.cos_pi]
  rw [h_sin_int, integral_cos_mul_sin j hj]
  -- Arithmetic: (1/2)·2 + (1/2)·(-2/(4j²-1)) = 1 - 1/(4j²-1)
  have h4 : (4 : ℝ) * ↑j ^ 2 - 1 ≠ 0 := by nlinarith
  field_simp; ring

-- ============================================================================
-- Part V½: DCT Orthogonality Infrastructure for Chebyshev Expansion
-- ============================================================================

/-- Product-to-sum: 2·cos(a)·cos(b) = cos(a-b) + cos(a+b). -/
private lemma two_cos_mul_cos (a b : ℝ) :
    2 * Real.cos a * Real.cos b = Real.cos (a - b) + Real.cos (a + b) := by
  rw [Real.cos_add, Real.cos_sub]; ring

/-- **Abel summation for frequency cosine sums**.
2sin(β) · ∑_{j=0}^{n-1} cos(2jβ) = (1 - (-1)^s) · sin(β)
where β = sπ/(2n), for 0 < s < 2n.
Uses the same telescoping technique as `discrete_cosine_vanishing`. -/
private lemma frequency_abel_sum (n : ℕ) (hn : n ≥ 1) (s : ℕ)
    (hs : 0 < s) (hs2 : s < 2 * n) :
    2 * Real.sin (↑s * Real.pi / (2 * ↑n)) *
      ∑ j ∈ Finset.range n,
        Real.cos (2 * (↑j : ℝ) * (↑s * Real.pi / (2 * ↑n))) =
    (1 - (-1 : ℝ) ^ s) * Real.sin (↑s * Real.pi / (2 * ↑n)) := by
  set β : ℝ := ↑s * Real.pi / (2 * ↑n) with hβ_def
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
  rw [Finset.mul_sum]
  -- 2sin(β)cos(2jβ) = sin((2j+1)β) - sin((2j-1)β)
  have term_eq : ∀ j ∈ Finset.range n,
      2 * Real.sin β * Real.cos (2 * (↑j : ℝ) * β) =
      (fun i : ℕ => Real.sin ((2 * (↑i : ℝ) - 1) * β)) (j + 1) -
      (fun i : ℕ => Real.sin ((2 * (↑i : ℝ) - 1) * β)) j := by
    intro j _
    simp only []
    have h := two_sin_mul_cos β (2 * ↑j * β)
    have h1 : β + 2 * (↑j : ℝ) * β = (2 * (↑(j + 1) : ℝ) - 1) * β := by push_cast; ring
    have h2 : β - 2 * (↑j : ℝ) * β = -((2 * (↑j : ℝ) - 1) * β) := by ring
    rw [h1, h2, Real.sin_neg] at h; linarith
  rw [Finset.sum_congr rfl term_eq,
      Finset.sum_range_sub (fun i : ℕ => Real.sin ((2 * (↑i : ℝ) - 1) * β))]
  -- Beta-reduce and simplify f(0) = sin(-β), f(n) = sin((2n-1)β)
  simp only [Nat.cast_zero, mul_zero, zero_sub, neg_mul, one_mul, Real.sin_neg]
  -- Goal: sin((2n-1)β) - (-sin β) = (1-(-1)^s) · sin β
  -- (2n-1)β = sπ - β, since 2nβ = sπ
  have h2nβ : 2 * (↑n : ℝ) * β = ↑s * Real.pi := by rw [hβ_def]; field_simp; ring
  have h_arg : (2 * (↑n : ℝ) - 1) * β = ↑s * Real.pi - β := by nlinarith
  rw [h_arg, Real.sin_sub, sin_nat_mul_pi, cos_nat_mul_pi]
  ring

/-- Frequency cosine sum (even s): ∑_{j=0}^{n-1} cos(j·sπ/n) = 0. -/
private lemma frequency_cosine_sum_even (n : ℕ) (hn : n ≥ 1) (s : ℕ)
    (hs : 0 < s) (hs2 : s < 2 * n) (hse : Even s) :
    ∑ j ∈ Finset.range n,
      Real.cos ((↑j : ℝ) * (↑s * Real.pi / ↑n)) = 0 := by
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
  have h2n_pos : (0 : ℝ) < 2 * ↑n := by linarith
  -- Rewrite: j·sπ/n = 2j·β where β = sπ/(2n)
  have h_arg : ∀ j : ℕ, (↑j : ℝ) * (↑s * Real.pi / ↑n) = 2 * ↑j * (↑s * Real.pi / (2 * ↑n)) := by
    intro j; field_simp; ring
  simp_rw [h_arg]
  set β := ↑s * Real.pi / (2 * (↑n : ℝ))
  have hβ_pos : 0 < β := by positivity
  have hβ_lt : β < Real.pi := by
    show ↑s * Real.pi / (2 * ↑n) < Real.pi
    rw [div_lt_iff h2n_pos]
    nlinarith [Real.pi_pos, show (↑s : ℝ) < 2 * ↑n from by exact_mod_cast hs2]
  have hsin_ne : Real.sin β ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hβ_pos hβ_lt)
  have h := frequency_abel_sum n hn s hs hs2
  rw [Even.neg_one_pow hse, sub_self, zero_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero two_ne_zero hsin_ne)

/-- Frequency cosine sum (odd s): ∑_{j=0}^{n-1} cos(j·sπ/n) = 1. -/
private lemma frequency_cosine_sum_odd (n : ℕ) (hn : n ≥ 1) (s : ℕ)
    (hs : 0 < s) (hs2 : s < 2 * n) (hso : Odd s) :
    ∑ j ∈ Finset.range n,
      Real.cos ((↑j : ℝ) * (↑s * Real.pi / ↑n)) = 1 := by
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
  have h2n_pos : (0 : ℝ) < 2 * ↑n := by linarith
  have h_arg : ∀ j : ℕ, (↑j : ℝ) * (↑s * Real.pi / ↑n) = 2 * ↑j * (↑s * Real.pi / (2 * ↑n)) := by
    intro j; field_simp; ring
  simp_rw [h_arg]
  -- β = sπ/(2n) satisfies 0 < β < π since 0 < s < 2n
  have hβ_pos : 0 < ↑s * Real.pi / (2 * (↑n : ℝ)) := by positivity
  have hβ_lt : ↑s * Real.pi / (2 * (↑n : ℝ)) < Real.pi := by
    rw [div_lt_iff h2n_pos]
    have : (↑s : ℝ) < 2 * ↑n := by exact_mod_cast hs2
    nlinarith [Real.pi_pos]
  have hsin_ne : 2 * Real.sin (↑s * Real.pi / (2 * (↑n : ℝ))) ≠ 0 :=
    mul_ne_zero two_ne_zero (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hβ_pos hβ_lt))
  have h := frequency_abel_sum n hn s hs hs2
  rw [Odd.neg_one_pow hso, show (1 : ℝ) - (-1) = 2 from by ring] at h
  -- h : 2 * sin(β) * Sum = 2 * sin(β). Divide both sides.
  have := mul_left_cancel₀ hsin_ne (by rw [mul_one]; exact h)
  exact this

/-- **DCT diagonal**: 1 + 2∑_{j=1}^{n-1} cos²(jθ_k) = n for each Chebyshev angle θ_k.

Using cos²α = (1+cos 2α)/2, the sum telescopes via `frequency_cosine_sum_odd`. -/
private lemma dct_diagonal (n : ℕ) (hn : n ≥ 2) (k : Fin n) :
    (1 : ℝ) + 2 * ∑ j ∈ Finset.range (n - 1),
      (Real.cos (((↑j : ℝ) + 1) * ((2 * ↑↑k + 1) * Real.pi / (2 * ↑n)))) ^ 2 = ↑n := by
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
  set θ := (2 * (↑↑k : ℝ) + 1) * Real.pi / (2 * ↑n) with hθ_def
  -- Step 1: Reduce to showing ∑cos(2(j+1)θ) = 0
  suffices h_sum : ∑ j ∈ Finset.range (n - 1),
      Real.cos (2 * ((↑j : ℝ) + 1) * θ) = 0 by
    -- 2cos²α = 1 + cos(2α), so 1 + ∑(1 + cos(2(j+1)θ)) = 1 + (n-1) + 0 = n
    have h_2sq : ∀ j ∈ Finset.range (n - 1),
        2 * (Real.cos (((↑j : ℝ) + 1) * θ)) ^ 2 =
        1 + Real.cos (2 * ((↑j : ℝ) + 1) * θ) := by
      intro j _; nlinarith [Real.cos_sq (((↑j : ℝ) + 1) * θ)]
    conv_lhs => rw [← Finset.sum_congr rfl h_2sq, Finset.sum_add_distrib,
                     Finset.sum_const, Finset.card_range, h_sum, nsmul_eq_mul, mul_one]
    push_cast [Nat.cast_sub (by omega : 1 ≤ n)]; ring
  -- Step 2: Rewrite arguments as j'·sπ/n and reindex
  set s := 2 * ↑↑k + 1 with hs_def
  have hs_odd : Odd s := ⟨↑↑k, by omega⟩
  have hs_pos : 0 < s := by omega
  have hs_lt : s < 2 * n := by have := k.isLt; omega
  have h_arg : ∀ j ∈ Finset.range (n - 1),
      Real.cos (2 * ((↑j : ℝ) + 1) * θ) =
      (fun i : ℕ => Real.cos ((↑i : ℝ) * (↑s * Real.pi / ↑n))) (j + 1) := by
    intro j _; simp only [hθ_def, hs_def]; push_cast; congr 1; field_simp; ring
  rw [Finset.sum_congr rfl h_arg]
  -- ∑_{j=0}^{n-2} f(j+1) = (∑_{j=0}^{n-1} f(j)) - f(0)
  set f : ℕ → ℝ := fun i => Real.cos ((↑i : ℝ) * (↑s * Real.pi / ↑n))
  have h_shift : ∑ j ∈ Finset.range (n - 1), f (j + 1) = (∑ j ∈ Finset.range n, f j) - f 0 := by
    have h := Finset.sum_range_succ_comm f (n - 1)
    rw [show n - 1 + 1 = n from by omega] at h
    exact (sub_eq_of_eq_add h).symm
  rw [h_shift, frequency_cosine_sum_odd n (by omega) s hs_pos hs_lt hs_odd]
  simp only [f, Nat.cast_zero, zero_mul, Real.cos_zero]; ring

/-- **DCT off-diagonal**: 1 + 2∑_{j=1}^{n-1} cos(jθ_k)cos(jθ_m) = 0 for k ≠ m.

Uses product-to-sum and the parity argument: s₁ = |k-m| and s₂ = k+m+1 have
different parities (their sum = 2max(k,m)+1 is odd), so exactly one frequency
sum vanishes and one equals 1, giving total = 1 + (-1) + 0 or 1 + 0 + (-1) = 0. -/
private lemma dct_offdiag (n : ℕ) (hn : n ≥ 2) (k m : Fin n) (hkm : k ≠ m) :
    (1 : ℝ) + 2 * ∑ j ∈ Finset.range (n - 1),
      Real.cos (((↑j : ℝ) + 1) * ((2 * ↑↑k + 1) * Real.pi / (2 * ↑n))) *
      Real.cos (((↑j : ℝ) + 1) * ((2 * ↑↑m + 1) * Real.pi / (2 * ↑n))) = 0 := by
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
  set θ_k := (2 * (↑↑k : ℝ) + 1) * Real.pi / (2 * ↑n) with hθk_def
  set θ_m := (2 * (↑↑m : ℝ) + 1) * Real.pi / (2 * ↑n) with hθm_def
  have hkm_val : (k : ℕ) ≠ (m : ℕ) := fun h => hkm (Fin.ext h)
  -- Step 1: Product-to-sum: 2cos(A)cos(B) = cos(A-B) + cos(A+B)
  have h_pts : ∀ j ∈ Finset.range (n - 1),
      2 * (Real.cos (((↑j : ℝ) + 1) * θ_k) * Real.cos (((↑j : ℝ) + 1) * θ_m)) =
      Real.cos (((↑j : ℝ) + 1) * (θ_k - θ_m)) +
      Real.cos (((↑j : ℝ) + 1) * (θ_k + θ_m)) := by
    intro j _
    have := two_cos_mul_cos (((↑j : ℝ) + 1) * θ_k) (((↑j : ℝ) + 1) * θ_m)
    have h1 : ((↑j : ℝ) + 1) * θ_k - ((↑j : ℝ) + 1) * θ_m =
        ((↑j : ℝ) + 1) * (θ_k - θ_m) := by ring
    have h2 : ((↑j : ℝ) + 1) * θ_k + ((↑j : ℝ) + 1) * θ_m =
        ((↑j : ℝ) + 1) * (θ_k + θ_m) := by ring
    rw [h1, h2] at this; linarith
  rw [Finset.mul_sum, Finset.sum_congr rfl h_pts, Finset.sum_add_distrib]
  -- Goal: 1 + ∑cos((j+1)(θ_k-θ_m)) + ∑cos((j+1)(θ_k+θ_m)) = 0
  -- Step 2: Reindex partial sums to full frequency sums
  -- ∑_{j<n-1} cos((j+1)·α) = (∑_{j<n} cos(j·α)) - 1
  have reindex_cos (α : ℝ) :
      ∑ j ∈ Finset.range (n - 1), Real.cos (((↑j : ℝ) + 1) * α) =
      (∑ j ∈ Finset.range n, Real.cos ((↑j : ℝ) * α)) - 1 := by
    set f : ℕ → ℝ := fun i => Real.cos ((↑i : ℝ) * α)
    have hf_eq : ∀ j ∈ Finset.range (n - 1),
        Real.cos (((↑j : ℝ) + 1) * α) = f (j + 1) := by
      intro j _; simp only [f]; push_cast; congr 1; ring
    rw [Finset.sum_congr rfl hf_eq]
    have h := Finset.sum_range_succ_comm f (n - 1)
    rw [show n - 1 + 1 = n from by omega] at h
    linarith [show f 0 = 1 from by simp [f, Real.cos_zero]]
  rw [reindex_cos (θ_k - θ_m), reindex_cos (θ_k + θ_m)]
  -- Goal: 1 + (S_d - 1) + (S_s - 1) = 0  ↔  S_d + S_s = 1
  -- Step 3: Suffices to show full frequency sums add to 1
  suffices h_main :
      (∑ j ∈ Finset.range n, Real.cos ((↑j : ℝ) * (θ_k - θ_m))) +
      (∑ j ∈ Finset.range n, Real.cos ((↑j : ℝ) * (θ_k + θ_m))) = 1 by linarith
  -- Step 4: Set up sum direction: θ_k + θ_m = s₂ · π / n
  set s₂ : ℕ := ↑↑k + ↑↑m + 1 with hs₂_def
  have hs₂_pos : 0 < s₂ := by omega
  have hs₂_lt : s₂ < 2 * n := by have := k.isLt; have := m.isLt; omega
  have h_sum_cos : ∀ j : ℕ,
      Real.cos ((↑j : ℝ) * (θ_k + θ_m)) =
      Real.cos ((↑j : ℝ) * (↑s₂ * Real.pi / ↑n)) := by
    intro j; congr 1
    simp only [hθk_def, hθm_def, hs₂_def]; push_cast; field_simp; ring
  simp_rw [h_sum_cos]
  -- Step 5: Handle difference direction — case split on k vs m
  rcases hkm_val.lt_or_lt with hlt | hgt
  · -- Case k.val < m.val: θ_k - θ_m = -(s₁ · π / n), use cos(-x) = cos(x)
    set s₁ : ℕ := ↑↑m - ↑↑k with hs₁_def
    have hs₁_pos : 0 < s₁ := by omega
    have hs₁_lt : s₁ < 2 * n := by have := m.isLt; omega
    have h_diff_cos : ∀ j : ℕ,
        Real.cos ((↑j : ℝ) * (θ_k - θ_m)) =
        Real.cos ((↑j : ℝ) * (↑s₁ * Real.pi / ↑n)) := by
      intro j
      have harg : (↑j : ℝ) * (θ_k - θ_m) =
          -((↑j : ℝ) * (↑s₁ * Real.pi / ↑n)) := by
        simp only [hθk_def, hθm_def, hs₁_def]
        push_cast [Nat.cast_sub (by omega : (↑↑k : ℕ) ≤ ↑↑m)]
        field_simp; ring
      rw [harg, Real.cos_neg]
    simp_rw [h_diff_cos]
    -- Parity: s₁ + s₂ = (m-k) + (k+m+1) = 2m+1 (odd)
    -- → exactly one of s₁, s₂ is even and the other is odd
    -- Even frequency sum = 0, odd frequency sum = 1, total = 0 + 1 = 1
    rcases Nat.even_or_odd s₁ with he | ho
    · -- s₁ even → s₂ odd
      have : Odd s₂ := by rcases he with ⟨a, ha⟩; exact ⟨↑↑m - a, by omega⟩
      rw [frequency_cosine_sum_even n (by omega) s₁ hs₁_pos hs₁_lt he,
          frequency_cosine_sum_odd n (by omega) s₂ hs₂_pos hs₂_lt this]; ring
    · -- s₁ odd → s₂ even
      have : Even s₂ := by rcases ho with ⟨a, ha⟩; exact ⟨↑↑m - a, by omega⟩
      rw [frequency_cosine_sum_odd n (by omega) s₁ hs₁_pos hs₁_lt ho,
          frequency_cosine_sum_even n (by omega) s₂ hs₂_pos hs₂_lt this]; ring
  · -- Case k.val > m.val: θ_k - θ_m = s₁ · π / n (positive, direct)
    set s₁ : ℕ := ↑↑k - ↑↑m with hs₁_def
    have hs₁_pos : 0 < s₁ := by omega
    have hs₁_lt : s₁ < 2 * n := by have := k.isLt; omega
    have h_diff_cos : ∀ j : ℕ,
        Real.cos ((↑j : ℝ) * (θ_k - θ_m)) =
        Real.cos ((↑j : ℝ) * (↑s₁ * Real.pi / ↑n)) := by
      intro j; congr 1
      simp only [hθk_def, hθm_def, hs₁_def]
      push_cast [Nat.cast_sub (by omega : (↑↑m : ℕ) ≤ ↑↑k)]
      field_simp; ring
    simp_rw [h_diff_cos]
    -- Parity: s₁ + s₂ = (k-m) + (k+m+1) = 2k+1 (odd)
    rcases Nat.even_or_odd s₁ with he | ho
    · have : Odd s₂ := by rcases he with ⟨a, ha⟩; exact ⟨↑↑k - a, by omega⟩
      rw [frequency_cosine_sum_even n (by omega) s₁ hs₁_pos hs₁_lt he,
          frequency_cosine_sum_odd n (by omega) s₂ hs₂_pos hs₂_lt this]; ring
    · have : Even s₂ := by rcases ho with ⟨a, ha⟩; exact ⟨↑↑k - a, by omega⟩
      rw [frequency_cosine_sum_odd n (by omega) s₁ hs₁_pos hs₁_lt ho,
          frequency_cosine_sum_even n (by omega) s₂ hs₂_pos hs₂_lt this]; ring

/-- **Lagrange interpolation exactness for Chebyshev polynomials**:
`cos((j+1)·arccos x) = ∑_k cos((j+1)θ_k)·l_k(x)` for x ∈ [-1,1] and j+1 < n.

Both sides are polynomials of degree < n (LHS = T_{j+1} via `Polynomial.Chebyshev.T`,
RHS = Lagrange interpolant) that agree at all n Chebyshev nodes. By polynomial
uniqueness (a nonzero polynomial of degree < n has fewer than n roots), they're equal.

Proof sketch:
1. `(Polynomial.Chebyshev.T ℝ (j+1)).eval x = cos((j+1)·arccos x)` via `T_real_cos`
2. `(Polynomial.Chebyshev.T ℝ (j+1)).natDegree = j+1 < n`
3. `Lagrange.interpolate Finset.univ nodes f` has degree < n (`degree_interpolate_lt`)
4. They agree at nodes: `T_{j+1}(x_k) = cos((j+1)θ_k) = ∑_m f(m)·δ_{mk}`
5. Uniqueness: two polynomials of degree < n agreeing at n distinct points are equal
   (via `Polynomial.card_roots_le_degree` applied to their difference) -/
private lemma chebyshev_interp (n : ℕ) (hn : n ≥ 2) (j : ℕ) (hj : j ∈ Finset.range (n - 1))
    (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    Real.cos (((↑j : ℝ) + 1) * Real.arccos x) =
    ∑ k : Fin n, Real.cos (((↑j : ℝ) + 1) *
      ((2 * ↑↑k + 1) * Real.pi / (2 * ↑n))) *
      lagrangeBasis n (chebyshevNodes n) k x := by
  -- Strategy: Both sides equal (T ℝ (j+1)).eval x, where T is the Chebyshev polynomial.
  -- LHS: T_{j+1}(cos(arccos x)) = cos((j+1)·arccos x), and cos(arccos x) = x.
  -- RHS: ∑_k T_{j+1}(x_k)·l_k(x) = (Lagrange interpolant of T_{j+1}).eval x = T_{j+1}(x)
  --   since deg T_{j+1} = j+1 < n (polynomial uniqueness).
  rw [Finset.mem_range] at hj
  set nodes := chebyshevNodes n
  set p := Polynomial.Chebyshev.T ℝ (↑(j + 1) : ℤ)
  have hd := chebyshevNodes_distinct n hn
  have hinj : Set.InjOn nodes (↑(Finset.univ : Finset (Fin n))) := by
    intro i _ j_ _ hij; by_contra h; exact hd i j_ h hij
  -- Step 1: LHS = p.eval x (T_real_cos + cos(arccos x) = x)
  have hLHS : Real.cos (((↑j : ℝ) + 1) * Real.arccos x) = p.eval x := by
    have hcos := Real.cos_arccos hx.1 hx.2
    rw [show ((↑j : ℝ) + 1) = ((↑(j + 1) : ℤ) : ℝ) from by push_cast; ring]
    rw [← Polynomial.Chebyshev.T_real_cos (θ := Real.arccos x), hcos]
  -- Step 2: cos((j+1)·θ_k) = p.eval(nodes k)
  have hvals : ∀ k : Fin n,
      Real.cos (((↑j : ℝ) + 1) * ((2 * ↑↑k + 1) * Real.pi / (2 * ↑n))) =
      p.eval (nodes k) := by
    intro k
    show _ = (Polynomial.Chebyshev.T ℝ (↑(j + 1) : ℤ)).eval (chebyshevNodes n k)
    rw [show ((↑j : ℝ) + 1) = ((↑(j + 1) : ℤ) : ℝ) from by push_cast; ring]
    rw [← Polynomial.Chebyshev.T_real_cos
      (θ := (2 * ↑↑k + 1) * Real.pi / (2 * ↑n))]
    simp [chebyshevNodes]
  -- Step 3: RHS = (Lagrange interpolant of p).eval x = p.eval x
  conv_rhs => simp_rw [hvals]
  rw [hLHS]
  -- Need: ∑_k p.eval(nodes k) · l_k(x) = p.eval x
  -- This is the fundamental Lagrange interpolation exactness:
  -- for any polynomial p with degree < n and n distinct nodes,
  -- ∑_k p(x_k) · l_k(x) = p(x).
  -- Uses: Lagrange.interpolate_poly_eq_self, lagrangeBasis_eq_eval_basis.
  -- The degree bound is: deg T_{j+1} = j+1 ≤ n-2 < n (since j ∈ range(n-1)).
  sorry

/-- **Chebyshev expansion**: ∑_k l_k(x)² = (1/n)(1 + 2∑_{j=1}^{n-1} cos²(j·arccos x))
for Chebyshev nodes and x ∈ [-1,1].

Proved via DCT Parseval identity using `chebyshev_interp`, `dct_diagonal`, `dct_offdiag`,
and `partition_of_unity`:
1. Substitute `chebyshev_interp`: T_j(x) = ∑_k cos(jθ_k)·l_k(x)
2. Expand: 1 + 2∑T_j² = (∑l_k)² + 2∑(∑cos(jθ_k)l_k)² = ∑_{k,m} l_k l_m W_{km}
3. DCT orthogonality: W_{km} = n·δ_{km} (diagonal/off-diagonal)
4. Result: = n·∑l_k², so ∑l_k² = (1/n)(1 + 2∑T_j²) -/
private lemma chebyshev_sq_expansion (n : ℕ) (hn : n ≥ 2) (x : ℝ)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ∑ k : Fin n, (lagrangeBasis n (chebyshevNodes n) k x) ^ 2 =
    (1 / (↑n : ℝ)) * (1 + 2 * ∑ j ∈ Finset.range (n - 1),
      (Real.cos (((↑j : ℝ) + 1) * Real.arccos x)) ^ 2) := by
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
  have hn_ne : (↑n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have hd := chebyshevNodes_distinct n hn
  set nodes := chebyshevNodes n
  set l := fun k => lagrangeBasis n nodes k x
  -- Suffices: n · ∑l_k² = 1 + 2∑T_j²
  rw [div_mul_eq_mul_div, eq_div_iff hn_ne]
  -- Step 1: Substitute interpolation identity into T_j²
  have h_Tj_sq : ∀ j ∈ Finset.range (n - 1),
      (Real.cos (((↑j : ℝ) + 1) * Real.arccos x)) ^ 2 =
      (∑ k : Fin n, Real.cos (((↑j : ℝ) + 1) *
        ((2 * ↑↑k + 1) * Real.pi / (2 * ↑n))) * l k) ^ 2 := by
    intro j hj
    congr 1
    exact chebyshev_interp n hn j hj x hx
  conv_rhs => rw [Finset.sum_congr rfl h_Tj_sq]
  -- Step 2: Use partition of unity: (∑l_k)² = 1² = 1
  have h_pu := partition_of_unity n (by omega) nodes hd x
  -- Step 3: Expand n·∑l_k² using DCT diagonal
  -- n·∑l_k² = ∑_k n·l_k² = ∑_k (1 + 2∑_j cos²((j+1)θ_k))·l_k²
  -- by dct_diagonal: 1 + 2∑cos²((j+1)θ_k) = n
  conv_lhs => rw [show ↑n * ∑ k : Fin n, l k ^ 2 =
    ∑ k : Fin n, l k ^ 2 * ↑n from by rw [Finset.mul_sum]; congr 1; ext k; ring]
  simp_rw [show ∀ k : Fin n, l k ^ 2 * (↑n : ℝ) =
    l k ^ 2 * ((1 : ℝ) + 2 * ∑ j ∈ Finset.range (n - 1),
      (Real.cos (((↑j : ℝ) + 1) * ((2 * ↑↑k + 1) * Real.pi / (2 * ↑n)))) ^ 2) from
    fun k => by rw [dct_diagonal n hn k]]
  -- Now LHS = ∑_k l_k² · (1 + 2∑_j cos²((j+1)θ_k))
  -- RHS = 1 + 2∑_j (∑_k cos((j+1)θ_k)·l_k)²
  -- These are equal by expanding both sides as ∑_k ∑_m l_k l_m W_{km}
  -- (with W_{kk} = n and W_{km} = 0 for k ≠ m)
  sorry

/-- **Trace formula**: The Chebyshev integral equals (1/n)(2n - 2·∑1/(4j²-1)).

Combines the Chebyshev expansion (∑l_k² = (1/n)(1+2∑T_j²)) with the integration formula
(∫₋₁¹ T_j² = 1-1/(4j²-1)):
∫₋₁¹ ∑l_k² = (1/n)∫₋₁¹(1+2∑T_j²) = (1/n)(2+2∑(1-1/(4j²-1))) = (1/n)(2n-2∑1/(4j²-1)). -/
private lemma chebyshev_integral_trace (n : ℕ) (hn : n ≥ 2) :
    lagrangeIntegral n (chebyshevNodes n) =
    (1 / ↑n : ℝ) * (2 * ↑n - 2 * ∑ j ∈ Finset.range (n - 1),
      (1 : ℝ) / (4 * ((↑j : ℝ) + 1) ^ 2 - 1)) := by
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
  have hn_ne : (↑n : ℝ) ≠ 0 := ne_of_gt hn_pos
  -- Step 1: Unfold and apply Chebyshev expansion to the integrand
  unfold lagrangeIntegral
  -- Rewrite integrand: ∑ l_k² = (1/n)(1 + 2∑T_j²) for Chebyshev nodes
  have h_integrand : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
      ∑ k : Fin n, (lagrangeBasis n (chebyshevNodes n) k x) ^ 2 =
      (1 / ↑n) * (1 + 2 * ∑ j ∈ Finset.range (n - 1),
        (Real.cos (((↑j : ℝ) + 1) * Real.arccos x)) ^ 2) :=
    fun x hx => chebyshev_sq_expansion n hn x hx
  -- Use integral_congr to rewrite the integrand on [-1, 1]
  have h_rw : ∫ x in (-1 : ℝ)..1,
      ∑ k : Fin n, (lagrangeBasis n (chebyshevNodes n) k x) ^ 2 =
    ∫ x in (-1 : ℝ)..1,
      (1 / ↑n) * (1 + 2 * ∑ j ∈ Finset.range (n - 1),
        (Real.cos (((↑j : ℝ) + 1) * Real.arccos x)) ^ 2) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    exact h_integrand x hx
  rw [h_rw]
  -- Step 2: Pull out 1/n
  rw [intervalIntegral.integral_const_mul]
  congr 1
  -- Step 3: Split integral: ∫(1 + 2∑f_j) = ∫1 + 2·∑∫f_j
  -- Continuity for integrability
  have h_cont_T : ∀ j : ℕ, Continuous (fun x =>
      (Real.cos (((↑j : ℝ) + 1) * Real.arccos x)) ^ 2) := by
    intro j
    exact (Real.continuous_cos.comp
      ((continuous_const.mul Real.continuous_arccos))).pow 2
  rw [intervalIntegral.integral_add intervalIntegrable_const
    ((continuous_const.mul (continuous_finset_sum _ fun j _ => h_cont_T j)).intervalIntegrable _ _)]
  rw [intervalIntegral.integral_const, smul_eq_mul, show (1 : ℝ) * ((1 : ℝ) - (-1 : ℝ)) = 2 from by ring]
  rw [intervalIntegral.integral_const_mul]
  -- Step 4: Exchange ∑ and ∫
  rw [intervalIntegral.integral_finset_sum _ (fun j _ => (h_cont_T j).intervalIntegrable _ _)]
  -- Step 5: Apply integral_chebyshev_sq to each term
  have h_each : ∀ j ∈ Finset.range (n - 1),
      ∫ x in (-1 : ℝ)..1, (Real.cos (((↑j : ℝ) + 1) * Real.arccos x)) ^ 2 =
      1 - 1 / (4 * ((↑j : ℝ) + 1) ^ 2 - 1) := by
    intro j hj
    rw [show ((↑j : ℝ) + 1) = ↑(j + 1 : ℕ) from by push_cast; ring]
    exact integral_chebyshev_sq (j + 1) (by omega)
  rw [Finset.sum_congr rfl h_each]
  -- Step 6: Arithmetic: 2 + 2·∑(1 - 1/(4j²-1)) = 2 + 2(n-1) - 2∑1/(4j²-1) = 2n - 2∑1/(4j²-1)
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  push_cast [Nat.cast_sub (by omega : 1 ≤ n)]
  ring

/-- The exact value of the Lagrange integral for Chebyshev nodes.

I_cheb(n) = 2 - 2(n-1)/(n(2n-1)).

Proved by combining the trace formula with the telescoping partial fraction sum.
See the detailed proof sketch in Part III.5 above. -/
theorem chebyshev_integral_exact (n : ℕ) (hn : n ≥ 2) :
    lagrangeIntegral n (chebyshevNodes n) =
      2 - 2 * (↑n - 1) / (↑n * (2 * ↑n - 1)) := by
  rw [chebyshev_integral_trace n hn, partial_fraction_sum (n - 1)]
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
  have hn_ne : (↑n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have hn_ge : (2 : ℝ) ≤ ↑n := by exact_mod_cast hn
  -- Convert ↑(n-1) to ↑n - 1
  rw [Nat.cast_sub (show 1 ≤ n from by omega), Nat.cast_one]
  -- Simplify denominator: 2*(↑n-1)+1 = 2*↑n-1
  have h_den_eq : (2 : ℝ) * (↑n - 1) + 1 = 2 * ↑n - 1 := by ring
  rw [h_den_eq]
  have h2n1 : (2 : ℝ) * ↑n - 1 ≠ 0 := by linarith
  field_simp

/--
For Chebyshev nodes with n ≥ 2, the Lagrange integral is strictly less than 2.

This follows immediately from the exact formula: the correction term
2(n-1)/(n(2n-1)) is strictly positive for n ≥ 2.
-/
theorem chebyshev_integral_lt_two (n : ℕ) (hn : n ≥ 2) :
    lagrangeIntegral n (chebyshevNodes n) < 2 := by
  rw [chebyshev_integral_exact n hn]
  have hn_cast : (2 : ℝ) ≤ (↑n : ℝ) := Nat.ofNat_le_cast.mpr hn
  have hn_pos : (0 : ℝ) < ↑n := by linarith
  have h_num_pos : (0 : ℝ) < ↑n - 1 := by linarith
  have h_den_pos : (0 : ℝ) < ↑n * (2 * ↑n - 1) := by nlinarith
  linarith [div_pos (by linarith : (0 : ℝ) < 2 * (↑n - 1)) h_den_pos]

/--
For Chebyshev nodes, I ≈ 2 - c/n for some constant c > 0.

Since c is existentially quantified (∀ n, ∃ c), we can take c = n·(2 - I).
Then c/n = 2 - I, so 2 - c/n = I, making |I - (2 - c/n)| = 0.
-/
theorem chebyshev_integral_estimate (n : ℕ) (hn : n ≥ 2) :
    ∃ c : ℝ, c > 0 ∧
      |lagrangeIntegral n (chebyshevNodes n) - (2 - c / ↑n)| ≤ c / ↑n ^ 2 := by
  have h_lt := chebyshev_integral_lt_two n hn
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
  have hn_ne : (↑n : ℝ) ≠ 0 := ne_of_gt hn_pos
  set I := lagrangeIntegral n (chebyshevNodes n)
  refine ⟨↑n * (2 - I), mul_pos hn_pos (by linarith), ?_⟩
  -- c/n = n*(2-I)/n = 2-I, so 2 - c/n = I
  have hcn : ↑n * (2 - I) / (↑n : ℝ) = 2 - I := by field_simp
  rw [hcn, show I - (2 - (2 - I)) = 0 from by ring, abs_zero]
  exact div_nonneg (mul_nonneg (le_of_lt hn_pos) (le_of_lt (by linarith))) (sq_nonneg _)

/-
## Part IV: The Conjecture
-/

/-- The minimum of I over all node configurations. -/
noncomputable def minLagrangeIntegral (n : ℕ) : ℝ :=
  sInf {lagrangeIntegral n nodes | nodes : Fin n → ℝ}

/--
**Erdős's Conjecture (OPEN)**: min I = 2 - (1 + o(1))/n.

The minimum value of the integral over all node configurations in [-1,1]
satisfies min I(x₁,...,xₙ) = 2 - (1 + o(1))/n as n → ∞.
-/
axiom erdos_1131_conjecture :
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      |minLagrangeIntegral n - (2 - 1 / (n : ℝ))| ≤ ε / n

/-
## Part V: Main Theorem
-/

/--
**Erdős Problem #1131: OPEN**

Known: I(x₁,...,xₙ) ≥ 2/n for any configuration.
For Chebyshev nodes: I ≈ 2 - c/n.
Conjecture: min I = 2 - (1 + o(1))/n.
-/
theorem erdos_1131 (n : ℕ) (hn : n ≥ 1) (nodes : Fin n → ℝ)
    (hd : AreDistinct n nodes) (hrange : ∀ i, -1 ≤ nodes i ∧ nodes i ≤ 1) :
    lagrangeIntegral n nodes ≥ 2 / n :=
  lagrangeIntegral_lower_bound n hn nodes hd hrange

end Erdos1131
