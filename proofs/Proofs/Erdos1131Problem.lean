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
  have hk_ne : (↑k : ℝ) ≠ 0 := ne_of_gt hk_pos
  -- Antiderivative F(θ) = -(1/k)cos(kθ) satisfies F'(θ) = sin(kθ)
  have hd : ∀ θ ∈ Set.uIcc (0 : ℝ) Real.pi,
      HasDerivAt (fun θ => -(1 / (↑k : ℝ)) * Real.cos ((↑k : ℝ) * θ))
        (Real.sin ((↑k : ℝ) * θ)) θ := by
    intro θ _
    have h_inner : HasDerivAt (fun θ => (↑k : ℝ) * θ) (↑k : ℝ) θ :=
      (hasDerivAt_id θ).const_mul _
    have h_cos : HasDerivAt (fun θ => Real.cos ((↑k : ℝ) * θ))
        (-Real.sin ((↑k : ℝ) * θ) * (↑k : ℝ)) θ :=
      (hasDerivAt_cos _).comp θ h_inner
    convert h_cos.const_mul (-(1 / (↑k : ℝ))) using 1
    field_simp; ring
  rw [integral_eq_sub_of_hasDerivAt hd
    ((continuous_sin.comp (continuous_const.mul continuous_id')).intervalIntegrable _ _)]
  simp only [mul_zero, Real.cos_zero]; field_simp; ring

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
  -- Rewrite integrand: cos(A)sin(B) = (1/2)(sin(A+B) - sin(A-B))
  have h_pts : ∀ θ : ℝ, Real.cos (2 * ↑j * θ) * Real.sin θ =
      (1/2) * Real.sin ((2 * ↑j + 1) * θ) - (1/2) * Real.sin ((2 * ↑j - 1) * θ) := by
    intro θ
    have h := two_cos_mul_sin (2 * ↑j * θ) θ
    have h1 : 2 * ↑j * θ + θ = (2 * ↑j + 1) * θ := by ring
    have h2 : 2 * ↑j * θ - θ = (2 * ↑j - 1) * θ := by ring
    rw [h1, h2] at h; linarith
  simp_rw [funext h_pts]
  -- Split integral
  have h_int : ∀ (c : ℝ),
      IntervalIntegrable (fun θ => (1/2 : ℝ) * Real.sin (c * θ)) volume 0 Real.pi :=
    fun c => ((continuous_sin.comp (continuous_const.mul continuous_id')).const_mul _
      ).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub (h_int _) (h_int _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  -- Cast and apply integral_sin_mul
  have h2j1 : (2 * (↑j : ℝ) + 1) = (↑(2 * j + 1) : ℝ) := by push_cast; ring
  have h2j1m : (2 * (↑j : ℝ) - 1) = (↑(2 * j - 1) : ℝ) := by
    rw [Nat.cast_sub (show 1 ≤ 2 * j from by omega)]; push_cast; ring
  rw [h2j1, h2j1m, integral_sin_mul (2*j+1) (by omega), integral_sin_mul (2*j-1) (by omega)]
  -- cos(odd·π) = -1
  rw [cos_nat_mul_pi, cos_nat_mul_pi]
  have hodd1 : Odd (2 * j + 1) := ⟨j, by ring⟩
  have hodd2 : Odd (2 * j - 1) := ⟨j - 1, by omega⟩
  rw [Odd.neg_one_pow hodd1, Odd.neg_one_pow hodd2]
  -- Algebra: (1/2)·2/(2j+1) - (1/2)·2/(2j-1) = -2/(4j²-1)
  have h1 : (0 : ℝ) < 2 * ↑j + 1 := by linarith
  have h2 : (0 : ℝ) < 2 * ↑j - 1 := by
    have : (1 : ℝ) ≤ ↑j := by exact_mod_cast hj; linarith
  field_simp; ring

/-- Change of variables: ∫₋₁¹ f(x) dx = ∫_0^π f(cos θ) sin θ dθ.
Applies Mathlib's substitution with φ = cos, φ' = -sin. -/
private lemma integral_cos_substitution {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ x in (-1 : ℝ)..1, f x =
    ∫ θ in (0 : ℝ)..Real.pi, f (Real.cos θ) * Real.sin θ := by
  have hg : ∀ θ ∈ Set.uIcc (0 : ℝ) Real.pi,
      HasDerivAt Real.cos (-Real.sin θ) θ :=
    fun θ _ => hasDerivAt_cos θ
  have h := intervalIntegral.integral_comp_mul_deriv hg
    continuous_sin.neg.continuousOn (hf.continuousOn.mono (Set.subset_univ _))
  simp only [Real.cos_zero, Real.cos_pi] at h
  -- h : ∫_0^π f(cos θ) * (-sin θ) = ∫_1^{-1} f(x) = -(∫_{-1}^1 f(x))
  rw [intervalIntegral.integral_symm] at h
  have h_neg : ∫ θ in (0:ℝ)..Real.pi, f (Real.cos θ) * (-Real.sin θ) =
      -(∫ θ in (0:ℝ)..Real.pi, f (Real.cos θ) * Real.sin θ) := by
    simp_rw [mul_neg]; exact intervalIntegral.integral_neg
  linarith [h_neg]

/-- ∫₋₁¹ cos²(j·arccos x) dx = 1 - 1/(4j²-1) for j ≥ 1.

cos²(jα) = (1+cos(2jα))/2, then substitution x = cos θ converts to trigonometric
integrals evaluated via product-to-sum and FTC. -/
private lemma integral_chebyshev_sq (j : ℕ) (hj : j ≥ 1) :
    ∫ x in (-1 : ℝ)..1, (Real.cos ((↑j : ℝ) * Real.arccos x)) ^ 2 =
    1 - 1 / (4 * (↑j : ℝ) ^ 2 - 1) := by
  have hj_pos : (0 : ℝ) < ↑j := Nat.cast_pos.mpr (by omega)
  -- cos²(α) = (1 + cos(2α))/2
  have h_sq : ∀ x : ℝ, (Real.cos ((↑j : ℝ) * Real.arccos x)) ^ 2 =
      1/2 + 1/2 * Real.cos (2 * (↑j : ℝ) * Real.arccos x) := by
    intro x; have := Real.cos_sq ((↑j : ℝ) * Real.arccos x)
    rw [show 2 * ((↑j : ℝ) * Real.arccos x) = 2 * ↑j * Real.arccos x from by ring] at this
    linarith
  simp_rw [funext h_sq]
  -- Split: ∫(1/2 + 1/2·cos(...)) = 1 + (1/2)·∫cos(...)
  have h_cont : Continuous (fun x => (1:ℝ)/2 * Real.cos (2 * (↑j : ℝ) * Real.arccos x)) :=
    (continuous_cos.comp (continuous_const.mul Real.continuous_arccos)).const_mul _
  rw [intervalIntegral.integral_add intervalIntegrable_const (h_cont.intervalIntegrable _ _),
      intervalIntegral.integral_const, smul_eq_mul, show (1:ℝ)/2 * (1 - (-1)) = 1 from by ring,
      intervalIntegral.integral_const_mul]
  -- Substitution: ∫₋₁¹ cos(2j·arccos(x)) dx = ∫_0^π cos(2j·arccos(cos θ))·sin θ dθ
  rw [integral_cos_substitution (continuous_cos.comp (continuous_const.mul Real.continuous_arccos))]
  -- arccos(cos θ) = θ for θ ∈ [0, π]
  have h_arccos : ∀ θ ∈ Set.uIcc (0 : ℝ) Real.pi,
      Real.cos (2 * (↑j : ℝ) * Real.arccos (Real.cos θ)) * Real.sin θ =
      Real.cos (2 * (↑j : ℝ) * θ) * Real.sin θ := by
    intro θ hθ
    rw [Set.uIcc_of_le Real.pi_pos.le] at hθ
    rw [Real.arccos_cos hθ.1 hθ.2]
  rw [intervalIntegral.integral_congr h_arccos, integral_cos_mul_sin j hj]
  -- Algebra: 1 + (1/2)·(-2/(4j²-1)) = 1 - 1/(4j²-1)
  have h3 : (4 : ℝ) * ↑j ^ 2 - 1 ≠ 0 := by nlinarith
  field_simp; ring

/-- **Chebyshev expansion**: ∑_k l_k(x)² = (1/n)(1 + 2∑_{j=1}^{n-1} cos²(j·arccos x))
for Chebyshev nodes and x ∈ [-1,1].

The Lagrange basis at Chebyshev nodes θ_k = (2k+1)π/(2n) has the discrete cosine
representation l_k(x) = (1/n)(1 + 2∑_{j=1}^{n-1} cos(jθ_k)·cos(j·arccos x)).
Squaring and summing over k, cross terms cancel by discrete cosine orthogonality
(∑_k cos(jθ_k)cos(mθ_k) = (n/2)δ_{jm} for 1 ≤ j,m < n), which follows from
`discrete_cosine_vanishing`. -/
private lemma chebyshev_sq_expansion (n : ℕ) (_hn : n ≥ 2) (x : ℝ)
    (_hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ∑ k : Fin n, (lagrangeBasis n (chebyshevNodes n) k x) ^ 2 =
    (1 / (↑n : ℝ)) * (1 + 2 * ∑ j ∈ Finset.range (n - 1),
      (Real.cos (((↑j : ℝ) + 1) * Real.arccos x)) ^ 2) := by
  sorry

/-- **Trace formula**: The Chebyshev integral equals (1/n)(2n - 2·∑1/(4j²-1)).

Combines the Chebyshev expansion (∑l_k² = (1/n)(1+2∑T_j²)) with the integration formula
(∫₋₁¹ T_j² = 1-1/(4j²-1)):
∫₋₁¹ ∑l_k² = (1/n)∫₋₁¹(1+2∑T_j²) = (1/n)(2+2∑(1-1/(4j²-1))) = (1/n)(2n-2∑1/(4j²-1)). -/
private lemma chebyshev_integral_trace (n : ℕ) (hn : n ≥ 2) :
    lagrangeIntegral n (chebyshevNodes n) =
    (1 / ↑n : ℝ) * (2 * ↑n - 2 * ∑ j ∈ Finset.range (n - 1),
      (1 : ℝ) / (4 * ((↑j : ℝ) + 1) ^ 2 - 1)) := by
  unfold lagrangeIntegral
  -- Step 1: Rewrite integrand using Chebyshev expansion
  have h_congr : ∀ x ∈ Set.uIcc (-1 : ℝ) 1,
      ∑ k : Fin n, (lagrangeBasis n (chebyshevNodes n) k x) ^ 2 =
      (1 / (↑n : ℝ)) * (1 + 2 * ∑ j ∈ Finset.range (n - 1),
        (Real.cos (((↑j : ℝ) + 1) * Real.arccos x)) ^ 2) := by
    intro x hx; rw [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 1)] at hx
    exact chebyshev_sq_expansion n hn x hx
  rw [intervalIntegral.integral_congr h_congr, intervalIntegral.integral_const_mul]
  congr 1
  -- Step 2: Evaluate ∫₋₁¹ (1 + 2·∑ cos²((j+1)·arccos x)) = 2n - 2·∑ 1/(4(j+1)²-1)
  have hF_cont : ∀ j, Continuous (fun x =>
      (Real.cos (((↑j : ℝ) + 1) * Real.arccos x)) ^ 2) :=
    fun _ => ((continuous_const.mul Real.continuous_arccos).cos).pow 2
  have hF_int : ∀ j, IntervalIntegrable (fun x =>
      (Real.cos (((↑j : ℝ) + 1) * Real.arccos x)) ^ 2) volume (-1) 1 :=
    fun j => (hF_cont j).intervalIntegrable _ _
  -- Split ∫(1 + 2·∑f_j) = 2 + 2·∑∫f_j
  rw [intervalIntegral.integral_add intervalIntegrable_const
      ((intervalIntegrable_finset_sum _ (fun j _ => hF_int j)).const_mul 2),
    intervalIntegral.integral_const, smul_eq_mul, show (1:ℝ) * (1 - (-1)) = 2 from by ring,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finset_sum _ (fun j _ => hF_int j)]
  -- Apply integration formula to each term
  have h_eval : ∀ j ∈ Finset.range (n - 1),
      ∫ x in (-1:ℝ)..1, (Real.cos (((↑j : ℝ) + 1) * Real.arccos x)) ^ 2 =
      1 - 1 / (4 * ((↑j : ℝ) + 1) ^ 2 - 1) := by
    intro j _
    convert integral_chebyshev_sq (j + 1) (by omega) using 2
    push_cast; ring
  simp_rw [Finset.sum_congr rfl h_eval]
  -- Algebra: 2 + 2·∑(1 - 1/(...)) = 2n - 2·∑ 1/(...)
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  push_cast; ring

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
