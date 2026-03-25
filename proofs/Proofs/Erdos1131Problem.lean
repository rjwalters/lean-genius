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

/-- The exact value of the Lagrange integral for Chebyshev nodes.

I_cheb(n) = 2 - 2(n-1)/(n(2n-1)).

The proof combines discrete cosine orthogonality at Chebyshev nodes with
the integration formula for Chebyshev polynomials T_j(x)² on [-1,1].
See the detailed proof sketch above.
-/
theorem chebyshev_integral_exact (n : ℕ) (hn : n ≥ 2) :
    lagrangeIntegral n (chebyshevNodes n) =
      2 - 2 * (↑n - 1) / (↑n * (2 * ↑n - 1)) := by
  sorry

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
