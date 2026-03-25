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
- `sum_sq_lagrangeBasis_ge`: ∑ₖ l_k(x)² ≥ 1/n (pointwise variance bound)
- `lagrangeIntegral_lower_bound`: I ≥ 2/n (integral monotonicity)
- `lagrangeBasis_continuous`: each l_k is continuous
- `quadrature_weights_sum`: ∑ₖ w_k = 2 (quadrature exactness for constants)
- `lagrangeIntegral_cross_term_identity`: I = 2 - ∫ off-diagonal Gram matrix
- `lagrangeIntegral_single`: I = 2 for n = 1
- `chebyshevNodes_in_range`: Chebyshev nodes lie in [-1, 1]
- `chebyshevNodes_distinct`: Chebyshev nodes are pairwise distinct

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
Continuity of the Lagrange basis function (polynomial in x, hence continuous).
-/
theorem lagrangeBasis_continuous (n : ℕ) (nodes : Fin n → ℝ) (k : Fin n) :
    Continuous (lagrangeBasis n nodes k) := by
  unfold lagrangeBasis
  exact continuous_finset_prod _ fun i _ => (continuous_id.sub continuous_const).div_const _

/--
Continuity of the sum of squared Lagrange basis functions.
-/
theorem sum_sq_lagrangeBasis_continuous (n : ℕ) (nodes : Fin n → ℝ) :
    Continuous (fun x => ∑ k : Fin n, (lagrangeBasis n nodes k x) ^ 2) := by
  apply continuous_finset_sum; intro k _
  exact (lagrangeBasis_continuous n nodes k).pow 2

/--
**Pointwise lower bound**: ∑ₖ l_k(x)² ≥ 1/n via variance bound on partition of unity.

The variance identity ∑(l_k - 1/n)² = ∑l_k² - 1/n together with non-negativity
of sums of squares gives ∑l_k² ≥ 1/n.
-/
theorem sum_sq_lagrangeBasis_ge (n : ℕ) (hn : n ≥ 1) (nodes : Fin n → ℝ)
    (hd : AreDistinct n nodes) (x : ℝ) :
    ∑ k : Fin n, (lagrangeBasis n nodes k x) ^ 2 ≥ 1 / n := by
  have hpou := partition_of_unity n hn nodes hd x
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hn_ne : (↑n : ℝ) ≠ 0 := ne_of_gt hn_pos
  rw [ge_iff_le, ← sub_nonneg]
  -- Variance: 0 ≤ ∑(l_k - 1/n)²
  have hvar : 0 ≤ ∑ k : Fin n, (lagrangeBasis n nodes k x - 1 / ↑n) ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  -- Expand (a - c)² = a² + (-2c·a + c²) and distribute sum
  have hexp : ∀ k : Fin n, (lagrangeBasis n nodes k x - 1 / ↑n) ^ 2 =
    (lagrangeBasis n nodes k x) ^ 2 +
    (-(2 / ↑n) * lagrangeBasis n nodes k x + 1 / ↑n ^ 2) := by intro k; ring
  simp_rw [hexp] at hvar
  rw [Finset.sum_add_distrib] at hvar
  -- Factor the remainder sum: ∑(-(2/n)·l_k + 1/n²) = -(2/n)·∑l_k + n·(1/n²)
  rw [show ∑ k : Fin n, (-(2 / ↑n) * lagrangeBasis n nodes k x + 1 / ↑n ^ 2) =
      -(2 / ↑n) * ∑ k : Fin n, lagrangeBasis n nodes k x + ↑n * (1 / ↑n ^ 2) from by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_fin,
        nsmul_eq_mul]] at hvar
  rw [hpou, mul_one] at hvar
  -- hvar : 0 ≤ ∑l_k² + (-(2/n) + n/n²), simplify -(2/n) + n/n² = -1/n
  have key : -(2 / (↑n : ℝ)) + ↑n * (1 / ↑n ^ 2) = -(1 / ↑n) := by field_simp; ring
  linarith

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
  have hn_ne : (↑n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have h_cont := sum_sq_lagrangeBasis_continuous n nodes
  rw [ge_iff_le, ← sub_nonneg]
  -- Rewrite 2/n as ∫₋₁¹ (1/n), then use linearity + nonnegativity
  rw [show (2 : ℝ) / ↑n = ∫ _ in (-1 : ℝ)..1, (1 : ℝ) / ↑n from by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring]
  rw [← intervalIntegral.integral_sub (h_cont.intervalIntegrable _ _) intervalIntegrable_const]
  exact intervalIntegral.integral_nonneg (by norm_num : (-1 : ℝ) ≤ 1)
    fun u _hu => by linarith [hpw u]

/--
The quadrature weight w_k = ∫₋₁¹ l_k(x) dx for the k-th node.
-/
noncomputable def quadratureWeight (n : ℕ) (nodes : Fin n → ℝ) (k : Fin n) : ℝ :=
  ∫ x in (-1 : ℝ)..1, lagrangeBasis n nodes k x

/--
**Quadrature weights sum to 2**: ∑_k w_k = 2.

Follows from the partition of unity ∑ l_k(x) = 1 and linearity of integration:
∑_k ∫₋₁¹ l_k(x) dx = ∫₋₁¹ ∑_k l_k(x) dx = ∫₋₁¹ 1 dx = 2.
-/
theorem quadrature_weights_sum (n : ℕ) (hn : n ≥ 1) (nodes : Fin n → ℝ)
    (hd : AreDistinct n nodes) :
    ∑ k : Fin n, quadratureWeight n nodes k = 2 := by
  unfold quadratureWeight
  -- Swap sum and integral: ∑_k ∫ l_k = ∫ ∑_k l_k
  have h_intble : ∀ k : Fin n, IntervalIntegrable (lagrangeBasis n nodes k)
      MeasureTheory.volume (-1 : ℝ) 1 :=
    fun k => (lagrangeBasis_continuous n nodes k).intervalIntegrable _ _
  rw [← intervalIntegral.integral_finset_sum (fun k _ => h_intble k)]
  -- Apply partition of unity: ∑_k l_k(x) = 1
  have hpou : (fun x => ∑ k ∈ Finset.univ, lagrangeBasis n nodes k x) = fun _ => (1 : ℝ) := by
    ext x; simp [partition_of_unity n hn nodes hd x]
  rw [hpou, intervalIntegral.integral_const, smul_eq_mul, mul_one]
  norm_num

/--
The off-diagonal Gram matrix contribution: ∑_{k≠j} l_k(x)·l_j(x).
-/
noncomputable def gramOffDiag (n : ℕ) (nodes : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ k : Fin n, (Finset.univ.filter (· ≠ k)).sum fun j =>
    lagrangeBasis n nodes k x * lagrangeBasis n nodes j x

/--
**Gram matrix decomposition**: I = 2 - ∫₋₁¹ ∑_{k≠j} l_k(x)·l_j(x) dx.

From the partition of unity ∑ l_k = 1, multiplying by l_k and summing gives
∑ l_k² + ∑_{k≠j} l_k·l_j = 1. Integrating: I = 2 - ∫ ∑_{k≠j} l_k·l_j dx.

This connects I to the off-diagonal entries of the Gram matrix G_{kj} = ⟨l_k, l_j⟩_L².
-/
theorem lagrangeIntegral_cross_term_identity (n : ℕ) (hn : n ≥ 1) (nodes : Fin n → ℝ)
    (hd : AreDistinct n nodes) (_hrange : ∀ i, -1 ≤ nodes i ∧ nodes i ≤ 1) :
    lagrangeIntegral n nodes = 2 - ∫ x in (-1 : ℝ)..1, gramOffDiag n nodes x := by
  unfold lagrangeIntegral gramOffDiag
  -- The cross-term function is continuous
  have h_cross_cont : Continuous (fun x =>
      ∑ k : Fin n, (Finset.univ.filter (· ≠ k)).sum fun j =>
        lagrangeBasis n nodes k x * lagrangeBasis n nodes j x) := by
    apply continuous_finset_sum; intro k _
    apply continuous_finset_sum; intro j _
    exact (lagrangeBasis_continuous n nodes k).mul (lagrangeBasis_continuous n nodes j)
  -- For each k: l_k² + ∑_{j≠k} l_k*l_j = l_k
  -- (from: l_k = l_k * 1 = l_k * ∑_j l_j = l_k*l_k + ∑_{j≠k} l_k*l_j)
  have h_each : ∀ x (k : Fin n),
      (lagrangeBasis n nodes k x) ^ 2 +
      ((Finset.univ.filter (· ≠ k)).sum fun j =>
        lagrangeBasis n nodes k x * lagrangeBasis n nodes j x) =
      lagrangeBasis n nodes k x := by
    intro x k
    -- ∑_j l_k*l_j = l_k (from POU)
    have h_total : (Finset.univ.sum fun j =>
        lagrangeBasis n nodes k x * lagrangeBasis n nodes j x) =
        lagrangeBasis n nodes k x := by
      rw [← Finset.mul_sum, partition_of_unity n hn nodes hd x, mul_one]
    -- Split: l_k*l_k + ∑_{erase k} l_k*l_j = ∑_univ l_k*l_j
    have h_split := Finset.add_sum_erase Finset.univ
      (fun j => lagrangeBasis n nodes k x * lagrangeBasis n nodes j x)
      (Finset.mem_univ k)
    -- Combine: l_k^2 + ∑_{≠k} = l_k*l_k + ∑_{erase k} = ∑_univ = l_k
    rw [sq, Finset.filter_ne']
    linarith
  -- Sum over k: ∑_k l_k² + cross = ∑_k l_k = 1
  have hpw : ∀ x, ∑ k : Fin n, (lagrangeBasis n nodes k x) ^ 2 =
      1 - ∑ k : Fin n, ((Finset.univ.filter (· ≠ k)).sum fun j =>
        lagrangeBasis n nodes k x * lagrangeBasis n nodes j x) := by
    intro x
    have h_sum : ∑ k : Fin n, ((lagrangeBasis n nodes k x) ^ 2 +
        ((Finset.univ.filter (· ≠ k)).sum fun j =>
          lagrangeBasis n nodes k x * lagrangeBasis n nodes j x)) =
        ∑ k : Fin n, lagrangeBasis n nodes k x :=
      Finset.sum_congr rfl (fun k _ => h_each x k)
    rw [Finset.sum_add_distrib, partition_of_unity n hn nodes hd x] at h_sum
    linarith
  -- Integrate both sides: I = ∫ (1 - cross) = 2 - ∫ cross
  have h_eq : (fun x => ∑ k : Fin n, (lagrangeBasis n nodes k x) ^ 2) =
      (fun x => 1 - ∑ k : Fin n, ((Finset.univ.filter (· ≠ k)).sum fun j =>
        lagrangeBasis n nodes k x * lagrangeBasis n nodes j x)) :=
    funext hpw
  rw [h_eq, intervalIntegral.integral_sub intervalIntegrable_const
      (h_cross_cont.intervalIntegrable _ _),
    intervalIntegral.integral_const, smul_eq_mul, mul_one]
  norm_num

/--
**Single-node case**: For n = 1, I = 2.

With one node, l₁(x) = 1 (empty product), so I = ∫₋₁¹ 1 dx = 2.
-/
theorem lagrangeIntegral_single (nodes : Fin 1 → ℝ) :
    lagrangeIntegral 1 nodes = 2 := by
  unfold lagrangeIntegral
  -- For Fin 1, the sum is a single term and l_0 = 1 (empty product)
  have hbasis : ∀ x, lagrangeBasis 1 nodes 0 x = 1 := by
    intro x; unfold lagrangeBasis
    convert Finset.prod_empty (f := fun (i : Fin 1) =>
      (x - nodes i) / (nodes 0 - nodes i))
  have hsq : ∀ x, ∑ k : Fin 1, (lagrangeBasis 1 nodes k x) ^ 2 = 1 := by
    intro x; rw [Fin.sum_univ_one, hbasis x, one_pow]
  simp_rw [hsq]; norm_num

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

/--
For Chebyshev nodes, I ≈ 2 - c/n for some constant c.
-/
axiom chebyshev_integral_estimate (n : ℕ) (hn : n ≥ 2) :
    ∃ c : ℝ, c > 0 ∧
      |lagrangeIntegral n (chebyshevNodes n) - (2 - c / n)| ≤ c / n ^ 2

/-
## Part III-b: Gram Matrix Structure
-/

/--
**Pointwise Gram identity**: ∑ₖ l_k(x)² + gramOffDiag(x) = 1.

Follows from the partition of unity: multiply ∑ l_k = 1 by each l_k, use l_k · ∑l_j = l_k,
then sum to get ∑l_k² + ∑_{k≠j} l_k l_j = ∑l_k = 1.
-/
theorem sum_sq_plus_gramOffDiag_eq_one (n : ℕ) (hn : n ≥ 1) (nodes : Fin n → ℝ)
    (hd : AreDistinct n nodes) (x : ℝ) :
    (∑ k : Fin n, (lagrangeBasis n nodes k x) ^ 2) + gramOffDiag n nodes x = 1 := by
  unfold gramOffDiag
  -- For each k: l_k² + ∑_{j≠k} l_k·l_j = l_k (from partition of unity)
  have h_each : ∀ (k : Fin n),
      (lagrangeBasis n nodes k x) ^ 2 +
      ((Finset.univ.filter (· ≠ k)).sum fun j =>
        lagrangeBasis n nodes k x * lagrangeBasis n nodes j x) =
      lagrangeBasis n nodes k x := by
    intro k
    have h_total : (Finset.univ.sum fun j =>
        lagrangeBasis n nodes k x * lagrangeBasis n nodes j x) =
        lagrangeBasis n nodes k x := by
      rw [← Finset.mul_sum, partition_of_unity n hn nodes hd x, mul_one]
    have h_split := Finset.add_sum_erase Finset.univ
      (fun j => lagrangeBasis n nodes k x * lagrangeBasis n nodes j x)
      (Finset.mem_univ k)
    rw [sq, Finset.filter_ne']
    linarith
  -- Sum over k: ∑(l_k² + cross_k) = ∑l_k = 1
  have h_sum : ∑ k : Fin n, ((lagrangeBasis n nodes k x) ^ 2 +
      ((Finset.univ.filter (· ≠ k)).sum fun j =>
        lagrangeBasis n nodes k x * lagrangeBasis n nodes j x)) =
      ∑ k : Fin n, lagrangeBasis n nodes k x :=
    Finset.sum_congr rfl (fun k _ => h_each k)
  rw [Finset.sum_add_distrib, partition_of_unity n hn nodes hd x] at h_sum
  linarith

/--
Continuity of the off-diagonal Gram function.
-/
theorem gramOffDiag_continuous (n : ℕ) (nodes : Fin n → ℝ) :
    Continuous (gramOffDiag n nodes) := by
  unfold gramOffDiag
  apply continuous_finset_sum; intro k _
  apply continuous_finset_sum; intro j _
  exact (lagrangeBasis_continuous n nodes k).mul (lagrangeBasis_continuous n nodes j)

/--
**Gram vanishing at nodes**: gramOffDiag(xⱼ) = 0 for each node xⱼ.

At node xⱼ, exactly one basis function is nonzero (l_j(xⱼ) = 1), so all cross terms
l_k · l_i with k ≠ i vanish (at least one factor is 0).
-/
theorem gramOffDiag_at_node (n : ℕ) (nodes : Fin n → ℝ) (hd : AreDistinct n nodes)
    (j : Fin n) : gramOffDiag n nodes (nodes j) = 0 := by
  unfold gramOffDiag
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mem_filter] at hi
  by_cases hkj : k = j
  · -- k = j: then i ≠ k = j, so l_i(xⱼ) = 0
    rw [hkj] at hi
    rw [lagrangeBasis_other n nodes hd i j hi.2, mul_zero]
  · -- k ≠ j: l_k(xⱼ) = 0, so the term is 0
    rw [lagrangeBasis_other n nodes hd k j hkj, zero_mul]

/--
**Sum of squared basis at nodes**: ∑ₖ l_k(xⱼ)² = 1 at each node.

Since l_j(xⱼ) = 1 and l_k(xⱼ) = 0 for k ≠ j, only the j-th term contributes.
-/
theorem sum_sq_at_node (n : ℕ) (nodes : Fin n → ℝ) (hd : AreDistinct n nodes)
    (j : Fin n) :
    ∑ k : Fin n, (lagrangeBasis n nodes k (nodes j)) ^ 2 = 1 := by
  have h : ∀ k : Fin n, (lagrangeBasis n nodes k (nodes j)) ^ 2 =
      if k = j then 1 else 0 := by
    intro k
    by_cases hkj : k = j
    · subst hkj; simp [lagrangeBasis_self n nodes hd]
    · simp [lagrangeBasis_other n nodes hd k j hkj, hkj]
  simp_rw [h, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-
## Part III-c: Quadrature Theory
-/

/--
**Gauss quadrature identity**: If the quadrature ∑ wₖ f(xₖ) is exact for the
squared Lagrange basis functions l_k², then I(x₁,...,xₙ) = 2.

This holds for Gauss-Legendre nodes (where quadrature is exact for degree ≤ 2n−1,
and l_k² has degree 2(n−1) ≤ 2n−2 < 2n−1). The hypothesis states exactness
directly for l_k², avoiding polynomial degree machinery.

Key insight: the minimum of I (conjectured ≈ 2 − (1+o(1))/n) is NOT at Gauss nodes.
-/
theorem lagrangeIntegral_eq_two_of_sq_exact (n : ℕ) (hn : n ≥ 1)
    (nodes : Fin n → ℝ) (hd : AreDistinct n nodes)
    (hexact : ∀ k : Fin n,
      ∫ x in (-1 : ℝ)..1, (lagrangeBasis n nodes k x) ^ 2 =
        ∑ j : Fin n, quadratureWeight n nodes j *
          (lagrangeBasis n nodes k (nodes j)) ^ 2) :
    lagrangeIntegral n nodes = 2 := by
  -- Step 1: Each ∫l_k² = w_k (by quadrature exactness + interpolation properties)
  have h_each : ∀ k : Fin n,
      ∫ x in (-1 : ℝ)..1, (lagrangeBasis n nodes k x) ^ 2 =
        quadratureWeight n nodes k := by
    intro k
    rw [hexact k]
    -- Evaluate: l_k(x_j)² = 1 if j = k, else 0
    have h_eval : ∀ j : Fin n, (lagrangeBasis n nodes k (nodes j)) ^ 2 =
        if j = k then 1 else 0 := by
      intro j
      by_cases hjk : j = k
      · subst hjk; simp [lagrangeBasis_self n nodes hd]
      · simp [lagrangeBasis_other n nodes hd k j (Ne.symm hjk), hjk]
    simp_rw [h_eval, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  -- Step 2: I = ∑∫l_k² = ∑w_k = 2
  unfold lagrangeIntegral
  rw [intervalIntegral.integral_finset_sum (fun k _ =>
    ((lagrangeBasis_continuous n nodes k).pow 2).intervalIntegrable _ _)]
  simp_rw [h_each]
  exact quadrature_weights_sum n hn nodes hd

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
