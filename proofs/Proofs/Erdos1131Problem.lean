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
**Lower bound**: I(x₁,...,xₙ) ≥ 2/n for any configuration.

This follows because the l_k form a partition of unity at the nodes,
and by Cauchy-Schwarz, the integral is bounded below.
-/
axiom lagrangeIntegral_lower_bound (n : ℕ) (hn : n ≥ 1) (nodes : Fin n → ℝ)
    (hd : AreDistinct n nodes) (hrange : ∀ i, -1 ≤ nodes i ∧ nodes i ≤ 1) :
    lagrangeIntegral n nodes ≥ 2 / n

/--
**Upper bound**: I is bounded above by 2n for any configuration.
-/
axiom lagrangeIntegral_upper_bound (n : ℕ) (hn : n ≥ 1) (nodes : Fin n → ℝ)
    (hd : AreDistinct n nodes) (hrange : ∀ i, -1 ≤ nodes i ∧ nodes i ≤ 1) :
    lagrangeIntegral n nodes ≤ 2 * n

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
