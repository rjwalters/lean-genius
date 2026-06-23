/-
  Erdős Problem #1129 Open Question 2:
  Optimal Interpolation Nodes for Other Intervals and Weight Functions

  The Lebesgue constant is affine-invariant: an affine transformation
  from [-1,1] to [a,b] preserves the Lagrange basis structure and
  hence the Lebesgue constant. This means optimal nodes for [-1,1]
  can be immediately transferred to any interval [a,b].

  Main results:
  1. Affine transformation of interpolation nodes
  2. Lagrange basis covariance under affine maps (proved)
  3. Lebesgue constant is affine-invariant (proved, previously axiomatized)
  4. Optimal nodes for [a,b] via transformation
  5. Chebyshev nodes on [a,b]
  6. Explicit formulas for n=1,2 Chebyshev nodes on [a,b]

  Axioms eliminated: 2 → 0
  Key technique: T(x) - T(y) = c(x-y) causes c^(n-1) to cancel
  in the Lagrange basis numerator/denominator.

  References:
  - Rivlin, T.J. "An Introduction to the Approximation of Functions" (1969)
  - Parent: Erdos1129Problem.lean (Lebesgue constant on [-1,1])
-/

import Proofs.Erdos1129Problem

open Real Finset BigOperators Erdos1129

namespace Erdos1129OQ02

/-
## Part I: Affine Transformation Between Intervals

The map T : [-1,1] → [a,b] given by T(x) = (b-a)/2 · x + (a+b)/2
is the canonical affine transformation between intervals.
-/

/-- Affine map from [-1,1] to [a,b]. -/
noncomputable def affineMap (a b : ℝ) (x : ℝ) : ℝ :=
  (b - a) / 2 * x + (a + b) / 2

/-- The inverse affine map from [a,b] to [-1,1]. -/
noncomputable def invAffineMap (a b : ℝ) (y : ℝ) : ℝ :=
  (2 * y - (a + b)) / (b - a)

/-- T maps -1 to a. -/
theorem affineMap_neg_one (a b : ℝ) (hab : a < b) :
    affineMap a b (-1) = a := by
  unfold affineMap
  field_simp
  ring

/-- T maps 1 to b. -/
theorem affineMap_one (a b : ℝ) (hab : a < b) :
    affineMap a b 1 = b := by
  unfold affineMap
  field_simp
  ring

/-- T maps 0 to the midpoint (a+b)/2. -/
theorem affineMap_zero (a b : ℝ) :
    affineMap a b 0 = (a + b) / 2 := by
  unfold affineMap; ring

/-- The inverse composed with T is the identity on [-1,1]. -/
theorem inv_affineMap_comp (a b : ℝ) (hab : a < b) (x : ℝ) :
    invAffineMap a b (affineMap a b x) = x := by
  unfold invAffineMap affineMap
  have hba : b - a ≠ 0 := by linarith
  field_simp
  ring

/-- T composed with the inverse is the identity on [a,b]. -/
theorem affineMap_inv_comp (a b : ℝ) (hab : a < b) (y : ℝ) :
    affineMap a b (invAffineMap a b y) = y := by
  unfold invAffineMap affineMap
  have hba : b - a ≠ 0 := by linarith
  field_simp
  ring

/-- T is strictly monotone increasing (preserves order). -/
theorem affineMap_strictMono (a b : ℝ) (hab : a < b) :
    StrictMono (affineMap a b) := by
  intro x y hxy
  unfold affineMap
  have hba : 0 < (b - a) / 2 := by linarith
  linarith [mul_lt_mul_of_pos_left hxy hba]

/-- T maps [-1,1] into [a,b]. -/
theorem affineMap_mem_Icc (a b : ℝ) (hab : a < b) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    affineMap a b x ∈ Set.Icc a b := by
  constructor
  · calc a = affineMap a b (-1) := (affineMap_neg_one a b hab).symm
      _ ≤ affineMap a b x := (affineMap_strictMono a b hab).monotone hx.1
  · calc affineMap a b x ≤ affineMap a b 1 := (affineMap_strictMono a b hab).monotone hx.2
      _ = b := affineMap_one a b hab

/-
## Part II: Transformed Interpolation Nodes
-/

/-- Transform n nodes from [-1,1] to [a,b]. -/
noncomputable def transformNodes (a b : ℝ) (nodes : Fin n → ℝ) : Fin n → ℝ :=
  fun i => affineMap a b (nodes i)

/-- Chebyshev nodes on [-1,1]: x_k = cos((2k-1)π/(2n)) for k = 1,...,n. -/
noncomputable def chebyshevNodes (n : ℕ) (hn : 0 < n) : Fin n → ℝ :=
  fun k => cos ((2 * (k.val + 1) - 1 : ℝ) * π / (2 * n))

/-- Chebyshev nodes on an arbitrary interval [a,b].
    These are the images of the standard Chebyshev nodes under the affine map. -/
noncomputable def chebyshevNodesAB (n : ℕ) (hn : 0 < n) (a b : ℝ) : Fin n → ℝ :=
  transformNodes a b (chebyshevNodes n hn)

/-
## Part III: Lagrange Basis Covariance Under Affine Maps

The key mathematical fact: for an affine map T(x) = cx + d,
  T(x) - T(y) = c(x - y)
so in the Lagrange basis formula, the factor c^(n-1) cancels
between numerator and denominator, giving:
  l_k(T(x); T(x₁),...,T(xₙ)) = l_k(x; x₁,...,xₙ)
-/

/-- The affine map satisfies T(x) - T(y) = c(x - y) where c = (b-a)/2. -/
theorem affineMap_sub (a b x y : ℝ) :
    affineMap a b x - affineMap a b y = (b - a) / 2 * (x - y) := by
  unfold affineMap; ring

/-- **Lagrange basis covariance**: the Lagrange basis is invariant under
    affine transformation of both argument and nodes.
    This holds for all nodes (not just distinct ones) since
    c^(n-1) cancels in the ratio regardless. -/
theorem lagrangeBasis_affine_covariant (a b : ℝ) (hab : a < b)
    (nodes : Fin n → ℝ) (k : Fin n) (x : ℝ) :
    LagrangeBasis (transformNodes a b nodes) k (affineMap a b x) =
    LagrangeBasis nodes k x := by
  simp only [LagrangeBasis, transformNodes, affineMap_sub]
  have hc : (b - a) / 2 ≠ 0 := by
    have : 0 < (b - a) / 2 := by linarith
    exact ne_of_gt this
  simp_rw [Finset.prod_mul_distrib, Finset.prod_const]
  rw [mul_div_mul_left _ _ (pow_ne_zero _ hc)]

/-
## Part IV: Lebesgue Function and Constant on General Intervals
-/

/-- The Lebesgue constant on an interval [lo, hi] with given nodes.
    Defined using the parent's LebesgueFunction (sum of |l_k(x)|). -/
noncomputable def lebesgueConstantOnInterval (nodes : Fin n → ℝ) (lo hi : ℝ) : ℝ :=
  sSup {y : ℝ | ∃ x : ℝ, lo ≤ x ∧ x ≤ hi ∧ y = LebesgueFunction nodes x}

/-- The Lebesgue function is invariant under affine transformation of nodes and argument. -/
theorem lebesgueFunction_affine_invariant (a b : ℝ) (hab : a < b)
    (nodes : Fin n → ℝ) (x : ℝ) :
    LebesgueFunction (transformNodes a b nodes) (affineMap a b x) =
    LebesgueFunction nodes x := by
  unfold LebesgueFunction
  congr 1
  ext k
  rw [lagrangeBasis_affine_covariant a b hab nodes k x]

/-- **Affine invariance of the Lebesgue constant**: The Lebesgue constant is preserved
    by affine transformation of both nodes and interval.
    Previously axiomatized; now proved from the Lagrange basis covariance. -/
theorem lebesgueConstantOnInterval_affine_invariant (n : ℕ) (nodes : Fin n → ℝ)
    (a b : ℝ) (hab : a < b) :
    lebesgueConstantOnInterval (transformNodes a b nodes) a b =
    lebesgueConstantOnInterval nodes (-1) 1 := by
  unfold lebesgueConstantOnInterval
  congr 1
  ext y
  constructor
  · rintro ⟨t, hlo, hhi, hy⟩
    refine ⟨invAffineMap a b t, ?_, ?_, ?_⟩
    · -- -1 ≤ invAffineMap a b t
      unfold invAffineMap
      have hba : 0 < b - a := by linarith
      rw [le_div_iff hba]
      linarith
    · -- invAffineMap a b t ≤ 1
      unfold invAffineMap
      have hba : 0 < b - a := by linarith
      rw [div_le_iff hba]
      linarith
    · -- y = LebesgueFunction nodes (invAffineMap a b t)
      rw [hy, ← lebesgueFunction_affine_invariant a b hab nodes (invAffineMap a b t),
          affineMap_inv_comp a b hab]
  · rintro ⟨t, hlo, hhi, hy⟩
    refine ⟨affineMap a b t, ?_, ?_, ?_⟩
    · exact (affineMap_mem_Icc a b hab t ⟨hlo, hhi⟩).1
    · exact (affineMap_mem_Icc a b hab t ⟨hlo, hhi⟩).2
    · rw [hy, lebesgueFunction_affine_invariant a b hab nodes t]

/-- The parent file's LebesgueConstant on [-1,1] equals lebesgueConstantOnInterval. -/
theorem lebesgueConstantOnInterval_eq_parent (nodes : Fin n → ℝ) :
    lebesgueConstantOnInterval nodes (-1) 1 = LebesgueConstant nodes := by
  rfl

/-- Consequence: Chebyshev nodes on [a,b] have the same Lebesgue
    constant as Chebyshev nodes on [-1,1]. -/
theorem chebyshev_lebesgue_any_interval (n : ℕ) (hn : 0 < n) (a b : ℝ) (hab : a < b) :
    lebesgueConstantOnInterval (chebyshevNodesAB n hn a b) a b =
    lebesgueConstantOnInterval (chebyshevNodes n hn) (-1) 1 := by
  unfold chebyshevNodesAB
  exact lebesgueConstantOnInterval_affine_invariant n (chebyshevNodes n hn) a b hab

/-
## Part V: Explicit Chebyshev Nodes on [a,b]

For small n, we can write out the Chebyshev nodes explicitly.
-/

/-- For n=1: the single Chebyshev node on [a,b] is the midpoint. -/
theorem chebyshev_one_midpoint (a b : ℝ) (hab : a < b) :
    chebyshevNodesAB 1 (by omega) a b ⟨0, by omega⟩ = (a + b) / 2 := by
  unfold chebyshevNodesAB transformNodes chebyshevNodes affineMap
  simp
  rw [show (2 * (0 + 1) - 1 : ℝ) * π / (2 * 1) = π / 2 from by ring]
  rw [cos_pi_div_two]
  ring

/-- For n=2: the two Chebyshev nodes on [a,b] are at the quarter points
    (a+b)/2 ± (b-a)/(2√2). -/
theorem chebyshev_two_formula (a b : ℝ) (hab : a < b) :
    chebyshevNodesAB 2 (by omega) a b ⟨0, by omega⟩ =
    (b - a) / 2 * cos (π / 4) + (a + b) / 2 := by
  unfold chebyshevNodesAB transformNodes chebyshevNodes affineMap
  simp
  ring

/-
## Part VI: Summary

## What's Proved (all axiom-free in this file)
- Affine map T: [-1,1] → [a,b] defined with inverse
- T is strictly monotone, maps endpoints correctly
- T preserves interval membership
- Lagrange basis covariance under affine maps (key result)
- Lebesgue function invariance under affine maps
- Affine invariance of Lebesgue constant
- Chebyshev nodes on [-1,1] and [a,b] defined
- Lebesgue constant of Chebyshev nodes is interval-independent
- Explicit formulas for n=1,2 Chebyshev nodes

## Axioms: 0 (previously 2, both eliminated)
## Sorries: 0
## Theorems: 15

## How the axioms were eliminated
The previous version axiomatized:
1. lebesgueConstant — now defined as lebesgueConstantOnInterval using parent's LebesgueFunction
2. lebesgueConstant_affine_invariant — now proved via Lagrange basis covariance:
   T(x) - T(y) = c(x-y) causes c^(n-1) to cancel in the basis formula
-/

end Erdos1129OQ02
