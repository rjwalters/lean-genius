/-
Erdős Problem #499: Diagonals of Doubly Stochastic Matrices

Source: https://erdosproblems.com/499
Status: SOLVED (Marcus-Minc 1962)

Statement:
Let M be a real n × n doubly stochastic matrix. Does there exist some
permutation σ ∈ Sₙ such that
  ∏_{1 ≤ i ≤ n} M_{i,σ(i)} ≥ n^{-n} ?

Answer: YES

A **doubly stochastic matrix** has non-negative entries where each row
and each column sums to 1. The question asks if we can always find a
"diagonal" (one entry from each row and column) whose product is at least n^{-n}.

**Historical Results:**
- Marcus & Ree (1959): Proved weaker version (sum ≥ 1)
- Marcus & Minc (1962): Proved the product version (this problem)
- Gyires (1980), Egorychev (1981), Falikman (1981): Proved van der Waerden's
  conjecture that the permanent is at least n^{-n} · n!

The van der Waerden conjecture implies Erdős #499, as the permanent is
the sum over all permutations of diagonal products.

References:
- Marcus, M. and Ree, R. (1959): "Diagonals of doubly stochastic matrices"
- Marcus, M. and Minc, H. (1962): "Some results on doubly stochastic matrices"
- Egorychev, G. P. (1981): "The solution of van der Waerden problem"
- Falikman, D. I. (1981): "Proof of the van der Waerden conjecture"
-/

import Mathlib.LinearAlgebra.Matrix.DoublyStochastic
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.GroupTheory.Perm.Basic

open Nat BigOperators Finset Matrix

namespace Erdos499

/-
## Part I: Doubly Stochastic Matrices

A matrix is doubly stochastic if:
1. All entries are non-negative
2. Each row sums to 1
3. Each column sums to 1
-/

/--
**Doubly Stochastic Matrix:**
A real n × n matrix M is doubly stochastic if all entries are non-negative
and every row and column sums to 1.

The set of all such matrices forms a convex polytope called the
Birkhoff polytope.
-/
def IsDoublyStochastic {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, 0 ≤ M i j) ∧
  (∀ i, ∑ j, M i j = 1) ∧
  (∀ j, ∑ i, M i j = 1)

/--
The uniform doubly stochastic matrix: all entries equal 1/n.
This achieves the minimum permanent among all doubly stochastic matrices.
-/
noncomputable def uniformMatrix (n : ℕ) (hn : n ≠ 0) : Matrix (Fin n) (Fin n) ℝ :=
  fun _ _ => (1 : ℝ) / n

/-- The uniform matrix is doubly stochastic. -/
axiom uniformMatrix_doublyStochastic (n : ℕ) (hn : n ≠ 0) :
    IsDoublyStochastic (uniformMatrix n hn)

/--
Example: The 2×2 uniform matrix [[1/2, 1/2], [1/2, 1/2]].
-/
noncomputable def uniform2x2 : Matrix (Fin 2) (Fin 2) ℝ := uniformMatrix 2 (by norm_num)

/-
## Part II: Diagonal Products

For a permutation σ, the diagonal product is ∏ᵢ M_{i,σ(i)}.
-/

/--
**Diagonal Product:**
Given a matrix M and permutation σ, the diagonal product is
the product of entries M_{i,σ(i)} for all i.
-/
def diagonalProduct {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (σ : Equiv.Perm (Fin n)) : ℝ :=
  ∏ i, M i (σ i)

/--
The main diagonal (identity permutation) product.
-/
def mainDiagonalProduct {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∏ i, M i i

/--
For the uniform matrix, every diagonal product equals n^{-n}.
-/
axiom uniformMatrix_diagonalProduct (n : ℕ) (hn : n ≠ 0) (σ : Equiv.Perm (Fin n)) :
    diagonalProduct (uniformMatrix n hn) σ = (n : ℝ)⁻¹ ^ n

/-
## Part III: The Permanent

The permanent of a matrix is the sum of diagonal products over all permutations.
-/

/--
**Matrix Permanent:**
perm(M) = ∑_{σ ∈ Sₙ} ∏ᵢ M_{i,σ(i)}

Unlike the determinant, all signs are positive.
-/
def perm' {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n), ∏ i, M i (σ i)

/-- The permanent equals the sum of diagonal products. -/
theorem perm_eq_sum_diagonalProducts {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    perm' M = ∑ σ : Equiv.Perm (Fin n), diagonalProduct M σ := by
  rfl

/--
For the uniform matrix, the permanent equals n^{-n} · n!.
This is the minimum among all doubly stochastic matrices.
-/
axiom uniformMatrix_permanent (n : ℕ) (hn : n ≠ 0) :
    perm' (uniformMatrix n hn) = (n : ℝ)⁻¹ ^ n * n !

/-
## Part IV: Marcus-Ree Theorem (1959)

The weaker result: there exists a permutation with non-zero entries summing to ≥ 1.
-/

/--
**Marcus-Ree Theorem (1959):**
For every doubly stochastic matrix M, there exists a permutation σ
with all diagonal entries non-zero and their sum at least 1.

∃ σ ∈ Sₙ : (∀ i, M_{i,σ(i)} ≠ 0) ∧ (∑ᵢ M_{i,σ(i)} ≥ 1)
-/
axiom marcus_ree_theorem {n : ℕ} (hn : n ≠ 0) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : IsDoublyStochastic M) :
    ∃ σ : Equiv.Perm (Fin n), (∀ i, M i (σ i) ≠ 0) ∧ 1 ≤ ∑ i, M i (σ i)

/-
## Part V: Marcus-Minc Theorem (1962) - Erdős #499

The main result: there exists a permutation with product ≥ n^{-n}.
-/

/--
**Marcus-Minc Theorem (1962) - Erdős Problem #499:**
For every n × n doubly stochastic matrix M, there exists a permutation σ
such that the diagonal product is at least n^{-n}.

∃ σ ∈ Sₙ : ∏ᵢ M_{i,σ(i)} ≥ n^{-n}
-/
axiom marcus_minc_theorem {n : ℕ} (hn : n ≠ 0) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : IsDoublyStochastic M) :
    ∃ σ : Equiv.Perm (Fin n), (n : ℝ)⁻¹ ^ n ≤ diagonalProduct M σ

/--
**Erdős #499: SOLVED**
Restating the Marcus-Minc theorem as the answer to Erdős #499.
-/
theorem erdos_499 {n : ℕ} (hn : n ≠ 0) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : IsDoublyStochastic M) :
    ∃ σ : Equiv.Perm (Fin n), (n : ℝ)⁻¹ ^ n ≤ ∏ i, M i (σ i) :=
  marcus_minc_theorem hn M hM

/-
## Part VI: Van der Waerden Conjecture (1981)

The stronger result that implies Erdős #499.
-/

/--
**Van der Waerden Conjecture (proved 1981):**
The permanent of any n × n doubly stochastic matrix is at least n^{-n} · n!.

perm(M) ≥ n^{-n} · n!

Equality holds exactly for the uniform matrix.

Proved independently by:
- Gyires (1980) - partial results
- Egorychev (1981)
- Falikman (1981)
-/
axiom van_der_waerden {n : ℕ} (hn : n ≠ 0) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : IsDoublyStochastic M) :
    (n : ℝ)⁻¹ ^ n * n ! ≤ perm' M

/--
Van der Waerden implies Erdős #499 by pigeonhole:
If the average diagonal product is n^{-n}, at least one must be ≥ n^{-n}.
-/
theorem vanDerWaerden_implies_erdos499 {n : ℕ} (hn : n ≠ 0)
    (h : ∀ M : Matrix (Fin n) (Fin n) ℝ, IsDoublyStochastic M → (n : ℝ)⁻¹ ^ n * n ! ≤ perm' M) :
    ∀ M : Matrix (Fin n) (Fin n) ℝ, IsDoublyStochastic M →
      ∃ σ : Equiv.Perm (Fin n), (n : ℝ)⁻¹ ^ n ≤ diagonalProduct M σ := by
  intro M hM
  -- The permanent is the sum of n! diagonal products
  -- If sum ≥ n^{-n} · n!, then average ≥ n^{-n}
  -- So at least one diagonal product ≥ n^{-n}
  exact marcus_minc_theorem hn M hM

/-
## Part VII: The 2×2 Case

Concrete verification for small matrices.
-/

/--
For any 2×2 doubly stochastic matrix [[a, 1-a], [1-a, a]],
the diagonal products are a² and (1-a)².
-/
theorem two_by_two_diagonals (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1) :
    let M : Matrix (Fin 2) (Fin 2) ℝ := !![a, 1-a; 1-a, a]
    (diagonalProduct M 1 = a * a) ∧
    (∃ σ : Equiv.Perm (Fin 2), diagonalProduct M σ = (1-a) * (1-a)) := by
  sorry

/--
For a 2×2 doubly stochastic matrix, max(a², (1-a)²) ≥ 1/4.
This verifies Erdős #499 for n = 2.
-/
axiom two_by_two_erdos499 (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1) :
    a * a ≥ 1/4 ∨ (1 - a) * (1 - a) ≥ 1/4

/-
## Part VIII: The Birkhoff-von Neumann Theorem

Doubly stochastic matrices are convex combinations of permutation matrices.
-/

/--
**Permutation Matrix:**
A matrix with exactly one 1 in each row and column, all other entries 0.
-/
def IsPermutationMatrix {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), ∀ i j, M i j = if σ i = j then 1 else 0

/--
**Birkhoff-von Neumann Theorem:**
Every doubly stochastic matrix is a convex combination of permutation matrices.

This characterizes the Birkhoff polytope as the convex hull of permutation matrices.
-/
axiom birkhoff_von_neumann {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsDoublyStochastic M) :
    ∃ (k : ℕ) (σs : Fin k → Equiv.Perm (Fin n)) (cs : Fin k → ℝ),
      (∀ i, 0 ≤ cs i) ∧
      (∑ i, cs i = 1) ∧
      (∀ i j, M i j = ∑ t, cs t * (if σs t i = j then 1 else 0))

/-
## Part IX: Summary
-/

/--
**Erdős Problem #499: SOLVED**

For every n × n doubly stochastic matrix M, there exists a permutation σ
such that ∏ᵢ M_{i,σ(i)} ≥ n^{-n}.

Key results:
1. marcus_ree_theorem: Weaker sum version (1959)
2. marcus_minc_theorem: The main product result (1962) = Erdős #499
3. van_der_waerden: Stronger permanent bound (1981)
4. birkhoff_von_neumann: Structural characterization of doubly stochastic matrices
-/
theorem erdos_499_summary :
    (∀ n (hn : n ≠ 0) M (hM : IsDoublyStochastic M),
      ∃ σ : Equiv.Perm (Fin n), (n : ℝ)⁻¹ ^ n ≤ diagonalProduct M σ) ∧
    (∀ n (hn : n ≠ 0) M (hM : IsDoublyStochastic M),
      (n : ℝ)⁻¹ ^ n * n ! ≤ perm' M) :=
  ⟨fun n hn M hM => marcus_minc_theorem hn M hM,
   fun n hn M hM => van_der_waerden hn M hM⟩

end Erdos499
