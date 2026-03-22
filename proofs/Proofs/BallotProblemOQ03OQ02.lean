import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-
# General r×r LGV Lemma (OQ-03-OQ-02)

## What This Proves

This file states and develops infrastructure for the general r×r
Lindström-Gessel-Viennot (LGV) Lemma, generalizing the 2×2 case
proved in BallotProblemOQ03.lean.

## The r×r LGV Lemma

**Theorem** (Lindström 1973, Gessel-Viennot 1985):
Let A₁,...,Aᵣ be source vertices and B₁,...,Bᵣ be sink vertices in a
directed acyclic graph. Then:

  #{non-intersecting r-tuples (P₁,...,Pᵣ) with Pᵢ: Aᵢ → Bᵢ}
  = det[e(Aᵢ, Bⱼ)]ᵢⱼ

where e(A,B) is the number of directed paths from A to B, weighted
by their edge weights in the general case.

## Proof Strategy

The proof uses a sign-reversing involution:
1. Write the determinant using the Leibniz formula:
   det[M] = Σ_σ sgn(σ) · Π_i M(i, σ(i))
2. Interpret each term as: sign(σ) × #{r-tuples with Pᵢ: Aᵢ → B_{σ(i)}}
3. Show that intersecting r-tuples cancel in pairs via Gessel-Viennot involution
4. The surviving terms have σ = id, contributing +1 × #{non-intersecting tuples}

## Extends
- BallotProblemOQ03.lean: 2×2 LGV fully proved (2878 lines, 0 axioms, 0 sorries)
-/

namespace LGV

open Matrix Equiv Finset BigOperators

-- ========================================================================
-- Part I: Path Weight Matrix
-- ========================================================================

/-- The path weight matrix M where M(i,j) = e(Aᵢ, Bⱼ) = number of paths
from source i to sink j. For lattice paths, this is a binomial coefficient. -/
def pathMatrix (r : ℕ) (e : Fin r → Fin r → ℤ) : Matrix (Fin r) (Fin r) ℤ :=
  Matrix.of e

/-- For lattice paths with m East steps, the weight e(Aᵢ, Bⱼ) = C(m + bⱼ - aᵢ, m)
when bⱼ ≥ aᵢ, and 0 otherwise. -/
def latticePathMatrix (r m : ℕ) (a b : Fin r → ℕ) : Matrix (Fin r) (Fin r) ℤ :=
  Matrix.of (fun i j =>
    if b j ≥ a i then (Nat.choose (m + (b j - a i)) m : ℤ) else 0)

-- ========================================================================
-- Part II: r-Tuples of Paths
-- ========================================================================

/-- An r-tuple of path counts: for each permutation σ, the product
Π_i e(Aᵢ, B_{σ(i)}) counts the total number of r-tuples of paths
where path i goes from Aᵢ to B_{σ(i)}. -/
def permPathCount (r : ℕ) (e : Fin r → Fin r → ℤ) (σ : Perm (Fin r)) : ℤ :=
  ∏ i : Fin r, e i (σ i)

/-- The signed contribution of a permutation σ to the determinant. -/
def signedPermPathCount (r : ℕ) (e : Fin r → Fin r → ℤ) (σ : Perm (Fin r)) : ℤ :=
  Perm.sign σ * permPathCount r e σ

-- ========================================================================
-- Part III: The Determinant as a Sum Over Permutations
-- ========================================================================

/-- The determinant of the path matrix equals the signed sum over all permutations.
This is the Leibniz formula for the determinant. -/
theorem det_eq_signed_sum (r : ℕ) (e : Fin r → Fin r → ℤ) :
    (pathMatrix r e).det = ∑ σ : Perm (Fin r), signedPermPathCount r e σ := by
  rw [← Matrix.det_transpose (pathMatrix r e)]
  simp [signedPermPathCount, permPathCount, pathMatrix,
    Matrix.det_apply, Matrix.transpose_apply, Matrix.of_apply, Units.smul_def]

-- ========================================================================
-- Part IV: Non-Intersecting r-Tuples
-- ========================================================================

/-- An r-tuple of "abstract paths" (here represented just by their indices)
is non-intersecting if no two paths share a vertex.

In the lattice path setting, this means the paths from different sources
never visit the same lattice point simultaneously. -/
def NonIntersecting (r : ℕ) (paths : Fin r → Type*) (visited : ∀ i, paths i → Set ℕ) : Prop :=
  ∀ i j : Fin r, i ≠ j → Disjoint (Set.range (visited i)) (Set.range (visited j))

-- ========================================================================
-- Part V: The Gessel-Viennot Involution
-- ========================================================================

/-
## The Sign-Reversing Involution

For each intersecting r-tuple P = (P₁,...,Pᵣ) with Pᵢ: Aᵢ → B_{σ(i)}:

1. **Find the first intersection**: Let i₀ be the smallest index such that
   path Pᵢ₀ shares a point with some later path Pⱼ (j > i₀).
   Let p be the first such shared point.

2. **Swap tails**: After point p, swap the tails of Pᵢ₀ and Pⱼ.
   This creates paths Pᵢ₀': Aᵢ₀ → B_{σ(j)} and Pⱼ': Aⱼ → B_{σ(i₀)}.

3. **Update the permutation**: The new r-tuple corresponds to the permutation
   σ' = σ ∘ (i₀ j), which has opposite sign: sign(σ') = -sign(σ).

4. **This is an involution**: Applying the same procedure to (P₁,...,Pᵢ₀',...,Pⱼ',...,Pᵣ)
   swaps the tails back, returning to the original tuple.

5. **Cancellation**: Since sign(σ') = -sign(σ), the signed contributions of
   P and its image cancel: sign(σ)·w(P) + sign(σ')·w(P') = 0.

6. **Survivors**: Only non-intersecting tuples (σ = id, all paths Aᵢ→Bᵢ)
   survive, contributing sign(id)·w(P) = +1·w(P).
-/

/-- The Gessel-Viennot involution pairs intersecting path tuples
with opposite-sign partners. This is the heart of the LGV proof. -/
theorem gv_involution_cancellation (r : ℕ) (e : Fin r → Fin r → ℤ) :
    ∑ σ ∈ Finset.univ.filter (fun σ : Perm (Fin r) => σ ≠ 1),
      signedPermPathCount r e σ = 0 := by
  sorry -- Requires: the involution construction + cancellation argument

-- ========================================================================
-- Part VI: The r×r LGV Lemma (Statement)
-- ========================================================================

/-- **The General LGV Lemma**: The number of non-intersecting r-tuples
of paths equals the determinant of the path weight matrix.

In the general DAG setting:
  #{NI r-tuples (Pᵢ: Aᵢ → Bᵢ)} = det[e(Aᵢ, Bⱼ)]

For lattice paths:
  #{NI r-tuples} = det[C(m + bⱼ - aᵢ, m)] -/
theorem lgv_lemma_general (r : ℕ) (e : Fin r → Fin r → ℤ)
    (h_involution : ∀ σ : Perm (Fin r), σ ≠ 1 →
      ∃ σ' : Perm (Fin r), σ' ≠ σ ∧
        signedPermPathCount r e σ + signedPermPathCount r e σ' = 0) :
    (pathMatrix r e).det = permPathCount r e 1 := by
  sorry -- Follows from: det = Σ_σ sign(σ)·Π e(i,σi), non-id terms cancel by h_involution

-- ========================================================================
-- Part VII: Specialization to 2×2
-- ========================================================================

/-- The 2×2 case: det[[e(A₁,B₁), e(A₁,B₂)], [e(A₂,B₁), e(A₂,B₂)]]
= e(A₁,B₁)·e(A₂,B₂) - e(A₁,B₂)·e(A₂,B₁). -/
theorem lgv_2x2_det (e : Fin 2 → Fin 2 → ℤ) :
    (pathMatrix 2 e).det = e 0 0 * e 1 1 - e 0 1 * e 1 0 := by
  simp [pathMatrix, Matrix.det_fin_two, Matrix.of_apply]

/-- The identity permutation contributes e(A₁,B₁)·e(A₂,B₂). -/
theorem lgv_2x2_identity (e : Fin 2 → Fin 2 → ℤ) :
    permPathCount 2 e 1 = e 0 0 * e 1 1 := by
  simp [permPathCount, Fin.prod_univ_two, Perm.one_apply]

-- ========================================================================
-- Part VIII: The LGV Determinant for 3×3
-- ========================================================================

/-- The 3×3 case statement: the determinant of the 3×3 path matrix. -/
theorem lgv_3x3_det (e : Fin 3 → Fin 3 → ℤ) :
    (pathMatrix 3 e).det =
      e 0 0 * e 1 1 * e 2 2 - e 0 0 * e 1 2 * e 2 1
    - e 0 1 * e 1 0 * e 2 2 + e 0 1 * e 1 2 * e 2 0
    + e 0 2 * e 1 0 * e 2 1 - e 0 2 * e 1 1 * e 2 0 := by
  simp [pathMatrix, Matrix.det_fin_three, Matrix.of_apply]

-- ========================================================================
-- Part IX: Properties of the LGV Determinant
-- ========================================================================

/-- Swapping two rows negates the determinant (antisymmetry of sources). -/
theorem lgv_swap_sources (r : ℕ) (e : Fin r → Fin r → ℤ) (i j : Fin r) (h : i ≠ j) :
    (pathMatrix r (fun a b => e (Equiv.swap i j a) b)).det =
    -(pathMatrix r e).det := by
  have : pathMatrix r (fun a b => e (Equiv.swap i j a) b) =
      (pathMatrix r e).submatrix (Equiv.swap i j) id := by
    ext a b; simp [pathMatrix, Matrix.submatrix, Matrix.of_apply]
  rw [this, Matrix.det_permute, Equiv.Perm.sign_swap h]; simp

/-- The determinant is zero if two sources are identical. -/
theorem lgv_repeated_source (r : ℕ) (e : Fin r → Fin r → ℤ) (i j : Fin r) (h : i ≠ j)
    (h_eq : ∀ k, e i k = e j k) :
    (pathMatrix r e).det = 0 := by
  have hrow : (pathMatrix r e) i = (pathMatrix r e) j := by
    ext k; simp [pathMatrix, Matrix.of_apply, h_eq k]
  exact Matrix.det_zero_of_row_eq h hrow

-- ========================================================================
-- Verification
-- ========================================================================

#check det_eq_signed_sum
#check lgv_lemma_general
#check lgv_2x2_det
#check lgv_2x2_identity
#check lgv_3x3_det

end LGV
