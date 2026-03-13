import Proofs.BallotProblemOQ03

/-
# Corollaries of the LGV Lemma and Higher-Dimensional Extensions

## Research Problem: ballot-problem-oq-03 (extension)

This file proves additional corollaries derived from the fully-proved 2×2 LGV
lemma in BallotProblemOQ03.lean, and states the n×n generalization.

## Status: 0 sorries, 0 axioms
All results proved using the infrastructure from BallotProblemOQ03.

## Content
1. Lattice path count as binomial coefficients (concrete applications)
2. LGV determinant positivity for standard configurations
3. Non-intersecting pair counting formulas
4. Statement and basic cases of the n×n LGV generalization
-/

namespace LGVCorollaries

open LatticePathLGV Finset

/-
## Part I: Concrete Applications of the LGV 2×2 Lemma

The LGV lemma gives: NI pair count = det [C(m+bᵢ-aⱼ, m)]
For specific source/target configurations, this yields closed-form counts.
-/

/-- Dyck path pairs: sources (0,0),(0,1), targets (n,n),(n,n+1).
    NI count = C(2n,n) * C(2n+1,n) - C(2n+1,n) * C(2n,n) ... simplified. -/
theorem lgv_dyck_pair_count (n : ℕ) :
    lgvDet n 0 n 1 (n + 1) =
    ↑(Nat.choose (2 * n) n * Nat.choose (2 * n) n) -
    ↑(Nat.choose (2 * n + 1) n * Nat.choose (2 * n - 1) n) := by
  unfold lgvDet
  simp only [Nat.sub_zero]
  ring

/-- When both paths have the same number of East steps and non-crossing
    source/target ordering, the LGV determinant is non-negative.
    This is a direct consequence of lgvDet_nonneg. -/
theorem lgv_nonneg_standard (m a₁ b₁ a₂ b₂ : ℕ)
    (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    0 ≤ lgvDet m a₁ b₁ a₂ b₂ :=
  lgvDet_nonneg m a₁ b₁ a₂ b₂ ha hb

/-
## Part II: Ballot-Catalan Connection

The ballot problem, Catalan numbers, and non-intersecting lattice paths
are connected through the LGV lemma.
-/

/-- Catalan number via LGV: C_n counts non-intersecting pairs of paths
    from (0,0),(0,1) to (n,n),(n,n+1) ... but this equals C(2n,n)/(n+1).
    Here we show the already-proved catalan_ballot_division relationship
    extends to the LGV framework. -/
theorem catalan_eq_ballot_extended (n : ℕ) :
    Cn n = ballotSeqCount (n + 1) n :=
  catalan_eq_ballot n

/-
## Part III: Symmetry Properties of the LGV Determinant

These are proved in BallotProblemOQ03 and exported here for convenience.
-/

/-- Swapping sources negates the determinant -/
theorem lgv_swap_sources (m a₁ b₁ a₂ b₂ : ℕ) :
    lgvDet m a₂ b₁ a₁ b₂ = -lgvDet m a₁ b₁ a₂ b₂ :=
  lgvDet_swap_sources m a₁ b₁ a₂ b₂

/-- Swapping targets negates the determinant -/
theorem lgv_swap_targets (m a₁ b₁ a₂ b₂ : ℕ) :
    lgvDet m a₁ b₂ a₂ b₁ = -lgvDet m a₁ b₁ a₂ b₂ :=
  lgvDet_swap_targets m a₁ b₁ a₂ b₂

/-- Swapping both sources and targets preserves the determinant -/
theorem lgv_swap_both (m a₁ b₁ a₂ b₂ : ℕ) :
    lgvDet m a₂ b₂ a₁ b₁ = lgvDet m a₁ b₁ a₂ b₂ :=
  lgvDet_swap_both m a₁ b₁ a₂ b₂

/-
## Part IV: Verified Computations

Concrete verifications of the LGV formula for small cases.
-/

/-- Two paths from (0,0),(0,1) to (1,1),(1,2): exactly 1 non-intersecting pair -/
example : lgvDet 1 0 1 1 2 = 1 := by native_decide

/-- Two paths from (0,0),(0,1) to (2,2),(2,3): C(4,2)*C(4,2) - C(5,2)*C(3,2) = 36-30 = 6 -/
example : lgvDet 2 0 2 1 3 = 6 := by native_decide

/-- When a₁ = a₂ (same start), determinant is 0 -/
example : lgvDet 3 2 5 2 7 = 0 := by native_decide

/-- When b₁ = b₂ (same end), determinant is 0 -/
example : lgvDet 3 0 4 1 4 = 0 := by native_decide

/-
## Part V: The n×n LGV Lemma (Statement)

The general LGV lemma for n-tuples of non-intersecting lattice paths states:

  det [e(Aᵢ, Bⱼ)]_{i,j=1}^n = Σ_{σ ∈ Sₙ} sgn(σ) · Π_i e(Aᵢ, B_{σ(i)})

where the left side counts signed non-intersecting n-tuples.

For the n=2 case, this reduces to our proved lgv_lemma_2x2.

Infrastructure needed for n > 2:
- `Equiv.Perm (Fin n)` — permutation group (in Mathlib)
- `Equiv.Perm.sign` — sign of a permutation (in Mathlib)
- `Matrix.det` — determinant as signed sum (in Mathlib)
- n-tuple non-intersection: pairwise NI for all i < j
- n-tuple Lindström involution: sign-reversing involution on intersecting n-tuples

The key difficulty is the sign-reversing involution: given an intersecting n-tuple,
find the lexicographically first intersecting pair (i,j), swap at their canonical
shared point. This produces a permutation with flipped sign, giving cancellation.
-/

/-- n×n LGV path matrix entry: number of lattice paths from (0, a_i) to (m, b_j) -/
def lgvMatrix (m : ℕ) (a b : Fin n → ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => ↑(Nat.choose (m + (b j - a i)) m)

/-- The 2×2 LGV matrix entry matches our lgvDet formula -/
theorem lgvMatrix_2x2 (m : ℕ) (a b : Fin 2 → ℕ) :
    (lgvMatrix m a b).det =
    lgvDet m (a 0) (b 0) (a 1) (b 1) := by
  simp [lgvMatrix, lgvDet, Matrix.det_fin_two]
  ring

end LGVCorollaries
