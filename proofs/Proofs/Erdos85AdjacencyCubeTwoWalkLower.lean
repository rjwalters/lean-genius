import Proofs.Erdos85MuNegThreeZeroFiveAntipodalPairedWitness

/-! # Two distinct length-three walks force a cubic adjacency lower bound -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Two explicitly distinct length-three walks from `a` to `b` force the
corresponding integral cubic adjacency entry to be at least two.  It is enough
that their second internal vertices differ. -/
theorem adjMatrix_cube_apply_ge_two_of_two_walks
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a b w₁ k₁ w₂ k₂ : V}
    (haw₁ : G.Adj a w₁) (hw₁k₁ : G.Adj w₁ k₁) (hk₁b : G.Adj k₁ b)
    (haw₂ : G.Adj a w₂) (hw₂k₂ : G.Adj w₂ k₂) (hk₂b : G.Adj k₂ b)
    (hk : k₁ ≠ k₂) :
    (2 : ℤ) ≤ (G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ) a b := by
  classical
  let A := G.adjMatrix ℤ
  have hnonneg : ∀ u v, 0 ≤ A a u * A u v * A v b := by
    intro u v
    simp only [A, SimpleGraph.adjMatrix_apply]
    split_ifs <;> norm_num
  have hwalk₁ : A a w₁ * A w₁ k₁ * A k₁ b = 1 := by
    simp [A, SimpleGraph.adjMatrix_apply, haw₁, hw₁k₁, hk₁b]
  have hwalk₂ : A a w₂ * A w₂ k₂ * A k₂ b = 1 := by
    simp [A, SimpleGraph.adjMatrix_apply, haw₂, hw₂k₂, hk₂b]
  change (2 : ℤ) ≤ (A * A * A) a b
  simp only [Matrix.mul_apply]
  calc
    (2 : ℤ) =
        ∑ p ∈ ({(k₁, w₁), (k₂, w₂)} : Finset (V × V)),
          A a p.2 * A p.2 p.1 * A p.1 b := by
            rw [Finset.sum_pair (by intro h; exact hk (congrArg Prod.fst h))]
            rw [hwalk₁, hwalk₂]
            norm_num
    _ ≤ ∑ p : V × V, A a p.2 * A p.2 p.1 * A p.1 b := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.subset_univ _
          · intro p _ _
            exact hnonneg p.2 p.1
    _ = ∑ x, (∑ y, A a y * A y x) * A x b := by
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_mul]

/-- The paired-center fan/six-walk dichotomy has an immediate cubic form:
either the target is adjacent to the paired witness, or there are two
distinct length-three walks from the target to that witness. -/
theorem c4Free_pairedCommonTarget_fan_or_cube_ge_two
    {X : Type*} [Fintype X] [DecidableEq X]
    (G : SimpleGraph X) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 X G)
    (a d b y w₀ w₂ : X) (had : a ≠ d)
    (haw₀ : G.Adj a w₀) (hbw₀ : G.Adj b w₀)
    (hdw₂ : G.Adj d w₂) (hbw₂ : G.Adj b w₂)
    (hay : G.Adj a y) (hdy : G.Adj d y) :
    G.Adj b y ∨
      (2 : ℤ) ≤ (G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ) b y := by
  rcases c4Free_pairedCommonTarget_fan_or_sixWalk G hfree
      a d b y w₀ w₂ had haw₀ hbw₀ hdw₂ hbw₂ hay hdy with hfan | hsix
  · exact Or.inl hfan
  · exact Or.inr (adjMatrix_cube_apply_ge_two_of_two_walks G
      hbw₀ haw₀.symm hay hbw₂ hdw₂.symm hdy had)

end

end Erdos85

#print axioms Erdos85.adjMatrix_cube_apply_ge_two_of_two_walks
#print axioms Erdos85.c4Free_pairedCommonTarget_fan_or_cube_ge_two
