import Proofs.Erdos85BinaryCutGraphTwoPoleRoute

/-!
# Star activity as a cut in the triangle-edge graph

If a binary potential is constant across every edge of `T`, then `T` edges
contribute zero to endpoint differences.  On a star with an even number of
selected neighbors, its activity sum is therefore exactly the parity of
selected non-`T` edges crossing the potential support.  This is the local
engine of `(73rnz_cjibkzh)`.
-/

open SimpleGraph

namespace Erdos85

/-- Selected neighbors joined to `y` by a non-`T` edge and lying across the
binary-potential cut from `y`. -/
def starTriangleEdgeCutNeighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (A T : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel T.Adj]
    (X : Finset V) (t : V → ZMod 2) (y : V) : Finset V :=
  (A.neighborFinset y ∩ X).filter fun u => ¬ T.Adj y u ∧ t u ≠ t y

/-- **Local triangle-edge cut identity.**  When the selected part of the
`A`-star at `y` has even size and `t` is constant on incident `T` edges,
the star activity is the parity of selected `(A \ T)` edges crossing
`supp(t)`. -/
theorem sum_f2_neighbor_inter_eq_starTriangleEdgeCutNeighbors_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (A T : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel T.Adj]
    (X : Finset V) (t : V → ZMod 2) (y : V)
    (heven : Even (A.neighborFinset y ∩ X).card)
    (hTconst : ∀ u, u ∈ A.neighborFinset y ∩ X →
      T.Adj y u → t u = t y) :
    (∑ u ∈ A.neighborFinset y ∩ X, t u) =
      ((starTriangleEdgeCutNeighbors A T X t y).card : ZMod 2) := by
  let S := A.neighborFinset y ∩ X
  have hchar : (2 : ZMod 2) = 0 := by decide
  have hcardZero : (S.card : ZMod 2) = 0 := by
    rcases heven with ⟨k, hk⟩
    rw [hk, Nat.cast_add, ← two_mul, hchar, zero_mul]
  have hshift : (∑ u ∈ S, t u) = ∑ u ∈ S, (t u + t y) := by
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [hcardZero, zero_mul, add_zero]
  rw [show A.neighborFinset y ∩ X = S from rfl, hshift]
  calc
    (∑ u ∈ S, (t u + t y)) =
        ∑ u ∈ S, if ¬ T.Adj y u ∧ t u ≠ t y then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      have hbinary : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
      by_cases hT : T.Adj y u
      · have heq := hTconst u (by simpa [S] using hu) hT
        simp only [hT, not_true_eq_false, false_and, ↓reduceIte, heq]
        rw [← two_mul, hchar, zero_mul]
      · by_cases hne : t u ≠ t y
        · rcases hbinary (t u) with hu0 | hu1 <;>
            rcases hbinary (t y) with hy0 | hy1 <;> simp_all
        · have heq : t u = t y := not_ne_iff.mp hne
          simp only [hT, not_false_eq_true, heq, ne_eq, not_true_eq_false,
            and_false, ↓reduceIte]
          rw [← two_mul, hchar, zero_mul]
    _ = ((starTriangleEdgeCutNeighbors A T X t y).card : ZMod 2) := by
      simp [starTriangleEdgeCutNeighbors, S]

/-- Block form of `(73rnz_cjibkzh)`: summing over a residual witness block
turns total activity into the parity of the completely located selected
`(A \ T)` support-cut incidences. -/
theorem sum_f2_neighbor_inter_eq_sum_starTriangleEdgeCut_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (A T : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel T.Adj]
    (R X : Finset V) (t : V → ZMod 2)
    (heven : ∀ y ∈ R, Even (A.neighborFinset y ∩ X).card)
    (hTconst : ∀ y ∈ R, ∀ u, u ∈ A.neighborFinset y ∩ X →
      T.Adj y u → t u = t y) :
    (∑ y ∈ R, ∑ u ∈ A.neighborFinset y ∩ X, t u) =
      ((∑ y ∈ R, (starTriangleEdgeCutNeighbors A T X t y).card : ℕ) :
        ZMod 2) := by
  calc
    (∑ y ∈ R, ∑ u ∈ A.neighborFinset y ∩ X, t u) =
        ∑ y ∈ R, ((starTriangleEdgeCutNeighbors A T X t y).card :
          ZMod 2) := by
      apply Finset.sum_congr rfl
      intro y hy
      exact sum_f2_neighbor_inter_eq_starTriangleEdgeCutNeighbors_card
        A T X t y (heven y hy) (hTconst y hy)
    _ = ((∑ y ∈ R, (starTriangleEdgeCutNeighbors A T X t y).card : ℕ) :
        ZMod 2) := by simp

end Erdos85

#print axioms Erdos85.sum_f2_neighbor_inter_eq_starTriangleEdgeCutNeighbors_card
#print axioms Erdos85.sum_f2_neighbor_inter_eq_sum_starTriangleEdgeCut_card
