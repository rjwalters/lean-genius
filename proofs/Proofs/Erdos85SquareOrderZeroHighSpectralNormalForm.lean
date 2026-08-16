import Proofs.Erdos85SquareOrderDefectEdgeBudget
import Proofs.Erdos85ExcessEigenspace

/-!
# Zero-high spectral normal form at square order

The square-order tight-minimizer problem splits according to whether the
degree-`d+1` sector is empty.  In the empty branch the original graph is
`d`-regular, its second-order defect graph is `(d-1)`-regular, and their
adjacency matrices satisfy the standard commuting square identity.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

def SquareOrderZeroHighTightMinimizer (d : Nat) : Prop :=
  ∃ (G : SimpleGraph (Fin (d * d))) (_ : DecidableRel G.Adj),
    ¬ containsC4 (Fin (d * d)) G ∧
    d ≤ G.minDegree ∧
    IsDegreeSquareMinimizer G d ∧
    (∀ ⦃u v⦄, G.Adj u v → G.degree u = d ∨ G.degree v = d) ∧
    (squareOrderHighVertices G d).card = 0

def SquareOrderPositiveHighTightMinimizer (d : Nat) : Prop :=
  ∃ (G : SimpleGraph (Fin (d * d))) (_ : DecidableRel G.Adj),
    ¬ containsC4 (Fin (d * d)) G ∧
    d ≤ G.minDegree ∧
    IsDegreeSquareMinimizer G d ∧
    (∀ ⦃u v⦄, G.Adj u v → G.degree u = d ∨ G.degree v = d) ∧
    0 < (squareOrderHighVertices G d).card

/-- Exact zero-high/positive-high split, retaining the same normalized
witness in either branch. -/
theorem squareOrderTightMinimizer_iff_zeroHigh_or_positiveHigh (d : Nat) :
    SquareOrderTightMinimizer d ↔
      SquareOrderZeroHighTightMinimizer d ∨
        SquareOrderPositiveHighTightMinimizer d := by
  constructor
  · rintro ⟨G, hdec, hfree, hmin, hminimal, hcover⟩
    by_cases hzero : (squareOrderHighVertices G d).card = 0
    · exact Or.inl ⟨G, hdec, hfree, hmin, hminimal, hcover, hzero⟩
    · exact Or.inr ⟨G, hdec, hfree, hmin, hminimal, hcover,
        Nat.pos_of_ne_zero hzero⟩
  · rintro (hzero | hpositive)
    · rcases hzero with ⟨G, hdec, hfree, hmin, hminimal, hcover, _⟩
      exact ⟨G, hdec, hfree, hmin, hminimal, hcover⟩
    · rcases hpositive with ⟨G, hdec, hfree, hmin, hminimal, hcover, _⟩
      exact ⟨G, hdec, hfree, hmin, hminimal, hcover⟩

/-- The zero-high branch feeds directly into the regular spectral library. -/
theorem SquareOrderZeroHighTightMinimizer.exists_regular_commuting_pair
    {d : Nat} (hd : 2 ≤ d)
    (hzero : SquareOrderZeroHighTightMinimizer d) :
    ∃ (G : SimpleGraph (Fin (d * d))) (_ : DecidableRel G.Adj),
      ¬ containsC4 (Fin (d * d)) G ∧
      (∀ x, G.degree x = d) ∧
      (∀ x, (secondOrderDefectGraph G).degree x = d - 1) ∧
      G.adjMatrix ℤ * G.adjMatrix ℤ =
        (↑d - 1 : ℤ) • (1 : Matrix (Fin (d * d)) (Fin (d * d)) ℤ) +
          FriendshipTheoremOQ01.onesMatrix (Fin (d * d)) -
            (secondOrderDefectGraph G).adjMatrix ℤ ∧
      G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ =
        (secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ := by
  classical
  rcases hzero with ⟨G, hdec, hfree, hmin, _hminimal, hcover, hhighZero⟩
  letI : DecidableRel G.Adj := hdec
  have hmindeg : ∀ x : Fin (d * d), d ≤ G.degree x := fun x =>
    hmin.trans (G.minDegree_le_degree x)
  have hhighEmpty : squareOrderHighVertices G d = ∅ :=
    Finset.card_eq_zero.mp hhighZero
  have hreg : ∀ x, G.degree x = d := by
    intro x
    rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
        G hfree hd hmindeg (@hcover) (by simp) x with hx | hx
    · exact hx
    · have hxmem : x ∈ squareOrderHighVertices G d :=
        Finset.mem_filter.mpr ⟨by simp, hx⟩
      rw [hhighEmpty] at hxmem
      simp at hxmem
  have hDreg : ∀ x, (secondOrderDefectGraph G).degree x = d - 1 := by
    intro x
    have hbudget :=
      squareOrder_defectDegree_add_highNeighborCount_eq_sub_one
        G hfree hd hmindeg (@hcover) (by simp) (hreg x)
    rw [hhighEmpty] at hbudget
    simpa using hbudget
  exact ⟨G, hdec, hfree, hreg, hDreg,
    adjMatrix_sq_eq_sub_secondOrderDefect_of_regular G hfree hreg,
    adjMatrix_comm_secondOrderDefect_of_regular G hfree hreg⟩

end

end Erdos85
