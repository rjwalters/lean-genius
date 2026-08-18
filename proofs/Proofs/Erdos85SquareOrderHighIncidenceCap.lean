import Proofs.Erdos85SquareOrderHighIncidence
import Proofs.Erdos85SquareOrderNonexistenceReduction

/-!
# Pointwise cap on the square-order high-incidence design

The exact first and second high-incidence moments become stronger when
combined with the local injection `2 k_x ≤ d`.  For a nonempty high sector
of cardinality `h`, this gives the linear restriction
`h + d ≤ (d / 2) * (d + 1)`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

theorem squareOrder_high_count_linear_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    (hpos : 0 < (squareOrderHighVertices G d).card) :
    (squareOrderHighVertices G d).card + d ≤ (d / 2) * (d + 1) := by
  classical
  let H := squareOrderHighVertices G d
  let k : V → Nat := fun x => (G.neighborFinset x ∩ H).card
  have hkcap : ∀ x : V, k x ≤ d / 2 := by
    intro x
    by_cases hx : x ∈ H
    · have hkzero : k x = 0 :=
        squareOrder_highNeighborCount_eq_zero_of_high G hcover hx
      simp [hkzero]
    · rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
        G hfree hd hmin hcover hcard x with hxlow | hxhigh
      · have htwice := squareOrder_two_mul_highNeighborCount_le_degree
          G hfree hd hmin hcover hcard hxlow
        change 2 * k x ≤ d at htwice
        omega
      · exact (hx (Finset.mem_filter.mpr ⟨by simp, hxhigh⟩)).elim
  have hkquad : ∀ x : V, k x * k x ≤ (d / 2) * k x := by
    intro x
    exact Nat.mul_le_mul_right (k x) (hkcap x)
  have hsumle :
      (∑ x : V, k x * k x) ≤ ∑ x : V, (d / 2) * k x :=
    Finset.sum_le_sum fun _x _hx => hkquad _x
  have hfirst : (∑ x : V, k x) = (d + 1) * H.card := by
    simpa [H, k] using squareOrder_sum_highNeighborCount_eq G d
  have hsecond :
      (∑ x : V, k x * k x) = H.card * (H.card + d) := by
    simpa [H, k, pow_two] using
      squareOrder_sum_highNeighborCount_sq_eq
        G hfree hd hmin hcover hcard
  rw [hsecond, ← Finset.mul_sum, hfirst] at hsumle
  have hfactor :
      H.card * (H.card + d) ≤ H.card * ((d / 2) * (d + 1)) := by
    convert hsumle using 1 <;> ring
  exact Nat.le_of_mul_le_mul_left hfactor (by simpa [H] using hpos)

/-- Tight-minimizer form of the linear high-count restriction. -/
theorem SquareOrderTightMinimizer.exists_high_count_linear_bound
    {d : Nat} (hd : 2 ≤ d) (hminimizer : SquareOrderTightMinimizer d) :
    ∃ h, h = 0 ∨ (0 < h ∧ h + d ≤ (d / 2) * (d + 1)) := by
  classical
  rcases hminimizer with ⟨G, hdec, hfree, hmin, _hminimal, hcover⟩
  letI : DecidableRel G.Adj := hdec
  have hmindeg : ∀ x : Fin (d * d), d ≤ G.degree x := fun x =>
    hmin.trans (G.minDegree_le_degree x)
  let h := (squareOrderHighVertices G d).card
  refine ⟨h, ?_⟩
  by_cases hhzero : h = 0
  · exact Or.inl hhzero
  · right
    have hhpos : 0 < h := Nat.pos_of_ne_zero hhzero
    exact ⟨hhpos, squareOrder_high_count_linear_bound
      G hfree hd hmindeg (@hcover) (by simp) (by simpa [h] using hhpos)⟩

/-- At even square order the surviving positive branch has an even high
count in addition to the linear incidence cap. -/
theorem SquareOrderTightMinimizer.exists_even_high_count_linear_bound
    {d : Nat} (hd : 2 ≤ d) (hdeven : Even d)
    (hminimizer : SquareOrderTightMinimizer d) :
    ∃ h, h = 0 ∨
      (Even h ∧ 0 < h ∧ h + d ≤ (d / 2) * (d + 1)) := by
  classical
  rcases hminimizer with ⟨G, hdec, hfree, hmin, _hminimal, hcover⟩
  letI : DecidableRel G.Adj := hdec
  have hmindeg : ∀ x : Fin (d * d), d ≤ G.degree x := fun x =>
    hmin.trans (G.minDegree_le_degree x)
  let h := (squareOrderHighVertices G d).card
  refine ⟨h, ?_⟩
  by_cases hhzero : h = 0
  · exact Or.inl hhzero
  · right
    have hhpos : 0 < h := Nat.pos_of_ne_zero hhzero
    have hsum := squareOrder_even_cube_add_card_high
      G hfree hd hmindeg (@hcover) (by simp)
    have hheven : Even h := by
      rw [Nat.even_iff] at hdeven ⊢
      rw [Nat.even_iff] at hsum
      simpa [h, Nat.add_mod, Nat.mul_mod, hdeven] using hsum
    exact ⟨hheven, hhpos, squareOrder_high_count_linear_bound
      G hfree hd hmindeg (@hcover) (by simp) (by simpa [h] using hhpos)⟩

end

end Erdos85
