import Proofs.Erdos85SquareOrderCommutatorSupport

/-!
# Row counts for the square-order commutator

The unit-support description of the adjacency/defect commutator can be
counted exactly in each row.  A high row sees every low nonneighbor; a low
row sees every high nonneighbor.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

theorem squareOrder_sum_commutator_entry_sq_row
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) (x : V) :
    let H := squareOrderHighVertices G d
    let C := G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ -
      (secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ
    (∑ y : V, C x y * C x y) =
      if x ∈ H then ((d * d - H.card - (d + 1) : Nat) : ℤ)
      else ((H.card - (G.neighborFinset x ∩ H).card : Nat) : ℤ) := by
  classical
  let H := squareOrderHighVertices G d
  let C := G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ -
    (secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ
  dsimp only
  have hentry : ∀ y : V, C x y * C x y =
      if ((((x ∈ H ∧ y ∉ H) ∨ (x ∉ H ∧ y ∈ H)) ∧ ¬ G.Adj x y))
      then 1 else 0 := by
    intro y
    simpa [C, H] using
      squareOrder_commutator_entry_sq_eq_crossNonedgeIndicator
        G hfree hd hmin hcover hcard x y
  by_cases hx : x ∈ H
  · rw [if_pos hx]
    have hsum : (∑ y : V, C x y * C x y) =
        (((Finset.univ : Finset V).filter
          fun y => y ∉ H ∧ ¬ G.Adj x y).card : ℤ) := by
      calc
        (∑ y : V, C x y * C x y) =
            ∑ y : V, if y ∉ H ∧ ¬ G.Adj x y then (1 : ℤ) else 0 := by
          apply Finset.sum_congr rfl
          intro y _hy
          rw [hentry y]
          simp [hx]
        _ = _ := by simpa using
          (Finset.sum_boole (R := ℤ)
            (fun y : V => y ∉ H ∧ ¬ G.Adj x y) Finset.univ)
    rw [hsum]
    congr 1
    let L : Finset V := Finset.univ \ H
    have hneighborsLow : G.neighborFinset x ⊆ L := by
      intro y hy
      refine Finset.mem_sdiff.mpr ⟨by simp, ?_⟩
      intro hyHigh
      have hxy : G.Adj x y := (G.mem_neighborFinset x y).mp hy
      have hxdegree : G.degree x = d + 1 := (Finset.mem_filter.mp hx).2
      have hydegree : G.degree y = d + 1 :=
        (Finset.mem_filter.mp hyHigh).2
      exact squareOrder_not_adj_degree_succ_of_tightEdgeCover
        G hcover hxdegree hydegree hxy
    have hfilter :
        (Finset.univ.filter fun y : V => y ∉ H ∧ ¬ G.Adj x y) =
          L \ G.neighborFinset x := by
      ext y
      simp [L, SimpleGraph.mem_neighborFinset]
    rw [hfilter, Finset.card_sdiff_of_subset hneighborsLow,
      G.card_neighborFinset_eq_degree, (Finset.mem_filter.mp hx).2]
    have hLcard : L.card = d * d - H.card := by
      dsimp [L]
      rw [Finset.card_sdiff, Finset.card_univ, hcard]
      simp
    rw [hLcard]
  · rw [if_neg hx]
    have hsum : (∑ y : V, C x y * C x y) =
        (((Finset.univ : Finset V).filter
          fun y => y ∈ H ∧ ¬ G.Adj x y).card : ℤ) := by
      calc
        (∑ y : V, C x y * C x y) =
            ∑ y : V, if y ∈ H ∧ ¬ G.Adj x y then (1 : ℤ) else 0 := by
          apply Finset.sum_congr rfl
          intro y _hy
          rw [hentry y]
          simp [hx]
        _ = _ := by simpa using
          (Finset.sum_boole (R := ℤ)
            (fun y : V => y ∈ H ∧ ¬ G.Adj x y) Finset.univ)
    rw [hsum]
    congr 1
    have hfilter :
        (Finset.univ.filter fun y : V => y ∈ H ∧ ¬ G.Adj x y) =
          H \ G.neighborFinset x := by
      ext y
      simp [SimpleGraph.mem_neighborFinset]
    rw [hfilter, Finset.card_sdiff]

end

end Erdos85
