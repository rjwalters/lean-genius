import Proofs.Erdos85BinarySquareSizeTwoCrossFactorIntertwining

/-! # Alternating path balance across size-two blocks -/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem ownerAdj_mul_crossIncidence_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c d : (secondOrderDefectGraph G).ConnectedComponent)
    (x : c.supp) (z : d.supp) :
    ((restrictedComponentOwnerGraph G c d).adjMatrix ℤ *
        defectComponentCrossIncidenceMatrix (K := ℤ) G c d) x z =
      (((Finset.univ : Finset c.supp).filter fun y =>
        (restrictedComponentOwnerGraph G c d).Adj x y ∧
          G.Adj y.1 z.1).card : ℤ) := by
  rw [Matrix.mul_apply]
  simp only [SimpleGraph.adjMatrix_apply,
    defectComponentCrossIncidenceMatrix,
    defectComponentNeighborIncidenceMatrix, ite_mul, one_mul, zero_mul]
  calc
    (∑ y : c.supp,
      if (restrictedComponentOwnerGraph G c d).Adj x y then
        if G.Adj y.1 z.1 then (1 : ℤ) else 0 else 0) =
        ∑ y : c.supp,
          if (restrictedComponentOwnerGraph G c d).Adj x y ∧
              G.Adj y.1 z.1 then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro y _hy
      by_cases hxy : (restrictedComponentOwnerGraph G c d).Adj x y <;>
        by_cases hyz : G.Adj y.1 z.1 <;> simp [hxy, hyz]
    _ = (((Finset.univ : Finset c.supp).filter fun y =>
        (restrictedComponentOwnerGraph G c d).Adj x y ∧
          G.Adj y.1 z.1).card : ℤ) := by
      rw [Finset.sum_boole]

private theorem crossIncidence_mul_ownerAdj_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c d : (secondOrderDefectGraph G).ConnectedComponent)
    (x : c.supp) (z : d.supp) :
    (defectComponentCrossIncidenceMatrix (K := ℤ) G c d *
        (restrictedComponentOwnerGraph G d c).adjMatrix ℤ) x z =
      (((Finset.univ : Finset d.supp).filter fun y =>
        G.Adj x.1 y.1 ∧
          (restrictedComponentOwnerGraph G d c).Adj y z).card : ℤ) := by
  rw [Matrix.mul_apply]
  simp only [SimpleGraph.adjMatrix_apply,
    defectComponentCrossIncidenceMatrix,
    defectComponentNeighborIncidenceMatrix, ite_mul, one_mul, zero_mul]
  calc
    (∑ y : d.supp,
      if G.Adj x.1 y.1 then
        if (restrictedComponentOwnerGraph G d c).Adj y z then
          (1 : ℤ) else 0 else 0) =
        ∑ y : d.supp,
          if G.Adj x.1 y.1 ∧
              (restrictedComponentOwnerGraph G d c).Adj y z then
            (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro y _hy
      by_cases hxy : G.Adj x.1 y.1 <;>
        by_cases hyz : (restrictedComponentOwnerGraph G d c).Adj y z <;>
          simp [hxy, hyz]
    _ = (((Finset.univ : Finset d.supp).filter fun y =>
        G.Adj x.1 y.1 ∧
          (restrictedComponentOwnerGraph G d c).Adj y z).card : ℤ) := by
      rw [Finset.sum_boole]

/-- At every ordered pair of vertices in two size-two defect components, the
number of paths taking first an owner-factor edge and then a cross edge equals
the number taking first a cross edge and then the reverse owner-factor edge. -/
theorem binarySquare_regular_twoSizeTwoParts_alternatingPath_card_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c d : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) (hd : d.supp.ncard = q * 2)
    (x : c.supp) (z : d.supp) :
    ((Finset.univ : Finset c.supp).filter fun y =>
      (restrictedComponentOwnerGraph G c d).Adj x y ∧
        G.Adj y.1 z.1).card =
      ((Finset.univ : Finset d.supp).filter fun y =>
        G.Adj x.1 y.1 ∧
          (restrictedComponentOwnerGraph G d c).Adj y z).card := by
  have hinter := congrArg (fun M : Matrix c.supp d.supp ℤ => M x z)
    (binarySquare_regular_twoSizeTwoParts_crossIncidence_intertwines_owner
      G hfree hq hreg hcard c d hc hd)
  rw [ownerAdj_mul_crossIncidence_apply,
    crossIncidence_mul_ownerAdj_apply] at hinter
  exact_mod_cast hinter

end

end Erdos85
