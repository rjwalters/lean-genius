import Proofs.Erdos85OddSquareOrderNineThreeHighSecondProfileRowCover

/-!
# Branch-four special-point selector at order 81

The row-cover development proves that the total special-defect mass over the
24 unmarked bin-one points is six in the four-edge high-root branch.  This
file records the direct pointwise consequence needed by the full-fiber price
route: at least one such point has positive special defect, hence its mixed
residual target is strictly larger than the branch-three baseline 27.
-/

namespace Erdos85

/-- In the four-edge high-root branch, some unmarked bin-one point is defect
adjacent to a special B0 row.  This is the formal existence half of the six
global puncture-miss selector; the separate mixed-column theorem upgrades its
residual-row count to `27 + specialDefects`. -/
theorem squareOrderNine_threeHigh_secondProfile_exists_positive_specialDefect
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (hbranch : (G.induce (G.neighborSet x)).edgeFinset.card = 4) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let D := secondOrderDefectGraph G
    ∃ b ∈ U1, 0 < (D.neighborFinset b ∩ S).card := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let D := secondOrderDefectGraph G
  have hmass :=
    squareOrderNine_threeHigh_secondProfile_special_defect_mass_dichotomy
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hmass
  rcases hmass with hthree | hfour
  · omega
  · have hsum :
        (∑ b ∈ U1, (D.neighborFinset b ∩ S).card) = 6 := hfour.2
    have hsumPos :
        0 < ∑ b ∈ U1, (D.neighborFinset b ∩ S).card := by omega
    exact (Finset.sum_pos_iff
      (s := U1) (f := fun b => (D.neighborFinset b ∩ S).card)).mp hsumPos

end Erdos85

#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_exists_positive_specialDefect
