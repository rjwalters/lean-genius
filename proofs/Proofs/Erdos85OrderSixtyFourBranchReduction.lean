import Proofs.Erdos85OrderSixtyFourHighCount

/-! # Branch interface for the order-64 obstruction -/

open SimpleGraph

namespace Erdos85

/-- Exclusion of one high-count stratum, with access to the complete
energy-minimal tight-core package. -/
def OrderSixtyFourTightBranchExcluded (h : Nat) : Prop :=
  ∀ (G : SimpleGraph (Fin 64)) (_ : DecidableRel G.Adj),
    ¬ containsC4 (Fin 64) G →
    8 ≤ G.minDegree →
    IsDegreeSquareMinimizer G 8 →
    (∀ ⦃u v⦄, G.Adj u v → G.degree u = 8 ∨ G.degree v = 8) →
    (∀ x y z : Fin 64, y ≠ z → G.Adj x z → ¬ G.Adj y z →
      G.degree y + 1 < G.degree x →
        HasThreeEdgeWalk (G.deleteEdges {s(x,z)}) y z) →
    (squareOrderHighVertices G 8).card = h → False

/-- The seven branch exclusions discharge an arbitrary order-64 witness after
energy-minimal normalization, without any cast between `Fin (8*8)` and
`Fin 64`. -/
theorem no_orderSixtyFour_witness_of_branches
    (h0 : OrderSixtyFourTightBranchExcluded 0)
    (h2 : OrderSixtyFourTightBranchExcluded 2)
    (h4 : OrderSixtyFourTightBranchExcluded 4)
    (h6 : OrderSixtyFourTightBranchExcluded 6)
    (h8 : OrderSixtyFourTightBranchExcluded 8)
    (h10 : OrderSixtyFourTightBranchExcluded 10)
    (h12 : OrderSixtyFourTightBranchExcluded 12) :
    ¬ C4FreeMinDegreeWitness 64 8 := by
  rintro ⟨G₀, hdec₀, hmin₀, hfree₀⟩
  letI : DecidableRel G₀.Adj := hdec₀
  letI : Nonempty (Fin 64) := ⟨⟨0, by norm_num⟩⟩
  obtain ⟨G, hdec, hfree, hmin, hminimal, hcover, hslide⟩ :=
    exists_degreeSquareMinimizer_with_tightCover_and_slideSaturation
      G₀ hfree₀ hmin₀
  letI : DecidableRel G.Adj := hdec
  letI : DecidableRel (antipodalGraph G).Adj := Classical.decRel _
  letI : DecidableRel (triangleFreeEdgeGraph G).Adj := Classical.decRel _
  have hmin' : ∀ x : Fin 64, 8 ≤ G.degree x :=
    fun x => hmin.trans (G.minDegree_le_degree x)
  rcases orderSixtyFour_high_count_cases G hfree hmin'
      (fun {_ _} huv => hcover huv) with
    hh | hh | hh | hh | hh | hh | hh
  · exact h0 G hdec hfree hmin hminimal hcover hslide hh
  · exact h2 G hdec hfree hmin hminimal hcover hslide hh
  · exact h4 G hdec hfree hmin hminimal hcover hslide hh
  · exact h6 G hdec hfree hmin hminimal hcover hslide hh
  · exact h8 G hdec hfree hmin hminimal hcover hslide hh
  · exact h10 G hdec hfree hmin hminimal hcover hslide hh
  · exact h12 G hdec hfree hmin hminimal hcover hslide hh

/-- Consequently the seven branches also discharge the normalized tight core. -/
theorem not_squareOrderTightCoreExists_eight_of_branches
    (h0 : OrderSixtyFourTightBranchExcluded 0)
    (h2 : OrderSixtyFourTightBranchExcluded 2)
    (h4 : OrderSixtyFourTightBranchExcluded 4)
    (h6 : OrderSixtyFourTightBranchExcluded 6)
    (h8 : OrderSixtyFourTightBranchExcluded 8)
    (h10 : OrderSixtyFourTightBranchExcluded 10)
    (h12 : OrderSixtyFourTightBranchExcluded 12) :
    ¬ SquareOrderTightCoreExists 8 := by
  intro hcore
  apply no_orderSixtyFour_witness_of_branches h0 h2 h4 h6 h8 h10 h12
  have hw := witness_of_squareOrderTightCoreExists hcore
  simpa using hw

end Erdos85
