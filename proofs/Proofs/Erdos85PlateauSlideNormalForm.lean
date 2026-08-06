import Proofs.Erdos85EnergyMinimalEdgeCover
import Proofs.Erdos85RamseyPlateau

/-!
# Edge-slide saturated plateau cores

A plateau core may be represented by a degree-square-minimal witness.  This
simultaneously retains exact minimum degree and the tight-edge cover, while
forcing every degree-balancing edge slide to carry a three-edge obstruction
which avoids the removed donor edge.
-/

open SimpleGraph

namespace Erdos85

/-- **Slide-saturated plateau normal form.** -/
theorem C4PlateauCore.exists_slideSaturated_core
    {m d : ℕ} (hm : 4 ≤ m) (hcore : C4PlateauCore m d) :
    ∃ (G : SimpleGraph (Fin m)) (_ : DecidableRel G.Adj),
      G.minDegree = d ∧
      ¬ containsC4 (Fin m) G ∧
      IsDegreeSquareMinimizer G d ∧
      (∀ ⦃u v⦄, G.Adj u v →
        G.degree u = d ∨ G.degree v = d) ∧
      (∀ x y z : Fin m, y ≠ z → G.Adj x z → ¬ G.Adj y z →
        G.degree y + 1 < G.degree x →
          HasThreeEdgeWalk (G.deleteEdges {s(x,z)}) y z) ∧
      ∀ (H : SimpleGraph (Fin (m + 1))) (_ : DecidableRel H.Adj),
        d ≤ H.minDegree → containsC4 (Fin (m + 1)) H := by
  rcases hcore with ⟨G₀, hdec₀, hmin₀, hfree₀, _hcover₀, hnext⟩
  letI : DecidableRel G₀.Adj := hdec₀
  letI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  obtain ⟨G, hdec, hfree, hmin, hminimal, hcover, hsat⟩ :=
    exists_degreeSquareMinimizer_with_tightCover_and_slideSaturation
      G₀ hfree₀ hmin₀.ge
  have hd : 2 ≤ d := C4PlateauCore.two_le_degree hm
    ⟨G₀, hdec₀, hmin₀, hfree₀, _hcover₀, hnext⟩
  have hne : G ≠ ⊥ := by
    intro hbot
    have hzero : G.minDegree = 0 := by simp [hbot]
    omega
  obtain ⟨u, v, huv⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hne
  have hminEq : G.minDegree = d := by
    rcases hcover huv with hu | hv
    · exact Nat.le_antisymm (G.minDegree_le_degree u |>.trans_eq hu) hmin
    · exact Nat.le_antisymm (G.minDegree_le_degree v |>.trans_eq hv) hmin
  exact ⟨G, hdec, hminEq, hfree, hminimal, hcover, hsat, hnext⟩

end Erdos85
