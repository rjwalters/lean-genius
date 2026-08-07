import Proofs.Erdos85MinimumLayerDefectCover
import Proofs.Erdos85EqualCycleResidual

/-!
# Classification of the saturated minimum-layer branch

The defect graph of the exact-boundary child is the parent defect graph
restricted to the minimum layer.  Its components are therefore all the
same size.  The complete equal-cycle theorem classifies the child degree,
and the saturation equation then leaves only two parent degrees.
-/

namespace Erdos85

noncomputable section

/-- A saturated exact-boundary descent whose child degree is itself in the
even boundary range has child degree `4` or `12`; consequently the parent
degree is `12` or `124`. -/
theorem minimumLayer_saturated_degree_eq_twelve_or_oneTwentyFour
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (hs4 : 4 ≤ s) (hsEven : Even s)
    (hsat : d = (s - 1) * (s - 1) + 3) :
    d = 12 ∨ d = 124 := by
  classical
  let D := secondOrderDefectGraph G
  let H := minimumLayerGraph G D c₀
  let P := minimumLayerParentDefect D c₀
  let DH := secondOrderDefectGraph H
  have hfreeChild : ¬ containsC4 _ H :=
    minimumLayerGraph_c4Free G D c₀ hfree
  obtain ⟨v₀, hv₀⟩ := c₀.nonempty_supp
  let a₀ : minimumLayerVertex D c₀ :=
    ⟨⟨c₀, rfl⟩, ⟨v₀, hv₀⟩⟩
  letI : Nonempty (minimumLayerVertex D c₀) := ⟨a₀⟩
  have hminChild : s ≤ H.minDegree := by
    exact H.le_minDegree_of_forall_le_degree s fun x => by
      rw [hregChild x]
  have hEq : P = DH :=
    minimumLayerParentDefect_eq_childDefect
      G hfree hd heven hmin hcard c₀ hregChild hcardChild
  let e : P ≃g DH :=
    { toEquiv := Equiv.refl _
      map_rel_iff' := by
        intro a b
        simpa only [Equiv.refl_apply, hEq] }
  have hlen : ∀ c : DH.ConnectedComponent,
      c.supp.ncard = c₀.supp.ncard := by
    intro c
    let cp : P.ConnectedComponent := e.connectedComponentEquiv.symm c
    obtain ⟨a, ha⟩ := cp.nonempty_supp
    have hcp : P.connectedComponentMk a = cp :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff cp a).mp ha
    have hpcard : cp.supp.ncard = c₀.supp.ncard := by
      rw [← hcp]
      exact minimumLayerParentDefect_component_card D c₀ a
    have hmap : e.connectedComponentEquiv cp = c :=
      e.connectedComponentEquiv.apply_symm_apply c
    have hcardIso : cp.supp.ncard =
        (e.connectedComponentEquiv cp).supp.ncard := by
      rw [← Set.fintypeCard_eq_ncard, ← Set.fintypeCard_eq_ncard]
      exact Fintype.card_congr
        (SimpleGraph.ConnectedComponent.isoEquivSupp e cp)
    rw [hmap] at hcardIso
    exact hcardIso.symm.trans hpcard
  have hsClass : s = 4 ∨ s = 12 :=
    equalCycle_degree_eq_four_or_twelve
      H hfreeChild hs4 hsEven hminChild hcardChild hlen
  rcases hsClass with rfl | rfl <;> omega

end

end Erdos85
