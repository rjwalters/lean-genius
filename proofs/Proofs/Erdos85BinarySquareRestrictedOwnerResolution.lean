import Proofs.Erdos85BinarySquareRoutingRainbowEquiv

/-! # Restricted owner colors resolve component complements -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Inside any defect component, its graph complement is exactly the union of
the restricted owner-color graphs, and every complement edge has a unique
owner color. -/
theorem inducedDefectComponent_compl_adj_iff_existsUnique_restrictedOwner_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (d : (secondOrderDefectGraph G).ConnectedComponent)
    (x y : d.supp) :
    ((secondOrderDefectGraph G).induce d.supp)ᶜ.Adj x y ↔
      ∃! owner : (secondOrderDefectGraph G).ConnectedComponent,
        (restrictedComponentOwnerGraph G d owner).Adj x y := by
  let D := secondOrderDefectGraph G
  constructor
  · intro hxy
    have hne : x.1 ≠ y.1 := by
      intro h
      apply ((show x ≠ y from ((D.induce d.supp)ᶜ.ne_of_adj hxy)))
      exact Subtype.ext h
    have hnotD : ¬ D.Adj x.1 y.1 := by
      intro hD
      exact hxy.2 hD
    obtain ⟨owner, ho, huniq⟩ :=
      (not_secondOrderDefect_adj_iff_existsUnique_componentOwnerGraph_adj
        G hfree hne).mp (by simpa [D] using hnotD)
    refine ⟨owner, ?_, ?_⟩
    · exact ho
    · intro owner' ho'
      exact huniq owner' ho'
  · rintro ⟨owner, ho, huniq⟩
    have hne : x.1 ≠ y.1 := fun h => ho.ne (Subtype.ext h)
    have hnotD :=
      (not_secondOrderDefect_adj_iff_existsUnique_componentOwnerGraph_adj
        G hfree hne).mpr ⟨owner, ho, fun owner' ho' => huniq owner' ho'⟩
    refine ⟨?_, ?_⟩
    · intro h
      exact hne (congrArg Subtype.val h)
    · simpa [D] using hnotD

/-- Two restricted owner colors cannot label the same component-complement
edge unless the colors coincide. -/
theorem restrictedOwner_adj_color_unique
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {d a b : (secondOrderDefectGraph G).ConnectedComponent}
    {x y : d.supp}
    (ha : (restrictedComponentOwnerGraph G d a).Adj x y)
    (hb : (restrictedComponentOwnerGraph G d b).Adj x y) : a = b := by
  have haData := (componentOwnerGraph_adj G (secondOrderDefectGraph G) a
    x.1 y.1).mp ha
  obtain ⟨z, hz⟩ := haData.2
  have hzData := Finset.mem_inter.mp hz
  have hxz : G.Adj x.1 z :=
    (G.mem_neighborFinset x.1 z).mp (Finset.mem_filter.mp hzData.1).1
  have hyz : G.Adj y.1 z :=
    (G.mem_neighborFinset y.1 z).mp (Finset.mem_filter.mp hzData.2).1
  have hnotD := not_secondOrderDefect_adj_of_commonNeighbor
    G hfree haData.1 hxz hyz
  have hcomp : ((secondOrderDefectGraph G).induce d.supp)ᶜ.Adj x y := by
    exact ⟨ha.ne, hnotD⟩
  obtain ⟨owner, howner, huniq⟩ :=
    (inducedDefectComponent_compl_adj_iff_existsUnique_restrictedOwner_adj
      G hfree d x y).1 hcomp
  exact (huniq a ha).trans (huniq b hb).symm

end

end Erdos85
