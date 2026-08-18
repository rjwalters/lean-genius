import Proofs.Erdos85OrderSixtyFourSmallBlockCoordinates

/-! # Exact adjacency characterization of small-block coordinates -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The order-64 grid coordinates are characterized exactly by adjacency:
a vertex in either coordinate block is adjacent to `z` iff it is the
corresponding coordinate of `z`. -/
theorem orderSixtyFour_seven_defect_components_smallBlock_coordinate_iff
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 7) :
    ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16 ∧
      ∀ e, e ≠ c → e.supp.ncard = 8 ∧
        ∀ f, f ≠ c → f.supp.ncard = 8 ∧
          ∀ (_hef : e ≠ f), ∃ φ : Fin 64 ≃ e.supp × f.supp,
            (∀ (z : Fin 64) (x : e.supp),
              G.Adj x.1 z ↔ x = (φ z).1) ∧
            ∀ (z : Fin 64) (y : f.supp),
              G.Adj y.1 z ↔ y = (φ z).2 := by
  classical
  obtain ⟨c, hc16, hsmall⟩ :=
    orderSixtyFour_seven_defect_components_smallBlock_coordinates
      G hfree hmin hcover hcount
  refine ⟨c, hc16, ?_⟩
  intro e hec
  obtain ⟨he8, hecoords⟩ := hsmall e hec
  refine ⟨he8, ?_⟩
  intro f hfc
  obtain ⟨hf8, hfcoords⟩ := hecoords f hfc
  refine ⟨hf8, ?_⟩
  intro hef
  obtain ⟨hcell, hvertex⟩ := hfcoords hef
  let coord : Fin 64 → e.supp × f.supp := fun z =>
    Classical.choose (hvertex z)
  have hcoord (z : Fin 64) :
      G.Adj (coord z).1.1 z ∧ G.Adj (coord z).2.1 z :=
    (Classical.choose_spec (hvertex z)).1
  have hinj : Function.Injective coord := by
    intro z w hzw
    have hz := hcoord z
    have hw : G.Adj (coord z).1.1 w ∧ G.Adj (coord z).2.1 w := by
      simpa [hzw] using hcoord w
    exact ((Classical.choose_spec (hcell (coord z))).2 z hz).trans
      ((Classical.choose_spec (hcell (coord z))).2 w hw).symm
  have hsurj : Function.Surjective coord := by
    intro p
    obtain ⟨z, hz, _hzuniq⟩ := hcell p
    exact ⟨z, ((Classical.choose_spec (hvertex z)).2 p hz).symm⟩
  let φ : Fin 64 ≃ e.supp × f.supp := Equiv.ofBijective coord ⟨hinj, hsurj⟩
  refine ⟨φ, ?_, ?_⟩
  · intro z x
    constructor
    · intro hx
      have hp : G.Adj x.1 z ∧ G.Adj (coord z).2.1 z :=
        ⟨hx, (hcoord z).2⟩
      have hpair := (Classical.choose_spec (hvertex z)).2 (x, (coord z).2) hp
      exact congrArg Prod.fst hpair
    · intro hx
      subst x
      exact (hcoord z).1
  · intro z y
    constructor
    · intro hy
      have hp : G.Adj (coord z).1.1 z ∧ G.Adj y.1 z :=
        ⟨(hcoord z).1, hy⟩
      have hpair := (Classical.choose_spec (hvertex z)).2 ((coord z).1, y) hp
      exact congrArg Prod.snd hpair
    · intro hy
      subst y
      exact (hcoord z).2

end

end Erdos85
