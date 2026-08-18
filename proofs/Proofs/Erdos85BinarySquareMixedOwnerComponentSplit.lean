import Proofs.Erdos85BinarySquareMixedOwnerTriangleCensus
import Proofs.Erdos85OrderSixtyFourRoutingCensusDichotomy

/-! # Defect-component split of the mixed owner triangle census -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Mixed colored triples whose three vertices lie in one connected component
of the comparison graph `D`. -/
def sameComponentCyclicColoredTriples
    {V : Type*} [Fintype V] [DecidableEq V]
    (D A B C : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj] :
    Finset (V × V × V) :=
  (cyclicColoredTriples A B C).filter fun p =>
    D.connectedComponentMk p.1 = D.connectedComponentMk p.2.2 ∧
      D.connectedComponentMk p.2.2 = D.connectedComponentMk p.2.1

/-- The complementary mixed colored triples, whose vertices do not all lie
in one connected component of `D`. -/
def crossComponentCyclicColoredTriples
    {V : Type*} [Fintype V] [DecidableEq V]
    (D A B C : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj] :
    Finset (V × V × V) :=
  (cyclicColoredTriples A B C).filter fun p =>
    ¬ (D.connectedComponentMk p.1 = D.connectedComponentMk p.2.2 ∧
      D.connectedComponentMk p.2.2 = D.connectedComponentMk p.2.1)

/-- The same-component census fiber routed through one fixed component. -/
def cyclicColoredTriplesInComponent
    {V : Type*} [Fintype V] [DecidableEq V]
    (D A B C : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj]
    (d : D.ConnectedComponent) : Finset (V × V × V) :=
  (sameComponentCyclicColoredTriples D A B C).filter fun p =>
    D.connectedComponentMk p.1 = d

/-- The same-component census is the sum of its uniquely indexed component
fibers. -/
theorem sum_card_cyclicColoredTriplesInComponent_eq_card_sameComponent
    {V : Type*} [Fintype V] [DecidableEq V]
    (D A B C : SimpleGraph V) [DecidableRel D.Adj]
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj] :
    (∑ d : D.ConnectedComponent,
      (cyclicColoredTriplesInComponent D A B C d).card) =
        (sameComponentCyclicColoredTriples D A B C).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (s := sameComponentCyclicColoredTriples D A B C)
    (t := (Finset.univ : Finset D.ConnectedComponent))
    (f := fun p => D.connectedComponentMk p.1)
    (fun _ _ => Finset.mem_univ _)]
  rfl

/-- The global colored-triple census splits exactly into its same-component
and cross-component parts. -/
theorem card_sameComponent_add_card_crossComponent_eq_card_cyclicColoredTriples
    {V : Type*} [Fintype V] [DecidableEq V]
    (D A B C : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj] :
    (sameComponentCyclicColoredTriples D A B C).card +
      (crossComponentCyclicColoredTriples D A B C).card =
        (cyclicColoredTriples A B C).card := by
  classical
  simpa [sameComponentCyclicColoredTriples,
    crossComponentCyclicColoredTriples] using
    (Finset.card_filter_add_card_filter_not
      (s := cyclicColoredTriples A B C)
      (p := fun p =>
        D.connectedComponentMk p.1 = D.connectedComponentMk p.2.2 ∧
          D.connectedComponentMk p.2.2 = D.connectedComponentMk p.2.1))

/-- Membership in the same-component part is equivalently witnessed by one
component support containing all three vertices. -/
theorem mem_sameComponentCyclicColoredTriples_iff_exists_component
    {V : Type*} [Fintype V] [DecidableEq V]
    (D A B C : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj]
    (p : V × V × V) :
    p ∈ sameComponentCyclicColoredTriples D A B C ↔
      p ∈ cyclicColoredTriples A B C ∧
        ∃ d : D.ConnectedComponent,
          p.1 ∈ d.supp ∧ p.2.2 ∈ d.supp ∧ p.2.1 ∈ d.supp := by
  classical
  rw [sameComponentCyclicColoredTriples, Finset.mem_filter]
  constructor
  · rintro ⟨hp, hxy, hyz⟩
    refine ⟨hp, D.connectedComponentMk p.1, ?_, ?_, ?_⟩
    · exact (ConnectedComponent.mem_supp_iff _ _).mpr rfl
    · exact (ConnectedComponent.mem_supp_iff _ _).mpr hxy.symm
    · exact (ConnectedComponent.mem_supp_iff _ _).mpr (hyz.symm.trans hxy.symm)
  · rintro ⟨hp, d, hx, hy, hz⟩
    have hx' := (ConnectedComponent.mem_supp_iff d p.1).mp hx
    have hy' := (ConnectedComponent.mem_supp_iff d p.2.2).mp hy
    have hz' := (ConnectedComponent.mem_supp_iff d p.2.1).mp hz
    exact ⟨hp, hx'.trans hy'.symm, hy'.trans hz'.symm⟩

/-- A fixed same-component fiber is nonempty exactly when that component
supports the corresponding routing-owner rainbow. -/
theorem cyclicColoredTriplesInComponent_nonempty_iff_routingOwnerRainbow
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (d a b c : (secondOrderDefectGraph G).ConnectedComponent) :
    (cyclicColoredTriplesInComponent (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) d).Nonempty ↔
        routingOwnerRainbow G d a b c := by
  classical
  let D := secondOrderDefectGraph G
  let A := componentOwnerGraph G D a
  let B := componentOwnerGraph G D b
  let C := componentOwnerGraph G D c
  constructor
  · rintro ⟨p, hp⟩
    have hpfiber := Finset.mem_filter.mp hp
    have hpsame := Finset.mem_filter.mp hpfiber.1
    have hpcolor := Finset.mem_filter.mp hpsame.1
    have hcompX : D.connectedComponentMk p.1 = d := hpfiber.2
    have hcompY : D.connectedComponentMk p.2.2 = d :=
      hpsame.2.1.symm.trans hcompX
    have hcompZ : D.connectedComponentMk p.2.1 = d :=
      hpsame.2.2.symm.trans hcompY
    let x : d.supp := ⟨p.1, (ConnectedComponent.mem_supp_iff d p.1).mpr hcompX⟩
    let y : d.supp := ⟨p.2.2, (ConnectedComponent.mem_supp_iff d p.2.2).mpr hcompY⟩
    let z : d.supp := ⟨p.2.1, (ConnectedComponent.mem_supp_iff d p.2.1).mpr hcompZ⟩
    refine ⟨x, y, z, ?_, ?_, ?_, hpcolor.2.1, hpcolor.2.2.1, hpcolor.2.2.2⟩
    · exact Subtype.coe_ne_coe.mp hpcolor.2.1.ne
    · exact Subtype.coe_ne_coe.mp hpcolor.2.2.1.ne
    · exact Subtype.coe_ne_coe.mp hpcolor.2.2.2.ne
  · rintro ⟨x, y, z, hxy, hyz, hzx, ha, hb, hc⟩
    refine ⟨(x.1, z.1, y.1), ?_⟩
    rw [cyclicColoredTriplesInComponent, Finset.mem_filter,
      sameComponentCyclicColoredTriples, Finset.mem_filter,
      cyclicColoredTriples, Finset.mem_filter]
    have hx : D.connectedComponentMk x.1 = d :=
      (ConnectedComponent.mem_supp_iff d x.1).mp x.2
    have hy : D.connectedComponentMk y.1 = d :=
      (ConnectedComponent.mem_supp_iff d y.1).mp y.2
    have hz : D.connectedComponentMk z.1 = d :=
      (ConnectedComponent.mem_supp_iff d z.1).mp z.2
    exact ⟨⟨⟨Finset.mem_univ _, ha, hb, hc⟩,
      hx.trans hy.symm, hy.trans hz.symm⟩, hx⟩

/-- At order 64, the fixed `3584` mixed-owner budget is the sum of its
same-defect-component and cross-defect-component pieces. -/
theorem orderSixtyFour_regular_fourComponents_mixedOwner_componentSplit
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (a b c : (secondOrderDefectGraph G).ConnectedComponent)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (sameComponentCyclicColoredTriples (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c)).card +
    (crossComponentCyclicColoredTriples (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c)).card = 3584 := by
  rw [card_sameComponent_add_card_crossComponent_eq_card_cyclicColoredTriples]
  exact orderSixtyFour_regular_fourComponents_card_mixedOwnerTriangles
    G hfree hreg hcount a b c hab hac hbc

end

end Erdos85
