import Proofs.Erdos85BinarySquareTwoOwnerRepeatedClosing
import Proofs.Erdos85OrderSixtyFourThreeComponentForkAdapter

/-! # A component-block repeated closing in the `[6,2]` stratum -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Cyclic rotation preserves the global colored-triple census. -/
theorem card_cyclicColoredTriples_rotate
    {V : Type*} [Fintype V] [DecidableEq V]
    (A B C : SimpleGraph V)
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj] :
    (cyclicColoredTriples A B C).card =
      (cyclicColoredTriples B C A).card := by
  classical
  apply Finset.card_bij (fun p _ => (p.2.2, p.1, p.2.1))
  · intro p hp
    simp only [cyclicColoredTriples, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp ⊢
    exact ⟨hp.2.1, hp.2.2, hp.1⟩
  · intro p hp q hq hpq
    rcases p with ⟨x, z, y⟩
    rcases q with ⟨x', z', y'⟩
    simp only at hpq
    cases hpq
    rfl
  · intro p hp
    refine ⟨(p.2.1, p.2.2, p.1), ?_, ?_⟩
    · simp only [cyclicColoredTriples, Finset.mem_filter, Finset.mem_univ,
        true_and] at hp ⊢
      exact ⟨hp.2.2, hp.1, hp.2.1⟩
    · rcases p with ⟨x, z, y⟩
      rfl

/-- If a colored-triple census is more than twice the directed first-edge
space and the defect graph has two components, then three triples share one
first edge; two of their closing vertices share a defect component, producing
a repeated closing inside one component block. -/
theorem exists_repeatedClosingInBlock_of_two_mul_directedEdge_card_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    (D A B C : SimpleGraph V) [DecidableRel D.Adj]
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj]
    (hcount : Fintype.card D.ConnectedComponent = 2)
    (hmore : (directedColoredEdges A).card * 2 <
      (cyclicColoredTriples A B C).card) :
    ∃ e f g : D.ConnectedComponent,
      HasRepeatedClosingInBlock D A B C e f g := by
  classical
  let S := cyclicColoredTriples A B C
  let T := directedColoredEdges A
  let F : V × V × V → (Σ _x : V, V) := fun p => ⟨p.1, p.2.2⟩
  have hmap : ∀ p ∈ S, F p ∈ T := by
    intro p hp
    have hpColor := (Finset.mem_filter.mp hp).2
    simp only [T, F, directedColoredEdges, Finset.mem_sigma,
      Finset.mem_univ, true_and]
    exact (A.mem_neighborFinset p.1 p.2.2).mpr hpColor.1
  obtain ⟨key, _hkey, hfiberCard⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (f := F) hmap hmore
  let P := S.filter fun p => F p = key
  let K : V × V × V → D.ConnectedComponent := fun p =>
    D.connectedComponentMk p.2.1
  have hPcard : Fintype.card D.ConnectedComponent < P.card := by
    rw [hcount]
    exact hfiberCard
  have hKmap : Set.MapsTo K (P : Set (V × V × V))
      ((Finset.univ : Finset D.ConnectedComponent) : Set D.ConnectedComponent) := by
    intro p hp
    exact Finset.mem_univ _
  obtain ⟨p, hp, r, hr, hpr, hK⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hPcard hKmap
  have hpData := Finset.mem_filter.mp hp
  have hrData := Finset.mem_filter.mp hr
  have hF : F p = F r := hpData.2.trans hrData.2.symm
  have hxy : p.1 = r.1 ∧ p.2.2 = r.2.2 := by
    simpa [F] using congrArg (fun z : (Σ _x : V, V) => (z.1, z.2)) hF
  have hz : p.2.1 ≠ r.2.1 := by
    intro hz
    apply hpr
    rcases p with ⟨x, z, y⟩
    rcases r with ⟨x', z', y'⟩
    apply Prod.ext hxy.1
    apply Prod.ext hz hxy.2
  let e := D.connectedComponentMk p.1
  let f := D.connectedComponentMk p.2.2
  let g := D.connectedComponentMk p.2.1
  have hrg : D.connectedComponentMk r.2.1 = g := by
    simpa [K, g] using hK.symm
  refine ⟨e, f, g, p, ?_, r, ?_, hpr, hxy.1, hxy.2, hz⟩
  · apply Finset.mem_filter.mpr
    refine ⟨hpData.1, ?_⟩
    simp [e, f, g]
  · apply Finset.mem_filter.mpr
    refine ⟨hrData.1, ?_⟩
    have hre : D.connectedComponentMk r.1 = e := by
      simpa [e] using congrArg D.connectedComponentMk hxy.1.symm
    have hrf : D.connectedComponentMk r.2.2 = f := by
      simpa [f] using congrArg D.connectedComponentMk hxy.2.symm
    exact ⟨(ConnectedComponent.mem_supp_iff e r.1).mpr hre,
      (ConnectedComponent.mem_supp_iff f r.2.2).mpr hrf,
      (ConnectedComponent.mem_supp_iff g r.2.1).mpr hrg⟩

/-- In the `[6,2]` stratum, orient the repeated owner color toward the
normalized size-two component.  The global mixed census is six times the
directed first-edge space, so the multiplicity theorem forces a genuine
component-block repeated closing despite the weak cross-budget bound. -/
theorem orderSixtyFour_sixTwo_exists_repeatedClosingInBlock
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 2)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ d, d.supp.ncard = 8 * m d)
    (a b : (secondOrderDefectGraph G).ConnectedComponent)
    (hab : a ≠ b) (hma : m a = 2) (hmb : m b = 6) :
    ∃ e f g,
      HasRepeatedClosingInBlock (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b) e f g := by
  let A := componentOwnerGraph G (secondOrderDefectGraph G) a
  let B := componentOwnerGraph G (secondOrderDefectGraph G) b
  have hAreg : ∀ x, A.degree x = m a * (8 - 1) :=
    binarySquare_regular_componentOwnerGraph_degree
      G hfree (q := 8) (by norm_num) hreg (by norm_num) a (hm a)
  have hedge : (directedColoredEdges A).card = 64 * (m a * 7) := by
    rw [card_directedColoredEdges_of_regular A (m a * (8 - 1)) hAreg]
    norm_num
  have htri := binarySquare_regular_card_twoOwnerColoredTriples
    G hfree (q := 8) (by norm_num) hreg (by norm_num) a b hab (hm a) (hm b)
  apply exists_repeatedClosingInBlock_of_two_mul_directedEdge_card_lt
    (secondOrderDefectGraph G) A A B hcount
  rw [hedge, htri, hma, hmb]
  norm_num

/-- The same multiplicity argument works before and after one cyclic
rotation, since both orientations still use the small owner `a` on their
first edge. -/
theorem orderSixtyFour_sixTwo_exists_twoCyclicRepeatedClosingInBlocks
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 2)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ d, d.supp.ncard = 8 * m d)
    (a b : (secondOrderDefectGraph G).ConnectedComponent)
    (hab : a ≠ b) (hma : m a = 2) (hmb : m b = 6) :
    (∃ e f g,
      HasRepeatedClosingInBlock (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b) e f g) ∧
    (∃ e f g,
      HasRepeatedClosingInBlock (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b)
        (componentOwnerGraph G (secondOrderDefectGraph G) a) e f g) := by
  refine ⟨orderSixtyFour_sixTwo_exists_repeatedClosingInBlock
    G hfree hreg hcount m hm a b hab hma hmb, ?_⟩
  let A := componentOwnerGraph G (secondOrderDefectGraph G) a
  let B := componentOwnerGraph G (secondOrderDefectGraph G) b
  have hAreg : ∀ x, A.degree x = m a * (8 - 1) :=
    binarySquare_regular_componentOwnerGraph_degree
      G hfree (q := 8) (by norm_num) hreg (by norm_num) a (hm a)
  have hedge : (directedColoredEdges A).card = 64 * (m a * 7) := by
    rw [card_directedColoredEdges_of_regular A (m a * (8 - 1)) hAreg]
    norm_num
  have htri := binarySquare_regular_card_twoOwnerColoredTriples
    G hfree (q := 8) (by norm_num) hreg (by norm_num) a b hab (hm a) (hm b)
  apply exists_repeatedClosingInBlock_of_two_mul_directedEdge_card_lt
    (secondOrderDefectGraph G) A B A hcount
  rw [← card_cyclicColoredTriples_rotate A A B, hedge, htri, hma, hmb]
  norm_num

end

end Erdos85

#print axioms Erdos85.card_cyclicColoredTriples_rotate
#print axioms Erdos85.exists_repeatedClosingInBlock_of_two_mul_directedEdge_card_lt
#print axioms Erdos85.orderSixtyFour_sixTwo_exists_repeatedClosingInBlock
#print axioms Erdos85.orderSixtyFour_sixTwo_exists_twoCyclicRepeatedClosingInBlocks
