import Proofs.Erdos85BinarySquareOwnerBlockPathCapacity

/-! # Repeated closings forced by owner-block pressure -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Directed owner-colored edges from defect component `e` to component `f`. -/
def ownerColoredEdgesInBlocks
    {V : Type*} [Fintype V] [DecidableEq V]
    (D A : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent] [DecidableRel A.Adj]
    (e f : D.ConnectedComponent) : Finset (Σ _x : V, V) :=
  (e.supp.toFinite.toFinset).sigma fun x => componentNeighborFinset A D f x

/-- Exact number of directed first edges available to a mixed-owner block. -/
theorem binarySquare_regular_card_ownerColoredEdgesInBlocks
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ d, d.supp.ncard = q * m d)
    (a e f : (secondOrderDefectGraph G).ConnectedComponent) :
    (ownerColoredEdgesInBlocks (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a) e f).card =
      q * m e *
        (if e = f then m a * (m f - 1) else m a * m f) := by
  classical
  let D := secondOrderDefectGraph G
  let A := componentOwnerGraph G D a
  let k := if e = f then m a * (m f - 1) else m a * m f
  have heCard : e.supp.toFinite.toFinset.card = q * m e := by
    simpa using (Set.ncard_eq_toFinset_card' e.supp).symm.trans (hm e)
  have hdeg : ∀ x ∈ e.supp.toFinite.toFinset,
      (componentNeighborFinset A D f x).card = k := by
    intro x hx
    have hx' : x ∈ e.supp := by simpa using hx
    simpa [A, D, k] using
      binarySquare_regular_componentOwnerGraph_blockNeighborCard
        G hfree hq hreg hcard m hm a e f ⟨x, hx'⟩
  simp only [ownerColoredEdgesInBlocks, Finset.card_sigma]
  calc
    (∑ x ∈ e.supp.toFinite.toFinset,
      (componentNeighborFinset A D f x).card) =
        ∑ _x ∈ e.supp.toFinite.toFinset, k := by
          apply Finset.sum_congr rfl
          intro x hx
          exact hdeg x hx
    _ = q * m e * k := by
      rw [Finset.sum_const, heCard, nsmul_eq_mul]
      simp [Nat.mul_assoc]
    _ = _ := by rfl

/-- If a fixed component-pattern triangle block is larger than its set of
first owner-colored edges, two distinct triples share their first two
vertices.  Consequently they have distinct closing vertices. -/
theorem exists_repeatedClosing_of_ownerEdge_card_lt_block_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (D A B C : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj]
    (e f g : D.ConnectedComponent)
    (hmore : (ownerColoredEdgesInBlocks D A e f).card <
      (cyclicColoredTriplesInBlocks D A B C e f g).card) :
    ∃ p ∈ cyclicColoredTriplesInBlocks D A B C e f g,
      ∃ r ∈ cyclicColoredTriplesInBlocks D A B C e f g,
        p ≠ r ∧ p.1 = r.1 ∧ p.2.2 = r.2.2 ∧ p.2.1 ≠ r.2.1 := by
  classical
  let S := cyclicColoredTriplesInBlocks D A B C e f g
  let T := ownerColoredEdgesInBlocks D A e f
  let F : V × V × V → (Σ _x : V, V) := fun p => ⟨p.1, p.2.2⟩
  have hmap : Set.MapsTo F (S : Set (V × V × V)) (T : Set (Σ _x : V, V)) := by
    intro p hp
    have hpBlock := Finset.mem_filter.mp hp
    have hpColor := (Finset.mem_filter.mp hpBlock.1).2
    change F p ∈ T
    simp only [T, F, ownerColoredEdgesInBlocks, Finset.mem_sigma]
    refine ⟨by simpa using hpBlock.2.1, ?_⟩
    rw [componentNeighborFinset, Finset.mem_filter]
    exact ⟨(A.mem_neighborFinset p.1 p.2.2).mpr hpColor.1,
      (ConnectedComponent.mem_supp_iff f p.2.2).mp hpBlock.2.2.1⟩
  obtain ⟨p, hp, r, hr, hpr, hF⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hmore hmap
  have hxy : p.1 = r.1 ∧ p.2.2 = r.2.2 := by
    simpa [F] using congrArg (fun z : (Σ _x : V, V) => (z.1, z.2)) hF
  have hz : p.2.1 ≠ r.2.1 := by
    intro hz
    apply hpr
    rcases p with ⟨x, z, y⟩
    rcases r with ⟨x', z', y'⟩
    apply Prod.ext hxy.1
    apply Prod.ext hz hxy.2
  exact ⟨p, hp, r, hr, hpr, hxy.1, hxy.2, hz⟩

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_card_ownerColoredEdgesInBlocks
#print axioms Erdos85.exists_repeatedClosing_of_ownerEdge_card_lt_block_card
