import Proofs.Erdos85BinarySquareLiteralMixedOwnerTriangleCensus

/-!
# Cross-component ambient triangles are literally mixed-owner

In an ambient `G`-triangle, each edge is owned by the defect component of the
opposite vertex.  Hence a triangle whose vertices meet two defect components
is a genuinely mixed triangle in the defect-complement owner coloring.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Ordered ambient triangles whose first and second tuple vertices lie in
distinct second-order defect components. -/
def crossComponentAmbientCyclicTriangles
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent] :
    Finset (V × V × V) :=
  (cyclicColoredTriples G G G).filter fun p =>
    (secondOrderDefectGraph G).connectedComponentMk p.1 ≠
      (secondOrderDefectGraph G).connectedComponentMk p.2.1

private theorem componentOwnerGraph_adj_of_common_neighbor_component
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : SimpleGraph V) [DecidableEq D.ConnectedComponent]
    {a b u : V} (hab : a ≠ b) (hau : G.Adj a u) (hbu : G.Adj b u) :
    (componentOwnerGraph G D (D.connectedComponentMk u)).Adj a b := by
  rw [componentOwnerGraph_adj]
  refine ⟨hab, ⟨u, ?_⟩⟩
  simp only [Finset.mem_inter, componentNeighborFinset, Finset.mem_filter,
    SimpleGraph.mem_neighborFinset]
  exact ⟨⟨hau, trivial⟩, ⟨hbu, trivial⟩⟩

/-- Pointwise bridge: every ordered ambient triangle crossing defect
components is a literal mixed-owner complement triangle. -/
theorem mem_literalMixedOwnerCyclicTriples_of_mem_crossComponentAmbient
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (p : V × V × V)
    (hp : p ∈ crossComponentAmbientCyclicTriangles G) :
    p ∈ literalMixedOwnerCyclicTriples G := by
  classical
  let D := secondOrderDefectGraph G
  simp only [crossComponentAmbientCyclicTriangles, Finset.mem_filter] at hp
  have htri := hp.1
  simp only [cyclicColoredTriples, Finset.mem_filter,
    Finset.mem_univ, true_and] at htri
  have hcolor : D.connectedComponentMk p.2.1 ≠
      D.connectedComponentMk p.1 := hp.2.symm
  have h₁ : (componentOwnerGraph G D (D.connectedComponentMk p.2.1)).Adj
      p.1 p.2.2 :=
    componentOwnerGraph_adj_of_common_neighbor_component G D htri.1.ne
      htri.2.2.symm htri.2.1
  have h₂ : (componentOwnerGraph G D (D.connectedComponentMk p.1)).Adj
      p.2.2 p.2.1 :=
    componentOwnerGraph_adj_of_common_neighbor_component G D htri.2.1.ne
      htri.1.symm htri.2.2
  have h₃ : (componentOwnerGraph G D (D.connectedComponentMk p.2.2)).Adj
      p.2.1 p.1 :=
    componentOwnerGraph_adj_of_common_neighbor_component G D htri.2.2.ne
      htri.2.1.symm htri.1
  have hownerTriangle : p ∈ cyclicColoredTriples
      (componentOwnerGraph G D (D.connectedComponentMk p.2.1))
      (componentOwnerGraph G D (D.connectedComponentMk p.1))
      (componentOwnerGraph G D (D.connectedComponentMk p.2.2)) := by
    simp only [cyclicColoredTriples, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨h₁, h₂, h₃⟩
  exact mem_literalMixedOwnerCyclicTriples_of_mem_ownerColored_of_ne
    G hfree _ _ _ hcolor p hownerTriangle

/-- Census form of the bridge: the number of ordered ambient triangles that
cross defect components is bounded by the literal mixed-owner census. -/
theorem card_crossComponentAmbientCyclicTriangles_le_literalMixedOwner
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) :
    (crossComponentAmbientCyclicTriangles G).card ≤
      (literalMixedOwnerCyclicTriples G).card := by
  exact Finset.card_le_card fun p hp =>
    mem_literalMixedOwnerCyclicTriples_of_mem_crossComponentAmbient
      G hfree p hp

/-- The ambient-`G` part of the literal mixed-owner census. -/
def literalMixedOwnerAmbientCyclicTriangles
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent] :
    Finset (V × V × V) :=
  (literalMixedOwnerCyclicTriples G).filter fun p =>
    p ∈ cyclicColoredTriples G G G

/-- The non-ambient part of the literal mixed-owner census. -/
def literalMixedOwnerNonambientCyclicTriples
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent] :
    Finset (V × V × V) :=
  (literalMixedOwnerCyclicTriples G).filter fun p =>
    p ∉ cyclicColoredTriples G G G

/-- Ordered ambient triangles whose vertices are not all in one defect
component. -/
def multiComponentAmbientCyclicTriangles
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent] :
    Finset (V × V × V) :=
  (cyclicColoredTriples G G G).filter fun p =>
    ¬ ((secondOrderDefectGraph G).connectedComponentMk p.1 =
          (secondOrderDefectGraph G).connectedComponentMk p.2.1 ∧
        (secondOrderDefectGraph G).connectedComponentMk p.1 =
          (secondOrderDefectGraph G).connectedComponentMk p.2.2)

/-- Exact identification: the ambient half of the literal mixed census is
precisely the set of ambient triangles spanning multiple defect components. -/
theorem literalMixedOwnerAmbientCyclicTriangles_eq_multiComponentAmbient
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) :
    literalMixedOwnerAmbientCyclicTriangles G =
      multiComponentAmbientCyclicTriangles G := by
  classical
  let D := secondOrderDefectGraph G
  ext p
  simp only [literalMixedOwnerAmbientCyclicTriangles,
    multiComponentAmbientCyclicTriangles, Finset.mem_filter]
  constructor
  · rintro ⟨hlit, htri⟩
    refine ⟨htri, ?_⟩
    rintro ⟨hxyComp, hxzComp⟩
    simp only [literalMixedOwnerCyclicTriples, Finset.mem_filter] at hlit
    apply hlit.2
    have ht := htri
    simp only [cyclicColoredTriples, Finset.mem_filter,
      Finset.mem_univ, true_and] at ht
    refine ⟨D.connectedComponentMk p.1, ?_⟩
    simp only [cyclicColoredTriples, Finset.mem_filter,
      Finset.mem_univ, true_and]
    have h₁ := componentOwnerGraph_adj_of_common_neighbor_component G D
      ht.1.ne ht.2.2.symm ht.2.1
    have h₂ := componentOwnerGraph_adj_of_common_neighbor_component G D
      ht.2.1.ne ht.1.symm ht.2.2
    have h₃ := componentOwnerGraph_adj_of_common_neighbor_component G D
      ht.2.2.ne ht.2.1.symm ht.1
    rw [← hxyComp] at h₁
    rw [← hxzComp] at h₃
    exact ⟨h₁, h₂, h₃⟩
  · rintro ⟨htri, hmulti⟩
    refine ⟨?_, htri⟩
    have ht := htri
    simp only [cyclicColoredTriples, Finset.mem_filter,
      Finset.mem_univ, true_and] at ht
    have h₁ : (componentOwnerGraph G D (D.connectedComponentMk p.2.1)).Adj
        p.1 p.2.2 :=
      componentOwnerGraph_adj_of_common_neighbor_component G D ht.1.ne
        ht.2.2.symm ht.2.1
    have h₂ : (componentOwnerGraph G D (D.connectedComponentMk p.1)).Adj
        p.2.2 p.2.1 :=
      componentOwnerGraph_adj_of_common_neighbor_component G D ht.2.1.ne
        ht.1.symm ht.2.2
    have h₃ : (componentOwnerGraph G D (D.connectedComponentMk p.2.2)).Adj
        p.2.1 p.1 :=
      componentOwnerGraph_adj_of_common_neighbor_component G D ht.2.2.ne
        ht.2.1.symm ht.1
    have howner : p ∈ cyclicColoredTriples
        (componentOwnerGraph G D (D.connectedComponentMk p.2.1))
        (componentOwnerGraph G D (D.connectedComponentMk p.1))
        (componentOwnerGraph G D (D.connectedComponentMk p.2.2)) := by
      simp only [cyclicColoredTriples, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact ⟨h₁, h₂, h₃⟩
    apply mem_literalMixedOwnerCyclicTriples_of_mem_ownerColored_of_not_all_eq
      G hfree _ _ _ _ p howner
    rintro ⟨hyx, hyz⟩
    exact hmulti ⟨hyx.symm, hyx.symm.trans hyz⟩

/-- Cross-component ambient triangles land specifically in the ambient half
of the sharp mixed-owner decomposition. -/
theorem card_crossComponentAmbientCyclicTriangles_le_literalMixedOwnerAmbient
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) :
    (crossComponentAmbientCyclicTriangles G).card ≤
      (literalMixedOwnerAmbientCyclicTriangles G).card := by
  apply Finset.card_le_card
  intro p hp
  simp only [literalMixedOwnerAmbientCyclicTriangles, Finset.mem_filter]
  exact ⟨mem_literalMixedOwnerCyclicTriples_of_mem_crossComponentAmbient
      G hfree p hp,
    (Finset.mem_filter.mp hp).1⟩

/-- Exact sharp-count decomposition: mixed ambient triangles plus mixed
non-ambient complement triangles account for `6Δ`. -/
theorem int_card_literalMixedOwnerAmbient_add_nonambient_eq_six_mul_deficit
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hcard : 3 ≤ Fintype.card V) :
    ((literalMixedOwnerAmbientCyclicTriangles G).card : ℤ) +
      ((literalMixedOwnerNonambientCyclicTriples G).card : ℤ) =
        6 * binarySquareMixedOwnerTriangleDeficit G := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := literalMixedOwnerCyclicTriples G)
    (fun p => p ∈ cyclicColoredTriples G G G)
  change (literalMixedOwnerAmbientCyclicTriangles G).card +
      (literalMixedOwnerNonambientCyclicTriples G).card =
        (literalMixedOwnerCyclicTriples G).card at hsplit
  rw [← int_card_literalMixedOwnerCyclicTriples_eq_six_mul_deficit
    G hfree hcard]
  exact_mod_cast hsplit

/-- Exact form with the ambient term expressed intrinsically as
multi-component ambient triangles. -/
theorem int_card_multiComponentAmbient_add_mixedNonambient_eq_six_mul_deficit
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hcard : 3 ≤ Fintype.card V) :
    ((multiComponentAmbientCyclicTriangles G).card : ℤ) +
      ((literalMixedOwnerNonambientCyclicTriples G).card : ℤ) =
        6 * binarySquareMixedOwnerTriangleDeficit G := by
  rw [← literalMixedOwnerAmbientCyclicTriangles_eq_multiComponentAmbient
    G hfree]
  exact int_card_literalMixedOwnerAmbient_add_nonambient_eq_six_mul_deficit
    G hfree hcard

/-- Uniform sharp modular constraint on the two literal sources of mixed
triangles: their combined ordered count is divisible by `3q^2`. -/
theorem binarySquare_regular_six_mul_two_pow_pred_dvd_multiComponentAmbient_add_mixedNonambient
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {k : ℕ} (hk : 2 ≤ k)
    (hreg : ∀ x, G.degree x = 2 ^ k)
    (hcard : Fintype.card V = (2 ^ k) * (2 ^ k))
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = (2 ^ k) * m c)
    (hsum : ∑ c, m c = 2 ^ k) :
    (6 * (2 : ℤ) ^ (2 * k - 1)) ∣
      ((multiComponentAmbientCyclicTriangles G).card : ℤ) +
        ((literalMixedOwnerNonambientCyclicTriples G).card : ℤ) := by
  obtain ⟨z, hz⟩ :=
    binarySquare_regular_two_pow_pred_dvd_mixedOwnerTriangleDeficit
      G hfree hk hreg hcard m hm hsum
  refine ⟨z, ?_⟩
  rw [int_card_multiComponentAmbient_add_mixedNonambient_eq_six_mul_deficit
    G hfree (by
      rw [hcard]
      have hq4 : 4 ≤ 2 ^ k := by
        calc
          4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      nlinarith), hz]
  ring

end

end Erdos85

#print axioms
  Erdos85.mem_literalMixedOwnerCyclicTriples_of_mem_crossComponentAmbient
#print axioms
  Erdos85.card_crossComponentAmbientCyclicTriangles_le_literalMixedOwner
#print axioms
  Erdos85.int_card_literalMixedOwnerAmbient_add_nonambient_eq_six_mul_deficit
#print axioms
  Erdos85.card_crossComponentAmbientCyclicTriangles_le_literalMixedOwnerAmbient
#print axioms
  Erdos85.literalMixedOwnerAmbientCyclicTriangles_eq_multiComponentAmbient
#print axioms
  Erdos85.int_card_multiComponentAmbient_add_mixedNonambient_eq_six_mul_deficit
#print axioms
  Erdos85.binarySquare_regular_six_mul_two_pow_pred_dvd_multiComponentAmbient_add_mixedNonambient
