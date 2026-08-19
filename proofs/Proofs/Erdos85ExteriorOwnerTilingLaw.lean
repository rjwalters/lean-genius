import Proofs.Erdos85BinarySquareRegularParity

/-!
# The exterior owner tiling law

Node: `SIZE-TWO-EIGENLINE(q)` beneath outline F.3 (shape-independent layer).

Fix a size-two defect component `c` (order `q * 2`) of a `q`-regular
`C4`-free graph on `q^2` vertices.  By the equitable law every vertex `z`
(internal or exterior) has exactly two ambient neighbors inside `c`; call
this 2-set the *tile* of `z`.

**Tiling law.**  For every exterior vertex `u`, the `q` tiles of the
neighbors of `u` are pairwise disjoint and exactly partition `c`:

* disjointness — two servers of the same internal vertex would give `u`
  and that vertex two common neighbors, a `C4`;
* coverage — `q` disjoint tiles of size `2` occupy `q * 2 = |c|` slots.

Equivalently (`..._unique_server`), every internal vertex has *exactly
one* common neighbor with every exterior vertex.  This is the rigid
system coupling the exterior of `c` to the 48 owner pairs at `q = 8`;
the surviving disconnected strata (6+10 high, all 8+8 sectors) are meant
to be refuted against it.  Only the size-two hypothesis enters — no
stratum, sector, or shape hypothesis.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- **Exterior owner tiling law.**  For an exterior vertex `u` of a size-two
defect component `c`, the neighbor tiles `N(z) ∩ c` for `z ∈ N(u)` are
pairwise disjoint and their union is exactly `c`. -/
theorem binarySquare_regular_sizeTwoPart_exteriorOwner_tiling
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hsize : c.supp.ncard = q * 2)
    {u : V} (hu : (secondOrderDefectGraph G).connectedComponentMk u ≠ c) :
    (∀ z ∈ G.neighborFinset u, ∀ z' ∈ G.neighborFinset u, z ≠ z' →
      Disjoint (componentNeighborFinset G (secondOrderDefectGraph G) c z)
        (componentNeighborFinset G (secondOrderDefectGraph G) c z')) ∧
    (G.neighborFinset u).biUnion
        (componentNeighborFinset G (secondOrderDefectGraph G) c) =
      Finset.univ.filter
        (fun v => (secondOrderDefectGraph G).connectedComponentMk v = c) := by
  -- Every vertex serves exactly two internal vertices.
  have hserve : ∀ z : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c z).card = 2 := by
    intro z
    have hz : z ∈ ((secondOrderDefectGraph G).connectedComponentMk z).supp :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff _ z).mpr rfl
    have h := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
      G hfree hq hreg hcard
      ((secondOrderDefectGraph G).connectedComponentMk z) c hz
    rw [hsize] at h
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) h
  -- Disjointness of the tiles of two distinct neighbors of `u`.
  have hdisj : ∀ z ∈ G.neighborFinset u, ∀ z' ∈ G.neighborFinset u, z ≠ z' →
      Disjoint (componentNeighborFinset G (secondOrderDefectGraph G) c z)
        (componentNeighborFinset G (secondOrderDefectGraph G) c z') := by
    intro z hz z' hz' hne
    rw [Finset.disjoint_left]
    intro v hv hv'
    rw [componentNeighborFinset, Finset.mem_filter, mem_neighborFinset] at hv hv'
    have huv : u ≠ v := by
      intro h
      exact hu (h ▸ hv.2)
    exact hfree (containsC4_of_two_common huv hne
      ((mem_neighborFinset G u z).mp hz).symm hv.1
      ((mem_neighborFinset G u z').mp hz').symm hv'.1)
  refine ⟨hdisj, ?_⟩
  -- The component support as a finset has `q * 2` elements.
  have hsuppcard : (Finset.univ.filter
      (fun v => (secondOrderDefectGraph G).connectedComponentMk v = c)).card
        = q * 2 := by
    rw [← hsize]
    have hset : c.supp =
        {v | (secondOrderDefectGraph G).connectedComponentMk v = c} := by
      ext v
      exact SimpleGraph.ConnectedComponent.mem_supp_iff c v
    rw [hset, Set.ncard_eq_toFinset_card', Set.toFinset_setOf]
  -- Coverage by cardinality.
  apply Finset.eq_of_subset_of_card_le
  · intro v hv
    rw [Finset.mem_biUnion] at hv
    obtain ⟨z, _, hvz⟩ := hv
    rw [componentNeighborFinset, Finset.mem_filter] at hvz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvz.2⟩
  · rw [hsuppcard, Finset.card_biUnion hdisj]
    have hsum : ∑ z ∈ G.neighborFinset u,
        (componentNeighborFinset G (secondOrderDefectGraph G) c z).card
          = q * 2 := by
      rw [Finset.sum_congr rfl (fun z _ => hserve z), Finset.sum_const,
        G.card_neighborFinset_eq_degree, hreg u, smul_eq_mul]
    omega

/-- **Unique server.**  Every internal vertex of a size-two defect component
has exactly one common ambient neighbor with every exterior vertex. -/
theorem binarySquare_regular_sizeTwoPart_exteriorOwner_unique_server
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hsize : c.supp.ncard = q * 2)
    {u : V} (hu : (secondOrderDefectGraph G).connectedComponentMk u ≠ c)
    {v : V} (hv : (secondOrderDefectGraph G).connectedComponentMk v = c) :
    ∃! z : V, G.Adj u z ∧ G.Adj z v := by
  obtain ⟨hdisj, hcover⟩ :=
    binarySquare_regular_sizeTwoPart_exteriorOwner_tiling
      G hfree hq hreg hcard c hsize hu
  have hvmem : v ∈ (G.neighborFinset u).biUnion
      (componentNeighborFinset G (secondOrderDefectGraph G) c) := by
    rw [hcover]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
  rw [Finset.mem_biUnion] at hvmem
  obtain ⟨z, hz, hvz⟩ := hvmem
  rw [componentNeighborFinset, Finset.mem_filter, mem_neighborFinset] at hvz
  refine ⟨z, ⟨(mem_neighborFinset G u z).mp hz, hvz.1⟩, ?_⟩
  intro z' ⟨huz', hz'v⟩
  by_contra hne
  have hv' : v ∈ componentNeighborFinset G (secondOrderDefectGraph G) c z' := by
    rw [componentNeighborFinset, Finset.mem_filter, mem_neighborFinset]
    exact ⟨hz'v, hv⟩
  have hvmem' : v ∈ componentNeighborFinset G (secondOrderDefectGraph G) c z := by
    rw [componentNeighborFinset, Finset.mem_filter, mem_neighborFinset]
    exact ⟨hvz.1, hv⟩
  exact Finset.disjoint_left.mp
    (hdisj z' ((mem_neighborFinset G u z').mpr huz') z hz hne)
    hv' hvmem'

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_exteriorOwner_tiling
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_exteriorOwner_unique_server
