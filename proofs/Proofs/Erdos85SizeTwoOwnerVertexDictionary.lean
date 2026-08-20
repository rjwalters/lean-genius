import Proofs.Erdos85ExteriorOwnerTilingLaw
import Proofs.Erdos85OrderSixtyFourExteriorPairGraph
import Proofs.Erdos85ExcessDefectRegular

/-!
# Owner-vertex dictionary for size-two defect components

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3 (bridge increment
3c-ii-a; squad msgs 13989/13994).

The owner-grid CNFs speak about *owner vertices*: for each active owner
pair of internal vertices, the unique exterior common ambient neighbor.
This file provides the mode-independent dictionary lemmas — existence
and uniqueness of owner vertices, the tile-pair identification, and the
exterior-server dichotomy — for any size-two component of the
eight-regular binary square.  The `(−1,1,4)` instantiation consumes
them; the other negative self and cross-orbit leaves can reuse them.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  [DecidableRel (antipodalGraph G).Adj]
  [DecidableRel (triangleFreeEdgeGraph G).Adj]
  [Fintype (secondOrderDefectGraph G).ConnectedComponent]
  [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]

/-- Any two distinct vertices of a C4-free graph have at most one common
neighbor, stated in server form. -/
theorem commonServer_unique
    (hfree : ¬ containsC4 V G) {x y : V} (hxy : x ≠ y)
    {t t' : V} (htx : G.Adj x t) (hty : G.Adj y t)
    (htx' : G.Adj x t') (hty' : G.Adj y t') : t = t' := by
  have hle := common_le_one_of_not_containsC4 hfree x y hxy
  have hmem : t ∈ G.neighborFinset x ∩ G.neighborFinset y :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x t).mpr htx,
      (G.mem_neighborFinset y t).mpr hty⟩
  have hmem' : t' ∈ G.neighborFinset x ∩ G.neighborFinset y :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x t').mpr htx',
      (G.mem_neighborFinset y t').mpr hty'⟩
  exact Finset.card_le_one.mp hle t hmem t' hmem'

/-- **Owner vertex of an exterior-pair edge.**  Two internal vertices
joined in the exterior-pair graph have exactly one common ambient
neighbor, and it lies outside the component support. -/
theorem exteriorPairGraph_ownerVertex
    (hfree : ¬ containsC4 V G) (s : Set V)
    {x y : s} (hR : (exteriorPairGraph G s).Adj x y) :
    ∃ t : V, t ∉ s ∧ G.Adj x.1 t ∧ G.Adj y.1 t ∧
      ∀ t' : V, G.Adj x.1 t' → G.Adj y.1 t' → t' = t := by
  obtain ⟨hne, z, hz, hxz, hyz⟩ := hR
  refine ⟨z, hz, hxz, hyz, ?_⟩
  intro t' hxt' hyt'
  exact commonServer_unique G hfree
    (fun h => hne (Subtype.ext h)) hxt' hyt' hxz hyz

/-- Every vertex's tile in a size-two component has exactly two
elements. -/
theorem sizeTwoPart_tile_card_two
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q) (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hsize : c.supp.ncard = q * 2) (z : V) :
    (componentNeighborFinset G (secondOrderDefectGraph G) c z).card = 2 := by
  have hz : z ∈ ((secondOrderDefectGraph G).connectedComponentMk z).supp :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff _ z).mpr rfl
  have h := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
    G hfree hq hreg hcard
    ((secondOrderDefectGraph G).connectedComponentMk z) c hz
  rw [hsize] at h
  exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) h

/-- A vertex adjacent to two distinct members of a size-two component
has exactly those two as its tile. -/
theorem sizeTwoPart_tile_eq_pair
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q) (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hsize : c.supp.ncard = q * 2)
    {t x y : V} (hxy : x ≠ y)
    (hxc : x ∈ c.supp) (hyc : y ∈ c.supp)
    (htx : G.Adj t x) (hty : G.Adj t y) :
    componentNeighborFinset G (secondOrderDefectGraph G) c t = {x, y} := by
  have hcard2 := sizeTwoPart_tile_card_two G hfree hq hreg hcard c hsize t
  have hxmem : x ∈ componentNeighborFinset G (secondOrderDefectGraph G) c t := by
    rw [componentNeighborFinset, Finset.mem_filter, mem_neighborFinset]
    exact ⟨htx, (SimpleGraph.ConnectedComponent.mem_supp_iff c x).mp hxc⟩
  have hymem : y ∈ componentNeighborFinset G (secondOrderDefectGraph G) c t := by
    rw [componentNeighborFinset, Finset.mem_filter, mem_neighborFinset]
    exact ⟨hty, (SimpleGraph.ConnectedComponent.mem_supp_iff c y).mp hyc⟩
  have hsub : ({x, y} : Finset V) ⊆
      componentNeighborFinset G (secondOrderDefectGraph G) c t := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hxmem
    · rw [Finset.mem_singleton] at hw
      subst hw
      exact hymem
  have hpaircard : ({x, y} : Finset V).card = 2 :=
    Finset.card_pair hxy
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

/-- **Server dichotomy.**  An internal ambient neighbor of any vertex
is a member of that vertex's tile. -/
theorem sizeTwoPart_server_mem_tile_of_internal
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    {t z : V} (htz : G.Adj t z) (hzc : z ∈ c.supp) :
    z ∈ componentNeighborFinset G (secondOrderDefectGraph G) c t := by
  rw [componentNeighborFinset, Finset.mem_filter, mem_neighborFinset]
  exact ⟨htz, (SimpleGraph.ConnectedComponent.mem_supp_iff c z).mp hzc⟩

/-- **Owner vertex of a non-defect cross pair.**  A non-defect pair with
no internal common neighbor has exactly one common ambient neighbor,
and it is exterior. -/
theorem nonDefect_ownerVertex_exterior
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    {x y : V} (hxy : x ≠ y)
    (hND : ¬ (secondOrderDefectGraph G).Adj x y)
    (hint : ∀ z ∈ c.supp, ¬ (G.Adj x z ∧ G.Adj y z)) :
    ∃ t : V, t ∉ c.supp ∧ G.Adj x t ∧ G.Adj y t ∧
      ∀ t' : V, G.Adj x t' → G.Adj y t' → t' = t := by
  have hcommon := card_common_eq_if_secondOrderDefect G hfree x y hxy
  rw [if_neg (by
    rw [mem_neighborFinset]
    exact hND)] at hcommon
  obtain ⟨z, hz⟩ : ∃ z, z ∈ G.neighborFinset x ∩ G.neighborFinset y :=
    Finset.card_pos.mp (by omega)
  rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset] at hz
  refine ⟨z, ?_, hz.1, hz.2, ?_⟩
  · intro hzc
    exact hint z hzc ⟨hz.1, hz.2⟩
  · intro t' hxt' hyt'
    exact commonServer_unique G hfree hxy hxt' hyt' hz.1 hz.2

/-- Distinct owner pairs sharing an owner vertex coincide: the tile of
the owner vertex recovers the unordered pair. -/
theorem ownerVertex_pair_eq
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q) (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hsize : c.supp.ncard = q * 2)
    {x y x' y' : V} (hxy : x ≠ y) (hxy' : x' ≠ y')
    (hxc : x ∈ c.supp) (hyc : y ∈ c.supp)
    (hxc' : x' ∈ c.supp) (hyc' : y' ∈ c.supp)
    {t : V} (htx : G.Adj t x) (hty : G.Adj t y)
    (htx' : G.Adj t x') (hty' : G.Adj t y') :
    ({x, y} : Finset V) = {x', y'} := by
  have h1 := sizeTwoPart_tile_eq_pair G hfree hq hreg hcard c hsize
    hxy hxc hyc htx hty
  have h2 := sizeTwoPart_tile_eq_pair G hfree hq hreg hcard c hsize
    hxy' hxc' hyc' htx' hty'
  rw [h1] at h2
  exact h2

end

end Erdos85

#print axioms Erdos85.exteriorPairGraph_ownerVertex
#print axioms Erdos85.sizeTwoPart_tile_eq_pair
#print axioms Erdos85.nonDefect_ownerVertex_exterior
#print axioms Erdos85.ownerVertex_pair_eq
