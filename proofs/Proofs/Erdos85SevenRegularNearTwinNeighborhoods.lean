import Proofs.Erdos85BinarySquareExactAdjacencyKernel
import Proofs.Erdos85BinarySquareRegularParity

/-! # Near-twin neighborhoods in a seven-regular graph

The large-codegree cases in the order-sixty-four defect-component census
contain nonedges with six common defect neighbors.  Since the defect graph is
seven-regular, such a pair has only one private neighbor on either side.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Vertices outside two roots and both of their neighborhoods.  For a
nonadjacent near-twin pair on sixteen vertices this is the six-element common
neighborhood in the complement graph. -/
def nearTwinExteriorFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x y : V) : Finset V :=
  Finset.univ \ insert x (insert y (H.neighborFinset x ∪ H.neighborFinset y))

/-- The exterior of two distinct roots is their common neighborhood in the
complement graph. -/
theorem nearTwinExteriorFinset_eq_compl_common
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x y : V) :
    nearTwinExteriorFinset H x y =
      Hᶜ.neighborFinset x ∩ Hᶜ.neighborFinset y := by
  ext z
  simp only [nearTwinExteriorFinset, Finset.mem_sdiff, Finset.mem_univ,
    true_and, Finset.mem_insert, Finset.mem_union, Finset.mem_inter,
    SimpleGraph.mem_neighborFinset, compl_adj]
  constructor
  · intro hz
    push Not at hz
    exact ⟨⟨Ne.symm hz.1, hz.2.2.1⟩, Ne.symm hz.2.1, hz.2.2.2⟩
  · rintro ⟨⟨hxz, hnotxz⟩, hyz, hnotyz⟩
    push Not
    exact ⟨Ne.symm hxz, Ne.symm hyz, hnotxz, hnotyz⟩

/-- Seven-regular vertices with six common neighbors each have exactly one
neighbor outside the other's neighborhood. -/
theorem sevenRegular_sdiff_neighborFinset_card_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ z, H.degree z = 7) {x y : V}
    (hcommon : (H.neighborFinset x ∩ H.neighborFinset y).card = 6) :
    (H.neighborFinset x \ H.neighborFinset y).card = 1 ∧
      (H.neighborFinset y \ H.neighborFinset x).card = 1 := by
  have hx := Finset.card_sdiff_add_card_inter
    (H.neighborFinset x) (H.neighborFinset y)
  have hy := Finset.card_sdiff_add_card_inter
    (H.neighborFinset y) (H.neighborFinset x)
  rw [H.card_neighborFinset_eq_degree, hreg x, hcommon] at hx
  rw [H.card_neighborFinset_eq_degree, hreg y,
    Finset.inter_comm, hcommon] at hy
  omega

/-- The two private neighbors of a six-common-neighbor pair exist uniquely. -/
theorem sevenRegular_existsUnique_private_neighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ z, H.degree z = 7) {x y : V}
    (hcommon : (H.neighborFinset x ∩ H.neighborFinset y).card = 6) :
    (∃! a, a ∈ H.neighborFinset x \ H.neighborFinset y) ∧
      (∃! b, b ∈ H.neighborFinset y \ H.neighborFinset x) := by
  have hcards := sevenRegular_sdiff_neighborFinset_card_eq_one H hreg hcommon
  rcases Finset.card_eq_one.mp hcards.1 with ⟨a, ha⟩
  rcases Finset.card_eq_one.mp hcards.2 with ⟨b, hb⟩
  constructor
  · exact ⟨a, by simp [ha], fun z hz => by simpa [ha] using hz⟩
  · exact ⟨b, by simp [hb], fun z hz => by simpa [hb] using hz⟩

/-- Exact near-twin normal form: both neighborhoods are obtained from their
six-element common core by adjoining one distinct private vertex. -/
theorem sevenRegular_neighborFinset_eq_insert_commonCore
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ z, H.degree z = 7) {x y : V}
    (hcommon : (H.neighborFinset x ∩ H.neighborFinset y).card = 6) :
    ∃ a b, a ≠ b ∧
      H.neighborFinset x =
        insert a (H.neighborFinset x ∩ H.neighborFinset y) ∧
      H.neighborFinset y =
        insert b (H.neighborFinset x ∩ H.neighborFinset y) := by
  have hcards := sevenRegular_sdiff_neighborFinset_card_eq_one H hreg hcommon
  rcases Finset.card_eq_one.mp hcards.1 with ⟨a, ha⟩
  rcases Finset.card_eq_one.mp hcards.2 with ⟨b, hb⟩
  have haMem : a ∈ H.neighborFinset x \ H.neighborFinset y := by simp [ha]
  have hbMem : b ∈ H.neighborFinset y \ H.neighborFinset x := by simp [hb]
  have hab : a ≠ b := by
    intro hab
    subst b
    exact (Finset.mem_sdiff.mp haMem).2 (Finset.mem_sdiff.mp hbMem).1
  have hxsplit := Finset.sdiff_union_inter
    (H.neighborFinset x) (H.neighborFinset y)
  have hysplit := Finset.sdiff_union_inter
    (H.neighborFinset y) (H.neighborFinset x)
  refine ⟨a, b, hab, ?_, ?_⟩
  · simpa [ha] using hxsplit.symm
  · simpa [hb, Finset.inter_comm] using hysplit.symm

/-- A nonadjacent near-twin pair in a seven-regular graph on sixteen vertices
leaves exactly six vertices outside the two roots and their neighborhoods. -/
theorem sevenRegular_nearTwinExteriorFinset_card_eq_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : Fintype.card V = 16) (hreg : ∀ z, H.degree z = 7)
    {x y : V} (hxy : x ≠ y) (hnot : ¬ H.Adj x y)
    (hcommon : (H.neighborFinset x ∩ H.neighborFinset y).card = 6) :
    (nearTwinExteriorFinset H x y).card = 6 := by
  let N := H.neighborFinset x ∪ H.neighborFinset y
  have hNcard : N.card = 8 := by
    have hsum := Finset.card_union_add_card_inter
      (H.neighborFinset x) (H.neighborFinset y)
    change N.card +
      (H.neighborFinset x ∩ H.neighborFinset y).card =
        (H.neighborFinset x).card + (H.neighborFinset y).card at hsum
    rw [H.card_neighborFinset_eq_degree, hreg x,
      H.card_neighborFinset_eq_degree, hreg y, hcommon] at hsum
    omega
  have hxN : x ∉ N := by
    simp only [N, Finset.mem_union, H.mem_neighborFinset]
    rintro (hxx | hyx)
    · exact H.loopless.irrefl x hxx
    · exact hnot hyx.symm
  have hyN : y ∉ N := by
    simp only [N, Finset.mem_union, H.mem_neighborFinset]
    rintro (hxy' | hyy)
    · exact hnot hxy'
    · exact H.loopless.irrefl y hyy
  have hxclosed : x ∉ insert y N := by
    simp [hxy, hxN]
  have hclosed : (insert x (insert y N)).card = 10 := by
    rw [Finset.card_insert_of_notMem hxclosed,
      Finset.card_insert_of_notMem hyN, hNcard]
  rw [nearTwinExteriorFinset,
    Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    hcard, hclosed]

/-- A nonadjacent codegree-six pair in a seven-regular graph on sixteen
vertices also has complement-codegree six.  Thus the six-core phenomenon is
self-dual. -/
theorem sevenRegular_compl_codegree_eq_six_of_codegree_eq_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : Fintype.card V = 16) (hreg : ∀ z, H.degree z = 7)
    {x y : V} (hxy : x ≠ y) (hnot : ¬ H.Adj x y)
    (hcommon : (H.neighborFinset x ∩ H.neighborFinset y).card = 6) :
    (Hᶜ.neighborFinset x ∩ Hᶜ.neighborFinset y).card = 6 := by
  rw [← nearTwinExteriorFinset_eq_compl_common H x y]
  exact sevenRegular_nearTwinExteriorFinset_card_eq_six
    H hcard hreg hxy hnot hcommon

/-- Near-twin neighborhoods differ in exactly two vertices. -/
theorem sevenRegular_neighborFinset_symmDiff_card_eq_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ z, H.degree z = 7) {x y : V}
    (hcommon : (H.neighborFinset x ∩ H.neighborFinset y).card = 6) :
    ((H.neighborFinset x \ H.neighborFinset y) ∪
      (H.neighborFinset y \ H.neighborFinset x)).card = 2 := by
  have hcards := sevenRegular_sdiff_neighborFinset_card_eq_one H hreg hcommon
  rw [Finset.card_union_of_disjoint]
  · omega
  · rw [Finset.disjoint_left]
    intro z hzx hzy
    exact (Finset.mem_sdiff.mp hzx).2 (Finset.mem_sdiff.mp hzy).1

/-- Order-sixty-four specialization: a defect-graph pair of codegree six is
a near-twin pair with one private defect neighbor on each side. -/
theorem orderSixtyFour_defect_codegree_six_private_neighbors
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ z, G.degree z = 8) {x y : Fin 64}
    (hcommon : ((secondOrderDefectGraph G).neighborFinset x ∩
      (secondOrderDefectGraph G).neighborFinset y).card = 6) :
    ((secondOrderDefectGraph G).neighborFinset x \
        (secondOrderDefectGraph G).neighborFinset y).card = 1 ∧
      ((secondOrderDefectGraph G).neighborFinset y \
        (secondOrderDefectGraph G).neighborFinset x).card = 1 := by
  apply sevenRegular_sdiff_neighborFinset_card_eq_one
    (secondOrderDefectGraph G) (fun z => ?_) hcommon
  have hz := secondOrderDefectGraph_degree_eq_excess_add_two
    G hfree (d := 8) (e := 5) hreg (by norm_num) z
  simpa using hz

/-- Every vertex in the six-element common defect neighborhood has its
selector disjoint from the union of the two near-twin selectors, in every
target component.  This is the direct bridge from defect codegree to the
selector-packing constraints. -/
theorem commonDefectNeighbor_selector_disjoint_nearTwin_union
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {x y z : V}
    (hz : z ∈ (secondOrderDefectGraph G).neighborFinset x ∩
      (secondOrderDefectGraph G).neighborFinset y)
    (target : (secondOrderDefectGraph G).ConnectedComponent) :
    Disjoint
      (componentNeighborFinset G (secondOrderDefectGraph G) target x ∪
        componentNeighborFinset G (secondOrderDefectGraph G) target y)
      (componentNeighborFinset G (secondOrderDefectGraph G) target z) := by
  have hzdata := Finset.mem_inter.mp hz
  have hxz : (secondOrderDefectGraph G).Adj x z :=
    ((secondOrderDefectGraph G).mem_neighborFinset x z).mp hzdata.1
  have hyz : (secondOrderDefectGraph G).Adj y z :=
    ((secondOrderDefectGraph G).mem_neighborFinset y z).mp hzdata.2
  exact Finset.disjoint_union_left.mpr
    ⟨componentNeighborFinset_disjoint_of_secondOrderDefect_adj
        G hfree hxz target,
      componentNeighborFinset_disjoint_of_secondOrderDefect_adj
        G hfree hyz target⟩

end

end Erdos85
