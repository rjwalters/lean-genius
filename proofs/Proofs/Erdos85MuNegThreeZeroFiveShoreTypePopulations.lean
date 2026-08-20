import Proofs.Erdos85EdgeIndexedServiceTypeHandshake
import Proofs.Erdos85MuNegThreeZeroFiveCorrectShoreGeometry
import Proofs.Erdos85ThreeLevelEigenSupportEdgeCensus

/-! # Shore-type edge populations for the h305 exterior graph -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Edges having both endpoints in `S` are exactly the image of the edge set
of the graph induced on `S`. -/
theorem shoreTypeEdgeFinset_two_map_eq_inter
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj] (S : Finset V) :
    (shoreTypeEdgeFinset R S 2).map
      (Function.Embedding.subtype (· ∈ R.edgeFinset)) =
        R.edgeFinset ∩ S.sym2 := by
  classical
  let eR : R.edgeFinset ↪ Sym2 V := Function.Embedding.subtype _
  have heq : (shoreTypeEdgeFinset R S 2).map eR =
      R.edgeFinset ∩ S.sym2 := by
    ext a
    simp only [Finset.mem_map, Finset.mem_inter]
    constructor
    · rintro ⟨b, hb, rfl⟩
      have h := Finset.mem_filter.mp hb
      have hinter : (b.1.toFinset ∩ S).card = b.1.toFinset.card := by
        rw [h.2, R.card_toFinset_mem_edgeFinset b]
      have heq : b.1.toFinset ∩ S = b.1.toFinset :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left
          (Nat.le_of_eq hinter.symm)
      refine ⟨b.2, Finset.mem_sym2_iff.mpr ?_⟩
      intro x hx
      have hxt : x ∈ b.1.toFinset := by simpa [eR] using hx
      exact (Finset.mem_inter.mp (heq.symm ▸ hxt)).2
    · rintro ⟨haR, h⟩
      rw [Finset.mem_sym2_iff] at h
      let b : R.edgeFinset := ⟨a, haR⟩
      refine ⟨b, ?_, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have heq : a.toFinset ∩ S = a.toFinset := by
        apply Finset.inter_eq_left.mpr
        intro x hx
        exact h x (by simpa using hx)
      rw [heq]
      exact R.card_toFinset_mem_edgeFinset b
  exact heq

/-- Cardinal form of `shoreTypeEdgeFinset_two_map_eq_inter`. -/
theorem shoreTypeEdgeFinset_two_card_eq_inter
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj] (S : Finset V) :
    (shoreTypeEdgeFinset R S 2).card =
      (R.edgeFinset ∩ S.sym2).card := by
  let eR : R.edgeFinset ↪ Sym2 V := Function.Embedding.subtype _
  calc
    (shoreTypeEdgeFinset R S 2).card =
        ((shoreTypeEdgeFinset R S 2).map eR).card :=
          (Finset.card_map eR).symm
    _ = (R.edgeFinset ∩ S.sym2).card := congrArg Finset.card
      (shoreTypeEdgeFinset_two_map_eq_inter R S)

/-- A shore of eight vertices with exactly three internal neighbors at every
vertex has exactly twelve shore-type-two edges. -/
theorem shoreTypeEdgeFinset_two_card_eq_twelve_of_internal_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj] (S : Finset V)
    (hcard : S.card = 8)
    (hinternal : ∀ x ∈ S,
      ((R.neighborFinset x).filter fun y ↦ y ∈ S).card = 3) :
    (shoreTypeEdgeFinset R S 2).card = 12 := by
  classical
  let H := R.induce (↑S : Set V)
  have hdegree : ∀ x : (↑S : Set V), H.degree x = 3 := by
    intro x
    have hmap : (H.neighborFinset x).map
        (Function.Embedding.subtype (· ∈ (↑S : Set V))) =
          R.neighborFinset x.1 ∩ S := by
      ext y
      simp [H, SimpleGraph.mem_neighborFinset]
    have hmapCard := congrArg Finset.card hmap
    rw [Finset.card_map] at hmapCard
    rw [← H.card_neighborFinset_eq_degree, hmapCard]
    simpa only [Finset.filter_mem_eq_inter] using hinternal x.1 x.2
  have hsum : (∑ x : (↑S : Set V), H.degree x) = 24 := by
    simp_rw [hdegree]
    simp [Fintype.card_coe, hcard]
  have htwice := H.sum_degrees_eq_twice_card_edges
  rw [hsum] at htwice
  have hmapEdges : H.edgeFinset.map
      (Function.Embedding.subtype (· ∈ (↑S : Set V))).sym2Map =
        R.edgeFinset ∩ S.sym2 := by
    aesop (add simp [Finset.ext_iff, Sym2.exists, Sym2.forall,
      SimpleGraph.adj_comm])
  have hedgeCard := congrArg Finset.card hmapEdges
  simp only [Finset.card_map] at hedgeCard
  rw [shoreTypeEdgeFinset_two_card_eq_inter R S, ← hedgeCard]
  omega

private theorem internalNeighbor_card_three_of_coordinate_rows
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (P : ZMod 8 → ZMod 8 → Prop) [DecidableRel P]
    (hrow : ∀ i j, R.Adj (u i) (u j) ↔ P i j)
    (hcount : ∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ P i j).card = 3)
    (i : ZMod 8) :
    ((R.neighborFinset (u i)).filter fun y ↦
      y ∈ (Finset.univ : Finset (ZMod 8)).image u).card = 3 := by
  classical
  let T := (Finset.univ : Finset (ZMod 8)).filter fun j ↦ P i j
  let eu : ZMod 8 ↪ V := ⟨u, huinj⟩
  have heq : T.map eu =
      (R.neighborFinset (u i)).filter fun y ↦
        y ∈ (Finset.univ : Finset (ZMod 8)).image u := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hx
      have hj' := Finset.mem_filter.mp hj
      apply Finset.mem_filter.mpr
      exact ⟨(R.mem_neighborFinset (u i) (u j)).mpr
          ((hrow i j).mpr hj'.2),
        Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
    · intro hx
      have hx' := Finset.mem_filter.mp hx
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx'.2
      apply Finset.mem_map.mpr
      exact ⟨j, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (hrow i j).mp
          ((R.mem_neighborFinset (u i) (u j)).mp hx'.1)⟩, rfl⟩
  rw [← heq, Finset.card_map]
  exact hcount i

/-- Either corrected h305 shore mode has exactly twelve within-shore exterior
edges.  In particular, the antipodal offset is included in the census. -/
theorem h305_correctShoreMode_typeTwo_card_twelve
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hmode : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u) :
    let U := (Finset.univ : Finset (ZMod 8)).image u
    (shoreTypeEdgeFinset R U 2).card = 12 := by
  classical
  dsimp only
  let U := (Finset.univ : Finset (ZMod 8)).image u
  have hUcard : U.card = 8 := by
    rw [Finset.card_image_of_injective _ huinj]
    decide
  apply shoreTypeEdgeFinset_two_card_eq_twelve_of_internal_three R U hUcard
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  rcases hmode with htri | htf
  · apply internalNeighbor_card_three_of_coordinate_rows R u huinj
      (fun i j ↦ j - i = 1 ∨ j - i = 4 ∨ j - i = 7)
      htri
    intro i
    generalize i = k
    revert k
    decide
  · apply internalNeighbor_card_three_of_coordinate_rows R u huinj
      (fun i j ↦ j - i = 3 ∨ j - i = 4 ∨ j - i = 5)
      htf
    intro i
    generalize i = k
    revert k
    decide

/-- Every graph edge has shore type zero, one, or two, and these three
classes partition the ambient edge set. -/
theorem shoreTypeEdgeFinset_card_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj] (S : Finset V) :
    (shoreTypeEdgeFinset R S 0).card +
      (shoreTypeEdgeFinset R S 1).card +
      (shoreTypeEdgeFinset R S 2).card = R.edgeFinset.card := by
  classical
  let E := fun t ↦ shoreTypeEdgeFinset R S t
  have hcover : (Finset.univ : Finset R.edgeFinset) =
      E 0 ∪ E 1 ∪ E 2 := by
    ext a
    simp only [Finset.mem_univ, Finset.mem_union, true_iff]
    have hle : (a.1.toFinset ∩ S).card ≤ 2 := by
      calc
        _ ≤ a.1.toFinset.card :=
          Finset.card_le_card Finset.inter_subset_left
        _ = 2 := R.card_toFinset_mem_edgeFinset a
    unfold E shoreTypeEdgeFinset
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have h01 : Disjoint (E 0) (E 1) := by
    rw [Finset.disjoint_left]
    intro a ha0 ha1
    simp only [E, shoreTypeEdgeFinset, Finset.mem_filter,
      Finset.mem_univ, true_and] at ha0 ha1
    omega
  have h02 : Disjoint (E 0) (E 2) := by
    rw [Finset.disjoint_left]
    intro a ha0 ha2
    simp only [E, shoreTypeEdgeFinset, Finset.mem_filter,
      Finset.mem_univ, true_and] at ha0 ha2
    omega
  have h12 : Disjoint (E 1) (E 2) := by
    rw [Finset.disjoint_left]
    intro a ha1 ha2
    simp only [E, shoreTypeEdgeFinset, Finset.mem_filter,
      Finset.mem_univ, true_and] at ha1 ha2
    omega
  have h0u1_2 : Disjoint (E 0 ∪ E 1) (E 2) :=
    Finset.disjoint_union_left.mpr ⟨h02, h12⟩
  have hcardUnion : (E 0 ∪ E 1 ∪ E 2).card =
      (E 0).card + (E 1).card + (E 2).card := by
    rw [Finset.card_union_of_disjoint h0u1_2,
      Finset.card_union_of_disjoint h01]
  have hc := congrArg Finset.card hcover
  rw [hcardUnion] at hc
  simpa [E] using hc.symm

/-- Shore type zero relative to `S` is shore type two relative to its
complement. -/
theorem shoreTypeEdgeFinset_zero_eq_two_compl
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj] (S : Finset V) :
    shoreTypeEdgeFinset R S 0 = shoreTypeEdgeFinset R Sᶜ 2 := by
  classical
  ext a
  simp only [shoreTypeEdgeFinset, Finset.mem_filter, Finset.mem_univ,
    true_and]
  have hsplit := Finset.card_inter_add_card_sdiff a.1.toFinset S
  have hcomp : (a.1.toFinset ∩ Sᶜ).card =
      (a.1.toFinset \ S).card := by
    congr 1
    ext x
    simp
  have hedge := R.card_toFinset_mem_edgeFinset a
  rw [hcomp]
  omega

/-- A six-regular graph on sixteen vertices has forty-eight edges. -/
theorem edgeFinset_card_eq_fortyEight_of_sixRegular_sixteen
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (hreg : ∀ x, R.degree x = 6) (hcard : Fintype.card V = 16) :
    R.edgeFinset.card = 48 := by
  have hsum := R.sum_degrees_eq_twice_card_edges
  have htotal : (∑ x : V, R.degree x) = 96 := by
    simp_rw [hreg]
    simp [hcard]
  rw [htotal] at hsum
  omega

/-- Full corrected h305 shore-type population census. -/
theorem h305_correctShoreModes_typePopulations
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u v : ZMod 8 → V)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (humode : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u)
    (hvmode : MuNegThreeZeroFiveTriangleShoreMode R v ∨
      MuNegThreeZeroFiveTfShoreMode R v)
    (hpartition : ((Finset.univ : Finset (ZMod 8)).image u)ᶜ =
      (Finset.univ : Finset (ZMod 8)).image v)
    (hreg : ∀ x, R.degree x = 6) (hcard : Fintype.card V = 16) :
    let U := (Finset.univ : Finset (ZMod 8)).image u
    (shoreTypeEdgeFinset R U 2).card = 12 ∧
      (shoreTypeEdgeFinset R U 1).card = 24 ∧
      (shoreTypeEdgeFinset R U 0).card = 12 := by
  classical
  dsimp only
  let U := (Finset.univ : Finset (ZMod 8)).image u
  let W := (Finset.univ : Finset (ZMod 8)).image v
  change (shoreTypeEdgeFinset R U 2).card = 12 ∧
    (shoreTypeEdgeFinset R U 1).card = 24 ∧
    (shoreTypeEdgeFinset R U 0).card = 12
  have hx := h305_correctShoreMode_typeTwo_card_twelve R u huinj humode
  have hw := h305_correctShoreMode_typeTwo_card_twelve R v hvinj hvmode
  have hx' : (shoreTypeEdgeFinset R U 2).card = 12 := by
    simpa [U] using hx
  have hz : (shoreTypeEdgeFinset R U 0).card = 12 := by
    rw [shoreTypeEdgeFinset_zero_eq_two_compl R U, hpartition]
    exact hw
  have hsum := shoreTypeEdgeFinset_card_sum R U
  have hedge := edgeFinset_card_eq_fortyEight_of_sixRegular_sixteen
    R hreg hcard
  refine ⟨hx', ?_, hz⟩
  omega

/-- Two disjoint labeled C8 shores covering the vertex type are finset
complements. -/
theorem h305_shoreImages_compl_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (u v : ZMod 8 → V)
    (hdisj : ∀ i j, u i ≠ v j)
    (hcover : ∀ x : V, (∃ i, x = u i) ∨ ∃ j, x = v j) :
    ((Finset.univ : Finset (ZMod 8)).image u)ᶜ =
      (Finset.univ : Finset (ZMod 8)).image v := by
  classical
  ext x
  constructor
  · intro hx
    have hxnot : x ∉ (Finset.univ : Finset (ZMod 8)).image u :=
      Finset.mem_compl.mp hx
    rcases hcover x with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · exact False.elim (hxnot (Finset.mem_image.mpr
        ⟨i, Finset.mem_univ _, rfl⟩))
    · exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  · intro hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    apply Finset.mem_compl.mpr
    intro hv
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hv
    exact hdisj i j hi

/-- Cardinality consequence of the two-shore coordinate cover. -/
theorem h305_card_eq_sixteen_of_shoreCoordinates
    {V : Type*} [Fintype V] [DecidableEq V]
    (u v : ZMod 8 → V)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hdisj : ∀ i j, u i ≠ v j)
    (hcover : ∀ x : V, (∃ i, x = u i) ∨ ∃ j, x = v j) :
    Fintype.card V = 16 := by
  classical
  let U := (Finset.univ : Finset (ZMod 8)).image u
  let W := (Finset.univ : Finset (ZMod 8)).image v
  have hU : U.card = 8 := by
    rw [Finset.card_image_of_injective _ huinj]
    decide
  have hW : W.card = 8 := by
    rw [Finset.card_image_of_injective _ hvinj]
    decide
  have hcomp : Uᶜ = W := h305_shoreImages_compl_eq u v hdisj hcover
  have hc := Finset.card_compl U
  rw [hcomp, hW, hU] at hc
  have hle : 8 ≤ Fintype.card V := by
    rw [← hU]
    exact Finset.card_le_univ U
  omega

/-- Coordinate-native version of the full population census. -/
theorem h305_correctShoreModes_typePopulations_of_coordinates
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u v : ZMod 8 → V)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hdisj : ∀ i j, u i ≠ v j)
    (hcover : ∀ x : V, (∃ i, x = u i) ∨ ∃ j, x = v j)
    (humode : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u)
    (hvmode : MuNegThreeZeroFiveTriangleShoreMode R v ∨
      MuNegThreeZeroFiveTfShoreMode R v)
    (hreg : ∀ x, R.degree x = 6) :
    let U := (Finset.univ : Finset (ZMod 8)).image u
    (shoreTypeEdgeFinset R U 2).card = 12 ∧
      (shoreTypeEdgeFinset R U 1).card = 24 ∧
      (shoreTypeEdgeFinset R U 0).card = 12 := by
  exact h305_correctShoreModes_typePopulations R u v huinj hvinj
    humode hvmode (h305_shoreImages_compl_eq u v hdisj hcover) hreg
      (h305_card_eq_sixteen_of_shoreCoordinates
        u v huinj hvinj hdisj hcover)

end

end Erdos85

#print axioms Erdos85.shoreTypeEdgeFinset_two_map_eq_inter
#print axioms Erdos85.shoreTypeEdgeFinset_two_card_eq_inter
#print axioms Erdos85.shoreTypeEdgeFinset_two_card_eq_twelve_of_internal_three
#print axioms Erdos85.h305_correctShoreMode_typeTwo_card_twelve
#print axioms Erdos85.shoreTypeEdgeFinset_card_sum
#print axioms Erdos85.shoreTypeEdgeFinset_zero_eq_two_compl
#print axioms Erdos85.edgeFinset_card_eq_fortyEight_of_sixRegular_sixteen
#print axioms Erdos85.h305_correctShoreModes_typePopulations
#print axioms Erdos85.h305_shoreImages_compl_eq
#print axioms Erdos85.h305_card_eq_sixteen_of_shoreCoordinates
#print axioms Erdos85.h305_correctShoreModes_typePopulations_of_coordinates
