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

end

end Erdos85

#print axioms Erdos85.shoreTypeEdgeFinset_two_map_eq_inter
#print axioms Erdos85.shoreTypeEdgeFinset_two_card_eq_inter
#print axioms Erdos85.shoreTypeEdgeFinset_two_card_eq_twelve_of_internal_three
#print axioms Erdos85.h305_correctShoreMode_typeTwo_card_twelve
