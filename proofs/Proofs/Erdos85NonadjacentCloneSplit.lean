import Proofs.Erdos85ManufacturedDefectClique
import Proofs.Erdos85DeleteGadget
import Proofs.Erdos85DistanceLayers

/-!
# Splitting a high-degree vertex into two nonadjacent clones

Unlike an adjacent split, a nonadjacent split imposes no condition on edges
crossing the two parts of the old neighbourhood.  Thus a vertex of degree at
least `2*d` can be replaced by two nonadjacent vertices of degree at least
`d`, raising the order by one while preserving `C₄`-freeness and minimum
degree `d`.
-/

open SimpleGraph

namespace Erdos85

/-- Pointwise version of the local-matching observation: every vertex in an
induced neighbourhood has degree at most one. -/
theorem degree_induce_neighborSet_le_one_of_not_containsC4
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (x : V)
    (y : {z : V // z ∈ G.neighborSet x}) :
    (G.induce (G.neighborSet x)).degree y ≤ 1 := by
  rw [degree_induce_neighborSet_eq_card_common]
  exact common_le_one_of_not_containsC4 hfree x y.1 (G.ne_of_adj y.2)

/-- A subset of the surviving neighbours of `x` meets the surviving
neighbourhood of any other vertex in at most one point. -/
theorem card_neighbor_inter_subset_survivingNeighbor_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (x : V)
    (R : Finset {v : V // v ∉ ({x} : Finset V)})
    (hR : R ⊆ survivingNeighborSelector G {x} x)
    (a : {v : V // v ∉ ({x} : Finset V)}) :
    ((deleteVertexSetGraph G {x}).neighborFinset a ∩ R).card ≤ 1 := by
  classical
  let e : {v : V // v ∉ ({x} : Finset V)} ↪ V :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hsub : (((deleteVertexSetGraph G {x}).neighborFinset a ∩ R).map e) ⊆
      G.neighborFinset a.1 ∩ G.neighborFinset x := by
    intro z hz
    rw [Finset.mem_map] at hz
    obtain ⟨v, hv, rfl⟩ := hz
    rw [Finset.mem_inter] at hv ⊢
    rw [mem_neighborFinset, mem_neighborFinset]
    constructor
    · have hvadj := ((deleteVertexSetGraph G {x}).mem_neighborFinset a v).mp hv.1
      dsimp [e]
      simpa only [deleteVertexSetGraph, SimpleGraph.induce_adj,
        Function.Embedding.coe_subtype] using hvadj
    · dsimp [e]
      exact (mem_survivingNeighborSelector G {x} x v).mp (hR hv.2)
  rw [← Finset.card_map e]
  exact (Finset.card_le_card hsub).trans
    (common_le_one_of_not_containsC4 hfree a.1 x (by simpa using a.2))

/-- Two disjoint parts of a deleted vertex's surviving neighbourhood are
compatible selectors for two *nonadjacent* new vertices. -/
theorem nonadjacentCloneSelectors_gadgetCompatible
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (x : V)
    (S T : Finset {v : V // v ∉ ({x} : Finset V)})
    (hS : S ⊆ survivingNeighborSelector G {x} x)
    (hT : T ⊆ survivingNeighborSelector G {x} x)
    (hdisj : Disjoint S T) :
    GadgetAttachmentCompatible (deleteVertexSetGraph G {x})
      (⊥ : SimpleGraph Bool) (fun b => if b then T else S) := by
  classical
  let A : Bool → Finset {v : V // v ∉ ({x} : Finset V)} :=
    fun b => if b then T else S
  change GadgetAttachmentCompatible (deleteVertexSetGraph G {x})
    (⊥ : SimpleGraph Bool) A
  have hsafeFull := commonNeighborIndependent_survivingNeighborSelector
    G {x} x (by simp) hfree
  have hsafeS : CommonNeighborIndependent (deleteVertexSetGraph G {x}) S := by
    intro a ha b hb hab
    exact hsafeFull (hS ha) (hS hb) hab
  have hsafeT : CommonNeighborIndependent (deleteVertexSetGraph G {x}) T := by
    intro a ha b hb hab
    exact hsafeFull (hT ha) (hT hb) hab
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    have hcommon :
        ((deleteVertexSetGraph G {x}).neighborFinset a ∩
          (deleteVertexSetGraph G {x}).neighborFinset b).card ≤ 1 :=
      (not_containsC4_iff_forall_common_le_one
        (deleteVertexSetGraph G {x})).mp (by
          intro hC4
          rcases hC4 with ⟨f, hf, hadj⟩
          exact hfree ⟨fun i => (f i).1, Subtype.val_injective.comp hf,
            fun i j hij => hadj i j hij⟩) a b hab
    have hindices :
        (Finset.univ.filter fun w : Bool => a ∈ A w ∧ b ∈ A w).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro u hu w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hw
      cases u <;> cases w
      · rfl
      · exact False.elim ((Finset.disjoint_left.mp hdisj) hu.1 hw.1)
      · exact False.elim ((Finset.disjoint_left.mp hdisj) hw.1 hu.1)
      · rfl
    by_cases hpos : 1 ≤
        (Finset.univ.filter fun w : Bool => a ∈ A w ∧ b ∈ A w).card
    · rw [Finset.one_le_card] at hpos
      obtain ⟨w, hw⟩ := hpos
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      cases w
      · have hz := hsafeS hw.1 hw.2 hab
        omega
      · have hz := hsafeT hw.1 hw.2 hab
        omega
    · omega
  · intro u w huw
    have hST : (S ∩ T).card = 0 := by
      rw [Finset.card_eq_zero]
      exact Finset.disjoint_iff_inter_eq_empty.mp hdisj
    have hTS : (T ∩ S).card = 0 := by
      rw [Finset.inter_comm]
      exact hST
    cases u <;> cases w <;> simp_all [A]
  · intro a w
    have hcapS := card_neighbor_inter_subset_survivingNeighbor_le_one
      G hfree x S hS a
    have hcapT := card_neighbor_inter_subset_survivingNeighbor_le_one
      G hfree x T hT a
    cases w with
    | false => simpa [A] using hcapS
    | true => simpa [A] using hcapT

/-- A finite set of size at least `2*d` admits a disjoint two-part cover with
both parts of size at least `d`. -/
theorem exists_disjoint_cover_card_ge_of_two_mul_le_card
    {X : Type*} [DecidableEq X] (N : Finset X) {d : ℕ}
    (hcard : 2 * d ≤ N.card) :
    ∃ S T : Finset X, S ⊆ N ∧ T ⊆ N ∧ Disjoint S T ∧
      S ∪ T = N ∧ d ≤ S.card ∧ d ≤ T.card := by
  obtain ⟨S, hSN, hScard⟩ := Finset.exists_subset_card_eq
    (show d ≤ N.card by omega)
  refine ⟨S, N \ S, hSN, Finset.sdiff_subset, Finset.disjoint_sdiff,
    Finset.union_sdiff_of_subset hSN, ?_, ?_⟩
  · omega
  · rw [Finset.card_sdiff_of_subset hSN, hScard]
    omega

/-- **Nonadjacent-clone split.**  If a `C₄`-free minimum-degree-`d` graph
has a vertex of degree at least `2*d`, splitting that vertex into two
nonadjacent clones produces a witness one order larger with the same minimum
degree. -/
theorem c4FreeMinDegreeWitness_succ_of_vertex_degree_ge_two_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    {N d : ℕ} (hVcard : Fintype.card V = N)
    (hmin : d ≤ G.minDegree) (hfree : ¬ containsC4 V G)
    (hxdegree : 2 * d ≤ G.degree x) :
    C4FreeMinDegreeWitness (N + 1) d := by
  classical
  let R : Finset {v : V // v ∉ ({x} : Finset V)} :=
    survivingNeighborSelector G {x} x
  have hRcard : R.card = G.degree x := by
    rw [← G.card_neighborFinset_eq_degree x]
    let e : {v : V // v ∉ ({x} : Finset V)} ↪ V :=
      ⟨Subtype.val, Subtype.val_injective⟩
    rw [← Finset.card_map e]
    congr 1
    ext z
    constructor
    · intro hz
      rw [Finset.mem_map] at hz
      obtain ⟨v, hv, rfl⟩ := hz
      change v ∈ survivingNeighborSelector G {x} x at hv
      exact (G.mem_neighborFinset x v.1).2
        ((mem_survivingNeighborSelector G {x} x v).1 hv)
    · intro hz
      rw [mem_neighborFinset] at hz
      rw [Finset.mem_map]
      let v : {v : V // v ∉ ({x} : Finset V)} :=
        ⟨z, by simpa using (G.ne_of_adj hz).symm⟩
      refine ⟨v, ?_, rfl⟩
      change v ∈ survivingNeighborSelector G {x} x
      exact (mem_survivingNeighborSelector G {x} x v).2 hz
  obtain ⟨S, T, hS, hT, hdisj, hcover, hScard, hTcard⟩ :=
    exists_disjoint_cover_card_ge_of_two_mul_le_card R (d := d) (by omega)
  let A : Bool → Finset {v : V // v ∉ ({x} : Finset V)} :=
    fun b => if b then T else S
  apply c4FreeMinDegreeWitness_succ_of_delete_set_add_gadget
    (N := N) (k := 1) (d := d)
    G {x} (⊥ : SimpleGraph Bool) A hVcard (by simp) (by decide)
  · exact nonadjacentCloneSelectors_gadgetCompatible
      G hfree x S T hS hT hdisj
  · intro v
    have hvdeg := hmin.trans (G.minDegree_le_degree v.1)
    by_cases hvx : G.Adj v.1 x
    · have hvR : v ∈ R := by
        exact (mem_survivingNeighborSelector G {x} x v).2 hvx.symm
      have hvST := Finset.mem_union.mp (hcover.symm ▸ hvR)
      cases hvST with
      | inl hvS =>
          have hatt : 1 ≤ (Finset.univ.filter fun w : Bool => v ∈ A w).card := by
            rw [Finset.one_le_card]
            exact ⟨false, by simp [A, hvS]⟩
          have hloss : (G.neighborFinset v.1 ∩ ({x} : Finset V)).card = 1 := by
            simp [hvx]
          rw [hloss]
          omega
      | inr hvT =>
          have hatt : 1 ≤ (Finset.univ.filter fun w : Bool => v ∈ A w).card := by
            rw [Finset.one_le_card]
            exact ⟨true, by simp [A, hvT]⟩
          have hloss : (G.neighborFinset v.1 ∩ ({x} : Finset V)).card = 1 := by
            simp [hvx]
          rw [hloss]
          omega
    · have hloss : (G.neighborFinset v.1 ∩ ({x} : Finset V)).card = 0 := by
          simp [hvx]
      rw [hloss, Nat.add_zero]
      exact hvdeg.trans (Nat.le_add_right _ _)
  · intro w
    cases w with
    | false => simpa [A] using hScard
    | true => simpa [A] using hTcard

end Erdos85
