import Proofs.Erdos85SizeTwoMuNegThreeSameSignExteriorOwners

/-! # Exterior incidence degrees at `mu = -3` -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- For each positive shore vertex, its neighbors among the 24 cross owners
are exactly its three normalized owners. -/
theorem MuNegThreeCrossOwnerNormalForm.positive_crossOwner_neighbors_eq_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2) (s : V → ℤ)
    (N : MuNegThreeCrossOwnerNormalForm G c s)
    (x : MuNegThreePositiveShore (secondOrderDefectGraph G) c s) :
    ((N.crossOwnerFinset G c s).filter fun z ↦ G.Adj x.1 z) =
      {N.o₀ x, N.oσ x, N.oτ x} ∧
    ((N.crossOwnerFinset G c s).filter fun z ↦ G.Adj x.1 z).card = 3 := by
  classical
  have howners := N.owner_maps_injective_disjoint G hfree hreg hcard c hc s
  have heq : ((N.crossOwnerFinset G c s).filter fun z ↦ G.Adj x.1 z) =
      {N.o₀ x, N.oσ x, N.oτ x} := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hzcross, hxz⟩
      obtain ⟨hzout, x', y, hx'z, hyz⟩ :=
        (N.mem_crossOwnerFinset_iff G hfree c s z).mp hzcross
      rcases (N.exhaust x y).mp
          ((orderSixtyFour_sizeTwo_muNegThree_cross_owner_rectangle
            G hfree c s x x y y z ⟨hxz, hyz⟩ ⟨hxz, hyz⟩).1) with hy | hy | hy
      · left
        exact (N.owner₀ x z).mp (by simpa [hy] using And.intro hxz hyz)
      · right; left
        exact (N.ownerσ x z).mp (by simpa [hy] using And.intro hxz hyz)
      · right; right
        exact (N.ownerτ x z).mp (by simpa [hy] using And.intro hxz hyz)
    · intro hz
      rcases hz with rfl | rfl | rfl
      · exact ⟨by simp [MuNegThreeCrossOwnerNormalForm.crossOwnerFinset],
          (N.owner₀ x (N.o₀ x)).2 rfl |>.1⟩
      · exact ⟨by simp [MuNegThreeCrossOwnerNormalForm.crossOwnerFinset],
          (N.ownerσ x (N.oσ x)).2 rfl |>.1⟩
      · exact ⟨by simp [MuNegThreeCrossOwnerNormalForm.crossOwnerFinset],
          (N.ownerτ x (N.oτ x)).2 rfl |>.1⟩
  have h01 : N.o₀ x ≠ N.oσ x := by
    intro h
    exact Finset.disjoint_left.mp howners.2.2.2.1
      (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)
      (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, h.symm⟩)
  have h02 : N.o₀ x ≠ N.oτ x := by
    intro h
    exact Finset.disjoint_left.mp howners.2.2.2.2.1
      (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)
      (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, h.symm⟩)
  have h12 : N.oσ x ≠ N.oτ x := by
    intro h
    exact Finset.disjoint_left.mp howners.2.2.2.2.2
      (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)
      (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, h.symm⟩)
  refine ⟨heq, ?_⟩
  rw [heq]
  exact Finset.card_eq_three.mpr
    ⟨N.o₀ x, N.oσ x, N.oτ x, h01, h02, h12, rfl⟩

/-- Every positive shore vertex is incident with exactly three vertices of
the positive-positive extreme owner fibre. -/
theorem MuNegThreeCrossOwnerNormalForm.positive_extreme_neighbors_card_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z,
        s y = (-3 : ℤ) * s z)
    (N : MuNegThreeCrossOwnerNormalForm G c s)
    (hshore : Fintype.card
      (MuNegThreePositiveShore (secondOrderDefectGraph G) c s) = 8)
    (x : MuNegThreePositiveShore (secondOrderDefectGraph G) c s) :
    ((Finset.univ.filter fun z : V ↦
      (G.adjMatrix ℤ).mulVec s z + 2 * s z = 2).filter
        fun z ↦ G.Adj x.1 z).card = 3 := by
  classical
  let w := fun z => (G.adjMatrix ℤ).mulVec s z + 2 * s z
  let Sp := (Finset.univ : Finset V).filter fun z ↦ w z = 2
  let Sm := (Finset.univ : Finset V).filter fun z ↦ w z = -2
  let X := N.crossOwnerFinset G c s
  let E := componentExteriorFinset c
  let Rp := Sp.filter fun z ↦ G.Adj x.1 z
  let Rm := Sm.filter fun z ↦ G.Adj x.1 z
  let Rx := X.filter fun z ↦ G.Adj x.1 z
  let Re := E.filter fun z ↦ G.Adj x.1 z
  have hpartition :=
    orderSixtyFour_sizeTwo_muNegThree_extremeFibers_eq_sameSignOwnerHalf
      G hfree hreg hcard c hc s hs_out hs_in hH hD N hshore
  have hXsub : X ⊆ E := by
    intro z hz
    change z ∈ Finset.univ.filter (fun z ↦ z ∉ c.supp)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (N.mem_crossOwnerFinset_iff G hfree c s z).mp hz |>.1⟩
  have hE : E = (Sp ∪ Sm) ∪ X := by
    calc
      E = (E \ X) ∪ X := (Finset.sdiff_union_of_subset hXsub).symm
      _ = (Sp ∪ Sm) ∪ X := by rw [hpartition]
  have hRe : Re = (Rp ∪ Rm) ∪ Rx := by
    simp only [Re, Rp, Rm, Rx, ← Finset.filter_union, ← hE]
  have hdpm : Disjoint Sp Sm := by
    rw [Finset.disjoint_left]
    intro z hp hm
    have hp' := (Finset.mem_filter.mp hp).2
    have hm' := (Finset.mem_filter.mp hm).2
    omega
  have hdSX : Disjoint (Sp ∪ Sm) X := by
    rw [hpartition]
    rw [Finset.disjoint_left]
    intro z hzsd hzX
    exact (Finset.mem_sdiff.mp hzsd).2 hzX
  have hdrowsPM : Disjoint Rp Rm :=
    hdpm.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hdrowsX : Disjoint (Rp ∪ Rm) Rx := by
    apply hdSX.mono
    · exact Finset.union_subset_union
        (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    · exact Finset.filter_subset _ _
  have hReCard : Re.card = 6 := by
    have hout := orderSixtyFour_sizeTwoComponent_exteriorNeighborCard_six
      G hfree hreg hcard c hc ⟨x.1, x.2.1⟩
    have heq : Re = (G.neighborFinset x.1).filter
        (fun y => (secondOrderDefectGraph G).connectedComponentMk y ≠ c) := by
      ext z
      simp [Re, E, componentExteriorFinset, SimpleGraph.mem_neighborFinset,
        ConnectedComponent.mem_supp_iff, G.adj_comm, and_comm]
    rw [heq, hout]
  have hRxCard : Rx.card = 3 := by
    exact (N.positive_crossOwner_neighbors_eq_three
      G hfree hreg hcard c hc s x).2
  have hRmCard : Rm.card = 0 := by
    rw [Finset.card_eq_zero]
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨z, hz⟩
    let zm : MuNegThreeNegativeExteriorFiber G s :=
      ⟨z, (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2⟩
    have hneighbors :=
      orderSixtyFour_sizeTwo_muNegThree_extremeExteriorFiber_neighborProfile
        G hfree hreg hcard c hc s hs_out hs_in hH hD
    have hxmem : x ∈ ((Finset.univ : Finset
        (MuNegThreePositiveShore (secondOrderDefectGraph G) c s)).filter
          fun u ↦ G.Adj u.1 zm.1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2⟩
    have hempty := Finset.card_eq_zero.mp (hneighbors.2 zm).1
    rw [hempty] at hxmem
    simp at hxmem
  have hsum : Re.card = Rp.card + Rm.card + Rx.card := by
    rw [hRe, Finset.card_union_of_disjoint hdrowsX,
      Finset.card_union_of_disjoint hdrowsPM]
  change Rp.card = 3
  omega

end

end Erdos85

#print axioms Erdos85.MuNegThreeCrossOwnerNormalForm.positive_crossOwner_neighbors_eq_three
#print axioms Erdos85.MuNegThreeCrossOwnerNormalForm.positive_extreme_neighbors_card_three
