import Proofs.Erdos85BinarySquareMuThreeExteriorRowHit

/-! # The partial-permutation code carried by an exterior neighbourhood

Two injective coordinate projections of one finite set canonically identify
their images.  Applied to a six-rook exterior neighbourhood, this is its
six-symbol permutation word.
-/

namespace Erdos85

noncomputable section

/-- Two injective coordinate maps on a finite set induce an equivalence of
their images, pairing precisely the two coordinates belonging to each source
element. -/
theorem finset_injectiveCoordinateImages_equiv
    {ι α β : Type*} [DecidableEq ι] [DecidableEq α] [DecidableEq β]
    (L : Finset ι) (r : ι → α) (c : ι → β)
    (hr : Set.InjOn r (L : Set ι))
    (hc : Set.InjOn c (L : Set ι)) :
    ∃ e : {x : α // x ∈ L.image r} ≃ {y : β // y ∈ L.image c},
      ∀ l (hl : l ∈ L),
        e ⟨r l, Finset.mem_image.mpr ⟨l, hl, rfl⟩⟩ =
          ⟨c l, Finset.mem_image.mpr ⟨l, hl, rfl⟩⟩ := by
  classical
  let R : {l : ι // l ∈ L} → {x : α // x ∈ L.image r} := fun l =>
    ⟨r l.1, Finset.mem_image.mpr ⟨l.1, l.2, rfl⟩⟩
  let C : {l : ι // l ∈ L} → {y : β // y ∈ L.image c} := fun l =>
    ⟨c l.1, Finset.mem_image.mpr ⟨l.1, l.2, rfl⟩⟩
  have hRinj : Function.Injective R := by
    intro x y hxy
    apply Subtype.ext
    apply hr x.2 y.2
    exact congrArg Subtype.val hxy
  have hRsurj : Function.Surjective R := by
    intro x
    obtain ⟨l, hl, hrl⟩ := Finset.mem_image.mp x.2
    refine ⟨⟨l, hl⟩, ?_⟩
    apply Subtype.ext
    exact hrl
  have hCinj : Function.Injective C := by
    intro x y hxy
    apply Subtype.ext
    apply hc x.2 y.2
    exact congrArg Subtype.val hxy
  have hCsurj : Function.Surjective C := by
    intro y
    obtain ⟨l, hl, hcl⟩ := Finset.mem_image.mp y.2
    refine ⟨⟨l, hl⟩, ?_⟩
    apply Subtype.ext
    exact hcl
  let eR : {l : ι // l ∈ L} ≃ {x : α // x ∈ L.image r} :=
    Equiv.ofBijective R ⟨hRinj, hRsurj⟩
  let eC : {l : ι // l ∈ L} ≃ {y : β // y ∈ L.image c} :=
    Equiv.ofBijective C ⟨hCinj, hCsurj⟩
  refine ⟨eR.symm.trans eC, ?_⟩
  intro l hl
  change eC (eR.symm ⟨r l, _⟩) = ⟨c l, _⟩
  have hR : eR ⟨l, hl⟩ = ⟨r l, Finset.mem_image.mpr ⟨l, hl, rfl⟩⟩ := rfl
  rw [← hR, eR.symm_apply_apply]
  rfl

/-- The equivalence above has the same cardinality as the source set.  In the
`mu = 3`, order-64 application this cardinality is six. -/
theorem finset_injectiveCoordinateImages_equiv_card
    {ι α β : Type*} [DecidableEq ι] [DecidableEq α] [DecidableEq β]
    (L : Finset ι) (r : ι → α) (c : ι → β)
    (hr : Set.InjOn r (L : Set ι))
    (hc : Set.InjOn c (L : Set ι)) :
    Fintype.card {x : α // x ∈ L.image r} = L.card ∧
      Fintype.card {y : β // y ∈ L.image c} = L.card := by
  constructor
  · rw [Fintype.card_coe]
    exact Finset.card_image_iff.mpr hr
  · rw [Fintype.card_coe]
    exact Finset.card_image_iff.mpr hc

/-- Every C4-free exterior grid neighbourhood carries a canonical partial
permutation from its hit positive coordinates to its hit negative coordinates.
The graph-theoretic rook law supplies both injections. -/
theorem c4Free_exteriorGridLabel_neighbor_partialPermutation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (d : (secondOrderDefectGraph G).ConnectedComponent)
    (s : V → ℤ)
    (label : {u : V // u ∉ d.supp} →
      {z : V // z ∈ d.supp ∧ s z = 1} ×
        {z : V // z ∈ d.supp ∧ s z = -1})
    (hadj : ∀ u, G.Adj u.1 (label u).1.1 ∧
      G.Adj u.1 (label u).2.1)
    (u : {u : V // u ∉ d.supp}) :
    let L := Finset.univ.filter fun v : {v : V // v ∉ d.supp} =>
      G.Adj u.1 v.1
    ∃ e : {x // x ∈ L.image fun v => (label v).1} ≃
        {y // y ∈ L.image fun v => (label v).2},
      ∀ v (hv : v ∈ L),
        e ⟨(label v).1, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩ =
          ⟨(label v).2, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩ := by
  classical
  let L := Finset.univ.filter fun v : {v : V // v ∉ d.supp} =>
    G.Adj u.1 v.1
  have hrook := c4Free_exteriorGridLabel_neighbor_coordinate_injective
    G hfree d s label hadj u
  have hr : Set.InjOn (fun v => (label v).1) (L : Set _) := by
    intro v hv w hw hvw
    let v' : {v : {v : V // v ∉ d.supp} // G.Adj u.1 (v : V)} :=
      ⟨v, (Finset.mem_filter.mp hv).2⟩
    let w' : {v : {v : V // v ∉ d.supp} // G.Adj u.1 (v : V)} :=
      ⟨w, (Finset.mem_filter.mp hw).2⟩
    exact congrArg (fun z => z.1) (hrook.1 hvw : v' = w')
  have hc : Set.InjOn (fun v => (label v).2) (L : Set _) := by
    intro v hv w hw hvw
    let v' : {v : {v : V // v ∉ d.supp} // G.Adj u.1 (v : V)} :=
      ⟨v, (Finset.mem_filter.mp hv).2⟩
    let w' : {v : {v : V // v ∉ d.supp} // G.Adj u.1 (v : V)} :=
      ⟨w, (Finset.mem_filter.mp hw).2⟩
    exact congrArg (fun z => z.1) (hrook.2 hvw : v' = w')
  exact finset_injectiveCoordinateImages_equiv L
    (fun v => (label v).1) (fun v => (label v).2) hr hc

end


end Erdos85

#print axioms Erdos85.finset_injectiveCoordinateImages_equiv
#print axioms Erdos85.finset_injectiveCoordinateImages_equiv_card
#print axioms Erdos85.c4Free_exteriorGridLabel_neighbor_partialPermutation
