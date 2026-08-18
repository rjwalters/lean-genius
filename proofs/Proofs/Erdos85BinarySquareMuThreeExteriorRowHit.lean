import Proofs.Erdos85BinarySquareMuThreeExteriorGridEmbedding

/-! # Exact row hits in the `mu = 3` exterior grid

The rook law gives an injection from the six exterior neighbours of a cell to
the eight positive coordinates.  A four-cycle excludes precisely the positive
coordinates adjacent to the cell's negative coordinate.  Once that forbidden
set has size two, counting upgrades the injection to an exact image formula.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The positive coordinates hit by the exterior neighbours of `u` are
exactly the positive coordinates not adjacent to the negative coordinate of
`u`.  This is the row half of the six-rook partial-permutation law. -/
theorem c4Free_exteriorGridLabel_positiveHit_image
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (s : V → ℤ)
    (label : {u : V // u ∉ c.supp} →
      {z : V // z ∈ c.supp ∧ s z = 1} ×
        {z : V // z ∈ c.supp ∧ s z = -1})
    (hadj : ∀ u, G.Adj u.1 (label u).1.1 ∧
      G.Adj u.1 (label u).2.1)
    (u : {u : V // u ∉ c.supp})
    (hout : (Finset.univ.filter fun v : {v : V // v ∉ c.supp} =>
      G.Adj u.1 v.1).card = 6)
    (hP : Fintype.card {z : V // z ∈ c.supp ∧ s z = 1} = 8)
    (hforbidden : (Finset.univ.filter fun p :
      {z : V // z ∈ c.supp ∧ s z = 1} =>
        G.Adj p.1 (label u).2.1).card = 2) :
    (Finset.univ.filter fun v : {v : V // v ∉ c.supp} =>
        G.Adj u.1 v.1).image (fun v => (label v).1) =
      Finset.univ.filter fun p : {z : V // z ∈ c.supp ∧ s z = 1} =>
        ¬ G.Adj p.1 (label u).2.1 := by
  classical
  let L := Finset.univ.filter fun v : {v : V // v ∉ c.supp} =>
    G.Adj u.1 v.1
  let A := Finset.univ.filter fun p :
    {z : V // z ∈ c.supp ∧ s z = 1} => G.Adj p.1 (label u).2.1
  let B := Finset.univ.filter fun p :
    {z : V // z ∈ c.supp ∧ s z = 1} => ¬ G.Adj p.1 (label u).2.1
  have hinj : Set.InjOn (fun v => (label v).1) (L : Set _) := by
    intro v hv w hw hvw
    have hrook :=
      (c4Free_exteriorGridLabel_neighbor_coordinate_injective
        G hfree c s label hadj u).1
    let v' : {v : {v : V // v ∉ c.supp} // G.Adj u.1 (v : V)} :=
      ⟨v, (Finset.mem_filter.mp hv).2⟩
    let w' : {v : {v : V // v ∉ c.supp} // G.Adj u.1 (v : V)} :=
      ⟨w, (Finset.mem_filter.mp hw).2⟩
    have hvw' : v' = w' := hrook hvw
    exact congrArg (fun z => z.1) hvw'
  have hsub : L.image (fun v => (label v).1) ⊆ B := by
    intro p hp
    obtain ⟨v, hvL, rfl⟩ := Finset.mem_image.mp hp
    have huv : G.Adj u.1 v.1 := (Finset.mem_filter.mp hvL).2
    have hvp : G.Adj v.1 (label v).1.1 := (hadj v).1
    have hun : G.Adj u.1 (label u).2.1 := (hadj u).2
    have hne : (label v).1.1 ≠ (label u).2.1 := by
      intro h
      have hs := (label v).1.2.2
      have ht := (label u).2.2.2
      rw [h] at hs
      omega
    have hnot : ¬ G.Adj (label v).1.1 (label u).2.1 := by
      intro hpn
      have hpu : (label v).1.1 ≠ u.1 := by
        intro h
        exact u.2 (h ▸ (label v).1.2.1)
      have hvn := c4Free_commonNeighborPair_injective G hfree hpu
        hvp.symm hpn huv hun
      exact v.2 (hvn ▸ (label u).2.2.1)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnot⟩
  have hLcard : L.card = 6 := hout
  have himage : (L.image fun v => (label v).1).card = 6 := by
    rw [Finset.card_image_iff.mpr hinj]
    exact hLcard
  have hAB : A.card + B.card = 8 := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset {z : V // z ∈ c.supp ∧ s z = 1}))
      (fun p => G.Adj p.1 (label u).2.1)
    change A.card + B.card = Fintype.card
      {z : V // z ∈ c.supp ∧ s z = 1} at h
    rw [hP] at h
    exact h
  have hBcard : B.card = 6 := by
    have hAcard : A.card = 2 := hforbidden
    omega
  exact Finset.eq_of_subset_of_card_le hsub (by rw [hBcard, himage])

end

end Erdos85

#print axioms Erdos85.c4Free_exteriorGridLabel_positiveHit_image
