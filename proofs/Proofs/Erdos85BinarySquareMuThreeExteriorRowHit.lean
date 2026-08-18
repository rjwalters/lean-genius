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

/-- Two signed entries with total `2` are both positive. -/
theorem signedPair_sum_two_positiveCard
    {α : Type*} [DecidableEq α] (T : Finset α) (s : α → ℤ)
    (hcard : T.card = 2)
    (hsign : ∀ x ∈ T, s x = -1 ∨ s x = 1)
    (hsum : ∑ x ∈ T, s x = 2) :
    (T.filter fun x => s x = 1).card = 2 := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
  have ha := hsign a (by simp)
  have hb := hsign b (by simp)
  have hab' : a ∉ ({b} : Finset α) := by simpa using hab
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · rw [Finset.sum_insert hab', Finset.sum_singleton, ha, hb] at hsum
    omega
  · rw [Finset.sum_insert hab', Finset.sum_singleton, ha, hb] at hsum
    omega
  · rw [Finset.sum_insert hab', Finset.sum_singleton, ha, hb] at hsum
    omega
  · have heq : ({a, b} : Finset α).filter (fun x => s x = 1) = {a, b} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · exact fun h => h.1
      · intro h
        rcases h with rfl | rfl <;> simp [ha, hb]
    rw [heq]
    simp [hab]

/-- A negative vertex of the signed size-two component has exactly two
positive neighbours inside that component.  This is the two-row forbidden
set used by the exact row-hit theorem. -/
theorem orderSixtyFour_signedSizeTwo_negative_positiveNeighborCard_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcardV : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hA_in : ∀ x, x ∈ c.supp →
      (G.adjMatrix ℤ).mulVec s x = -2 * s x)
    (x : V) (hxc : x ∈ c.supp) (hsx : s x = -1) :
    (Finset.univ.filter fun p : {z : V // z ∈ c.supp ∧ s z = 1} =>
      G.Adj p.1 x).card = 2 := by
  classical
  let T := componentNeighborFinset G (secondOrderDefectGraph G) c x
  have hTcard : T.card = 2 := by
    have h := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
      G hfree (q := 8) (by norm_num) hreg hcardV c c
      (x := x) hxc
    rw [hc] at h
    change 8 * T.card = 8 * 2 at h
    omega
  have hTsign : ∀ y ∈ T, s y = -1 ∨ s y = 1 := by
    intro y hy
    exact hs_in y (by
      rw [ConnectedComponent.mem_supp_iff]
      exact (Finset.mem_filter.mp hy).2)
  have hxsum : ∑ y ∈ G.neighborFinset x, s y = 2 := by
    have h := hA_in x hxc
    rw [SimpleGraph.adjMatrix_mulVec_apply, hsx] at h
    norm_num at h
    exact h
  have hTsum : ∑ y ∈ T, s y = 2 := by
    calc
      ∑ y ∈ T, s y = ∑ y ∈ G.neighborFinset x, s y := by
        change (∑ y ∈ (G.neighborFinset x).filter
          (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c), s y) = _
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro y hy
        by_cases hyc : (secondOrderDefectGraph G).connectedComponentMk y = c
        · simp [hyc]
        · have hyn : y ∉ c.supp := by
            rw [ConnectedComponent.mem_supp_iff]
            exact hyc
          simp [hyc, hs_out y hyn]
      _ = 2 := hxsum
  have hpos := signedPair_sum_two_positiveCard T s hTcard hTsign hTsum
  let A := Finset.univ.filter fun p : {z : V // z ∈ c.supp ∧ s z = 1} =>
    G.Adj p.1 x
  have heq : A.attach.image (fun p => p.1.1) = T.filter fun y => s y = 1 := by
    ext y
    simp [A, T, componentNeighborFinset, ConnectedComponent.mem_supp_iff,
      SimpleGraph.mem_neighborFinset, G.adj_comm]
    tauto
  have hattach : A.attach.card = A.card := Finset.card_attach
  have hinj : Set.InjOn (fun p : {p // p ∈ A} => p.1.1) (A.attach : Set _) := by
    intro p hp q hq hpq
    apply Subtype.ext
    apply Subtype.ext
    exact hpq
  have himage : (A.attach.image fun p => p.1.1).card = A.card := by
    rw [Finset.card_image_iff.mpr hinj, hattach]
  rw [heq] at himage
  change A.card = 2
  omega

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

#print axioms Erdos85.signedPair_sum_two_positiveCard
#print axioms Erdos85.orderSixtyFour_signedSizeTwo_negative_positiveNeighborCard_two
#print axioms Erdos85.c4Free_exteriorGridLabel_positiveHit_image
