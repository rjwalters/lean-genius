import Proofs.Erdos85MuNegThreeZeroFiveProfileMultiplicityLedger
import Proofs.Erdos85MuNegThreeZeroFiveMiddleProfileParity
import Proofs.Erdos85MuNegThreeZeroFiveCrossServiceProfiles
import Proofs.Erdos85MuNegThreeZeroFiveShoreTypePopulations
import Proofs.Erdos85EdgeIndexedServiceTypeHandshake

/-! # Turning pointwise h305 service profiles into the multiplicity ledger -/

namespace Erdos85

open Finset SimpleGraph Matrix

noncomputable section

/-- Type two in a shore is type zero in the complementary shore. -/
theorem serviceNeighborShoreTypeCount_two_eq_zero_compl
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (a : R.edgeFinset) (S : Finset V) :
    serviceNeighborShoreTypeCount R Cedge a S 2 =
      serviceNeighborShoreTypeCount R Cedge a Sᶜ 0 := by
  rw [serviceNeighborShoreTypeCount_zero_eq_two_compl R Cedge a Sᶜ]
  simp

/-- Type one is unchanged when the shore is complemented. -/
theorem serviceNeighborShoreTypeCount_one_eq_one_compl
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (a : R.edgeFinset) (S : Finset V) :
    serviceNeighborShoreTypeCount R Cedge a S 1 =
      serviceNeighborShoreTypeCount R Cedge a Sᶜ 1 := by
  have hS := edgeIndexedService_shoreTypeCounts_sum R Cedge a S
  have hSc := edgeIndexedService_shoreTypeCounts_sum R Cedge a Sᶜ
  have h0 := serviceNeighborShoreTypeCount_zero_eq_two_compl R Cedge a S
  have h2 := serviceNeighborShoreTypeCount_two_eq_zero_compl R Cedge a S
  omega

/-- Every type-one edge has one labeled endpoint in each shore. -/
theorem h305_typeOneEdge_exists_cross_endpoints
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u v : ZMod 8 → V)
    (hcover : ∀ x : V, (∃ i, x = u i) ∨ ∃ j, x = v j)
    (a : R.edgeFinset)
    (ha : a ∈ shoreTypeEdgeFinset R
      ((Finset.univ : Finset (ZMod 8)).image u) 1) :
    ∃ i j : ZMod 8, a.1.toFinset = {u i, v j} := by
  classical
  rcases a with ⟨a, haR⟩
  induction a using Sym2.inductionOn with
  | _ x y =>
    let U := (Finset.univ : Finset (ZMod 8)).image u
    have hinter : (({x, y} : Finset V) ∩ U).card = 1 := by
      simpa [U, Sym2.toFinset_mk_eq] using (Finset.mem_filter.mp ha).2
    have hxy : x ≠ y := by
      intro h
      subst y
      exact R.loopless.irrefl x (R.mem_edgeFinset.mp haR)
    by_cases hx : x ∈ U <;> by_cases hy : y ∈ U
    · simp [hxy, hx, hy] at hinter
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      rcases hcover y with ⟨k, hyk⟩ | ⟨j, rfl⟩
      · exfalso
        apply hy
        exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hyk.symm⟩
      · exact ⟨i, j, Sym2.toFinset_mk_eq⟩
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
      rcases hcover x with ⟨k, hxk⟩ | ⟨j, rfl⟩
      · exfalso
        apply hx
        exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hxk.symm⟩
      · refine ⟨i, j, ?_⟩
        simp [Sym2.toFinset_mk_eq, Finset.pair_comm]
    · simp [hx, hy] at hinter

private theorem threeProfile_card_and_sum
    {α : Type*} [DecidableEq α] (s : Finset α) (tag value : α → ℕ)
    (w0 w1 w2 : ℕ)
    (h : ∀ a ∈ s, (tag a = 0 ∧ value a = w0) ∨
      (tag a = 1 ∧ value a = w1) ∨
      (tag a = 2 ∧ value a = w2)) :
    (s.filter fun a ↦ tag a = 0).card +
        (s.filter fun a ↦ tag a = 1).card +
        (s.filter fun a ↦ tag a = 2).card = s.card ∧
      ∑ a ∈ s, value a =
        w0 * (s.filter fun a ↦ tag a = 0).card +
        w1 * (s.filter fun a ↦ tag a = 1).card +
        w2 * (s.filter fun a ↦ tag a = 2).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hi := ih (fun b hb ↦ h b (Finset.mem_insert_of_mem hb))
      rcases h a (Finset.mem_insert_self a s) with h0 | h1 | h2
      · constructor
        · simp [Finset.filter_insert, ha, h0.1]
          omega
        · rw [Finset.sum_insert ha, h0.2, hi.2]
          simp [Finset.filter_insert, ha, h0.1]
          ring
      · constructor
        · simp [Finset.filter_insert, ha, h1.1]
          omega
        · rw [Finset.sum_insert ha, h1.2, hi.2]
          simp [Finset.filter_insert, ha, h1.1]
          ring
      · constructor
        · simp [Finset.filter_insert, ha, h2.1]
          omega
        · rw [Finset.sum_insert ha, h2.2, hi.2]
          simp [Finset.filter_insert, ha, h2.1]
          ring

private theorem fourProfile_card_and_sum
    {α : Type*} [DecidableEq α] (s : Finset α) (tag value : α → ℕ)
    (w0 w1 w2 w3 : ℕ)
    (h : ∀ a ∈ s, (tag a = 0 ∧ value a = w0) ∨
      (tag a = 1 ∧ value a = w1) ∨
      (tag a = 2 ∧ value a = w2) ∨
      (tag a = 3 ∧ value a = w3)) :
    (s.filter fun a ↦ tag a = 0).card +
        (s.filter fun a ↦ tag a = 1).card +
        (s.filter fun a ↦ tag a = 2).card +
        (s.filter fun a ↦ tag a = 3).card = s.card ∧
      ∑ a ∈ s, value a =
        w0 * (s.filter fun a ↦ tag a = 0).card +
        w1 * (s.filter fun a ↦ tag a = 1).card +
        w2 * (s.filter fun a ↦ tag a = 2).card +
        w3 * (s.filter fun a ↦ tag a = 3).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hi := ih (fun b hb ↦ h b (Finset.mem_insert_of_mem hb))
      rcases h a (Finset.mem_insert_self a s) with h0 | h1 | h2 | h3
      · constructor
        · simp [Finset.filter_insert, ha, h0.1]
          omega
        · rw [Finset.sum_insert ha, h0.2, hi.2]
          simp [Finset.filter_insert, ha, h0.1]
          ring
      · constructor
        · simp [Finset.filter_insert, ha, h1.1]
          omega
        · rw [Finset.sum_insert ha, h1.2, hi.2]
          simp [Finset.filter_insert, ha, h1.1]
          ring
      · constructor
        · simp [Finset.filter_insert, ha, h2.1]
          omega
        · rw [Finset.sum_insert ha, h2.2, hi.2]
          simp [Finset.filter_insert, ha, h2.1]
          ring
      · constructor
        · simp [Finset.filter_insert, ha, h3.1]
          omega
        · rw [Finset.sum_insert ha, h3.2, hi.2]
          simp [Finset.filter_insert, ha, h3.1]
          ring

/-- The generic assembly step behind the h305 profile ledger.  Its inputs
are exactly the three local profile classifications, the three undirected
transition handshakes, the `12/24/12` population census, and the two middle
profile parities. -/
noncomputable def h305_profileMultiplicityLedger_of_pointwise
    {α : Type*} [DecidableEq α]
    (E2 E1 E0 : Finset α) (c2 c1 c0 : α → ℕ)
    (hcard2 : E2.card = 12) (hcard1 : E1.card = 24)
    (hcard0 : E0.card = 12)
    (hp2 : ∀ a ∈ E2,
      (c2 a = 0 ∧ c1 a = 4 ∧ c0 a = 2) ∨
      (c2 a = 1 ∧ c1 a = 2 ∧ c0 a = 3) ∨
      (c2 a = 2 ∧ c1 a = 0 ∧ c0 a = 4))
    (hp1 : ∀ a ∈ E1,
      (c2 a = 0 ∧ c1 a = 6 ∧ c0 a = 0) ∨
      (c2 a = 1 ∧ c1 a = 4 ∧ c0 a = 1) ∨
      (c2 a = 2 ∧ c1 a = 2 ∧ c0 a = 2) ∨
      (c2 a = 3 ∧ c1 a = 0 ∧ c0 a = 3))
    (hp0 : ∀ a ∈ E0,
      (c0 a = 0 ∧ c1 a = 4 ∧ c2 a = 2) ∨
      (c0 a = 1 ∧ c1 a = 2 ∧ c2 a = 3) ∨
      (c0 a = 2 ∧ c1 a = 0 ∧ c2 a = 4))
    (h21 : (∑ a ∈ E2, c1 a) = ∑ a ∈ E1, c2 a)
    (h10 : (∑ a ∈ E1, c0 a) = ∑ a ∈ E0, c1 a)
    (h20 : (∑ a ∈ E2, c0 a) = ∑ a ∈ E0, c2 a)
    (heven2 : Even ((E2.filter fun a ↦ c2 a = 1).card : ℕ))
    (heven0 : Even ((E0.filter fun a ↦ c0 a = 1).card : ℕ)) :
    H305ProfileMultiplicityLedger := by
  let u0 := (E2.filter fun a ↦ c2 a = 0).card
  let u1 := (E2.filter fun a ↦ c2 a = 1).card
  let u2 := (E2.filter fun a ↦ c2 a = 2).card
  let y0 := (E1.filter fun a ↦ c2 a = 0).card
  let y1 := (E1.filter fun a ↦ c2 a = 1).card
  let y2 := (E1.filter fun a ↦ c2 a = 2).card
  let y3 := (E1.filter fun a ↦ c2 a = 3).card
  let v0 := (E0.filter fun a ↦ c0 a = 0).card
  let v1 := (E0.filter fun a ↦ c0 a = 1).card
  let v2 := (E0.filter fun a ↦ c0 a = 2).card
  have hu1 := threeProfile_card_and_sum E2 c2 c1 4 2 0 (by
    intro a ha
    rcases hp2 a ha with h | h | h
    · exact Or.inl ⟨h.1, h.2.1⟩
    · exact Or.inr (Or.inl ⟨h.1, h.2.1⟩)
    · exact Or.inr (Or.inr ⟨h.1, h.2.1⟩))
  have hu0 := threeProfile_card_and_sum E2 c2 c0 2 3 4 (by
    intro a ha
    rcases hp2 a ha with h | h | h
    · exact Or.inl ⟨h.1, h.2.2⟩
    · exact Or.inr (Or.inl ⟨h.1, h.2.2⟩)
    · exact Or.inr (Or.inr ⟨h.1, h.2.2⟩))
  have hy2 := fourProfile_card_and_sum E1 c2 c2 0 1 2 3 (by
    intro a ha
    rcases hp1 a ha with h | h | h | h
    · exact Or.inl ⟨h.1, h.1⟩
    · exact Or.inr (Or.inl ⟨h.1, h.1⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h.1, h.1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h.1, h.1⟩)))
  have hy0 := fourProfile_card_and_sum E1 c2 c0 0 1 2 3 (by
    intro a ha
    rcases hp1 a ha with h | h | h | h
    · exact Or.inl ⟨h.1, h.2.2⟩
    · exact Or.inr (Or.inl ⟨h.1, h.2.2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h.1, h.2.2⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h.1, h.2.2⟩)))
  have hv1 := threeProfile_card_and_sum E0 c0 c1 4 2 0 (by
    intro a ha
    rcases hp0 a ha with h | h | h
    · exact Or.inl ⟨h.1, h.2.1⟩
    · exact Or.inr (Or.inl ⟨h.1, h.2.1⟩)
    · exact Or.inr (Or.inr ⟨h.1, h.2.1⟩))
  have hv2 := threeProfile_card_and_sum E0 c0 c2 2 3 4 (by
    intro a ha
    rcases hp0 a ha with h | h | h
    · exact Or.inl ⟨h.1, h.2.2⟩
    · exact Or.inr (Or.inl ⟨h.1, h.2.2⟩)
    · exact Or.inr (Or.inr ⟨h.1, h.2.2⟩))
  refine {
    u0 := u0, u1 := u1, u2 := u2,
    y0 := y0, y1 := y1, y2 := y2, y3 := y3,
    v0 := v0, v1 := v1, v2 := v2
    u_total := ?_, y_total := ?_, v_total := ?_
    handshake_u_y := ?_, handshake_y_v := ?_, handshake_u_v := ?_
    u1_even := ?_, v1_even := ?_ }
  · simpa [u0, u1, u2, hcard2] using hu1.1
  · simpa [y0, y1, y2, y3, hcard1] using hy2.1
  · simpa [v0, v1, v2, hcard0] using hv1.1
  · dsimp [u0, u1, y1, y2, y3]
    have hs := hu1.2.symm.trans (h21.trans hy2.2)
    omega
  · dsimp [v0, v1, y1, y2, y3]
    have hs := hy0.2.symm.trans (h10.trans hv1.2)
    omega
  · dsimp [u0, u1, u2, v0, v1, v2]
    rw [← hu0.2, h20, hv2.2]
  · simpa [u1] using heven2
  · simpa [v1] using heven0

/-- The actual graph-facing h305 ledger: all ten multiplicities are the
corresponding filters of the three shore-type edge populations. -/
noncomputable def h305_graphProfileMultiplicityLedger
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hCreg : ∀ b, Cedge.degree b = 6)
    (u v : ZMod 8 → V)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (hv : ∀ z, H.neighborFinset (v z) = {v (z - 1), v (z + 1)})
    (hdisj : ∀ k l, u k ≠ v l)
    (hcover : ∀ x : V, (∃ k, x = u k) ∨ ∃ l, x = v l)
    (humode : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u)
    (hvmode : MuNegThreeZeroFiveTriangleShoreMode R v ∨
      MuNegThreeZeroFiveTfShoreMode R v)
    (hRreg : ∀ x, R.degree x = 6) :
    H305ProfileMultiplicityLedger := by
  classical
  let U : Finset V := Finset.univ.image u
  let W : Finset V := Finset.univ.image v
  let E2 := shoreTypeEdgeFinset R U 2
  let E1 := shoreTypeEdgeFinset R U 1
  let E0 := shoreTypeEdgeFinset R U 0
  let c2 := fun a ↦ serviceNeighborShoreTypeCount R Cedge a U 2
  let c1 := fun a ↦ serviceNeighborShoreTypeCount R Cedge a U 1
  let c0 := fun a ↦ serviceNeighborShoreTypeCount R Cedge a U 0
  have hpop := h305_correctShoreModes_typePopulations_of_coordinates
    R u v huinj hvinj hdisj hcover humode hvmode hRreg
  have hpart : Uᶜ = W := h305_shoreImages_compl_eq u v hdisj hcover
  have hdisj' : ∀ k l, v k ≠ u l := fun k l h ↦ hdisj l k h.symm
  have hcover' : ∀ x : V, (∃ k, x = v k) ∨ ∃ l, x = u l := by
    intro x
    rcases hcover x with h | h
    · exact Or.inr h
    · exact Or.inl h
  apply h305_profileMultiplicityLedger_of_pointwise E2 E1 E0 c2 c1 c0
  · simpa [E2, U] using hpop.1
  · simpa [E1, U] using hpop.2.1
  · simpa [E0, U] using hpop.2.2
  · intro a ha
    obtain ⟨i, j, haij, hoffset⟩ :=
      h305_typeTwoEdge_exists_coordinate_endpoints R u humode a (by
        simpa [E2, U] using ha)
    simpa [c2, c1, c0, U] using
      (h305_serviceNeighbor_shoreType_profiles H R Cedge hservice hCreg
        u v huinj hvinj hu hdisj hcover a i j haij hoffset)
  · intro a ha
    obtain ⟨i, j, haij⟩ :=
      h305_typeOneEdge_exists_cross_endpoints R u v hcover a (by
        simpa [E1, U] using ha)
    simpa [c2, c1, c0, U] using
      (h305_cross_serviceNeighbor_shoreType_profiles H R Cedge hservice
        hCreg u v huinj hvinj hu hv hdisj hcover a i j haij)
  · intro a ha
    have haW : a ∈ shoreTypeEdgeFinset R W 2 := by
      have ha0 : a ∈ shoreTypeEdgeFinset R U 0 := by
        simpa [E0] using ha
      rw [shoreTypeEdgeFinset_zero_eq_two_compl R U, hpart] at ha0
      exact ha0
    obtain ⟨i, j, haij, hoffset⟩ :=
      h305_typeTwoEdge_exists_coordinate_endpoints R v hvmode a haW
    have hp := h305_serviceNeighbor_shoreType_profiles H R Cedge hservice
      hCreg v u hvinj huinj hv hdisj' hcover' a i j haij hoffset
    have hz : c0 a = serviceNeighborShoreTypeCount R Cedge a W 2 := by
      dsimp [c0]
      rw [serviceNeighborShoreTypeCount_zero_eq_two_compl, hpart]
    have ho : c1 a = serviceNeighborShoreTypeCount R Cedge a W 1 := by
      dsimp [c1]
      rw [serviceNeighborShoreTypeCount_one_eq_one_compl, hpart]
    have ht : c2 a = serviceNeighborShoreTypeCount R Cedge a W 0 := by
      dsimp [c2]
      rw [serviceNeighborShoreTypeCount_two_eq_zero_compl, hpart]
    rcases hp with hp | hp | hp
    · exact Or.inl ⟨hz.trans hp.1, ho.trans hp.2.1, ht.trans hp.2.2⟩
    · exact Or.inr (Or.inl
        ⟨hz.trans hp.1, ho.trans hp.2.1, ht.trans hp.2.2⟩)
    · exact Or.inr (Or.inr
        ⟨hz.trans hp.1, ho.trans hp.2.1, ht.trans hp.2.2⟩)
  · simpa [E2, E1, c1, c2] using
      (serviceNeighborShoreTypeCount_handshake R Cedge U 2 1)
  · simpa [E1, E0, c0, c1] using
      (serviceNeighborShoreTypeCount_handshake R Cedge U 1 0)
  · simpa [E2, E0, c0, c2] using
      (serviceNeighborShoreTypeCount_handshake R Cedge U 2 0)
  · simpa [E2, c2, U] using
      (h305_typeTwo_middleProfile_even H R Cedge hservice hCreg
        u v huinj hvinj hu hdisj hcover humode)
  · simpa [E0, c0, U] using
      (h305_typeZero_middleProfile_even H R Cedge hservice hCreg
        u v huinj hvinj hv hdisj hcover hvmode)

end

end Erdos85
