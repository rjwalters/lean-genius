import Proofs.Erdos85SizeTwoMuNegOneEightEightDiagonalShapeConsumer
import Proofs.Erdos85SizeTwoMuNegOneEightEightParameterBoundsConsumer

/-! # The signed normal form of the `mu=-1` C8+C8 branch -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The apparent four diagonal shapes collapse to two: the `k=2` and `k=3`
shapes contain an offset-two defect edge, impossible because the intervening
C8 vertex is a common ambient neighbor. -/
theorem orderSixtyFour_sizeTwo_muNegOne_eightEight_signed_normalForm
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
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z,
        s y = (-1 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    ∃ k r : ℕ, k ≤ 1 ∧ 2 ≤ r ∧ r ≤ 7 ∧
      ((k = 0 ∧
        (∀ x ∈ (Finset.univ : Finset c.supp).filter (fun x ↦ x ∈ a.supp),
          (((Finset.univ : Finset c.supp).filter
              (fun x ↦ x ∈ b.supp)).filter
            (fun y ↦ ((secondOrderDefectGraph G).induce c.supp).Adj x y ∧
              s y.1 = s x.1)).card = 3) ∧
        (∀ x ∈ (Finset.univ : Finset c.supp).filter (fun x ↦ x ∈ b.supp),
          (((Finset.univ : Finset c.supp).filter
              (fun x ↦ x ∈ a.supp)).filter
            (fun y ↦ ((secondOrderDefectGraph G).induce c.supp).Adj x y ∧
              s y.1 = s x.1)).card = 3)) ∨
      (k = 1 ∧
        (∀ x ∈ (Finset.univ : Finset c.supp).filter (fun x ↦ x ∈ a.supp),
          (((Finset.univ : Finset c.supp).filter
              (fun x ↦ x ∈ b.supp)).filter
            (fun y ↦ ((secondOrderDefectGraph G).induce c.supp).Adj x y ∧
              s y.1 = s x.1)).card = 2) ∧
        (∀ x ∈ (Finset.univ : Finset c.supp).filter (fun x ↦ x ∈ b.supp),
          (((Finset.univ : Finset c.supp).filter
              (fun x ↦ x ∈ a.supp)).filter
            (fun y ↦ ((secondOrderDefectGraph G).induce c.supp).Adj x y ∧
              s y.1 = s x.1)).card = 2))) := by
  classical
  let Hc := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
  obtain ⟨_ha8, _hb8, r, hr2, hr7, _haa, _habq, _hbaq, _hbb⟩ :=
    orderSixtyFour_sizeTwo_muNegOne_distinctCycles_eightEight
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
  obtain ⟨k, _hk3, hA, _hB, hcrossA, hcrossB⟩ :=
    orderSixtyFour_sizeTwo_muNegOne_eightEight_signedParameter
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
  obtain ⟨k₂, _hk₂3, hshapeU, _hshapeV⟩ :=
    orderSixtyFour_sizeTwo_muNegOne_eightEight_diagonalSame_shapes
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
        u v huinj hvinj hurange hvrange hu hv
  have hAfull := sizeTwo_internal_full_sum_of_filtered G c s hs_out hH
  have hflip : ∀ i, s (u (i + 1)).1 = -(s (u i).1) := by
    intro i
    have hadj : Hc.Adj (u i) (u (i + 1)) := by
      rw [← Hc.mem_neighborFinset, hu]
      simp
    have hmem : (u (i + 1)).1 ∈ componentNeighborFinset G
        (secondOrderDefectGraph G) c (u i).1 := by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset _ _).mpr hadj, (u (i + 1)).2⟩
    exact (internal_alternation G hfree (by omega) hreg hcard c hc s
      hs_in hs_out hAfull (u i).2).2 _ hmem
  have hsign : ∀ i, s (u i).1 = -1 ∨ s (u i).1 = 1 :=
    fun i ↦ hs_in _ (u i).2
  have heven := zmodEight_alternating_sign_eq_iff_evenOffset
    (fun i ↦ s (u i).1) hsign hflip
  have hurangeA : Set.range u = ↑A := by
    rw [hurange]
    ext x
    simp [A]
  have hu0A : u 0 ∈ A := by
    change u 0 ∈ (↑A : Set c.supp)
    rw [← hurangeA]
    exact ⟨0, rfl⟩
  have hrow : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      s (u j).1 = s (u 0).1 ∧ K.Adj (u 0) (u j)).card = k := by
    rw [coordinate_sameSign_adj_card_eq_support K A u huinj hurangeA
      (fun x : c.supp ↦ s x.1) 0]
    exact hA (u 0) hu0A
  have hmid : ¬ K.Adj (u 0) (u 2) := by
    intro hadj
    have hDadj : (secondOrderDefectGraph G).Adj (u 0).1 (u 2).1 := hadj
    have h01 : Hc.Adj (u 0) (u 1) := by
      rw [← Hc.mem_neighborFinset, hu]
      norm_num
    have h21 : Hc.Adj (u 2) (u 1) := by
      rw [← Hc.mem_neighborFinset, hu]
      norm_num
    have hne : (u 0).1 ≠ (u 2).1 := by
      intro h
      exact (by decide : (0 : ZMod 8) ≠ 2) (huinj (Subtype.ext h))
    exact not_secondOrderDefect_adj_of_commonNeighbor G hfree hne
      h01 h21 hDadj
  rcases hshapeU with hsmall | ⟨hk₂3, hiff3⟩
  · rcases hsmall with ⟨hk₂0, hempty⟩ | ⟨hk₂1, hiff1⟩ | ⟨hk₂2, hiff2⟩
    · have hk0 : k = 0 := by
        rw [← hrow, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        rintro j - ⟨hfeq, hadj⟩
        exact hempty 0 j hfeq (by
          simp only [SimpleGraph.adjMatrix_apply]
          rw [if_pos hadj])
      refine ⟨0, r, by norm_num, hr2, hr7, Or.inl ⟨rfl, ?_, ?_⟩⟩
      · intro x hx
        simpa [hk0, K] using hcrossA x (by simpa [A] using hx)
      · intro x hx
        simpa [hk0, A, K] using hcrossB x (by simpa using hx)
    · have hk1 : k = 1 := by
        rw [← hrow]
        have hset : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
            s (u j).1 = s (u 0).1 ∧ K.Adj (u 0) (u j)) = {4} := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_singleton]
          constructor
          · rintro ⟨hfeq, hadj⟩
            have hM : (K.adjMatrix ℤ) (u 0) (u j) = 1 := by
              simp only [SimpleGraph.adjMatrix_apply]
              rw [if_pos hadj]
            simpa using (hiff1 0 j hfeq).mp hM
          · rintro rfl
            have hfeq : s (u 4).1 = s (u 0).1 :=
              (heven 0 4).mpr (by decide)
            have hM := (hiff1 0 4 hfeq).mpr (by decide)
            refine ⟨hfeq, ?_⟩
            by_contra h
            simp only [SimpleGraph.adjMatrix_apply] at hM
            rw [if_neg h] at hM
            norm_num at hM
        rw [hset, Finset.card_singleton]
      refine ⟨1, r, le_refl 1, hr2, hr7, Or.inr ⟨rfl, ?_, ?_⟩⟩
      · intro x hx
        simpa [hk1, K] using hcrossA x (by simpa [A] using hx)
      · intro x hx
        simpa [hk1, A, K] using hcrossB x (by simpa using hx)
    · exfalso
      have hfeq : s (u 2).1 = s (u 0).1 := (heven 0 2).mpr (by decide)
      have hM := (hiff2 0 2 hfeq).mpr (Or.inl (by decide))
      apply hmid
      by_contra h
      simp only [SimpleGraph.adjMatrix_apply] at hM
      rw [if_neg h] at hM
      norm_num at hM
  · exfalso
    have hfeq : s (u 2).1 = s (u 0).1 := (heven 0 2).mpr (by decide)
    have hM := (hiff3 0 2 hfeq).mpr (Or.inl (by decide))
    apply hmid
    by_contra h
    simp only [SimpleGraph.adjMatrix_apply] at hM
    rw [if_neg h] at hM
    norm_num at hM

end


end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegOne_eightEight_signed_normalForm
