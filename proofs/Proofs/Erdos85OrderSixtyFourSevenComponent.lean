import Proofs.Erdos85OrderSixtyFourPrincipalTrace

/-! # The seven-component defect partition at order 64 -/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem seven_part_partition_of_sixtyFour
    {C : Type*} [Fintype C] [DecidableEq C]
    (s : C → ℕ) (hcard : Fintype.card C = 7)
    (hlower : ∀ c, 8 ≤ s c) (hdiv : ∀ c, 8 ∣ s c)
    (hsum : (∑ c, s c) = 64) :
    ∃ c, s c = 16 ∧ ∀ e, e ≠ c → s e = 8 := by
  classical
  have hex : ∃ c, s c ≠ 8 := by
    by_contra h
    push_neg at h
    have hall : ∀ c, s c = 8 := h
    have : (∑ c, s c) = 56 := by simp [hall, hcard]
    omega
  obtain ⟨c, hcne⟩ := hex
  obtain ⟨k, hk⟩ := hdiv c
  have hc16 : 16 ≤ s c := by
    rw [hk] at hcne ⊢
    have := hlower c
    rw [hk] at this
    omega
  have hcmem : c ∈ (Finset.univ : Finset C) := Finset.mem_univ c
  have hrestLower : 48 ≤ ∑ e ∈ (Finset.univ.erase c), s e := by
    calc
      48 = ∑ _e ∈ (Finset.univ.erase c : Finset C), 8 := by
        simp [hcard]
      _ ≤ ∑ e ∈ (Finset.univ.erase c), s e := by
        exact Finset.sum_le_sum fun e _ => hlower e
  have hsplit : (∑ e ∈ (Finset.univ.erase c : Finset C), s e) + s c = 64 := by
    calc
      (∑ e ∈ (Finset.univ.erase c : Finset C), s e) + s c =
          ∑ e : C, s e := Finset.sum_erase_add _ _ hcmem
      _ = 64 := hsum
  have hc : s c = 16 := by omega
  refine ⟨c, hc, ?_⟩
  intro e hec
  have hemem : e ∈ (Finset.univ.erase c : Finset C) := by simp [hec]
  have hothersLower : 40 ≤
      ∑ z ∈ ((Finset.univ.erase c : Finset C).erase e), s z := by
    calc
      40 = ∑ _z ∈ ((Finset.univ.erase c : Finset C).erase e), 8 := by
        simp [hcard, hec]
      _ ≤ ∑ z ∈ ((Finset.univ.erase c : Finset C).erase e), s z := by
        exact Finset.sum_le_sum fun z _ => hlower z
  have herest :
      (∑ z ∈ ((Finset.univ.erase c : Finset C).erase e), s z) + s e = 48 := by
    have herase := Finset.sum_erase_add
      (Finset.univ.erase c : Finset C) s hemem
    have hrest : (∑ z ∈ (Finset.univ.erase c : Finset C), s z) = 48 := by
      omega
    exact herase.trans hrest
  exact Nat.le_antisymm (by omega) (hlower e)

/-- If the defect graph has seven components, their orders are exactly one
`16` and six `8`s. -/
theorem orderSixtyFour_seven_defect_components_partition
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 7) :
    ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16 ∧ ∀ e, e ≠ c → e.supp.ncard = 8 := by
  classical
  let D := secondOrderDefectGraph G
  apply seven_part_partition_of_sixtyFour
    (fun c : D.ConnectedComponent => c.supp.ncard) hcount
  · intro c
    apply Nat.le_of_dvd c.nonempty_supp.ncard_pos
    exact orderSixtyFour_eight_dvd_defect_component_order
      G hfree hmin hcover c
  · intro c
    exact orderSixtyFour_eight_dvd_defect_component_order
      G hfree hmin hcover c
  · calc
      (∑ c : D.ConnectedComponent, c.supp.ncard) =
          ∑ c : D.ConnectedComponent, Fintype.card c.supp := by
        apply Finset.sum_congr rfl
        intro c _
        simpa [Nat.card_eq_fintype_card] using
          (Nat.card_coe_set_eq c.supp).symm
      _ = Fintype.card (Σ c : D.ConnectedComponent, c.supp) :=
        Fintype.card_sigma.symm
      _ = Fintype.card (Fin 64) :=
        (Fintype.card_congr (vertexConnectedComponentEquiv D)).symm
      _ = 64 := by simp

end

end Erdos85
