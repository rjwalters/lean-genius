import Proofs.Erdos85SizeTwoMuNegThreeEightEightDiagonalSameShape
import Proofs.Erdos85EvenCycleOrientation

/-! # The cross same-sign matching in the `mu=-3`, `k=1` C8+C8 case -/

open Finset Matrix

namespace Erdos85

noncomputable section

/-- Masking a C8 intertwiner by equality of two alternating sign lines
preserves the cycle-intertwining recurrence. -/
theorem alternating_sameSign_mask_cycleIntertwine
    (M : Matrix (ZMod 8) (ZMod 8) ℤ)
    (f g : ZMod 8 → ℤ)
    (hinter : ∀ i j,
      M (i - 1) j + M (i + 1) j = M i (j + 1) + M i (j - 1))
    (hfflip : ∀ i, f (i + 1) = -f i)
    (hgflip : ∀ j, g (j + 1) = -g j) :
    let P : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ if f i = g j then M i j else 0
    ∀ i j,
      P (i - 1) j + P (i + 1) j = P i (j + 1) + P i (j - 1) := by
  dsimp only
  intro i j
  have hfplus : f (i + 1) = -f i := hfflip i
  have hfminus : f (i - 1) = -f i := by
    have h := hfflip (i - 1)
    have hi : (i - 1) + 1 = i := by ring
    rw [hi] at h
    omega
  have hgplus : g (j + 1) = -g j := hgflip j
  have hgminus : g (j - 1) = -g j := by
    have h := hgflip (j - 1)
    have hj : (j - 1) + 1 = j := by ring
    rw [hj] at h
    omega
  by_cases h : -f i = g j
  · have hLminus : f (i - 1) = g j := hfminus.trans h
    have hLplus : f (i + 1) = g j := hfplus.trans h
    have hRplus : f i = g (j + 1) := by rw [hgplus, ← h]; ring
    have hRminus : f i = g (j - 1) := by rw [hgminus, ← h]; ring
    simp only [if_pos hLminus, if_pos hLplus, if_pos hRplus, if_pos hRminus]
    exact hinter i j
  · have hLminus : f (i - 1) ≠ g j := by
      rw [hfminus]
      exact h
    have hLplus : f (i + 1) ≠ g j := by
      rw [hfplus]
      exact h
    have hRplus : f i ≠ g (j + 1) := by
      rw [hgplus]
      intro heq
      apply h
      linear_combination -heq
    have hRminus : f i ≠ g (j - 1) := by
      rw [hgminus]
      intro heq
      apply h
      linear_combination -heq
    simp [hLminus, hLplus, hRplus, hRminus]

/-- A binary C8 intertwiner with alternating row and column signs and one
same-sign entry in every row is an oriented perfect matching after masking. -/
theorem binary_C8Intertwiner_sameSign_rowOne_orientation
    (M : Matrix (ZMod 8) (ZMod 8) ℤ)
    (f g : ZMod 8 → ℤ)
    (hinter : ∀ i j,
      M (i - 1) j + M (i + 1) j = M i (j + 1) + M i (j - 1))
    (hbinary : ∀ i j, M i j = 0 ∨ M i j = 1)
    (hfflip : ∀ i, f (i + 1) = -f i)
    (hgflip : ∀ j, g (j + 1) = -g j)
    (hdegree : ∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        f i = g j ∧ M i j = 1).card = 1) :
    ∃ φ : ZMod 8 → ZMod 8,
      (∀ i j, (f i = g j ∧ M i j = 1) ↔ j = φ i) ∧
      ((∀ i, φ (i + 1) = φ i + 1) ∨
        (∀ i, φ (i + 1) = φ i - 1)) := by
  classical
  let P : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ if f i = g j then M i j else 0
  have hinterP := alternating_sameSign_mask_cycleIntertwine
    M f g hinter hfflip hgflip
  have hbinaryP : ∀ i j, P i j = 0 ∨ P i j = 1 := by
    intro i j
    dsimp [P]
    split
    · exact hbinary i j
    · exact Or.inl rfl
  have hone : ∀ i j, P i j = 1 ↔ f i = g j ∧ M i j = 1 := by
    intro i j
    dsimp [P]
    by_cases hsign : f i = g j
    · simp [hsign]
    · simp [hsign]
  have hrow : ∀ i, ∑ j, P i j = 1 := by
    intro i
    calc
      ∑ j, P i j = ∑ j, if P i j = 1 then (1 : ℤ) else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        rcases hbinaryP i j with hz | ho
        · simp [hz]
        · simp [ho]
      _ = (((Finset.univ : Finset (ZMod 8)).filter fun j ↦
          P i j = 1).card : ℤ) := by
        simpa only using (Finset.sum_boole (R := ℤ)
          (fun j : ZMod 8 ↦ P i j = 1) Finset.univ)
      _ = 1 := by
        rw [show ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
            P i j = 1) = ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
            f i = g j ∧ M i j = 1) by
          ext j; simp [hone]]
        exact_mod_cast hdegree i
  obtain ⟨φ, hφ, horient⟩ := binary_rowOne_cycleIntertwiner_orientation
    (r := 8) (by omega) P hinterP hbinaryP hrow
  refine ⟨φ, ?_, horient⟩
  intro i j
  rw [← hφ i j, hone i j]

/-- Coordinate-card transport with an arbitrary source vertex. -/
theorem coordinate_sameSign_adj_card_eq_support_from
    {X : Type*} [Fintype X] [DecidableEq X]
    (K : SimpleGraph X) [DecidableRel K.Adj]
    (B : Finset X) (v : ZMod 8 → X) (hvinj : Function.Injective v)
    (hvrange : Set.range v = ↑B) (s : X → ℤ) (x : X) :
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      s (v j) = s x ∧ K.Adj x (v j)).card =
    (B.filter fun y ↦ K.Adj x y ∧ s y = s x).card := by
  classical
  apply Finset.card_bij (fun j _ ↦ v j)
  · intro j hj
    have hj' := Finset.mem_filter.mp hj
    rw [Finset.mem_filter]
    refine ⟨?_, hj'.2.2, hj'.2.1⟩
    change v j ∈ (↑B : Set X)
    rw [← hvrange]
    exact ⟨j, rfl⟩
  · intro j₁ hj₁ j₂ hj₂ h
    exact hvinj h
  · intro y hy
    have hy' := Finset.mem_filter.mp hy
    have hyB : y ∈ (↑B : Set X) := hy'.1
    rw [← hvrange] at hyB
    obtain ⟨j, rfl⟩ := hyB
    refine ⟨j, ?_, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hy'.2.2, hy'.2.1⟩

set_option maxHeartbeats 1200000 in
/-- If one diagonal row has same-sign degree one in the normalized
`mu=-3` C8+C8 branch, then the cross same-sign block is an oriented perfect
matching. -/
theorem orderSixtyFour_sizeTwo_muNegThree_eightEight_crossSame_orientation_of_one
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
        s y = (-3 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (i₀ : ZMod 8)
    (hone :
      (((Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp).filter
        (fun y ↦ (secondOrderDefectGraph G).Adj (u i₀).1 y.1 ∧
          s y.1 = s (u i₀).1)).card = 1) :
    ∃ φ : ZMod 8 → ZMod 8,
      (∀ i j,
        (s (u i).1 = s (v j).1 ∧
          (secondOrderDefectGraph G).Adj (u i).1 (v j).1) ↔ j = φ i) ∧
      ((∀ i, φ (i + 1) = φ i + 1) ∨
        (∀ i, φ (i + 1) = φ i - 1)) := by
  classical
  let Hc := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
  let B := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ b.supp
  obtain ⟨k, hk, hA, _hB, hcrossA, _hcrossB⟩ :=
    orderSixtyFour_sizeTwo_muNegThree_eightEight_signedParameter
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
  have huiA : u i₀ ∈ A := by
    have h : u i₀ ∈ a.supp := by
      rw [← hurange]
      exact ⟨i₀, rfl⟩
    simpa [A] using h
  have hk1 : k = 1 := by
    have hi := hA (u i₀) huiA
    have hone' : (A.filter fun y ↦ K.Adj (u i₀) y ∧
        s y.1 = s (u i₀).1).card = 1 := by
      simpa [A, K] using hone
    rw [hone'] at hi
    omega
  have hvrangeB : Set.range v = ↑B := by
    rw [hvrange]
    ext x
    simp [B]
  have hdegree : ∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        s (u i).1 = s (v j).1 ∧ K.Adj (u i) (v j)).card = 1 := by
    intro i
    rw [show ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        s (u i).1 = s (v j).1 ∧ K.Adj (u i) (v j)) =
        ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
          s (v j).1 = s (u i).1 ∧ K.Adj (u i) (v j)) by
      ext j; simp [eq_comm]]
    rw [coordinate_sameSign_adj_card_eq_support_from K B v hvinj hvrangeB
      (fun x : c.supp ↦ s x.1) (u i)]
    have hui : u i ∈ A := by
      have h : u i ∈ a.supp := by
        rw [← hurange]
        exact ⟨i, rfl⟩
      simpa [A] using h
    simpa [B, K, hk1] using hcrossA (u i) hui
  have hcomm : K.adjMatrix ℤ * Hc.adjMatrix ℤ =
      Hc.adjMatrix ℤ * K.adjMatrix ℤ := by
    exact (adjMatrix_comm_secondOrderDefect_induce_component_of_regular
      G hfree hreg c).symm
  let M : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (v j)
  have hupair : ∀ z, u (z - 1) ≠ u (z + 1) := fun z ↦
    huinj.ne (zmod_sub_one_ne_add_one_of_three_le (by omega) z)
  have hvpair : ∀ z, v (z - 1) ≠ v (z + 1) := fun z ↦
    hvinj.ne (zmod_sub_one_ne_add_one_of_three_le (by omega) z)
  have hinter : ∀ i j,
      M (i - 1) j + M (i + 1) j = M i (j + 1) + M i (j - 1) := by
    simpa only [M] using entry_cycleIntertwine_of_adjMatrix_comm
      K Hc u v (1 : ZMod 8) (1 : ZMod 8) hcomm hu hv hupair hvpair
  have hbinary : ∀ i j, M i j = 0 ∨ M i j = 1 := by
    intro i j
    simp only [M, SimpleGraph.adjMatrix_apply]
    split <;> simp
  have hAfull := sizeTwo_internal_full_sum_of_filtered G c s hs_out hH
  have flip_of_coordinates
      (w : ZMod 8 → c.supp)
      (hw : ∀ z, Hc.neighborFinset (w z) = {w (z - 1), w (z + 1)}) :
      ∀ i, s (w (i + 1)).1 = -s (w i).1 := by
    intro i
    have hadj : Hc.Adj (w i) (w (i + 1)) := by
      rw [← Hc.mem_neighborFinset, hw]
      simp
    have hmem : (w (i + 1)).1 ∈ componentNeighborFinset G
        (secondOrderDefectGraph G) c (w i).1 := by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset _ _).mpr hadj, (w (i + 1)).2⟩
    exact (internal_alternation G hfree (by omega) hreg hcard c hc s
      hs_in hs_out hAfull (w i).2).2 _ hmem
  have hdegreeM : ∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        s (u i).1 = s (v j).1 ∧ M i j = 1).card = 1 := by
    intro i
    calc
      _ = ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
          s (u i).1 = s (v j).1 ∧ K.Adj (u i) (v j)).card := by
        congr 1
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        simp [M, SimpleGraph.adjMatrix_apply]
      _ = 1 := hdegree i
  obtain ⟨φ, hφ, horient⟩ := binary_C8Intertwiner_sameSign_rowOne_orientation
    M (fun i ↦ s (u i).1) (fun j ↦ s (v j).1) hinter hbinary
      (flip_of_coordinates u hu) (flip_of_coordinates v hv) hdegreeM
  refine ⟨φ, ?_, horient⟩
  intro i j
  simpa [M, K, SimpleGraph.adjMatrix_apply] using hφ i j

end

end Erdos85

#print axioms Erdos85.binary_C8Intertwiner_sameSign_rowOne_orientation
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_eightEight_crossSame_orientation_of_one
