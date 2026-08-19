import Proofs.Erdos85BinarySquareSizeTwoSignedJointPackage

/-! # Signed internal structure at defect eigenvalue `-1` -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- At defect eigenvalue `-1`, a positive component vertex has three positive
and four negative defect neighbors. A negative vertex has the dual census. -/
theorem orderSixtyFour_sizeTwo_muNegOne_defectNeighborCensus_of_local
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
        s y = (-1 : ℤ) * s z) :
    ∀ x, x ∈ c.supp →
      (s x = 1 →
        (((secondOrderDefectGraph G).neighborFinset x).filter
          fun y ↦ s y = 1).card = 3 ∧
        (((secondOrderDefectGraph G).neighborFinset x).filter
          fun y ↦ s y = -1).card = 4) ∧
      (s x = -1 →
        (((secondOrderDefectGraph G).neighborFinset x).filter
          fun y ↦ s y = -1).card = 3 ∧
        (((secondOrderDefectGraph G).neighborFinset x).filter
          fun y ↦ s y = 1).card = 4) := by
  let D := secondOrderDefectGraph G
  have P := orderSixtyFour_sizeTwo_signedJoint_derived
    G hfree hreg hcard c hc s (-1) hs_out hs_in hH hD
  have hmem : ∀ x, x ∈ c.supp ↔ D.connectedComponentMk x = c :=
    fun x ↦ ConnectedComponent.mem_supp_iff c x
  have hclosed : ∀ x y, x ∈ c.supp → D.Adj x y → y ∈ c.supp := by
    intro x y hx hxy
    rw [hmem] at hx ⊢
    rw [← hx]
    exact (ConnectedComponent.connectedComponentMk_eq_of_adj hxy).symm
  intro x hx
  let T := D.neighborFinset x
  let Tp := T.filter fun y ↦ s y = 1
  let Tm := T.filter fun y ↦ s y = -1
  have hTcard : T.card = 7 := P.defectDegree x
  have hcover : T = Tp ∪ Tm := by
    ext y
    simp only [Finset.mem_union, Finset.mem_filter, Tp, Tm]
    constructor
    · intro hy
      have hyc := hclosed x y hx ((D.mem_neighborFinset x y).mp hy)
      rcases hs_in y hyc with hs | hs
      · exact Or.inr ⟨hy, hs⟩
      · exact Or.inl ⟨hy, hs⟩
    · rintro (hy | hy) <;> exact hy.1
  have hdisj : Disjoint Tp Tm := by
    rw [Finset.disjoint_left]
    intro y hp hm
    have hp' := (Finset.mem_filter.mp hp).2
    have hm' := (Finset.mem_filter.mp hm).2
    omega
  have hcards : Tp.card + Tm.card = 7 := by
    rw [← Finset.card_union_of_disjoint hdisj, ← hcover, hTcard]
  have hsum : (Tp.card : ℤ) - Tm.card = -1 * s x := by
    have hact := hD x hx
    change ∑ y ∈ T, s y = -1 * s x at hact
    rw [hcover, Finset.sum_union hdisj] at hact
    have hp : ∑ y ∈ Tp, s y = (Tp.card : ℤ) := by
      calc
        _ = ∑ _y ∈ Tp, (1 : ℤ) := Finset.sum_congr rfl
          (fun y hy ↦ (Finset.mem_filter.mp hy).2)
        _ = _ := by simp
    have hm : ∑ y ∈ Tm, s y = -(Tm.card : ℤ) := by
      calc
        _ = ∑ _y ∈ Tm, (-1 : ℤ) := Finset.sum_congr rfl
          (fun y hy ↦ (Finset.mem_filter.mp hy).2)
        _ = _ := by simp
    rw [hp, hm] at hact
    exact hact
  constructor
  · intro hs
    change Tp.card = 3 ∧ Tm.card = 4
    rw [hs] at hsum
    omega
  · intro hs
    change Tm.card = 3 ∧ Tp.card = 4
    rw [hs] at hsum
    omega

/-- Complete signed degree profile at `mu = -1`: the component has two
eight-vertex sign shores; ambient adjacency inside it is entirely across the
shores with degree two, while defect adjacency has degrees `3+4`. -/
theorem orderSixtyFour_sizeTwo_muNegOne_signed_internal_degreeProfile
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
        s y = (-1 : ℤ) * s z) :
    let Xp := Finset.univ.filter (fun x ↦ x ∈ c.supp ∧ s x = 1)
    let Xm := Finset.univ.filter (fun x ↦ x ∈ c.supp ∧ s x = -1)
    let C := fun x ↦ (G.neighborFinset x).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c)
    let D := secondOrderDefectGraph G
    Xp.card = 8 ∧ Xm.card = 8 ∧
    ∀ x, x ∈ c.supp →
      (s x = 1 →
        ((C x).filter fun y ↦ s y = 1).card = 0 ∧
        ((C x).filter fun y ↦ s y = -1).card = 2 ∧
        ((D.neighborFinset x).filter fun y ↦ s y = 1).card = 3 ∧
        ((D.neighborFinset x).filter fun y ↦ s y = -1).card = 4) ∧
      (s x = -1 →
        ((C x).filter fun y ↦ s y = -1).card = 0 ∧
        ((C x).filter fun y ↦ s y = 1).card = 2 ∧
        ((D.neighborFinset x).filter fun y ↦ s y = -1).card = 3 ∧
        ((D.neighborFinset x).filter fun y ↦ s y = 1).card = 4) := by
  dsimp only
  let D := secondOrderDefectGraph G
  let Xp := Finset.univ.filter (fun x ↦ x ∈ c.supp ∧ s x = 1)
  let Xm := Finset.univ.filter (fun x ↦ x ∈ c.supp ∧ s x = -1)
  have P := orderSixtyFour_sizeTwo_signedJoint_derived
    G hfree hreg hcard c hc s (-1) hs_out hs_in hH hD
  have hmem : ∀ x, x ∈ c.supp ↔ D.connectedComponentMk x = c :=
    fun x ↦ ConnectedComponent.mem_supp_iff c x
  have hsupportCard :
      (Finset.univ.filter fun x ↦ x ∈ c.supp).card = 16 := by
    calc
      _ = c.supp.toFinset.card := by
        congr
        ext x
        simp
      _ = c.supp.ncard := (Set.ncard_eq_toFinset_card' c.supp).symm
      _ = 16 := by omega
  have hpartition :
      (Finset.univ.filter fun x ↦ x ∈ c.supp) = Xp ∪ Xm := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Xp, Xm]
    constructor
    · intro hx
      rcases hs_in x hx with hs | hs
      · exact Or.inr ⟨hx, hs⟩
      · exact Or.inl ⟨hx, hs⟩
    · rintro (hx | hx) <;> exact hx.1
  have hdisj : Disjoint Xp Xm := by
    rw [Finset.disjoint_left]
    intro x hp hm
    have hp' := (Finset.mem_filter.mp hp).2.2
    have hm' := (Finset.mem_filter.mp hm).2.2
    omega
  have hcards : Xp.card + Xm.card = 16 := by
    rw [← Finset.card_union_of_disjoint hdisj, ← hpartition, hsupportCard]
  have hsignedCard : (Xp.card : ℤ) - Xm.card = 0 := by
    have hsum := P.componentSum_eq_zero
    have heq : Finset.univ.filter
        (fun x ↦ D.connectedComponentMk x = c) = Xp ∪ Xm := by
      rw [← hpartition]
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hmem x).symm
    rw [heq, Finset.sum_union hdisj] at hsum
    have hp : ∑ x ∈ Xp, s x = (Xp.card : ℤ) := by
      rw [Finset.sum_congr rfl (fun x hx ↦ (Finset.mem_filter.mp hx).2.2)]
      simp
    have hm : ∑ x ∈ Xm, s x = -(Xm.card : ℤ) := by
      rw [Finset.sum_congr rfl (fun x hx ↦ (Finset.mem_filter.mp hx).2.2)]
      simp
    rw [hp, hm] at hsum
    exact hsum
  have hshore : Xp.card = 8 ∧ Xm.card = 8 := by omega
  refine ⟨hshore.1, hshore.2, ?_⟩
  have hDcensus :=
    orderSixtyFour_sizeTwo_muNegOne_defectNeighborCensus_of_local
      G hfree hreg hcard c hc s hs_out hs_in hH hD
  intro x hx
  let C := (G.neighborFinset x).filter
    (fun y ↦ D.connectedComponentMk y = c)
  let Cp := C.filter fun y ↦ s y = 1
  let Cm := C.filter fun y ↦ s y = -1
  have hCcard : C.card = 2 := P.componentNeighborCard x
  have hCcover : C = Cp ∪ Cm := by
    ext y
    simp only [Finset.mem_union, Finset.mem_filter, Cp, Cm]
    constructor
    · intro hy
      have hyC : y ∈ C := hy
      have hyc : y ∈ c.supp :=
        (hmem y).mpr (Finset.mem_filter.mp hyC).2
      rcases hs_in y hyc with hs | hs
      · exact Or.inr ⟨hy, hs⟩
      · exact Or.inl ⟨hy, hs⟩
    · rintro (hy | hy) <;> exact hy.1
  have hCdisj : Disjoint Cp Cm := by
    rw [Finset.disjoint_left]
    intro y hp hm
    have hp' := (Finset.mem_filter.mp hp).2
    have hm' := (Finset.mem_filter.mp hm).2
    omega
  have hCcards : Cp.card + Cm.card = 2 := by
    rw [← Finset.card_union_of_disjoint hCdisj, ← hCcover, hCcard]
  have hCsum : (Cp.card : ℤ) - Cm.card = -2 * s x := by
    have hsum := hH x hx
    change ∑ y ∈ C, s y = -2 * s x at hsum
    rw [hCcover, Finset.sum_union hCdisj] at hsum
    have hp : ∑ y ∈ Cp, s y = (Cp.card : ℤ) := by
      calc
        _ = ∑ _y ∈ Cp, (1 : ℤ) := Finset.sum_congr rfl
          (fun y hy ↦ (Finset.mem_filter.mp hy).2)
        _ = _ := by simp
    have hm : ∑ y ∈ Cm, s y = -(Cm.card : ℤ) := by
      calc
        _ = ∑ _y ∈ Cm, (-1 : ℤ) := Finset.sum_congr rfl
          (fun y hy ↦ (Finset.mem_filter.mp hy).2)
        _ = _ := by simp
    rw [hp, hm] at hsum
    exact hsum
  constructor
  · intro hsx
    have hDcounts := (hDcensus x hx).1 hsx
    change Cp.card = 0 ∧ Cm.card = 2 ∧ _
    rw [hsx] at hCsum
    exact ⟨by omega, by omega, hDcounts.1, hDcounts.2⟩
  · intro hsx
    have hDcounts := (hDcensus x hx).2 hsx
    change Cm.card = 0 ∧ Cp.card = 2 ∧ _
    rw [hsx] at hCsum
    exact ⟨by omega, by omega, hDcounts.1, hDcounts.2⟩

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegOne_defectNeighborCensus_of_local
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegOne_signed_internal_degreeProfile
