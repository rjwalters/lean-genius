import Proofs.Erdos85BinarySquareSizeTwoJointEigenvectorMuOneExclusion
import Proofs.Erdos85SignedRegularEigenvalueRange

/-!
# Derived package for a signed size-two joint eigenline

The campaign repeatedly starts with the same local data on a normalized
size-two defect component: a vector is signed on the component, zero outside,
the internal ambient two-factor acts by `-2`, and the defect component acts by
an integer `mu`.  This file derives all global hypotheses needed by the energy
and support arguments once and for all.
-/

open SimpleGraph Matrix

namespace Erdos85

noncomputable section

structure SizeTwoSignedJointDerived
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (s : V → ℤ) (mu : ℤ) : Prop where
  defectDegree : ∀ x, (secondOrderDefectGraph G).degree x = 7
  componentNeighborCard : ∀ x, ((G.neighborFinset x).filter
    (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c)).card = 2
  componentSum_eq_zero : ∑ x ∈ Finset.univ.filter
    (fun x => (secondOrderDefectGraph G).connectedComponentMk x = c), s x = 0
  sum_eq_zero : ∑ x, s x = 0
  defectAction : ∀ x,
    ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y = mu * s x
  ambientAction_in : ∀ x, x ∈ c.supp →
    (G.adjMatrix ℤ).mulVec s x = -2 * s x
  ambientAction_out : ∀ x, x ∉ c.supp →
    (G.adjMatrix ℤ).mulVec s x = -2 ∨
    (G.adjMatrix ℤ).mulVec s x = 0 ∨
    (G.adjMatrix ℤ).mulVec s x = 2

/-- Derive the global signed-joint package from the standard local interface. -/
theorem orderSixtyFour_sizeTwo_signedJoint_derived
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
    (s : V → ℤ) (mu : ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c), s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y = mu * s z) :
    SizeTwoSignedJointDerived G c s mu := by
  have hmem : ∀ x, x ∈ c.supp ↔
      (secondOrderDefectGraph G).connectedComponentMk x = c :=
    fun x => ConnectedComponent.mem_supp_iff c x
  have hcensus : Fintype.card V = 8 * (8 - 1) + 3 + (8 - 3) := by
    rw [hcard]
  have hDdeg : ∀ x, (secondOrderDefectGraph G).degree x = 7 := by
    intro x
    have h := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcensus x
    omega
  have hDin : ∀ x y, x ∈ c.supp →
      (secondOrderDefectGraph G).Adj x y → y ∈ c.supp := by
    intro x y hx hxy
    rw [hmem] at hx ⊢
    rw [← hx]
    exact (ConnectedComponent.connectedComponentMk_eq_of_adj hxy).symm
  have hDout : ∀ x y, x ∉ c.supp →
      (secondOrderDefectGraph G).Adj x y → y ∉ c.supp := by
    intro x y hx hxy hy
    exact hx (hDin y x hy hxy.symm)
  have htwo : ∀ x, ((G.neighborFinset x).filter
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c)).card = 2 := by
    intro x
    have h := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
      G hfree (q := 8) (by norm_num) hreg hcard
      ((secondOrderDefectGraph G).connectedComponentMk x) c
      (x := x) ((ConnectedComponent.mem_supp_iff _ x).mpr rfl)
    rw [hc] at h
    change 8 * ((G.neighborFinset x).filter
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c)).card =
      8 * 2 at h
    omega
  let Sc : Finset V := Finset.univ.filter
    (fun x => (secondOrderDefectGraph G).connectedComponentMk x = c)
  have hSc_mem : ∀ x, x ∈ Sc ↔ x ∈ c.supp := by
    intro x
    simp only [Sc, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hmem x).symm
  have hfilt_eq : ∀ x, (G.neighborFinset x).filter
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c) =
      (G.neighborFinset x).filter (fun y => y ∈ Sc) := by
    intro x
    apply Finset.filter_congr
    intro y _
    simp only [Sc, Finset.mem_filter, Finset.mem_univ, true_and]
  have hsum_c : ∑ x ∈ Sc, s x = 0 := by
    have hcomm : ∑ x ∈ Sc,
        ∑ y ∈ (G.neighborFinset x).filter (fun y => y ∈ Sc), s y =
        ∑ y ∈ Sc,
        ∑ x ∈ (G.neighborFinset y).filter (fun x => x ∈ Sc), s y :=
      sum_sum_filter_neighborFinset_comm G Sc Sc (fun _ y => s y)
    have hl : ∑ x ∈ Sc,
        ∑ y ∈ (G.neighborFinset x).filter (fun y => y ∈ Sc), s y =
        -2 * ∑ x ∈ Sc, s x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [← hfilt_eq x]
      exact hH x ((hSc_mem x).mp hx)
    have hr : ∑ y ∈ Sc,
        ∑ x ∈ (G.neighborFinset y).filter (fun x => x ∈ Sc), s y =
        2 * ∑ y ∈ Sc, s y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_const, ← hfilt_eq y, htwo y, nsmul_eq_mul]
      norm_num
    rw [hl, hr] at hcomm
    linarith
  have hsum : ∑ x, s x = 0 := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun x => (secondOrderDefectGraph G).connectedComponentMk x = c)]
    have hout : ∑ x ∈ Finset.univ.filter
        (fun x => ¬ (secondOrderDefectGraph G).connectedComponentMk x = c), s x = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      exact hs_out x (fun h => (Finset.mem_filter.mp hx).2 ((hmem x).mp h))
    rw [hout, add_zero]
    exact hsum_c
  have hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      mu * s x := by
    intro x
    by_cases hx : x ∈ c.supp
    · exact hD x hx
    · rw [hs_out x hx]
      simp only [mul_zero]
      apply Finset.sum_eq_zero
      intro y hy
      exact hs_out y (hDout x y hx
        (((secondOrderDefectGraph G).mem_neighborFinset x y).mp hy))
  let a : V → ℤ := fun x => ∑ y ∈ G.neighborFinset x, s y
  have ha_split : ∀ x, a x = ∑ y ∈ (G.neighborFinset x).filter
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c), s y := by
    intro x
    simp only [a]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : (secondOrderDefectGraph G).connectedComponentMk y = c
    · simp [hy]
    · rw [if_neg hy, hs_out y (fun h => hy ((hmem y).mp h))]
  have ha_in : ∀ x, x ∈ c.supp → a x = -2 * s x := by
    intro x hx
    rw [ha_split x]
    exact hH x hx
  have ha_val : ∀ x, a x = -2 ∨ a x = 0 ∨ a x = 2 := by
    intro x
    rw [ha_split x]
    obtain ⟨u, v, huv, hpair⟩ := Finset.card_eq_two.mp (htwo x)
    rw [hpair, Finset.sum_pair huv]
    have hu : u ∈ c.supp := by
      rw [hmem]
      exact (Finset.mem_filter.mp (show u ∈ (G.neighborFinset x).filter
        (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c) by
          rw [hpair]
          simp)).2
    have hv : v ∈ c.supp := by
      rw [hmem]
      exact (Finset.mem_filter.mp (show v ∈ (G.neighborFinset x).filter
        (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c) by
          rw [hpair]
          simp)).2
    rcases hs_in u hu with hu' | hu' <;>
      rcases hs_in v hv with hv' | hv' <;> simp [hu', hv']
  refine ⟨hDdeg, htwo, ?_, hsum, hDs, ?_, ?_⟩
  · simpa only [Sc] using hsum_c
  · intro x hx
    rw [SimpleGraph.adjMatrix_mulVec_apply]
    exact ha_in x hx
  · intro x _
    rw [SimpleGraph.adjMatrix_mulVec_apply]
    exact ha_val x

/-- Thin campaign-facing candidate wrapper with only the standard local joint
line hypotheses. -/
theorem orderSixtyFour_sizeTwo_signedJoint_candidates_of_local
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
    (s : V → ℤ) (mu : ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c), s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y = mu * s z)
    (x : V) (hx : x ∈ c.supp) :
    mu = -7 ∨ mu = -5 ∨ mu = -3 ∨ mu = -1 ∨ mu = 1 ∨ mu = 3 := by
  have P := orderSixtyFour_sizeTwo_signedJoint_derived
    G hfree hreg hcard c hc s mu hs_out hs_in hH hD
  exact orderSixtyFour_sizeTwo_jointEigenvalue_candidates
    G hfree hreg P.defectDegree c hc s mu hs_in hs_out P.sum_eq_zero
      P.defectAction P.ambientAction_in P.ambientAction_out x hx

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_signedJoint_derived
#print axioms Erdos85.orderSixtyFour_sizeTwo_signedJoint_candidates_of_local
