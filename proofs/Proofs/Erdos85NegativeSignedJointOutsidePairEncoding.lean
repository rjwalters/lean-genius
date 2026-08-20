import Proofs.Erdos85NegativeSignedJointConnectedOwnerProfile
import Proofs.Erdos85OrderSixtyFourOutsideEdgeBijection
import Proofs.Erdos85OrderSixtyFourRegularOutsideFeasibility
import Proofs.Erdos85BinarySquareRegularParity

/-! # Coordinate-free outside-pair encoding for negative signed joints -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Every exterior vertex is represented by its canonical unordered pair of
component neighbours.  The map is injective, and the three owner fibres have
the advertised endpoint signs. -/
structure NegativeSignedJointOutsidePairEncoding
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (s : Fin 64 → ℤ) where
  pair : {x : Fin 64 // x ∉ c.supp} → Sym2 c.supp
  injective : Function.Injective pair
  pair_toFinset_card : ∀ z, (pair z).toFinset.card = 2
  mem_pair_iff_adj : ∀ z u, u ∈ (pair z).toFinset ↔ G.Adj u.1 z.1
  positivePair_signs : ∀ z,
    z.1 ∈ negativeSignedJointPositivePairOwners G c s →
      ∀ u ∈ (pair z).toFinset, s u.1 = 1
  mixedPair_signs : ∀ z,
    z.1 ∈ negativeSignedJointMixedPairOwners G c s →
      ∃ u ∈ (pair z).toFinset, s u.1 = 1 ∧
      ∃ v ∈ (pair z).toFinset, s v.1 = -1
  negativePair_signs : ∀ z,
    z.1 ∈ negativeSignedJointNegativePairOwners G c s →
      ∀ u ∈ (pair z).toFinset, s u.1 = -1

/-- At regular order 64 the canonical injection exhausts the exterior-pair
graph: its 48 outside owners are exactly the 48 edges. -/
theorem orderSixtyFour_regular_sizeSixteen_exists_outsidePairEdgeEquiv
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x : Fin 64, G.degree x = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 16) :
    Nonempty ({x : Fin 64 // x ∉ c.supp} ≃
      (exteriorPairGraph G c.supp).edgeFinset) := by
  classical
  obtain ⟨_label, hqcard, hcard, hinc, _himage, _hRreg, hRedges,
      _houtreg, _houtfree, _hcross⟩ :=
    orderSixtyFour_regular_sizeSixteen_outsidePair_feasibility
      G hfree hreg c hc
  exact ⟨outsidePairEdgeEquiv G (secondOrderDefectGraph G) c
    hcard hinc hqcard hRedges⟩

theorem exists_negativeSignedJointOutsidePairEncoding
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 16)
    (s : Fin 64 → ℤ) (mu : ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y = mu * s z) :
    Nonempty (NegativeSignedJointOutsidePairEncoding G c s) := by
  classical
  let D := secondOrderDefectGraph G
  have P := orderSixtyFour_sizeTwo_signedJoint_derived
    G hfree hreg (by norm_num) c (by simpa using hc) s mu
      hs_out hs_in hH hD
  have hcard : ∀ x : Fin 64,
      (componentNeighborFinset G D c x).card = 2 := P.componentNeighborCard
  let pair : {x : Fin 64 // x ∉ c.supp} → Sym2 c.supp :=
    outsidePair G D c hcard
  have hinc : Function.Injective (componentNeighborFinset G D c) :=
    binarySquare_regular_sizeTwoPart_componentNeighborFinset_injective
      G hfree (q := 8) (by omega) hreg (by norm_num) c (by simpa using hc)
  have hpairInjective : Function.Injective pair := by
    intro z w hzw
    apply Subtype.ext
    apply hinc
    have hz := outsidePair_toFinset G D c hcard z
    have hw := outsidePair_toFinset G D c hcard w
    have hsub : componentNeighborSubtypeFinset G D c z.1 =
        componentNeighborSubtypeFinset G D c w.1 := by
      rw [← hz, ← hw]
      exact congrArg Sym2.toFinset hzw
    ext x
    constructor
    · intro hx
      have hxs : x ∈ c.supp :=
        (ConnectedComponent.mem_supp_iff c x).mpr (Finset.mem_filter.mp hx).2
      have : (⟨x, hxs⟩ : c.supp) ∈
          componentNeighborSubtypeFinset G D c z.1 := Finset.mem_subtype.mpr hx
      rw [hsub] at this
      exact Finset.mem_subtype.mp this
    · intro hx
      have hxs : x ∈ c.supp :=
        (ConnectedComponent.mem_supp_iff c x).mpr (Finset.mem_filter.mp hx).2
      have : (⟨x, hxs⟩ : c.supp) ∈
          componentNeighborSubtypeFinset G D c w.1 := Finset.mem_subtype.mpr hx
      rw [← hsub] at this
      exact Finset.mem_subtype.mp this
  have hsum (z : {x : Fin 64 // x ∉ c.supp}) :
      ∑ u ∈ (pair z).toFinset, s u.1 = (G.adjMatrix ℤ).mulVec s z.1 := by
    rw [outsidePair_toFinset G D c hcard z]
    calc
      (∑ u ∈ componentNeighborSubtypeFinset G D c z.1, s u.1) =
          ∑ y ∈ componentNeighborFinset G D c z.1, s y := by
        apply Finset.sum_bij (fun u _ ↦ u.1)
        · intro u hu
          exact Finset.mem_subtype.mp hu
        · intro u _ v _ huv
          exact Subtype.ext huv
        · intro y hy
          have hys : y ∈ c.supp :=
            (ConnectedComponent.mem_supp_iff c y).mpr
              (Finset.mem_filter.mp hy).2
          exact ⟨⟨y, hys⟩, Finset.mem_subtype.mpr hy, rfl⟩
        · simp
      _ = ∑ y ∈ G.neighborFinset z.1, s y := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro y hy hyout
        have hyc : y ∉ c.supp := by
          intro hyin
          apply hyout
          exact Finset.mem_filter.mpr ⟨hy,
            (ConnectedComponent.mem_supp_iff c y).mp hyin⟩
        simp [hs_out y hyc]
      _ = (G.adjMatrix ℤ).mulVec s z.1 := by
        rw [SimpleGraph.adjMatrix_mulVec_apply]
  have endpointSigns
      (z : {x : Fin 64 // x ∉ c.supp}) :
      ∀ u ∈ (pair z).toFinset, s u.1 = -1 ∨ s u.1 = 1 := by
    intro u hu
    exact hs_in u.1 u.2
  refine ⟨⟨pair, hpairInjective, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro z
    rw [outsidePair_toFinset G D c hcard z,
      componentNeighborSubtypeFinset_card]
    exact hcard z.1
  · intro z u
    exact mem_outsidePair_toFinset_iff_adj G D c hcard z u
  · intro z hz u hu
    have hzsum : (G.adjMatrix ℤ).mulVec s z.1 = 2 := by
      simpa [negativeSignedJointPositivePairOwners] using
        (Finset.mem_filter.mp hz).2.2
    have htwo : (pair z).toFinset.card = 2 := by
      rw [outsidePair_toFinset G D c hcard z,
        componentNeighborSubtypeFinset_card]
      exact hcard z.1
    obtain ⟨v, w, hvw, hp⟩ := Finset.card_eq_two.mp htwo
    have huvw : u = v ∨ u = w := by simpa [hp] using hu
    have hsv := endpointSigns z v (by rw [hp]; simp [hvw])
    have hsw := endpointSigns z w (by rw [hp]; simp)
    have htotal : s v.1 + s w.1 = 2 := by
      rw [← hzsum, ← hsum z, hp]
      simp [hvw]
    rcases huvw with rfl | rfl <;> omega
  · intro z hz
    have hzsum : (G.adjMatrix ℤ).mulVec s z.1 = 0 := by
      simpa [negativeSignedJointMixedPairOwners] using
        (Finset.mem_filter.mp hz).2.2
    have htwo : (pair z).toFinset.card = 2 := by
      rw [outsidePair_toFinset G D c hcard z,
        componentNeighborSubtypeFinset_card]
      exact hcard z.1
    obtain ⟨u, v, huv, hp⟩ := Finset.card_eq_two.mp htwo
    have hsu := endpointSigns z u (by rw [hp]; simp [huv])
    have hsv := endpointSigns z v (by rw [hp]; simp)
    have htotal : s u.1 + s v.1 = 0 := by
      rw [← hzsum, ← hsum z, hp]
      simp [huv]
    rcases hsu with hsu | hsu
    · refine ⟨v, by rw [hp]; simp, ?_, u, by rw [hp]; simp [huv], hsu⟩
      omega
    · refine ⟨u, by rw [hp]; simp [huv], hsu, v, by rw [hp]; simp, ?_⟩
      omega
  · intro z hz u hu
    have hzsum : (G.adjMatrix ℤ).mulVec s z.1 = -2 := by
      simpa [negativeSignedJointNegativePairOwners] using
        (Finset.mem_filter.mp hz).2.2
    have htwo : (pair z).toFinset.card = 2 := by
      rw [outsidePair_toFinset G D c hcard z,
        componentNeighborSubtypeFinset_card]
      exact hcard z.1
    obtain ⟨v, w, hvw, hp⟩ := Finset.card_eq_two.mp htwo
    have huvw : u = v ∨ u = w := by simpa [hp] using hu
    have hsv := endpointSigns z v (by rw [hp]; simp [hvw])
    have hsw := endpointSigns z w (by rw [hp]; simp)
    have htotal : s v.1 + s w.1 = -2 := by
      rw [← hzsum, ← hsum z, hp]
      simp [hvw]
    rcases huvw with rfl | rfl <;> omega

end

end Erdos85

#print axioms Erdos85.exists_negativeSignedJointOutsidePairEncoding
#print axioms Erdos85.orderSixtyFour_regular_sizeSixteen_exists_outsidePairEdgeEquiv
