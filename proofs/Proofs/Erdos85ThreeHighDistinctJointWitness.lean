import Proofs.Erdos85OrderFortyNineThreeHighTripleDistinctColorNeighbor
import Proofs.Erdos85ThreeHighJointRelabeling

/-! Joint H3 families retaining a distinct compatible neighbor for every color,
including the same color. Actual graph witnesses and orbit relabeling preserve
this stronger interface. No finite rejection is asserted here. -/

namespace Erdos85
open SimpleGraph

def ThreeHighDistinctJointWitness (B : Fin 24 → Fin 24 → Bool) : Prop :=
  ∃ F : Fin 3 → Finset (Finset (Fin 24)),
    (∀ k, F k ∈ threeHighResolutionDomain B (threeHighCanonicalResidual k)) ∧
    (∀ k S, S ∈ F k → encodedTripleBlockCap threeHighCanonicalRow S = true) ∧
    (∀ i j, encodedDistinctFamilyCompatibility B (F i) (F j) = true) ∧
    (∀ i j, i ≠ j → encodedFamilyIntersectionCap (F i) (F j) = true)

theorem ThreeHighDistinctJointWitness.forget
    (B : Fin 24 → Fin 24 → Bool) (hB : ThreeHighDistinctJointWitness B) :
    ThreeHighJointWitness B := by
  obtain ⟨F, hF, hblock, hcompat, hcap⟩ := hB
  exact ⟨F, hF, hblock,
    fun i j => encodedDistinctFamilyCompatibility_forget B (F i) (F j) (hcompat i j), hcap⟩

theorem ThreeHighDistinctJointWitness.relabel
    (B : Fin 24 → Fin 24 → Bool) (hB : ThreeHighDistinctJointWitness B)
    (e : Equiv.Perm (Fin 24)) (σ : Equiv.Perm (Fin 3))
    (hroot : e 23 = 23)
    (hrows : ∀ k, (threeHighCanonicalRow k).image e = threeHighCanonicalRow (σ k)) :
    ThreeHighDistinctJointWitness (fun x y => B (e.symm x) (e.symm y)) := by
  classical
  obtain ⟨F,hF,hblock,hcompat,hcap⟩ := hB
  refine ⟨fun k => (F (σ.symm k)).image (fun S => S.image e),?_,?_,?_,?_⟩
  · intro k
    have h := threeHighResolutionDomain_relabel B (threeHighCanonicalResidual (σ.symm k))
      (F (σ.symm k)) e (hF (σ.symm k))
    simpa only [threeHighCanonicalResidual_relabel e σ hroot hrows,Equiv.apply_symm_apply] using h
  · intro k S hS
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hS
    have h := encodedTripleBlockCap_relabel threeHighCanonicalRow T e
    have ht := hblock (σ.symm k) T hT
    unfold encodedTripleBlockCap at h ht ⊢
    apply decide_eq_true_iff.mpr
    intro j
    have hsrc : ∀ j, (T.image e ∩ (threeHighCanonicalRow j).image e).card ≤ 1 := by
      apply of_decide_eq_true
      exact h.trans ht
    simpa only [hrows,Equiv.apply_symm_apply] using hsrc (σ.symm j)
  · intro i j
    simpa only [encodedDistinctFamilyCompatibility_relabel] using hcompat (σ.symm i) (σ.symm j)
  · intro i j hij
    unfold encodedFamilyIntersectionCap
    apply decide_eq_true_iff.mpr
    apply (family_inter_cap_relabel (F (σ.symm i)) (F (σ.symm j)) e).mpr
    exact of_decide_eq_true (hcap (σ.symm i) (σ.symm j) (fun h => hij (σ.symm.injective h)))

noncomputable section

theorem threeHigh_triple_distinct_joint_block_families
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj] [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G) (hmin : ∀ x, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z)
    (s : Fin 3 → Fin 49) (hs : ∀ k, s k ∈ threeHighTripleSpecialSet G z)
    (hsinj : Function.Injective s)
    (e : Fin 24 ≃ (↑(threeHighTripleEmptySet G) : Set (Fin 49)))
    (heu : (e 23).val = u)
    (hrow : ∀ k i, (e (threeHighEmptyUIndex ((@finProdFinEquiv 3 5) (k,i)))).val ∈
      G.neighborFinset (s k) ∩ threeHighTripleEmptySet G)
    (B : Fin 24 → Fin 24 → Bool)
    (hB : ∀ i j, decide (G.Adj (e i).val (e j).val) = B i j) :
    ThreeHighDistinctJointWitness B := by
  classical
  obtain ⟨h,F,hactual,hres,hcompat,hinter⟩ := threeHigh_triple_joint_color_families
    G hfree hmin hHigh hone z hz hu huz s hs hsinj e heu hrow B hB
  refine ⟨F,hres,?_,?_,hinter⟩
  · intro k
    obtain ⟨hh,hsh,hF⟩ := hactual k
    have hsz : G.Adj (s k) z :=
      ((G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp (hs k)).1).symm
    have hblocks : ∀ l, threeHighCanonicalRow l = threeHighSingletonCoordinates G e (s l) := by
      intro l
      exact (threeHigh_triple_special_coordinates_eq_row G hfree hmin hHigh hone z hz
        (hs l) e l (hrow l)).symm
    have hf := threeHigh_triple_actual_block_family G hfree hmin hHigh hone
      z (h k) (s k) hz hh ((G.mem_neighborFinset _ _).mpr hsh.symm) hsz e B hB
      s hs threeHighCanonicalRow hblocks
    rw [hF]
    exact hf.2
  · intro k l
    obtain ⟨hk, hsk, hFk⟩ := hactual k
    obtain ⟨hl, hsl, hFl⟩ := hactual l
    have hsz (i : Fin 3) : G.Adj (s i) z :=
      ((G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp (hs i)).1).symm
    rw [hFk, hFl]
    exact threeHigh_triple_distinct_color_family_compatibility G hfree hmin hHigh hone
      z (h k) (h l) (s k) (s l) hz hk hl
      ((G.mem_neighborFinset _ _).mpr hsk.symm)
      ((G.mem_neighborFinset _ _).mpr hsl.symm) (hsz k) (hsz l) e B hB

end
end Erdos85

#print axioms Erdos85.ThreeHighDistinctJointWitness.forget
#print axioms Erdos85.ThreeHighDistinctJointWitness.relabel
#print axioms Erdos85.threeHigh_triple_distinct_joint_block_families
