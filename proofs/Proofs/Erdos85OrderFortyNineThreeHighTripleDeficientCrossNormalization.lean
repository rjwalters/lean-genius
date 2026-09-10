import Proofs.Erdos85OrderFortyNineThreeHighTripleCrossBijection
import Proofs.Erdos85OrderFortyNineThreeHighTripleCrossCompletion

/-! Normalize a chosen 5/5/4 cross pattern with one deleted permutation pair. -/
namespace Erdos85
open SimpleGraph
noncomputable section

theorem threeHigh_triple_deficient_cross_normalization
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {s t v : Fin 49}
    (hs : s ∈ threeHighTripleSpecialSet G z)
    (ht : t ∈ threeHighTripleSpecialSet G z)
    (hv : v ∈ threeHighTripleSpecialSet G z)
    (hc01 : threeHighTripleBlockCrossCount G s t = 5)
    (hc02 : threeHighTripleBlockCrossCount G s v = 5)
    (hc12 : threeHighTripleBlockCrossCount G t v = 4) :
    let A := G.neighborFinset s ∩ threeHighTripleEmptySet G
    let B := G.neighborFinset t ∩ threeHighTripleEmptySet G
    let C := G.neighborFinset v ∩ threeHighTripleEmptySet G
    ∃ (l0 : Fin 5 ≃ (↑A : Set (Fin 49)))
      (l1 : Fin 5 ≃ (↑B : Set (Fin 49)))
      (l2 : Fin 5 ≃ (↑C : Set (Fin 49))) (π : Equiv.Perm (Fin 5)) (d : Fin 5),
      (∀ i j, G.Adj (l0 i).val (l1 j).val ↔ i = j) ∧
      (∀ i j, G.Adj (l0 i).val (l2 j).val ↔ i = j) ∧
      (∀ i j, G.Adj (l1 i).val (l2 j).val ↔ i ≠ d ∧ π i = j) := by
  classical
  let A := G.neighborFinset s ∩ threeHighTripleEmptySet G
  let B := G.neighborFinset t ∩ threeHighTripleEmptySet G
  let C := G.neighborFinset v ∩ threeHighTripleEmptySet G
  obtain ⟨e01,he01⟩ := threeHigh_triple_cross_count_five_equiv G hfree hmin hHigh hone z hz hs ht hc01
  obtain ⟨e02,he02⟩ := threeHigh_triple_cross_count_five_equiv G hfree hmin hHigh hone z hz hs hv hc02
  obtain ⟨a,b,e12,hab,he12⟩ := threeHigh_triple_cross_count_four_completion G hfree hmin hHigh hone z hz ht hv hc12
  have hAc : A.card = 5 := threeHigh_triple_special_empty_count G hfree hmin hHigh hone z hz
    (Finset.mem_filter.mp hs).2 (((G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hs).1).symm)
  have hA : Fintype.card (↑A : Set (Fin 49)) = 5 := by simpa using hAc
  let l0 : Fin 5 ≃ (↑A : Set (Fin 49)) := (Fintype.equivFinOfCardEq hA).symm
  let l1 : Fin 5 ≃ (↑B : Set (Fin 49)) := l0.trans e01
  let l2 : Fin 5 ≃ (↑C : Set (Fin 49)) := l0.trans e02
  let π : Equiv.Perm (Fin 5) := (l1.trans e12).trans l2.symm
  let d : Fin 5 := l1.symm a
  refine ⟨l0,l1,l2,π,d,?_,?_,?_⟩
  · intro i j
    rw [he01]
    change e01 (l0 i) = e01 (l0 j) ↔ i = j
    exact e01.injective.eq_iff.trans l0.injective.eq_iff
  · intro i j
    rw [he02]
    change e02 (l0 i) = e02 (l0 j) ↔ i = j
    exact e02.injective.eq_iff.trans l0.injective.eq_iff
  · intro i j
    rw [he12]
    have hd : l1 i ≠ a ↔ i ≠ d := by
      change l1 i ≠ a ↔ i ≠ l1.symm a
      apply not_congr
      constructor
      · intro h
        simpa only [Equiv.symm_apply_apply] using congrArg l1.symm h
      · intro h
        simpa only [Equiv.apply_symm_apply] using congrArg l1 h
    have hp : e12 (l1 i) = l2 j ↔ π i = j := by
      change e12 (l1 i) = l2 j ↔ l2.symm (e12 (l1 i)) = j
      constructor
      · intro h
        simpa only [Equiv.symm_apply_apply] using congrArg l2.symm h
      · intro h
        simpa only [Equiv.apply_symm_apply] using congrArg l2 h
    exact and_congr hd hp

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_deficient_cross_normalization
