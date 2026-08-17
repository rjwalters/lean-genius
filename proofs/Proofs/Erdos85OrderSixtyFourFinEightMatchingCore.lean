import Proofs.Erdos85OrderSixtyFourMatchingNoFourCycle

/-! # A Fin 8 permutation core for the order-64 matching network -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- After independently identifying each small block with `Fin 8`, the
order-64 branch supplies a six-by-six matrix of permutations.  Transposed
entries are mutual inverses, diagonal entries are derangements, and every
fourfold composition with distinct opposite block indices is a derangement. -/
theorem orderSixtyFour_seven_defect_components_finEight_matchingCore
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
    ∃ p : Fin 6 → Fin 6 → Equiv.Perm (Fin 8),
      (∀ i j a, p j i (p i j a) = a) ∧
      (∀ i a, p i i a ≠ a) ∧
      ∀ i j k l, i ≠ k → j ≠ l → ∀ a,
        p l i (p k l (p j k (p i j a))) ≠ a := by
  classical
  let D := secondOrderDefectGraph G
  obtain ⟨c, hc16, κ, m, _hmadj, hrecip, hdiag, hno4⟩ :=
    orderSixtyFour_seven_defect_components_matching_noFourCycle
      G hfree hmin hcover hcount
  obtain ⟨c', hc'16, hsmall'⟩ :=
    orderSixtyFour_seven_defect_components_partition
      G hfree hmin hcover hcount
  have hcc' : c = c' := by
    by_contra hne
    have hc8 := hsmall' c hne
    omega
  have hsize (i : Fin 6) : (κ i).1.supp.ncard = 8 := by
    exact hsmall' (κ i).1 (by simpa [hcc'] using (κ i).2)
  have hcard (i : Fin 6) : Fintype.card (κ i).1.supp = 8 := by
    have hs : Fintype.card (κ i).1.supp = (κ i).1.supp.ncard := by
      simpa [Nat.card_eq_fintype_card] using
        Nat.card_coe_set_eq (κ i).1.supp
    rw [hs, hsize i]
  let θ (i : Fin 6) : (κ i).1.supp ≃ Fin 8 :=
    (Fintype.equivFin (κ i).1.supp).trans (finCongr (hcard i))
  let p (i j : Fin 6) : Equiv.Perm (Fin 8) :=
    ((θ i).symm.trans (m i j)).trans (θ j)
  have hambient_ne {i k : Fin 6} (hik : i ≠ k)
      (x : (κ i).1.supp) (z : (κ k).1.supp) : x.1 ≠ z.1 := by
    intro hxz
    have hxi : D.connectedComponentMk x.1 = (κ i).1 :=
      (ConnectedComponent.mem_supp_iff (κ i).1 x.1).mp x.2
    have hzk : D.connectedComponentMk z.1 = (κ k).1 :=
      (ConnectedComponent.mem_supp_iff (κ k).1 z.1).mp z.2
    have hikComp : (κ i).1 = (κ k).1 := by
      rw [← hxi, hxz, hzk]
    exact hik (κ.injective (Subtype.ext hikComp))
  refine ⟨p, ?_, ?_, ?_⟩
  · intro i j a
    simp [p, hrecip]
  · intro i a hfix
    let x : (κ i).1.supp := (θ i).symm a
    apply hdiag i x
    apply (θ i).injective
    simpa [x, p] using hfix
  · intro i j k l hik hjl a
    let x : (κ i).1.supp := (θ i).symm a
    let y : (κ j).1.supp := m i j x
    let z : (κ k).1.supp := m j k y
    let w : (κ l).1.supp := m k l z
    have hxz : x.1 ≠ z.1 := hambient_ne hik x z
    have hyw : y.1 ≠ w.1 := hambient_ne hjl y w
    intro hclose
    apply hno4 i j k l x hxz hyw
    apply (θ i).injective
    simpa [x, y, z, w, p] using hclose

end

end Erdos85
