import Proofs.Erdos85OrderSixtyFourOrthogonalArrayHRestriction

/-! # The finite six-column code carried by H16 -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- After relabeling rows and each symbol alphabet, H16 is a sixteen-word
six-column code over `Fin 8`.  Every symbol occurs twice in every column,
and every two columns separate all sixteen words. -/
theorem orderSixtyFour_seven_defect_components_finSix_H_code
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
    ∃ a : Fin 6 → Fin 16 → Fin 8,
      (∀ i x, ((Finset.univ : Finset (Fin 16)).filter
        (fun u => a i u = x)).card = 2) ∧
      ∀ i j, i ≠ j →
        Function.Injective (fun u : Fin 16 => (a i u, a j u)) := by
  classical
  obtain ⟨c, hc16, κ, ℓ, hpair, _hiff, hbalance⟩ :=
    orderSixtyFour_seven_defect_components_orthogonalArray_H_restriction
      G hfree hmin hcover hcount
  obtain ⟨c', hc'16, hsmall'⟩ :=
    orderSixtyFour_seven_defect_components_partition
      G hfree hmin hcover hcount
  have hcc' : c = c' := by
    by_contra hne
    have hc8 := hsmall' c hne
    omega
  have hHcard : Fintype.card c.supp = 16 := by
    have hs : Fintype.card c.supp = c.supp.ncard := by
      simpa [Nat.card_eq_fintype_card] using Nat.card_coe_set_eq c.supp
    rw [hs, hc16]
  have hKcard (i : Fin 6) : Fintype.card (κ i).1.supp = 8 := by
    have hs : Fintype.card (κ i).1.supp = (κ i).1.supp.ncard := by
      simpa [Nat.card_eq_fintype_card] using
        Nat.card_coe_set_eq (κ i).1.supp
    rw [hs, hsmall' (κ i).1 (by simpa [hcc'] using (κ i).2)]
  let θH : c.supp ≃ Fin 16 :=
    (Fintype.equivFin c.supp).trans (finCongr hHcard)
  let θK (i : Fin 6) : (κ i).1.supp ≃ Fin 8 :=
    (Fintype.equivFin (κ i).1.supp).trans (finCongr (hKcard i))
  let a (i : Fin 6) (u : Fin 16) : Fin 8 :=
    θK i (ℓ i (θH.symm u).1)
  refine ⟨a, ?_, ?_⟩
  · intro i x
    let S : Finset c.supp :=
      (Finset.univ : Finset c.supp).filter
        (fun u => ℓ i u.1 = (θK i).symm x)
    let T : Finset (Fin 16) :=
      (Finset.univ : Finset (Fin 16)).filter (fun u => a i u = x)
    have hmap : S.map θH.toEmbedding = T := by
      ext u
      simp [S, T, a]
      constructor
      · intro h
        rw [h]
        exact (θK i).apply_symm_apply x
      · intro h
        apply (θK i).injective
        simpa using h
    change T.card = 2
    rw [← hmap, Finset.card_map]
    exact hbalance i ((θK i).symm x)
  · intro i j hij u v huv
    have hi : ℓ i (θH.symm u).1 = ℓ i (θH.symm v).1 := by
      apply (θK i).injective
      exact congrArg Prod.fst huv
    have hj : ℓ j (θH.symm u).1 = ℓ j (θH.symm v).1 := by
      apply (θK j).injective
      exact congrArg Prod.snd huv
    have hz : (θH.symm u).1 = (θH.symm v).1 :=
      (hpair i j hij).1 (Prod.ext hi hj)
    apply θH.symm.injective
    exact Subtype.ext hz

end

end Erdos85
