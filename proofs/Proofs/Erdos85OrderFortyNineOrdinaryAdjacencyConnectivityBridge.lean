import Proofs.Erdos85OrderFortyNineOrdinaryAdjacencyConnected
import Proofs.Erdos85OrderFortyNineHighIncidenceCensus

/-! # Incidence-census bridge for ordinary adjacency connectivity -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Under the canonical three-high labeling, the support fibers on `Fin 46`
are exactly the global low-vertex high-incidence fibers. -/
theorem orderFortyNineOrdinarySupportFiber_card_eq_highIncidenceCount
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x, 7 ≤ G.degree x)
    (hhigh : ∀ y : Fin 49, G.degree y = 8 ↔ y.val < 3)
    (k : ℕ) :
    (orderFortyNineOrdinarySupportFiber G Finset.univ (k : ℤ)).card =
      orderFortyNineHighIncidenceCount G k := by
  let f := orderFortyNineOrdinaryVertex
  unfold orderFortyNineOrdinarySupportFiber
  unfold orderFortyNineHighIncidenceCount
  apply Finset.card_bij (fun i _ => f i)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    constructor
    · change f i ∈ (Finset.univ : Finset (Fin 49)) \
          orderFortyNineHighVertices G
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hi7 : G.degree (f i) = 7 := by
        rcases orderFortyNine_degree_eq_seven_or_eight
            G hfree hmin (by decide) (f i) with h | h
        · exact h
        · have := (hhigh _).1 h
          simp [f, orderFortyNineOrdinaryVertex] at this
      simp [orderFortyNineHighVertices, hi7]
    · have hc := orderFortyNineOrdinaryHighSupportCountInt_eq_card
        G hhigh i
      rw [hc] at hi
      exact_mod_cast hi
  · intro i hi j hj hij
    exact (Fin.natAdd_inj 3).mp hij
  · intro y hy
    simp only [Finset.mem_filter] at hy
    have hylow := (Finset.mem_sdiff.mp hy.1).2
    have hy7 : G.degree y = 7 := by
      rcases orderFortyNine_degree_eq_seven_or_eight
          G hfree hmin (by decide) y with h | h
      · exact h
      · exact (hylow (by simp [orderFortyNineHighVertices, h])).elim
    have hy3 : 3 ≤ y.val := by
      by_contra hlt
      have hy8 := (hhigh y).2 (by omega)
      omega
    let i : Fin 46 := ⟨y.val - 3, by omega⟩
    have hfi : f i = y := by
      apply Fin.ext
      simp [f, i, orderFortyNineOrdinaryVertex]
      omega
    refine ⟨i, ?_, hfi⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [orderFortyNineOrdinaryHighSupportCountInt_eq_card G hhigh i]
    change ((G.neighborFinset (f i) ∩
      orderFortyNineHighVertices G).card : ℤ) = (k : ℤ)
    rw [hfi]
    exact_mod_cast hy.2

/-- The global no-triple profile supplies the two fiber cardinalities needed
by the closed-shore connectivity theorem. -/
theorem orderFortyNineOrdinaryGraph_preconnected_of_noTriple_count
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x, 7 ≤ G.degree x)
    (hhigh : ∀ y : Fin 49, G.degree y = 8 ↔ y.val < 3)
    (hrange : ∀ i,
      orderFortyNineOrdinaryHighSupportCountInt G i = 0 ∨
      orderFortyNineOrdinaryHighSupportCountInt G i = 1 ∨
      orderFortyNineOrdinaryHighSupportCountInt G i = 2)
    (hnoTriple : orderFortyNineHighIncidenceCount G 3 = 0) :
    (orderFortyNineOrdinaryGraph G).Preconnected := by
  have hH : orderFortyNineHighVertices G = {0, 1, 2} := by
    ext y
    simp [orderFortyNineHighVertices, hhigh]
    omega
  have hHcard : (orderFortyNineHighVertices G).card = 3 := by
    rw [hH]
    decide
  rcases orderFortyNine_highIncidence_profile_of_three_high
      G hfree hmin (by decide) hHcard with hp | hp
  · apply orderFortyNineOrdinaryGraph_preconnected_of_noTriple_profile
      G hfree hmin hhigh hrange
    · simpa using (orderFortyNineOrdinarySupportFiber_card_eq_highIncidenceCount
        G hfree hmin hhigh 2).trans hp.2.2.1
    · simpa using (orderFortyNineOrdinarySupportFiber_card_eq_highIncidenceCount
        G hfree hmin hhigh 1).trans hp.2.1
  · omega

end

end Erdos85

#print axioms Erdos85.orderFortyNineOrdinarySupportFiber_card_eq_highIncidenceCount
#print axioms Erdos85.orderFortyNineOrdinaryGraph_preconnected_of_noTriple_count
