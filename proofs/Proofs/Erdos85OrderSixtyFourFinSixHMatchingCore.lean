import Proofs.Erdos85OrderSixtyFourHMatchingFamily

/-! # A `Fin 16` matching core for the distinguished component -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- After identifying the distinguished sixteen-vertex component with
`Fin 16`, its six small-block matchings become pairwise pointwise-disjoint
fixed-point-free involutions. -/
theorem orderSixtyFour_seven_defect_components_finSix_H_matchingCore
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
    ∃ μ : Fin 6 → Equiv.Perm (Fin 16),
      (∀ i, Function.Involutive (μ i)) ∧
      (∀ i u, μ i u ≠ u) ∧
      ∀ i j, i ≠ j → ∀ u, μ i u ≠ μ j u := by
  classical
  obtain ⟨c, hc16, κ, m, hinvol, hfreePoint, hdisj, _hadj⟩ :=
    orderSixtyFour_seven_defect_components_H_matchingFamily
      G hfree hmin hcover hcount
  have hcard : Fintype.card c.supp = 16 := by
    have hs : Fintype.card c.supp = c.supp.ncard := by
      simpa [Nat.card_eq_fintype_card] using Nat.card_coe_set_eq c.supp
    rw [hs, hc16]
  let θ : c.supp ≃ Fin 16 :=
    (Fintype.equivFin c.supp).trans (finCongr hcard)
  let μ : Fin 6 → Equiv.Perm (Fin 16) := fun i =>
    (θ.symm.trans (m i)).trans θ
  refine ⟨μ, ?_, ?_, ?_⟩
  · intro i u
    simpa [μ] using congrArg θ (hinvol i (θ.symm u))
  · intro i u hfix
    apply hfreePoint i (θ.symm u)
    apply θ.injective
    simpa [μ] using hfix
  · intro i j hij u heq
    apply hdisj i j hij (θ.symm u)
    apply θ.injective
    simpa [μ] using heq

end

end Erdos85
