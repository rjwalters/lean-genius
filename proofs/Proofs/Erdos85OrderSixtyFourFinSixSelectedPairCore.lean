import Proofs.Erdos85OrderSixtyFourHSelectedPairCore

/-! # A finite selected-pair core on `Fin 16` -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Relabeling H16 produces a completely finite selected-pair core: six
disjoint perfect matchings and sixteen distinct residual pairs. -/
theorem orderSixtyFour_seven_defect_components_finSix_selectedPairCore
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
      ∃ r : Fin 16 → Finset (Fin 16),
        (∀ i, Function.Involutive (μ i)) ∧
        (∀ i u, μ i u ≠ u) ∧
        (∀ i j, i ≠ j → ∀ u, μ i u ≠ μ j u) ∧
        (∀ u, (r u).card = 2) ∧
        Function.Injective r ∧
        ∀ i u y, {u, μ i u} ≠ r y := by
  classical
  obtain ⟨c, hc16, m, q, hinvol, hfreePoint, hmatchDisj,
      hqcard, hqinj, hqdisj⟩ :=
    orderSixtyFour_seven_defect_components_H_selectedPairCore
      G hfree hmin hcover hcount
  have hcard : Fintype.card c.supp = 16 := by
    have hs : Fintype.card c.supp = c.supp.ncard := by
      simpa [Nat.card_eq_fintype_card] using Nat.card_coe_set_eq c.supp
    rw [hs, hc16]
  let θ : c.supp ≃ Fin 16 :=
    (Fintype.equivFin c.supp).trans (finCongr hcard)
  let μ : Fin 6 → Equiv.Perm (Fin 16) := fun i =>
    (θ.symm.trans (m i)).trans θ
  let r : Fin 16 → Finset (Fin 16) := fun u =>
    (q (θ.symm u)).map θ.toEmbedding
  have hrinj : Function.Injective r := by
    intro u v huv
    have hbase : q (θ.symm u) = q (θ.symm v) := by
      ext z
      have hz := Finset.ext_iff.mp huv (θ z)
      simpa [r] using hz
    have huvBase := hqinj hbase
    exact θ.symm.injective huvBase
  refine ⟨μ, r, ?_, ?_, ?_, ?_, hrinj, ?_⟩
  · intro i u
    simpa [μ] using congrArg θ (hinvol i (θ.symm u))
  · intro i u hfix
    apply hfreePoint i (θ.symm u)
    apply θ.injective
    simpa [μ] using hfix
  · intro i j hij u heq
    apply hmatchDisj i j hij (θ.symm u)
    apply θ.injective
    simpa [μ] using heq
  · intro u
    simp [r, hqcard]
  · intro i u y heq
    apply hqdisj i (θ.symm u) (θ.symm y)
    ext z
    have hz := Finset.ext_iff.mp heq (θ z)
    have hz' : (θ z = u ∨ z = m i (θ.symm u)) ↔
        z ∈ q (θ.symm y) := by
      simpa [μ, r] using hz
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (hzu | hzm)
      · apply hz'.mp
        exact Or.inl (by simpa using congrArg θ hzu)
      · exact hz'.mp (Or.inr hzm)
    · intro hzq
      rcases hz'.mpr hzq with hzu | hzm
      · left
        apply θ.injective
        simpa using hzu
      · exact Or.inr hzm

end

end Erdos85
