import Proofs.Erdos85RestrictedOwnerCommutesInducedDefect
import Proofs.Erdos85RoutingOwnerRainbowExactColors

/-! # Unique commuting local factor excludes multiple owner colors

This file isolates the graph-theoretic consumer of the finite lambda-six
census.  A representative-specific calculation only has to prove uniqueness
of a commuting two-factor in the defect complement.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- If every two-regular graph commuting with one order-sixteen defect block
is the same graph `H`, then that block cannot support two distinct owner
colors.  The order-64 owner resolution supplies four such colors, so this is
the direct consumer of a representative-specific uniqueness certificate. -/
theorem orderSixtyFour_false_of_unique_commuting_twoFactor
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (source owner₁ owner₂ : (secondOrderDefectGraph G).ConnectedComponent)
    (hsource : source.supp.ncard = 16)
    (howner₁ : owner₁.supp.ncard = 16)
    (howner₂ : owner₂.supp.ncard = 16)
    (hne : owner₁ ≠ owner₂)
    (H : SimpleGraph source.supp)
    (hunique : ∀ F : SimpleGraph source.supp, [DecidableRel F.Adj] →
      (∀ x, F.degree x = 2) →
      F.adjMatrix ℤ *
          ((secondOrderDefectGraph G).induce source.supp).adjMatrix ℤ =
        ((secondOrderDefectGraph G).induce source.supp).adjMatrix ℤ *
          F.adjMatrix ℤ →
      F = H) : False := by
  let F₁ := restrictedComponentOwnerGraph G source owner₁
  let F₂ := restrictedComponentOwnerGraph G source owner₂
  have hdeg₁ : ∀ x, F₁.degree x = 2 := by
    intro x
    exact binarySquare_regular_twoSizeTwoParts_restrictedOwner_degree_two
      G hfree (q := 8) (by omega) hreg (by norm_num)
      source owner₁ (by norm_num; exact hsource)
      (by norm_num; exact howner₁) x
  have hdeg₂ : ∀ x, F₂.degree x = 2 := by
    intro x
    exact binarySquare_regular_twoSizeTwoParts_restrictedOwner_degree_two
      G hfree (q := 8) (by omega) hreg (by norm_num)
      source owner₂ (by norm_num; exact hsource)
      (by norm_num; exact howner₂) x
  have hcomm₁ := orderSixtyFour_restrictedOwner_adjMatrix_comm_inducedDefect
    G hfree hreg source owner₁ howner₁
  have hcomm₂ := orderSixtyFour_restrictedOwner_adjMatrix_comm_inducedDefect
    G hfree hreg source owner₂ howner₂
  have hF₁ : F₁ = H := hunique F₁ hdeg₁ hcomm₁
  have hF₂ : F₂ = H := hunique F₂ hdeg₂ hcomm₂
  obtain ⟨xval, hxval⟩ := source.nonempty_supp
  let x : source.supp := ⟨xval, hxval⟩
  have hpos : 0 < (F₁.neighborFinset x).card := by
    rw [F₁.card_neighborFinset_eq_degree, hdeg₁]
    omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
  have hadj₁ : F₁.Adj x y := (F₁.mem_neighborFinset x y).mp hy
  have hadj₂ : F₂.Adj x y := by rw [hF₂, ← hF₁]; exact hadj₁
  have hglobal₁ :
      (componentOwnerGraph G (secondOrderDefectGraph G) owner₁).Adj x.1 y.1 :=
    hadj₁
  have hglobal₂ :
      (componentOwnerGraph G (secondOrderDefectGraph G) owner₂).Adj x.1 y.1 :=
    hadj₂
  have := (componentOwnerGraph_adj_iff_owner_eq_of_adj
    G hfree owner₁ hglobal₁ owner₂).mp hglobal₂
  exact hne this.symm

end

end Erdos85
