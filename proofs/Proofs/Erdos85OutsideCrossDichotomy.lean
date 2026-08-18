import Proofs.Erdos85OutsideCrossEigenTransport
import Proofs.Erdos85OrderSixtyFourExteriorPairGraph

/-!
# The graph-facing centered-mode dichotomy at order 64

This synchronizes the cross-block and row-Gram packages on the unique
size-sixteen defect component.  A centered internal eigenmode either crosses
nontrivially to the exterior adjacency block, or lies in the `-6` eigenspace
of the exterior-pair graph.
-/

open SimpleGraph Matrix

namespace Erdos85

noncomputable section

theorem orderSixtyFour_seven_components_outside_centeredMode_dichotomy
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
    ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16 ∧
      let p : Fin 64 → Prop := fun x ↦ x ∈ c.supp
      let q : Set (Fin 64) := {x | ¬p x}
      let H := (G.induce c.supp).adjMatrix ℂ
      let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ x ∈ q)
      let C := (G.induce q).adjMatrix ℂ
      let J : Matrix c.supp q ℂ := fun _ _ ↦ 1
      let R := (exteriorPairGraph G c.supp).adjMatrix ℂ
      ∀ (v : c.supp → ℂ) (lambda : ℂ),
        H.mulVec v = lambda • v →
        J.transpose.mulVec v = 0 →
        (B.transpose.mulVec v ≠ 0 ∧
          C.mulVec (B.transpose.mulVec v) =
            (-lambda) • B.transpose.mulVec v) ∨
          R.mulVec v = (-6 : ℂ) • v := by
  classical
  obtain ⟨c, hc, _label, _hqcard, _htwo, _hinj, _himage,
      _hRreg, _hRedges, _hCreg, _hC4, hcross⟩ :=
    orderSixtyFour_seven_components_outside_feasibility
      G hfree hmin hcover hcount
  obtain ⟨cR, hcR, hgram, _hRreg'⟩ :=
    orderSixtyFour_seven_components_exteriorGram_eq_six_add_sixRegular
      G hfree hmin hcover hcount
  obtain ⟨d, _hd, hsmall⟩ :=
    orderSixtyFour_seven_defect_components_partition
      G hfree hmin hcover hcount
  have heq_of_16 : ∀ {a}, a.supp.ncard = 16 → a = d := by
    intro a ha
    by_contra hne
    have := hsmall a hne
    omega
  have hccR : c = cR :=
    (heq_of_16 hc).trans (heq_of_16 hcR).symm
  subst cR
  refine ⟨c, hc, ?_⟩
  dsimp only
  intro v lambda hHv hcenter
  let p : Fin 64 → Prop := fun x ↦ x ∈ c.supp
  let q : Set (Fin 64) := {x | ¬p x}
  let Hg := G.induce c.supp
  let Cg := G.induce q
  let H := Hg.adjMatrix ℂ
  let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ x ∈ q)
  let C := Cg.adjMatrix ℂ
  let J : Matrix c.supp q ℂ := fun _ _ ↦ 1
  let R := (exteriorPairGraph G c.supp).adjMatrix ℂ
  have hgramT : B * B.transpose =
      (6 : ℂ) • (1 : Matrix c.supp c.supp ℂ) + R := by
    change B * Matrix.conjTranspose B =
      (6 : ℂ) • (1 : Matrix c.supp c.supp ℂ) + R at hgram
    rw [adjMatrix_complex_toBlock_conjTranspose_eq_transpose] at hgram
    exact hgram
  have hHvT : H.transpose.mulVec v = lambda • v := by
    rw [Hg.isSymm_adjMatrix.eq]
    exact hHv
  have hdich := rectangular_cross_centered_eigenpair_or_negative_gram_residual
    H B C J R (6 : ℂ) lambda v hcross hHvT hcenter hgramT
  rcases hdich with hcrossed | hkernel
  · left
    refine ⟨hcrossed.1, ?_⟩
    rw [Cg.isSymm_adjMatrix.eq] at hcrossed
    exact hcrossed.2
  · exact Or.inr hkernel

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_seven_components_outside_centeredMode_dichotomy
