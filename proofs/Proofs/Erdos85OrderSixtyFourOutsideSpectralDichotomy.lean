import Proofs.Erdos85OutsideCrossEigenTransport
import Proofs.Erdos85AdjacencyDefectEigenvector

/-!
# Graph-facing spectral dichotomy for the order-64 outside block

This synchronizes the cross-block feasibility package with the exterior Gram
package on the unique order-16 defect component.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Every centered internal adjacency mode either crosses to a nonzero
exterior mode with negated eigenvalue, or is a negative-degree mode of the
six-regular exterior-pair graph. -/
theorem orderSixtyFour_seven_components_outside_centered_spectral_dichotomy
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
  obtain ⟨d, hd, hgram, _hdRreg⟩ :=
    orderSixtyFour_seven_components_exteriorGram_eq_six_add_sixRegular
      G hfree hmin hcover hcount
  obtain ⟨base, _hbase, hsmall⟩ :=
    orderSixtyFour_seven_defect_components_partition
      G hfree hmin hcover hcount
  have heq_of_16 : ∀ {a : (secondOrderDefectGraph G).ConnectedComponent},
      a.supp.ncard = 16 → a = base := by
    intro a ha
    by_contra hne
    have := hsmall a hne
    omega
  have hcd : c = d := (heq_of_16 hc).trans (heq_of_16 hd).symm
  subst d
  refine ⟨c, hc, ?_⟩
  dsimp only
  intro vec lambda hHv hcenter
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
    rw [← adjMatrix_complex_toBlock_conjTranspose_eq_transpose G p
      (fun x ↦ x ∈ q)]
    exact hgram
  have hdich := rectangular_cross_centered_eigenpair_or_negative_gram_residual
    H B C J R 6 lambda vec hcross (by
      rw [Hg.isSymm_adjMatrix.eq]
      exact hHv) hcenter hgramT
  rcases hdich with htransport | hresidual
  · left
    refine ⟨htransport.1, ?_⟩
    rw [Cg.isSymm_adjMatrix.eq] at htransport
    exact htransport.2
  · right
    exact hresidual

/-- The centering hypothesis in the outside spectral dichotomy is automatic
for every nonprincipal mode of the internal two-factor. -/
theorem orderSixtyFour_seven_components_outside_nonprincipal_spectral_dichotomy
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
      let R := (exteriorPairGraph G c.supp).adjMatrix ℂ
      ∀ (v : c.supp → ℂ) (lambda : ℂ),
        lambda ≠ 2 →
        H.mulVec v = lambda • v →
        (B.transpose.mulVec v ≠ 0 ∧
          C.mulVec (B.transpose.mulVec v) =
            (-lambda) • B.transpose.mulVec v) ∨
          R.mulVec v = (-6 : ℂ) • v := by
  classical
  obtain ⟨c, hc, hdich⟩ :=
    orderSixtyFour_seven_components_outside_centered_spectral_dichotomy
      G hfree hmin hcover hcount
  obtain ⟨d, hd, hdtwo⟩ :=
    orderSixtyFour_seven_defect_components_sixteenBlock_twoRegular
      G hfree hmin hcover hcount
  obtain ⟨base, _hbase, hsmall⟩ :=
    orderSixtyFour_seven_defect_components_partition
      G hfree hmin hcover hcount
  have heq_of_16 : ∀ {a : (secondOrderDefectGraph G).ConnectedComponent},
      a.supp.ncard = 16 → a = base := by
    intro a ha
    by_contra hne
    have := hsmall a hne
    omega
  have hcd : c = d := (heq_of_16 hc).trans (heq_of_16 hd).symm
  subst d
  refine ⟨c, hc, ?_⟩
  dsimp only at hdich ⊢
  intro v lambda hlambda hHv
  apply hdich v lambda hHv
  let Hg := G.induce c.supp
  let Jsq : Matrix c.supp c.supp ℂ := fun _ _ ↦ 1
  have hzero : Jsq.mulVec v = 0 :=
    ones_mulVec_eq_zero_of_adj_eigenvector_ne_degree
      Hg hdtwo (by simpa using hlambda) v hHv
  have hcne : c.supp.ncard ≠ 0 := by omega
  obtain ⟨x, hx⟩ := Set.nonempty_of_ncard_ne_zero hcne
  ext z
  have hz := congrFun hzero ⟨x, hx⟩
  simpa [Matrix.mulVec, Jsq] using hz

end


end Erdos85

#print axioms Erdos85.orderSixtyFour_seven_components_outside_centered_spectral_dichotomy
#print axioms Erdos85.orderSixtyFour_seven_components_outside_nonprincipal_spectral_dichotomy
