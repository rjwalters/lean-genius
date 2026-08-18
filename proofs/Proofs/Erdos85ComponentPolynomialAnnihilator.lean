import Proofs.Erdos85ComponentFactorization
import Proofs.Erdos85ComponentLocalObstruction
import Proofs.Erdos85SixteenVertexCanonicalRelabel
import Proofs.Erdos85PrincipalIndicatorTrace
import Proofs.Erdos85OrderSixtyFourBipartiteDefectTrace
import Proofs.Erdos85OrderSixtyFourPrincipalTrace

/-! # Polynomial annihilators assembled over connected components

Polynomial evaluation respects the dependent block diagonal decomposition of
an adjacency matrix.  Consequently, a common annihilator of every connected
component is an annihilator of the whole graph.
-/

namespace Erdos85

open SimpleGraph
open Polynomial

noncomputable section

theorem aeval_blockDiagonal'
    {C R : Type*} [Fintype C] [DecidableEq C]
    {V : C → Type*} [∀ c, Fintype (V c)] [∀ c, DecidableEq (V c)]
    [CommSemiring R] (M : ∀ c, Matrix (V c) (V c) R)
    (p : Polynomial R) :
    Polynomial.aeval (Matrix.blockDiagonal' M) p =
      Matrix.blockDiagonal' (fun c =>
        (@Polynomial.aeval R (Matrix (V c) (V c) R) _ _ _ (M c)) p) := by
  induction p using Polynomial.induction_on with
  | C a =>
      ext ⟨c, x⟩ ⟨c', y⟩
      by_cases hcc : c = c'
      · subst c'
        simp [Matrix.blockDiagonal'_apply_eq, Matrix.algebraMap_eq_diagonal,
          Matrix.diagonal_apply, Pi.algebraMap_apply]
      · simp [Matrix.blockDiagonal'_apply_ne _ _ _ hcc,
          Matrix.algebraMap_eq_diagonal, hcc]
  | add p q hp hq =>
      rw [map_add, hp, hq, ← Matrix.blockDiagonal'_add]
      congr 1
      funext c
      exact (Polynomial.aeval_add (M c)).symm
  | monomial n a ih =>
      simp only [pow_succ, ← mul_assoc, map_mul, ih, Polynomial.aeval_X,
        ← Matrix.blockDiagonal'_mul]

/-- A polynomial annihilating every induced connected component annihilates
the adjacency matrix of the whole graph. -/
theorem adjMatrix_aeval_eq_zero_of_connectedComponents
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    (p : Polynomial ℚ)
    (hcomponent : ∀ c : D.ConnectedComponent,
      Polynomial.aeval
        (Matrix.toLin' ((D.induce c.supp).adjMatrix ℚ)) p = 0) :
    Polynomial.aeval (Matrix.toLin' (D.adjMatrix ℚ)) p = 0 := by
  have hcomponentMatrix : ∀ c : D.ConnectedComponent,
      Polynomial.aeval ((D.induce c.supp).adjMatrix ℚ) p = 0 := by
    intro c
    apply Matrix.toLin'.injective
    simpa only [aeval_toLin', map_zero] using hcomponent c
  let e := vertexConnectedComponentEquiv D
  have hreindex : Polynomial.aeval
      ((Matrix.reindexAlgEquiv ℚ ℚ e) (D.adjMatrix ℚ)) p = 0 := by
    rw [show (Matrix.reindexAlgEquiv ℚ ℚ e) (D.adjMatrix ℚ) =
        Matrix.blockDiagonal'
          (fun c : D.ConnectedComponent =>
            (D.induce c.supp).adjMatrix ℚ) by
      exact reindex_adjMatrix_eq_componentBlockDiagonal D]
    rw [aeval_blockDiagonal']
    ext ⟨c, x⟩ ⟨c', y⟩
    by_cases hcc : c = c'
    · subst c'
      simp [hcomponentMatrix c, Matrix.blockDiagonal'_apply_eq]
    · simp [Matrix.blockDiagonal'_apply_ne _ _ _ hcc]
  have hmatrix : Polynomial.aeval (D.adjMatrix ℚ) p = 0 := by
    apply (Matrix.reindexAlgEquiv ℚ ℚ e).injective
    have hmap := Polynomial.map_aeval_eq_aeval_map
      (R := ℚ) (φ := RingHom.id ℚ)
      (ψ := (Matrix.reindexAlgEquiv ℚ ℚ e).toAlgHom.toRingHom)
      (S := Matrix V V ℚ)
      (T := ℚ)
      (U := Matrix (Σ c : D.ConnectedComponent, c.supp)
        (Σ c : D.ConnectedComponent, c.supp) ℚ)
      (by
        ext x i j
        simp [Matrix.reindexAlgEquiv, Matrix.reindex_apply,
          Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply,
          Pi.algebraMap_apply]) p (D.adjMatrix ℚ)
    calc
      (Matrix.reindexAlgEquiv ℚ ℚ e)
          (Polynomial.aeval (D.adjMatrix ℚ) p) =
          Polynomial.aeval
            ((Matrix.reindexAlgEquiv ℚ ℚ e) (D.adjMatrix ℚ)) p := by
              simpa using hmap
      _ = 0 := hreindex
      _ = (Matrix.reindexAlgEquiv ℚ ℚ e) 0 := by simp
  rw [aeval_toLin', hmatrix, map_zero]

/-- The triangle-free, seven-regular, sixteen-vertex classification supplies
the same four-factor annihilator on every connected component, hence globally. -/
theorem triangleFree_sevenRegular_sixteenComponents_aeval_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    (hcard : ∀ c : D.ConnectedComponent, Fintype.card c.supp = 16)
    (htriangle : D.CliqueFree 3)
    (hreg : ∀ x : V, D.degree x = 7) :
    Polynomial.aeval (Matrix.toLin' (D.adjMatrix ℚ))
      ((Polynomial.X - Polynomial.C (7 : ℚ)) *
       (Polynomial.X - Polynomial.C (1 : ℚ)) *
       (Polynomial.X - Polynomial.C (-1 : ℚ)) *
       (Polynomial.X - Polynomial.C (-7 : ℚ))) = 0 := by
  apply adjMatrix_aeval_eq_zero_of_connectedComponents D _
  intro c
  apply triangleFree_sevenRegular_sixteen_aeval_eq_zero
    (D.induce c.supp) (hcard c)
  · rw [cliqueFree_induce_iff]
    intro t _ ht
    exact htriangle t ht
  · intro x
    rw [degree_induce_connectedComponent_supp]
    exact hreg x
  · have hcpos : 0 < Fintype.card c.supp := by rw [hcard c]; norm_num
    letI : Nonempty c.supp := Fintype.card_pos_iff.mp hcpos
    exact Classical.choice inferInstance

/-- The primary-sector restriction and the eigenspace restriction are the
same operator up to the canonical equality of their carrier submodules, so
their traces agree. -/
theorem trace_kerAevalRestrict_eq_trace_defectEigenspaceRestrict
    {V : Type*} [Fintype V] [DecidableEq V]
    (A D : Matrix V V ℚ) (hcommM : A * D = D * A) (μ : ℚ) :
    LinearMap.trace ℚ _
        (kerAevalRestrict (Matrix.toLin' A) (Matrix.toLin' D)
          (toLin'_comm_of_matrix_comm hcommM)
          (Polynomial.X - Polynomial.C μ)) =
      LinearMap.trace ℚ (defectEigenspace D μ)
        (defectEigenspaceRestrict A hcommM μ) := by
  let K := LinearMap.ker
    (Polynomial.aeval (Matrix.toLin' D)
      (Polynomial.X - Polynomial.C μ))
  have hspace : K = defectEigenspace D μ :=
    (defectEigenspace_eq_ker_aeval D μ).symm
  let e : K ≃ₗ[ℚ] defectEigenspace D μ :=
    LinearEquiv.ofEq K (defectEigenspace D μ) hspace
  rw [← LinearMap.trace_conj'
    (kerAevalRestrict (Matrix.toLin' A) (Matrix.toLin' D)
      (toLin'_comm_of_matrix_comm hcommM)
      (Polynomial.X - Polynomial.C μ)) e]
  congr 1

/-- The all-size-sixteen, triangle-free defect branch at order 64 is
impossible.  This is the graph-facing terminal: local classification gives
the global defect annihilator, while the previously established four sector
traces sum to the contradiction `0 = 8`. -/
theorem false_of_orderSixtyFour_all_sizeSixteen_triangleFree_defect
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hm : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16)
    (htriangle : (secondOrderDefectGraph G).CliqueFree 3) : False := by
  let Dg := secondOrderDefectGraph G
  let A := G.adjMatrix ℚ
  let D := Dg.adjMatrix ℚ
  have hreg : ∀ x : Fin 64, G.degree x = 8 :=
    orderSixtyFour_regular_of_tightCover G hfree hmin hcover
  have hDreg : ∀ x : Fin 64, Dg.degree x = 7 :=
    (orderSixtyFour_regular_defect_kernel G hfree hmin hcover).2.2.1
  have hcompCard : ∀ c : Dg.ConnectedComponent,
      Fintype.card c.supp = 16 := by
    intro c
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact hm c
  have hann : Polynomial.aeval (Matrix.toLin' D)
      ((Polynomial.X - Polynomial.C (7 : ℚ)) *
       (Polynomial.X - Polynomial.C (1 : ℚ)) *
       (Polynomial.X - Polynomial.C (-1 : ℚ)) *
       (Polynomial.X - Polynomial.C (-7 : ℚ))) = 0 := by
    exact triangleFree_sevenRegular_sixteenComponents_aeval_eq_zero
      Dg hcompCard htriangle hDreg
  have hcommM : A * D = D * A := by
    exact adjMatrix_comm_secondOrderDefect_of_regular_rat G hfree hreg
  have hcomm : Matrix.toLin' A * Matrix.toLin' D =
      Matrix.toLin' D * Matrix.toLin' A := by
    simpa only [Module.End.mul_eq_comp, Matrix.toLin'_mul] using
      congrArg Matrix.toLin' hcommM
  apply false_of_bipartite_defect_four_sector_traces
    (Matrix.toLin' A) (Matrix.toLin' D) hcomm hann
  · rw [trace_toLin'_eq_matrix_trace]
    exact SimpleGraph.trace_adjMatrix ℚ G
  · simpa [A, D, Dg] using
      orderSixtyFour_principal_defect_sector_trace_eq_eight
        G hfree hmin hcover
  · rw [trace_kerAevalRestrict_eq_trace_defectEigenspaceRestrict
      A D hcommM (1 : ℚ)]
    simpa [A, D, Dg] using
      orderSixtyFour_plusOne_defect_sector_trace_eq_zero G hfree hmin hcover
  · simpa [A, D, Dg] using
      orderSixtyFour_minusOne_defect_sector_trace_eq_zero
        G hfree hmin hcover
  · rw [trace_kerAevalRestrict_eq_trace_defectEigenspaceRestrict
      A D hcommM (-7 : ℚ)]
    simpa [A, D, Dg] using
      orderSixtyFour_minusSeven_defect_sector_trace_eq_zero G hfree hmin hcover

end

end Erdos85
