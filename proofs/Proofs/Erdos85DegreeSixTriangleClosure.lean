import Proofs.Erdos85DegreeSixFiniteFieldTrace

/-!
# Closing the degree-six eleven-triangle boundary

The finite-field quotient trace certificate and the quadratic trace theorem
are combined here to rule out a 33-vertex degree-six `C₄`-free boundary
graph whose second-order defect consists entirely of triangles.
-/

namespace Erdos85

open SimpleGraph

theorem no_degreeSix_boundary_of_secondOrder_all_triangles
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (hthree : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 3) : False := by
  let DG := secondOrderDefectGraph G
  let AM := G.adjMatrix ℚ
  let DM := DG.adjMatrix ℚ
  let JM : Matrix V V ℚ := Matrix.of fun _ _ => 1
  let A : (V → ℚ) →ₗ[ℚ] (V → ℚ) := AM.toLin'
  let D : (V → ℚ) →ₗ[ℚ] (V → ℚ) := DM.toLin'
  let J : (V → ℚ) →ₗ[ℚ] (V → ℚ) := JM.toLin'
  have hboundary : Fintype.card V = 6 * (6 - 1) + 3 := by
    norm_num [hcard]
  have hregD : ∀ x : V, DG.degree x = 2 :=
    secondOrderDefectGraph_degree_eq_two
      G hfree (d := 6) (by norm_num) (by norm_num) hmin hboundary
  have htri : IsLocallyTriangleUnion DG :=
    locallyTriangleUnion_of_component_order_three DG hregD hthree
  have hpoly : D * D = D + (2 : ℚ) • LinearMap.id := by
    exact adjMatrix_toLin_sq_eq_add_two_of_locallyTriangleUnion DG hregD htri
  have hcommMZ := adjMatrix_comm_secondOrderDefect_of_even
    G hfree (d := 6) (by norm_num) (by norm_num) hmin hboundary
  have hcommMQ : AM * DM = DM * AM := by
    dsimp only [AM, DM, DG]
    ext x y
    have hxy := congrArg (fun M : Matrix V V ℤ => M x y) hcommMZ
    simp only [Matrix.mul_apply] at hxy ⊢
    have hc := congrArg (fun z : ℤ => (z : ℚ)) hxy
    push_cast at hc
    simpa [SimpleGraph.adjMatrix_apply] using hc
  have hcomm : A * D = D * A := by
    simpa only [A, D, Module.End.mul_eq_comp, Matrix.toLin'_mul] using
      congrArg Matrix.toLin' hcommMQ
  have hsqMZ := adjMatrix_sq_eq_sub_secondOrderDefect_of_even
    G hfree (d := 6) (by norm_num) (by norm_num) hmin hboundary
  have hsqMQ : AM * AM = (5 : ℚ) • (1 : Matrix V V ℚ) + JM - DM := by
    dsimp only [AM, DM, JM, DG]
    ext x y
    have hxy := congrArg (fun M : Matrix V V ℤ => M x y) hsqMZ
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply] at hxy ⊢
    have hc := congrArg (fun z : ℤ => (z : ℚ)) hxy
    push_cast at hc
    simpa [SimpleGraph.adjMatrix_apply,
      FriendshipTheoremOQ01.onesMatrix] using hc
  have hsq : A * A = (5 : ℚ) • LinearMap.id + J - D := by
    simpa only [A, D, J, Module.End.mul_eq_comp, Matrix.toLin'_mul,
      map_smul, Matrix.toLin'_one, map_add, map_sub] using
      congrArg Matrix.toLin' hsqMQ
  have hJDZ := onesMatrix_mul_adjMatrix_of_regular DG 2 hregD
  have hJDM : JM * DM = (2 : ℚ) • JM := by
    dsimp only [JM, DM, DG]
    ext x y
    have hxy := congrArg (fun M : Matrix V V ℤ => M x y) hJDZ
    simp only [Matrix.mul_apply, Matrix.smul_apply] at hxy ⊢
    have hc := congrArg (fun z : ℤ => (z : ℚ)) hxy
    push_cast at hc
    simpa [SimpleGraph.adjMatrix_apply,
      FriendshipTheoremOQ01.onesMatrix] using hc
  have hJD : J * D = (2 : ℚ) • J := by
    simpa only [J, D, Module.End.mul_eq_comp, Matrix.toLin'_mul,
      map_smul] using
      congrArg Matrix.toLin' hJDM
  have htrace : LinearMap.trace ℚ (V → ℚ) A = 0 := by
    change LinearMap.trace ℚ (V → ℚ) AM.toLin' = 0
    rw [Matrix.trace_toLin'_eq]
    exact SimpleGraph.trace_adjMatrix ℚ G
  have hmixed := secondOrder_mixed_trace_eq_eighteen_of_eleven_triangles
    G hfree hmin hcard hthree
  have hplus : LinearMap.trace ℚ
      (LinearMap.range (trianglePlusProjection D))
      (A.restrict
        (mapsTo_trianglePlusProjection_range_of_commute A D hcomm)) = 6 := by
    rw [trace_restrict_trianglePlusProjection_range_eq_trace_mul A D hpoly hcomm]
    rw [trace_mul_trianglePlusProjection]
    have hAD : LinearMap.trace ℚ (V → ℚ) (A * D) = 18 := by
      have hADlin : A * D = (AM * DM).toLin' := by
        simp only [A, D, Module.End.mul_eq_comp, Matrix.toLin'_mul]
      rw [hADlin]
      rw [Matrix.trace_toLin'_eq]
      simpa [AM, DM, DG] using hmixed
    rw [hAD, htrace]
    norm_num
  have hkerfin : Module.finrank ℚ
      (LinearMap.ker (trianglePlusProjection D)) = 22 := by
    exact finrank_trianglePlusProjection_ker_eq_twentyTwo
      DG hcard hregD htri
  have hkersq := restrict_trianglePlusProjection_ker_sq_eq_six_of_J_mul_D
    A D J hcomm hsq hJD
  exact false_of_triangle_projection_traces_sq_six
    A D hpoly hcomm htrace 6 (by norm_num) hplus hkerfin hkersq

end Erdos85
