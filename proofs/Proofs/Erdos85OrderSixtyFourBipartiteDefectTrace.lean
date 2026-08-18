import Proofs.Erdos85OrderSixtyFourMinusOneTrace
import Proofs.Erdos85ExcessEigenspace
import Proofs.Erdos85RationalPrimaryTraceSplit

/-! # Trace vanishing on the bipartite order-sixteen defect spectrum

For a regular order-64 candidate, adjacency restricted to the defect
`mu`-eigenspace squares to `7-mu`.  The three nonprincipal eigenvalues of
`K_{8,8}` minus a perfect matching are `1`, `-1`, and `-7`; the corresponding
scalars `6`, `8`, and `14` are rational nonsquares.  The `-1` case already
appears in `Erdos85OrderSixtyFourMinusOneTrace`; this file supplies the two
remaining graph-facing sectors.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- If `T² = I + 6P` and `P² = 8P`, then `T` satisfies the fourth-power
identity of `K_{8,8}` minus a perfect matching.  This pointwise proof avoids
any choice of basis or spectral argument. -/
theorem bipartite_defect_fourth_eq_zero_of_square_projection
    {E : Type*} [AddCommGroup E] [Module ℚ E]
    (T P : E →ₗ[ℚ] E)
    (hsq : T * T = 1 + (6 : ℚ) • P)
    (hP : P * P = (8 : ℚ) • P) :
    T ^ 4 - (50 : ℚ) • T ^ 2 + (49 : ℚ) • 1 = 0 := by
  apply LinearMap.ext
  intro v
  have hsqv (w : E) : T (T w) = w + (6 : ℚ) • P w := by
    have h := LinearMap.congr_fun hsq w
    simpa only [Module.End.mul_apply, LinearMap.add_apply,
      LinearMap.smul_apply, Module.End.one_apply] using h
  have hPv : P (P v) = (8 : ℚ) • P v := by
    have h := LinearMap.congr_fun hP v
    simpa only [Module.End.mul_apply, LinearMap.smul_apply] using h
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply, LinearMap.zero_apply, pow_succ, pow_zero,
    Module.End.mul_apply]
  rw [hsqv (T (T v)), hsqv v, map_add, map_smul, hPv]
  module

/-- The fourth-power matrix identity for `K_{8,8}` minus a perfect matching
is exactly the four-linear-factor annihilation needed by primary trace
decomposition.  Keeping this conversion separate leaves the graph-facing
task as the concrete identity `T⁴ - 50T² + 49I = 0`. -/
theorem aeval_bipartite_defect_polynomial_eq_zero_of_fourth
    {E : Type*} [AddCommGroup E] [Module ℚ E]
    (T : E →ₗ[ℚ] E)
    (hfourth : T ^ 4 - (50 : ℚ) • T ^ 2 + (49 : ℚ) • 1 = 0) :
    Polynomial.aeval T
      ((Polynomial.X - Polynomial.C (7 : ℚ)) *
       (Polynomial.X - Polynomial.C (1 : ℚ)) *
       (Polynomial.X - Polynomial.C (-1 : ℚ)) *
       (Polynomial.X - Polynomial.C (-7 : ℚ))) = 0 := by
  have hpoly :
      ((Polynomial.X - Polynomial.C (7 : ℚ)) *
       (Polynomial.X - Polynomial.C (1 : ℚ)) *
       (Polynomial.X - Polynomial.C (-1 : ℚ)) *
       (Polynomial.X - Polynomial.C (-7 : ℚ))) =
      Polynomial.X ^ 4 - Polynomial.C 50 * Polynomial.X ^ 2 +
        Polynomial.C 49 := by
    norm_num [pow_two, ← Polynomial.C_mul]
    ring_nf
    norm_num [pow_two, ← Polynomial.C_mul]
    rw [show Polynomial.C (50 : ℚ) =
      Polynomial.C 49 + Polynomial.C 1 by
        rw [← Polynomial.C_add]
        norm_num]
    simp
    ring
  rw [hpoly]
  simpa only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X,
    Polynomial.aeval_C, Module.algebraMap_end_eq_smul_id,
    Module.End.one_eq_id, Module.End.mul_eq_comp, LinearMap.id_comp,
    Algebra.smul_mul_assoc, one_mul] using hfourth

/-- Abstract terminal for the `K_{8,8}`-minus-matching spectrum.  Once the
defect operator is annihilated by the four distinct linear factors with roots
`7, 1, -1, -7`, trace additivity makes ambient trace zero incompatible with
sector traces `8, 0, 0, 0`. -/
theorem false_of_bipartite_defect_four_sector_traces
    {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (S T : E →ₗ[ℚ] E) (hcomm : S * T = T * S)
    (hann : Polynomial.aeval T
      ((Polynomial.X - Polynomial.C (7 : ℚ)) *
       (Polynomial.X - Polynomial.C (1 : ℚ)) *
       (Polynomial.X - Polynomial.C (-1 : ℚ)) *
       (Polynomial.X - Polynomial.C (-7 : ℚ))) = 0)
    (htotal : LinearMap.trace ℚ E S = 0)
    (h7 : LinearMap.trace ℚ _
      (kerAevalRestrict S T hcomm
        (Polynomial.X - Polynomial.C (7 : ℚ))) = 8)
    (h1 : LinearMap.trace ℚ _
      (kerAevalRestrict S T hcomm
        (Polynomial.X - Polynomial.C (1 : ℚ))) = 0)
    (hm1 : LinearMap.trace ℚ _
      (kerAevalRestrict S T hcomm
        (Polynomial.X - Polynomial.C (-1 : ℚ))) = 0)
    (hm7 : LinearMap.trace ℚ _
      (kerAevalRestrict S T hcomm
        (Polynomial.X - Polynomial.C (-7 : ℚ))) = 0) : False := by
  let g : Fin 4 → Polynomial ℚ := ![
    Polynomial.X - Polynomial.C (7 : ℚ),
    Polynomial.X - Polynomial.C (1 : ℚ),
    Polynomial.X - Polynomial.C (-1 : ℚ),
    Polynomial.X - Polynomial.C (-7 : ℚ)]
  have hpw : Pairwise fun i j : Fin 4 =>
      IsCoprime (g i) (g j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd rfl hij
        | (dsimp [g]
           rw [(Polynomial.irreducible_X_sub_C _).coprime_iff_not_dvd,
              Polynomial.dvd_iff_isRoot]
           norm_num [Polynomial.IsRoot.def])
  have hprod : (∏ i, g i) =
      ((Polynomial.X - Polynomial.C (7 : ℚ)) *
       (Polynomial.X - Polynomial.C (1 : ℚ)) *
       (Polynomial.X - Polynomial.C (-1 : ℚ)) *
       (Polynomial.X - Polynomial.C (-7 : ℚ))) := by
    rw [Fin.prod_univ_four]
    rfl
  have hsplit := trace_eq_sum_trace_restrict_ker_aeval
    S T hcomm g hpw (by rw [hprod]; exact hann)
  rw [Fin.sum_univ_four] at hsplit
  change LinearMap.trace ℚ E S =
    LinearMap.trace ℚ _
        (kerAevalRestrict S T hcomm
          (Polynomial.X - Polynomial.C (7 : ℚ))) +
      LinearMap.trace ℚ _
        (kerAevalRestrict S T hcomm
          (Polynomial.X - Polynomial.C (1 : ℚ))) +
      LinearMap.trace ℚ _
        (kerAevalRestrict S T hcomm
          (Polynomial.X - Polynomial.C (-1 : ℚ))) +
      LinearMap.trace ℚ _
        (kerAevalRestrict S T hcomm
          (Polynomial.X - Polynomial.C (-7 : ℚ))) at hsplit
  rw [htotal, h7, h1, hm1, hm7] at hsplit
  norm_num at hsplit

/-- The defect eigenvalue `1` carries zero rational adjacency trace because
the restricted adjacency operator squares to the nonsquare scalar `6`. -/
theorem orderSixtyFour_plusOne_defect_sector_trace_eq_zero
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8) :
    let A := G.adjMatrix ℚ
    let D := (secondOrderDefectGraph G).adjMatrix ℚ
    let hcomm : A * D = D * A :=
      adjMatrix_comm_secondOrderDefect_of_regular_rat G hfree
        (orderSixtyFour_regular_of_tightCover G hfree hmin hcover)
    LinearMap.trace ℚ (defectEigenspace D (1 : ℚ))
      (defectEigenspaceRestrict A hcomm (1 : ℚ)) = 0 := by
  have hreg : ∀ x : Fin 64, G.degree x = 8 :=
    orderSixtyFour_regular_of_tightCover G hfree hmin hcover
  have hDreg : ∀ x : Fin 64,
      (secondOrderDefectGraph G).degree x = 5 + 2 := by
    intro x
    simpa using (orderSixtyFour_regular_defect_kernel
      G hfree hmin hcover).2.2.1 x
  exact graph_trace_defectEigenspaceRestrict_eq_zero_of_regular_excess
    G hfree (d := 8) (e := 5) hreg hDreg (μ := (1 : ℚ))
      (by norm_num) (by norm_num)

/-- The defect eigenvalue `-7` carries zero rational adjacency trace because
the restricted adjacency operator squares to the nonsquare scalar `14`. -/
theorem orderSixtyFour_minusSeven_defect_sector_trace_eq_zero
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8) :
    let A := G.adjMatrix ℚ
    let D := (secondOrderDefectGraph G).adjMatrix ℚ
    let hcomm : A * D = D * A :=
      adjMatrix_comm_secondOrderDefect_of_regular_rat G hfree
        (orderSixtyFour_regular_of_tightCover G hfree hmin hcover)
    LinearMap.trace ℚ (defectEigenspace D (-7 : ℚ))
      (defectEigenspaceRestrict A hcomm (-7 : ℚ)) = 0 := by
  have hreg : ∀ x : Fin 64, G.degree x = 8 :=
    orderSixtyFour_regular_of_tightCover G hfree hmin hcover
  have hDreg : ∀ x : Fin 64,
      (secondOrderDefectGraph G).degree x = 5 + 2 := by
    intro x
    simpa using (orderSixtyFour_regular_defect_kernel
      G hfree hmin hcover).2.2.1 x
  exact graph_trace_defectEigenspaceRestrict_eq_zero_of_regular_excess
    G hfree (d := 8) (e := 5) hreg hDreg (μ := (-7 : ℚ))
      (by norm_num) (by norm_num)

end

end Erdos85
