import Proofs.Erdos85ExcessDefectRegular
import Proofs.Erdos85FrequencyPairEigenspace

/-!
# The defect-eigenspace bridge at arbitrary positive excess

The cycle/Fourier description of the zero-excess defect graph does not
survive at positive excess, but its operator-theoretic core does.  If the
combined defect graph has degree `e + 2`, then every nonprincipal defect
eigenspace is killed by the all-ones operator and the commuting adjacency
restriction squares to `d - 1 - μ`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- **Graph-facing excess eigenspace identity.**  For a regular `C₄`-free
graph whose combined defect graph is `(e+2)`-regular, the adjacency operator
on every defect eigenspace away from the principal eigenvalue `e+2` has
square `(d-1)-μ`.  This is valid at every excess and uses no component
classification. -/
theorem graph_defectEigenspaceRestrict_sq_of_regular_excess
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ}
    (hreg : ∀ x, G.degree x = d)
    (hregD : ∀ x, (secondOrderDefectGraph G).degree x = e + 2)
    {μ : ℚ} (hμ : μ ≠ (e + 2 : ℕ)) :
    let A := G.adjMatrix ℚ
    let D := (secondOrderDefectGraph G).adjMatrix ℚ
    let hcomm : A * D = D * A := by
      change G.adjMatrix ℚ * (secondOrderDefectGraph G).adjMatrix ℚ =
        (secondOrderDefectGraph G).adjMatrix ℚ * G.adjMatrix ℚ
      ext x y
      have hxy := congrArg (fun M : Matrix V V ℤ => M x y)
        (adjMatrix_comm_secondOrderDefect_of_regular G hfree hreg)
      simp only [Matrix.mul_apply] at hxy ⊢
      have hc := congrArg (fun z : ℤ => (z : ℚ)) hxy
      push_cast at hc
      simpa [SimpleGraph.adjMatrix_apply] using hc
    defectEigenspaceRestrict A hcomm μ * defectEigenspaceRestrict A hcomm μ =
      ((d : ℚ) - 1 - μ) • LinearMap.id := by
  let A := G.adjMatrix ℚ
  let D := (secondOrderDefectGraph G).adjMatrix ℚ
  let J : Matrix V V ℚ := Matrix.of fun _ _ => 1
  have hcommZ := adjMatrix_comm_secondOrderDefect_of_regular G hfree hreg
  have hcomm : A * D = D * A := by
    change G.adjMatrix ℚ * (secondOrderDefectGraph G).adjMatrix ℚ =
      (secondOrderDefectGraph G).adjMatrix ℚ * G.adjMatrix ℚ
    ext x y
    have hxy := congrArg (fun M : Matrix V V ℤ => M x y) hcommZ
    simp only [Matrix.mul_apply] at hxy ⊢
    have hc := congrArg (fun z : ℤ => (z : ℚ)) hxy
    push_cast at hc
    simpa [SimpleGraph.adjMatrix_apply] using hc
  have hsqZ := adjMatrix_sq_eq_sub_secondOrderDefect_of_regular G hfree hreg
  have hsq : A * A = ((d : ℚ) - 1) • (1 : Matrix V V ℚ) + J - D := by
    change G.adjMatrix ℚ * G.adjMatrix ℚ =
      ((d : ℚ) - 1) • (1 : Matrix V V ℚ) +
        Matrix.of (fun _ _ => (1 : ℚ)) -
          (secondOrderDefectGraph G).adjMatrix ℚ
    ext x y
    have hxy := congrArg (fun M : Matrix V V ℤ => M x y) hsqZ
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply] at hxy ⊢
    have hc := congrArg (fun z : ℤ => (z : ℚ)) hxy
    push_cast at hc
    simpa [SimpleGraph.adjMatrix_apply,
      FriendshipTheoremOQ01.onesMatrix] using hc
  have hJDZ := onesMatrix_mul_adjMatrix_of_regular
    (secondOrderDefectGraph G) (e + 2) hregD
  have hJD : J * D = (e + 2 : ℕ) • J := by
    change Matrix.of (fun _ _ => (1 : ℚ)) *
        (secondOrderDefectGraph G).adjMatrix ℚ =
      (e + 2 : ℕ) • Matrix.of (fun _ _ => (1 : ℚ))
    ext x y
    have hxy := congrArg (fun M : Matrix V V ℤ => M x y) hJDZ
    simp only [Matrix.mul_apply, Matrix.smul_apply] at hxy ⊢
    have hc := congrArg (fun z : ℤ => (z : ℚ)) hxy
    push_cast at hc
    simpa [SimpleGraph.adjMatrix_apply,
      FriendshipTheoremOQ01.onesMatrix] using hc
  dsimp only
  exact defectEigenspaceRestrict_sq_of_scalar hcomm hsq hJD hμ

end

end Erdos85
