import Proofs.Erdos85ExcessEigenspace
import Proofs.Erdos85NonprincipalCharpoly
import Proofs.Erdos85AdjoinSquareTranslate

/-!
# Transporting a nonprincipal adjacency eigenvector to the defect spectrum

This is the final operator link in the global asymmetric-orbit argument.
An adjacency eigenvector away from the regular eigenvalue is killed by the
all-ones matrix.  The defect identity then turns its squared adjacency
eigenvalue into a defect eigenvalue.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

theorem defect_mulVec_eq_of_adj_eigenvector
    {K V : Type*} [Field K] [Fintype V] [DecidableEq V]
    (A D J : Matrix V V K) (c θ : K) (v : V → K)
    (hsq : A * A = c • (1 : Matrix V V K) + J - D)
    (hv : A.mulVec v = θ • v) (hJ : J.mulVec v = 0) :
    D.mulVec v = (c - θ ^ 2) • v := by
  have happ := congrArg (fun M : Matrix V V K => M.mulVec v) hsq
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, hJ,
    add_zero] at happ
  have hAA : (A * A).mulVec v = θ ^ 2 • v := by
    calc
      (A * A).mulVec v = A.mulVec (A.mulVec v) :=
        (Matrix.mulVec_mulVec v A A).symm
      _ = A.mulVec (θ • v) := by rw [hv]
      _ = θ • A.mulVec v := Matrix.mulVec_smul A θ v
      _ = θ • (θ • v) := by rw [hv]
      _ = θ ^ 2 • v := by rw [← mul_smul, pow_two]
  rw [hAA] at happ
  ext i
  have hi := congrFun happ i
  simp only [Pi.smul_apply, Pi.sub_apply] at hi ⊢
  rw [pow_two]
  linear_combination hi

/-- For a regular graph, an adjacency eigenvector with eigenvalue different
from `d` has coordinate sum zero, equivalently the all-ones matrix kills it. -/
theorem ones_mulVec_eq_zero_of_adj_eigenvector_ne_degree
    {K V : Type*} [Field K] [CharZero K] [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hreg : ∀ x, G.degree x = d)
    {θ : K} (hθ : θ ≠ (d : K)) (v : V → K)
    (hv : (G.adjMatrix K).mulVec v = θ • v) :
    (Matrix.of (fun _ _ => (1 : K)) : Matrix V V K).mulVec v = 0 := by
  let J : Matrix V V K := Matrix.of fun _ _ => 1
  have hJAZ := onesMatrix_mul_adjMatrix_of_regular G d hreg
  have hJA : J * G.adjMatrix K = (d : K) • J := by
    ext x y
    have hxy := congrArg (fun M : Matrix V V ℤ => M x y) hJAZ
    simp only [Matrix.mul_apply, Matrix.smul_apply] at hxy ⊢
    have hc := congrArg (fun z : ℤ => (z : K)) hxy
    push_cast at hc
    simpa [J, SimpleGraph.adjMatrix_apply,
      FriendshipTheoremOQ01.onesMatrix] using hc
  have happ := congrArg (fun M : Matrix V V K => M.mulVec v) hJA
  rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul,
    Matrix.smul_mulVec] at happ
  change J.mulVec v = 0
  ext i
  have hi := congrFun happ i
  simp only [Pi.smul_apply, Pi.zero_apply] at hi ⊢
  have hz : (θ - (d : K)) * (J.mulVec v i) = 0 := by
    calc
      (θ - (d : K)) * (J.mulVec v i) =
          θ * (J.mulVec v i) - (d : K) * (J.mulVec v i) := by ring
      _ = 0 := sub_eq_zero.mpr hi
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hθ)

/-- Graph-facing pairing: every nonprincipal adjacency eigenvector is a
defect eigenvector with eigenvalue `d-1-θ²`. -/
theorem secondOrderDefect_mulVec_of_adj_eigenvector_ne_degree
    {K V : Type*} [Field K] [CharZero K] [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ x, G.degree x = d)
    {θ : K} (hθ : θ ≠ (d : K)) (v : V → K)
    (hv : (G.adjMatrix K).mulVec v = θ • v) :
    ((secondOrderDefectGraph G).adjMatrix K).mulVec v =
      ((d : K) - 1 - θ ^ 2) • v := by
  let A := G.adjMatrix K
  let D := (secondOrderDefectGraph G).adjMatrix K
  let J : Matrix V V K := Matrix.of fun _ _ => 1
  have hsqZ := adjMatrix_sq_eq_sub_secondOrderDefect_of_regular G hfree hreg
  have hsq : A * A = ((d : K) - 1) • (1 : Matrix V V K) + J - D := by
    ext x y
    have hxy := congrArg (fun M : Matrix V V ℤ => M x y) hsqZ
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply] at hxy ⊢
    have hc := congrArg (fun z : ℤ => (z : K)) hxy
    push_cast at hc
    simpa [A, D, J, SimpleGraph.adjMatrix_apply,
      FriendshipTheoremOQ01.onesMatrix] using hc
  have hJ : J.mulVec v = 0 :=
    ones_mulVec_eq_zero_of_adj_eigenvector_ne_degree G hreg hθ v hv
  exact defect_mulVec_eq_of_adj_eigenvector A D J ((d : K) - 1) θ v hsq hv hJ

end

end Erdos85
