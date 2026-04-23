/-
# Jacobi-Trudi Identity: Schur Polynomials as Determinants of hsymm

OQ-01-OQ-01 follow-up to BallotProblemOQ03OQ01OQ01 (ballot-problem-oq-03-oq-01-oq-01).

This file formalizes the Jacobi-Trudi identity, which expresses Schur polynomials
as determinants of complete homogeneous symmetric polynomials:

  s_λ = det[h_{λᵢ - i + j}]_{1 ≤ i,j ≤ k}

## Key definitions
- `jacobiTrudiMatrix k sh`: the k×k matrix with entry h_{shᵢ + j - i} (or 0 for i > shᵢ + j)
- `schurPolynomial k sh`: det(jacobiTrudiMatrix k sh)

## Status: badge=wip
5 sorries. The symmetry proofs and base cases are stated; the two-row formula,
hook-length evaluation, and the LGV combinatorial connection require more work.
The LGV connection (jacobiTrudi_lgv_connection) requires RSK correspondence (~400 lines).
-/

import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Proofs.BallotProblemOQ03OQ01OQ01

open MvPolynomial Matrix Finset

namespace JacobiTrudi

variable {σ R : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]

/-
## Part I: Definitions
-/

/-- The Jacobi-Trudi matrix for a partition `sh : Fin k → ℕ`.
    Entry (i, j) = h_{sh_i + j - i} when i.val ≤ sh i + j.val, else 0. -/
noncomputable def jacobiTrudiMatrix (k : ℕ) (sh : Fin k → ℕ) :
    Matrix (Fin k) (Fin k) (MvPolynomial σ R) :=
  fun i j =>
    if i.val ≤ sh i + j.val
    then hsymm σ R (sh i + j.val - i.val)
    else 0

/-- The Schur polynomial s_λ defined as the determinant of the Jacobi-Trudi matrix. -/
noncomputable def schurPolynomial (k : ℕ) (sh : Fin k → ℕ) :
    MvPolynomial σ R :=
  (jacobiTrudiMatrix k sh).det

/-
## Part II: Base Cases
-/

/-- The Schur polynomial of the empty partition is 1 (0×0 determinant). -/
theorem schurPolynomial_empty :
    schurPolynomial 0 (fun i => i.elim0) = (1 : MvPolynomial σ R) := by
  simp [schurPolynomial, jacobiTrudiMatrix, det_fin_zero]

/-- The Schur polynomial of the one-row partition [n] is hsymm σ R n. -/
theorem schurPolynomial_one_row (n : ℕ) :
    schurPolynomial 1 (fun _ => n) = hsymm σ R n := by
  simp [schurPolynomial, jacobiTrudiMatrix, det_fin_one]

/-
## Part III: Symmetry
-/

/-- Each entry of the Jacobi-Trudi matrix is a symmetric polynomial.
    Proof sketch: hsymm_isSymmetric for the nonzero case; 0 for the zero case. -/
theorem jacobiTrudiMatrix_entry_isSymmetric (k : ℕ) (sh : Fin k → ℕ)
    (i j : Fin k) : IsSymmetric (jacobiTrudiMatrix k sh i j) := by
  sorry

/-- The Schur polynomial is symmetric: rename e (schurPolynomial k sh) = schurPolynomial k sh.
    Proof sketch: AlgHom.map_det + jacobiTrudiMatrix_entry_isSymmetric. -/
theorem schurPolynomial_isSymmetric (k : ℕ) (sh : Fin k → ℕ) :
    IsSymmetric (schurPolynomial k sh) := by
  sorry

/-
## Part IV: Two-Row Formula
-/

/-- Explicit formula for the two-row Schur polynomial:
    s_{[a,b]} = h_a * h_b - h_{a+1} * h_{b-1}  (or h_a * h_b when b = 0).
    Proof sketch: expand det_fin_two, simplify matrix entries. -/
theorem schurPolynomial_two_row (a b : ℕ) :
    schurPolynomial 2 (Fin.cons a (Fin.cons b Fin.elim0)) =
    hsymm σ R a * hsymm σ R b -
    hsymm σ R (a + 1) * (if 1 ≤ b then hsymm σ R (b - 1) else 0) := by
  sorry

/-
## Part V: Hook-Length Connection
-/

/-- Evaluation of the one-row Schur polynomial at all-ones.
    eval (fun _ => 1) (s_[n]) in k variables = C(n+k-1, k-1). -/
theorem schurPolynomial_one_row_at_one (n k : ℕ) :
    eval (fun _ : Fin k => (1 : R)) (schurPolynomial 1 (fun _ => n)) =
    (Nat.choose (n + k - 1) (k - 1) : ℕ) := by
  sorry

/-
## Part VI: LGV Connection (Open)

The LGV lemma (Lindström-Gessel-Viennot, 1973/1985) provides a combinatorial proof
of the Jacobi-Trudi identity via:
  - Semi-Standard Young Tableaux (SSYT) — one per monomial term
  - RSK correspondence: SSYT ↔ Non-Intersecting Lattice Paths
  - Weight matching: each NI-path tuple contributes one monomial to det[e(Aᵢ,Bⱼ)]

Full formalization requires:
  1. SSYT type and weight function (~100 lines)
  2. RSK bijection (~200 lines)
  3. Weight matching with e(Aᵢ,Bⱼ) from the parent file (~100 lines)

The theorem below is stated as a sorry until these are available.
-/

/-- The LGV combinatorial proof of the Jacobi-Trudi identity.
    The schurPolynomial equals the generating function of semi-standard Young tableaux
    (SSYT) of shape sh: schurPolynomial k sh = ∑_{T : SSYT(sh)} ∏ᵢ x_{T(i)}.
    This requires RSK correspondence (~400 additional lines). -/
theorem jacobiTrudi_lgv_connection (k : ℕ) (sh : Fin k → ℕ) :
    schurPolynomial k sh = schurPolynomial k sh := by
  -- TODO: Replace RHS with ssytGeneratingFunction k sh once SSYT is defined.
  -- The equality s_λ = ∑_{T:SSYT(λ)} x^T is the Jacobi-Trudi identity.
  sorry

end JacobiTrudi
