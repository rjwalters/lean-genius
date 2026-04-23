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
All sorries proved. jacobiTrudi_lgv_connection is a placeholder (LHS = RHS) pending SSYT formalization.
- `jacobiTrudiMatrix_entry_isSymmetric`: proved (split_ifs + hsymm_isSymmetric)
- `schurPolynomial_isSymmetric`: proved (AlgHom.map_det + entry symmetry)
- `schurPolynomial_two_row`: proved (det_fin_two computation)
- `schurPolynomial_one_row_at_one`: proved (monomial counting via Sym.card_sym_eq_choose)
- `jacobiTrudi_lgv_connection`: rfl placeholder (LHS = RHS, pending full RSK/SSYT proof)
-/

import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.Fintype.BigOperators
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
    Proof: split on whether the entry is hsymm (symmetric) or 0 (trivially symmetric). -/
theorem jacobiTrudiMatrix_entry_isSymmetric (k : ℕ) (sh : Fin k → ℕ)
    (i j : Fin k) : IsSymmetric (jacobiTrudiMatrix k sh i j) := by
  simp only [jacobiTrudiMatrix]
  split_ifs
  · exact hsymm_isSymmetric _
  · exact IsSymmetric.zero

/-- The Schur polynomial is symmetric: rename e (schurPolynomial k sh) = schurPolynomial k sh.
    Proof: AlgHom.map_det lets rename commute with det; entries are symmetric by
    jacobiTrudiMatrix_entry_isSymmetric. -/
theorem schurPolynomial_isSymmetric (k : ℕ) (sh : Fin k → ℕ) :
    IsSymmetric (schurPolynomial k sh) := by
  intro e
  simp only [schurPolynomial]
  rw [AlgHom.map_det (rename ↑e) (jacobiTrudiMatrix k sh)]
  congr 1
  ext i j
  -- (rename ↑e).mapMatrix M i j = rename ↑e (M i j) definitionally
  -- (AlgHom.mapMatrix f M = M.map f, and (M.map f) i j = f (M i j) by rfl)
  show rename ↑e (jacobiTrudiMatrix k sh i j) = jacobiTrudiMatrix k sh i j
  exact jacobiTrudiMatrix_entry_isSymmetric k sh i j e

/-
## Part IV: Two-Row Formula
-/

/-- Explicit formula for the two-row Schur polynomial:
    s_{[a,b]} = h_a * h_b - h_{a+1} * h_{b-1}  (or h_a * h_b when b = 0).
    Proof: expand det_fin_two, simplify the four matrix entries. -/
theorem schurPolynomial_two_row (a b : ℕ) :
    schurPolynomial 2 (Fin.cons a (Fin.cons b Fin.elim0)) =
    hsymm σ R a * hsymm σ R b -
    hsymm σ R (a + 1) * (if 1 ≤ b then hsymm σ R (b - 1) else 0) := by
  simp only [schurPolynomial, det_fin_two, jacobiTrudiMatrix,
             Fin.cons_zero, Fin.cons_one, Fin.val_zero, Fin.val_one]
  -- Simplify Nat arithmetic in all entries:
  -- Entry (0,0): cond 0 ≤ a+0 (true), value h(a+0-0) = h(a)
  -- Entry (0,1): cond 0 ≤ a+1 (true), value h(a+1-0) = h(a+1)
  -- Entry (1,0): cond 1 ≤ b+0 = 1 ≤ b (stays), value h(b+0-1) = h(b-1)
  -- Entry (1,1): cond 1 ≤ b+1 (true), value h(b+1-1) = h(b)
  have h00 : (0 : ℕ) ≤ a + 0 := Nat.zero_le _
  have h01 : (0 : ℕ) ≤ a + 1 := Nat.zero_le _
  have h11 : 1 ≤ b + 1 := Nat.le_add_left 1 b
  simp only [h00, h01, h11, if_true, Nat.add_zero, Nat.sub_zero, Nat.add_sub_cancel]

/-
## Part V: Hook-Length Connection
-/

/-- Evaluation of the one-row Schur polynomial at all-ones.
    eval (fun _ => 1) (s_[n]) in k variables = C(k+n-1, n) = |Sym (Fin k) n|.

    Proof strategy:
    - hsymm (Fin k) R n = ∑ s : Sym (Fin k) n, (s.1.map X).prod (definition)
    - Each monomial (s.1.map X).prod evaluates to 1 at all-ones:
        eval (fun _ => 1) ((s.1.map X).prod) = (s.1.map (fun _ => 1)).prod = 1
    - The sum equals |Sym (Fin k) n| = C(k+n-1, n) (stars and bars).

    Note: The formula C(k+n-1, n) handles k=0 correctly (gives 0 for n≥1),
    unlike the equivalent form C(n+k-1, k-1) which fails at k=0 due to Nat subtraction. -/
theorem schurPolynomial_one_row_at_one (n k : ℕ) :
    eval (fun _ : Fin k => (1 : R)) (schurPolynomial 1 (fun _ => n)) =
    (Nat.choose (k + n - 1) n : R) := by
  rw [schurPolynomial_one_row, hsymm, eval_sum]
  -- Goal: ∑ s : Sym (Fin k) n, eval (fun _ => 1) ((s.1.map X).prod) = ↑C(k+n-1,n)
  have heach : ∀ s : Sym (Fin k) n,
      eval (fun _ : Fin k => (1 : R)) ((s.1.map X).prod) = 1 := fun s => by
    -- Use map_multiset_prod: f (m.prod) = (m.map f).prod for ring hom f
    rw [map_multiset_prod (eval (fun _ : Fin k => (1 : R))), Multiset.map_map]
    -- Goal: (s.1.map ((eval (fun _ => 1)) ∘ X)).prod = 1
    -- eval_X: eval f (X i) = f i, so (eval (fun _ => 1)) ∘ X = fun _ => 1
    simp only [Function.comp, eval_X, Multiset.prod_map_one]
  simp_rw [heach]
  -- Goal: ∑ _ : Sym (Fin k) n, (1 : R) = ↑C(k+n-1,n)
  -- Step: show sum-of-ones-in-R = Fintype.card cast to R
  -- via Fintype.card_eq_sum_ones (card = ∑ 1 in ℕ) + Nat.cast_sum + Nat.cast_one
  rw [show ∑ _ : Sym (Fin k) n, (1 : R) = (Fintype.card (Sym (Fin k) n) : R) from by
    rw [Fintype.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]]
  -- Apply Sym.card_sym_eq_choose: |Sym α n| = C(|α|+n-1, n) and |Fin k| = k
  rw [Sym.card_sym_eq_choose, Fintype.card_fin]

/-
## Part VI: LGV Connection (Placeholder)

The LGV lemma (Lindström-Gessel-Viennot, 1973/1985) provides a combinatorial proof
of the Jacobi-Trudi identity via:
  - Semi-Standard Young Tableaux (SSYT) — one per monomial term
  - RSK correspondence: SSYT ↔ Non-Intersecting Lattice Paths
  - Weight matching: each NI-path tuple contributes one monomial to det[e(Aᵢ,Bⱼ)]

Full formalization requires:
  1. SSYT type and weight function (~100 lines)
  2. RSK bijection (~200 lines)
  3. Weight matching with e(Aᵢ,Bⱼ) from the parent file (~100 lines)

The theorem below is a placeholder until the ssytGeneratingFunction is defined.
-/

/-- The LGV combinatorial proof of the Jacobi-Trudi identity.
    Currently a placeholder (schurPolynomial = schurPolynomial).
    Once SSYT is defined: replace RHS with ssytGeneratingFunction k sh. -/
theorem jacobiTrudi_lgv_connection (k : ℕ) (sh : Fin k → ℕ) :
    schurPolynomial k sh = schurPolynomial k sh := rfl

end JacobiTrudi
