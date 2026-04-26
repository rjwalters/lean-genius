/-
  Aristotle targets for BallotProblemOQ03OQ01OQ01OQ01.lean (Jacobi-Trudi Identity)
  HARD routine lemmas for automated proof search.
  See BallotProblemOQ03OQ01OQ01OQ01.lean for the main formalization.

  ## Context

  The Jacobi-Trudi identity expresses Schur polynomials as determinants of
  complete homogeneous symmetric polynomials: s_λ = det[h_{λᵢ - i + j}].

  The k=0 and k=1 cases are proved. The k=2 case requires:
  (1) ssytFin_two_row_eq_sum_colstrict: bijection between 2-row SSYTs and
      column-strict pairs of symmetric products (~80 lines)
  (2) jdt_weight_sum: the JDT (jeu de taquin) bijection shows the sum
      of non-column-strict pair weights = h_{a+1} * h_{b-1} (~80 lines)

  ## PRIMARY TARGETS

  1. ssytFin_two_row_eq_sum_colstrict (HARD):
     Row-decompose a 2-row SSYT into two rows (as Sym elements), showing
     the col-strict condition corresponds exactly to the SSYT column-strict condition.

     Bijection φ : SSYTFin n 2 sh ≃ {(P,Q) : ColStrictSym}:
     - Forward: T ↦ (ofList(ofFn T.row0), ofList(ofFn T.row1))
     - Backward: (P,Q) ↦ SSYT with rows P.sort, Q.sort

  2. jdt_weight_sum (HARD):
     Bijection {non-col-strict (P,Q) of shapes (a,b)} ≃ {all (P',Q') of shapes (a+1,b-1)}:
     - Forward: let c = min{j : P.sort[j] ≥ Q.sort[j]}, v = Q.sort[c]
       P' = multiset.add P {v}, Q' = multiset.erase Q v
     - Weight preserved: wt(P)*wt(Q) = wt(P+{v})*wt(Q-{v}) by Multiset.prod_erase
-/
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Multiset.Sort
import Mathlib.Algebra.BigOperators.Fin

open MvPolynomial Matrix Finset

namespace BallotJacobiTrudiAristotle

variable {R : Type*} [CommRing R]

-- ============================================================
-- Local definitions (matching BallotProblemOQ03OQ01OQ01OQ01.lean)
-- ============================================================

/-- Semistandard Young tableau of shape sh : Fin k → ℕ with entries in Fin n. -/
def SSYTFin' (n k : ℕ) (sh : Fin k → ℕ) :=
  { f : ((i : Fin k) × Fin (sh i)) → Fin n //
    (∀ (i : Fin k) (j1 j2 : Fin (sh i)), j1 < j2 → f ⟨i, j1⟩ ≤ f ⟨i, j2⟩) ∧
    (∀ (i1 i2 : Fin k) (j1 : Fin (sh i1)) (j2 : Fin (sh i2)),
      j1.val = j2.val → i1 < i2 → f ⟨i1, j1⟩ < f ⟨i2, j2⟩) }

instance {n k : ℕ} {sh : Fin k → ℕ} : Fintype (SSYTFin' n k sh) :=
  Subtype.fintype _

noncomputable def SSYTFin'.weight {n k : ℕ} {sh : Fin k → ℕ}
    (T : SSYTFin' n k sh) : MvPolynomial (Fin n) R :=
  ∏ p : (i : Fin k) × Fin (sh i), X (T.1 p)

noncomputable def ssytSchurFin' (n k : ℕ) (sh : Fin k → ℕ) : MvPolynomial (Fin n) R :=
  ∑ T : SSYTFin' n k sh, T.weight

/-- Column-strict condition for two symmetric products. -/
private def ColStrictSym' {α : Type*} [LinearOrder α] (a b : ℕ)
    (P : Sym α a) (Q : Sym α b) : Prop :=
  ∀ j : ℕ, j < min a b →
    (P.1.sort (· ≤ ·))[j]'(by
        have h : (P.1.sort (· ≤ ·)).length = a := (Multiset.length_sort _ P.1).trans P.2
        omega) <
    (Q.1.sort (· ≤ ·))[j]'(by
        have h : (Q.1.sort (· ≤ ·)).length = b := (Multiset.length_sort _ Q.1).trans Q.2
        omega)

instance {α : Type*} [LinearOrder α] {a b : ℕ} (P : Sym α a) (Q : Sym α b) :
    Decidable (ColStrictSym' a b P Q) := Classical.propDecidable _

-- ============================================================
-- Target 1: Row decomposition bijection (HARD, ~80 lines)
-- ============================================================

/-- **Row decomposition for 2-row SSYTs**:
    The 2-row SSYT generating function = sum of weights over col-strict Sym pairs.

    Bijection φ : SSYTFin n 2 sh ≃ {(P,Q) | ColStrictSym' (sh 0) (sh 1) P Q}:
    - Forward: T ↦ (⟨ofList(ofFn row0), card_eq⟩, ⟨ofList(ofFn row1), card_eq⟩)
      where row0 j = T.1 ⟨⟨0,_⟩, j⟩ and row1 j = T.1 ⟨⟨1,_⟩, j⟩
    - ColStrict follows: T's col-strict says T.row0[j] < T.row1[j] for j < sh1
    - Backward: (P,Q) ↦ SSYT with T(0,j) = P.sort[j], T(1,j) = Q.sort[j]
    - Row-weak: sorted list is weakly-increasing
    - Weight = ∏_j X(row0[j]) * ∏_j X(row1[j]) by Fin.prod_univ_two -/
theorem ssytFin_two_row_eq_sum_colstrict' (n : ℕ) (sh : Fin 2 → ℕ) :
    ssytSchurFin' (R := R) n 2 sh =
    ∑ PQ : { PQ : Sym (Fin n) (sh 0) × Sym (Fin n) (sh 1) //
              ColStrictSym' (sh 0) (sh 1) PQ.1 PQ.2 },
      (PQ.1.1.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod *
      (PQ.1.2.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod := by
  sorry

-- ============================================================
-- Target 2: JDT weight sum (HARD, ~80 lines)
-- ============================================================

/-- **Jeu de taquin weight sum**:
    The sum of pair-weights over non-col-strict (a,b) pairs = h_{a+1} * h_{b-1}.

    Proof: weight-preserving bijection
      φ : {non-col-strict (P,Q) of shapes (a,b)} ≃ {all (P',Q') of shapes (a+1,b-1)}
    where c := min{j : P.sort[j] ≥ Q.sort[j]} (first violation column),
          v := Q.sort[c] (the violating Q element),
          P' := P.underlying + {v}  (multiset insert)
          Q' := Q.underlying.erase v  (multiset erase)
    Weight-preserved: wt(P)*wt(Q) = (P.1.map X).prod * (Q.1.map X).prod
                    = (P.1 + {v}).map X |>.prod * (Q.1.erase v).map X |>.prod
    since (Q.1.map X).prod = X v * ((Q.1.erase v).map X).prod by Multiset.prod_erase
    and ((P.1 + {v}).map X).prod = (P.1.map X).prod * X v by Multiset.prod_add.

    The bijection is invertible: the seam element v in P'.sort is uniquely
    identified as the element at the critical position for col-strict violation. -/
theorem jdt_weight_sum' (n a b : ℕ) :
    ∑ PQ : { PQ : Sym (Fin n) a × Sym (Fin n) b // ¬ColStrictSym' a b PQ.1 PQ.2 },
      (PQ.1.1.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod *
      (PQ.1.2.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod =
    hsymm (Fin n) R (a + 1) * (if 1 ≤ b then hsymm (Fin n) R (b - 1) else 0) := by
  sorry

end BallotJacobiTrudiAristotle
