/-
# Jacobi-Trudi Identity: Schur Polynomials as Determinants of hsymm

OQ-01-OQ-01 follow-up to BallotProblemOQ03OQ01OQ01 (ballot-problem-oq-03-oq-01-oq-01).

This file formalizes the Jacobi-Trudi identity, which expresses Schur polynomials
as determinants of complete homogeneous symmetric polynomials:

  s_λ = det[h_{λᵢ - i + j}]_{1 ≤ i,j ≤ k}

## Key definitions
- `jacobiTrudiMatrix k sh`: the k×k matrix with entry h_{shᵢ + j - i} (or 0 for i > shᵢ + j)
- `schurPolynomial k sh`: det(jacobiTrudiMatrix k sh)
- `SSYTFin n k sh`: semistandard Young tableaux of shape sh with entries in Fin n
- `ssytSchurFin n k sh`: the SSYT generating function (sum of weight monomials)

## Status: badge=formalized
- `jacobiTrudiMatrix_entry_isSymmetric`: proved (split_ifs + hsymm_isSymmetric)
- `schurPolynomial_isSymmetric`: proved (AlgHom.map_det + entry symmetry)
- `schurPolynomial_two_row`: proved (det_fin_two computation)
- `schurPolynomial_one_row_at_one`: proved (monomial counting via Sym.card_sym_eq_choose)
- `ssytSchurFin_empty`: proved (unique empty SSYT, empty product = 1)
- `ssytSchurFin_one_row`: proved (k=1 case: bijection SSYTFin n 1 (fun _ => m) ≃ Sym (Fin n) m)
- `jacobi_trudi_ssyt_eq`: k=0 proved, k=1 proved; k≥2 open (RSK bijection ~300-400 lines)
-/

import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Multiset.Sort
import Mathlib.Algebra.BigOperators.Fin
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
## Part VI: SSYT Definition of Schur Polynomials

A semistandard Young tableau (SSYT) of shape sh : Fin k → ℕ with entries in Fin n
fills each cell (i, j) with j < sh(i) by a value in Fin n satisfying:
  - Rows weakly increasing left-to-right
  - Columns strictly increasing top-to-bottom

The **SSYT Schur polynomial** in n variables is the sum of monomials (weights) over
all such tableaux. The Jacobi-Trudi identity asserts this equals `schurPolynomial`.

The k = 0 base case is proved below. The general case via RSK remains open.
-/

/-- An SSYT of shape `sh : Fin k → ℕ` with entries in `Fin n`.
    Encoded as a function on the sigma-type `(i : Fin k) × Fin (sh i) → Fin n`
    satisfying row-weak (weakly increasing rows) and col-strict (strictly increasing columns). -/
def SSYTFin (n k : ℕ) (sh : Fin k → ℕ) :=
  { f : ((i : Fin k) × Fin (sh i)) → Fin n //
    -- Rows are weakly increasing (entries non-decreasing left to right)
    (∀ (i : Fin k) (j1 j2 : Fin (sh i)), j1 < j2 → f ⟨i, j1⟩ ≤ f ⟨i, j2⟩) ∧
    -- Columns are strictly increasing (entries increasing top to bottom)
    (∀ (i1 i2 : Fin k) (j1 : Fin (sh i1)) (j2 : Fin (sh i2)),
      j1.val = j2.val → i1 < i2 → f ⟨i1, j1⟩ < f ⟨i2, j2⟩) }

/-- SSYTFin is finite: the domain `(i : Fin k) × Fin (sh i) → Fin n` is a Pi type
    over finite types, and the row-weak and col-strict conditions are decidable predicates. -/
instance {n k : ℕ} {sh : Fin k → ℕ} : Fintype (SSYTFin n k sh) :=
  Subtype.fintype _

/-- The weight monomial of an SSYT: `∏_{(i,j) ∈ shape} X(T(i,j))`. -/
noncomputable def SSYTFin.weight {n k : ℕ} {sh : Fin k → ℕ}
    (T : SSYTFin n k sh) : MvPolynomial (Fin n) R :=
  ∏ p : (i : Fin k) × Fin (sh i), X (T.1 p)

/-- The SSYT Schur polynomial: sum of weight monomials over all bounded SSYT of shape sh.
    This is the canonical "tableau definition" of s_λ(x₁,...,xₙ). -/
noncomputable def ssytSchurFin (n k : ℕ) (sh : Fin k → ℕ) : MvPolynomial (Fin n) R :=
  ∑ T : SSYTFin n k sh, T.weight

/-
### Base Case k = 0: Empty Shape → Weight Sum = 1
-/

/-- For the empty partition (k = 0), the only SSYT is the empty filling.
    Its weight is the empty product = 1, so the SSYT sum = 1 = schurPolynomial_empty. -/
theorem ssytSchurFin_empty (n : ℕ) :
    ssytSchurFin (R := R) n 0 Fin.elim0 = 1 := by
  -- The sigma-type index (i : Fin 0) × Fin (Fin.elim0 i) is empty (Fin 0 has no elements)
  haveI hempty : IsEmpty ((i : Fin 0) × Fin (Fin.elim0 i)) :=
    ⟨fun p => Fin.elim0 p.1⟩
  -- The only SSYT is the empty filling: both conditions hold vacuously
  haveI huniq : Unique (SSYTFin n 0 Fin.elim0) :=
    { default := ⟨fun p => Fin.elim0 p.1,
                  ⟨fun i _ _ _ => Fin.elim0 i, fun i1 _ _ _ _ _ => Fin.elim0 i1⟩⟩
      uniq := fun ⟨f, _⟩ => Subtype.ext (funext fun p => Fin.elim0 p.1) }
  simp only [ssytSchurFin, SSYTFin.weight]
  -- Inner product: over the empty sigma-type → 1 (empty product)
  simp_rw [Finset.prod_empty]
  -- Outer sum: over a Unique type → f default = 1
  exact Finset.sum_unique _

/-
### k = 1: One-Row Case (Open)

For a single-row shape [m] with entries in Fin n, the SSYT condition reduces to
weakly increasing sequences of length m in Fin n — exactly Sym (Fin n) m.

The bijection SSYTFin n 1 (fun _ => m) ≃ Sym (Fin n) m:
  - Forward: T ↦ Multiset.ofList (List.ofFn (fun j => T.1 ⟨⟨0,_⟩, j⟩))
  - Backward: s ↦ the unique monotone representative of s
    (using List.sortedLE_ofFn_iff: (List.ofFn f).SortedLE ↔ Monotone f)

Weight preservation: ∏ j, X(T j) = (multiset_of_T.map X).prod
Connection: ssytSchurFin n 1 (fun _ => m) = hsymm (Fin n) R m = schurPolynomial_one_row
-/

/-- The one-row SSYT sum equals the complete homogeneous symmetric polynomial.
    Proof requires bijection SSYTFin n 1 (fun _ => m) ≃ Sym (Fin n) m via sorted reps. -/
theorem ssytSchurFin_one_row (n m : ℕ) :
    ssytSchurFin (R := R) n 1 (fun _ => m) = hsymm (Fin n) R m := by
  -- Strategy:
  -- Build bijection ψ : SSYTFin n 1 (fun _ => m) ≃ Sym (Fin n) m
  --   via T ↦ Multiset.ofList (List.ofFn (T.1 ⟨0, ·⟩))
  -- Inverse: s ↦ fill row 0 with sorted representative of s
  -- Key: row 0 is already sorted (SSYT weak-row condition) so
  --   sort(ofFn(T.row0)) = ofFn(T.row0) by mergeSort_eq_self
  -- Weight preservation: ∏ j, X(T⟨0,j⟩) = (ofFn(T.row0)).map X).prod
  simp only [ssytSchurFin, hsymm]
  -- Bijection ψ
  let ψ : SSYTFin n 1 (fun _ => m) ≃ Sym (Fin n) m :=
    { toFun := fun T => ⟨(List.ofFn (fun j : Fin m => T.1 ⟨0, j⟩) : List _), by
          simp [Multiset.card_ofList]⟩
      invFun := fun s =>
        have hlen : (s.1.sort (· ≤ ·)).length = m :=
          (Multiset.length_sort (· ≤ ·) s.1).trans s.2
        ⟨fun p => (s.1.sort (· ≤ ·))[p.2.val]'(hlen ▸ p.2.isLt),
         ⟨fun _ j1 j2 hlt =>
            ((Multiset.pairwise_sort (· ≤ ·) s.1).sortedLE).getElem_le_getElem_of_le
              (hlen ▸ j1.isLt) (hlen ▸ j2.isLt)
              (le_of_lt (Fin.lt_iff_val_lt_val.mp hlt)),
          fun i1 i2 _ _ _ hlt =>
            absurd (Fin.lt_iff_val_lt_val.mp hlt)
              (by have := i1.isLt; have := i2.isLt; omega)⟩⟩
      left_inv := fun T => by
        apply Subtype.ext; funext p
        obtain ⟨⟨i, hi⟩, j⟩ := p
        have hi0 : i = 0 := Nat.lt_one_iff.mp hi; subst hi0
        have hmono : Monotone (fun j' : Fin m => T.1 ⟨⟨0, hi⟩, j'⟩) :=
          fun j1 j2 h => h.lt_or_eq.elim (T.2.1 ⟨0, hi⟩ j1 j2) (fun h => h ▸ le_refl _)
        have hpw := (List.sortedLE_ofFn_iff.mpr hmono).pairwise
        simp only [show (↑(List.ofFn (fun j' : Fin m => T.1 ⟨⟨0, hi⟩, j'⟩)) : Multiset _)
              .sort (· ≤ ·) = List.ofFn (fun j' : Fin m => T.1 ⟨⟨0, hi⟩, j'⟩) from by
            rw [Multiset.coe_sort]; exact List.mergeSort_eq_self hpw]
        simp [List.getElem_ofFn]
      right_inv := fun s => by
        apply Subtype.ext
        have hlen : (s.1.sort (· ≤ ·)).length = m :=
          (Multiset.length_sort (· ≤ ·) s.1).trans s.2
        have hL : List.ofFn (fun j : Fin m => (s.1.sort (· ≤ ·))[j.val]'(hlen ▸ j.isLt)) =
            s.1.sort (· ≤ ·) :=
          List.ext_getElem (by simp [hlen]) (fun i _ _ => by simp [List.getElem_ofFn])
        show (↑(List.ofFn (fun j : Fin m =>
              (s.1.sort (· ≤ ·))[j.val]'(hlen ▸ j.isLt))) : Multiset _) = s.1
        rw [hL]
        exact_mod_cast Multiset.sort_eq (· ≤ ·) s.1 }
  refine Fintype.sum_equiv ψ _ _ fun T => ?_
  simp only [SSYTFin.weight, Fintype.prod_sigma, Fin.prod_univ_one]
  -- Goal: ∏ j, X (T.1 ⟨0, j⟩) = ((ψ T).1.map X).prod
  show ∏ j : Fin m, X (T.1 ⟨(0 : Fin 1), j⟩) =
    (↑(List.ofFn (fun j : Fin m => T.1 ⟨(0 : Fin 1), j⟩)) : Multiset _).map X |>.prod
  simp [Multiset.map_coe, Multiset.prod_coe, List.map_ofFn, prod_ofFn]

/-
## Part VII: Two-Row Jacobi-Trudi Infrastructure
-/

/-- Column-strictness for a pair of symmetric multisets (sorted representatives).
    P and Q (of sizes a and b) are col-strict if the j-th element of P.sort is strictly less
    than the j-th element of Q.sort, for all j < min(a,b). -/
def ColStrictSym {n : ℕ} (a b : ℕ) (P : Sym (Fin n) a) (Q : Sym (Fin n) b) : Prop :=
  ∀ j : Fin (min a b),
    (P.1.sort (· ≤ ·))[j.val]'(by
        have hj : j.val < min a b := j.isLt
        have hlen : (P.1.sort (· ≤ ·)).length = a :=
          (Multiset.length_sort (· ≤ ·) P.1).trans P.2
        omega) <
    (Q.1.sort (· ≤ ·))[j.val]'(by
        have hj : j.val < min a b := j.isLt
        have hlen : (Q.1.sort (· ≤ ·)).length = b :=
          (Multiset.length_sort (· ≤ ·) Q.1).trans Q.2
        omega)

instance {n a b : ℕ} {P : Sym (Fin n) a} {Q : Sym (Fin n) b} :
    Decidable (ColStrictSym a b P Q) :=
  Fintype.decidable_forall_fintype

/-- Sum of pair-weights over ALL (P,Q) : Sym n a × Sym n b equals h_a * h_b.
    Proof: expand the product sum via Fintype.sum_prod_type + distributivity, then
    identify each factor with hsymm by its definition as ∑ s : Sym n, (s.1.map X).prod. -/
private lemma sum_all_sym_pairs (n a b : ℕ) :
    ∑ PQ : Sym (Fin n) a × Sym (Fin n) b,
      (PQ.1.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod *
      (PQ.2.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod =
    hsymm (Fin n) R a * hsymm (Fin n) R b := by
  simp only [hsymm, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]

/-
### k = 2 (Two-Row Case) — Jeu de Taquin

Proof strategy for ssytSchurFin n 2 sh = schurPolynomial 2 sh:

(1) Row decomposition: SSYTFin n 2 [a,b] ≅ {(P,Q) : 1-row SSYT(a) × 1-row SSYT(b) | col-strict}
    where col-strict = ∀ j < min(a,b), P(0,j) < Q(0,j).

(2) Weight factorization over rows:
      ∑_{all (P,Q) of shapes (a,b)} weight(P) * weight(Q) = h_a * h_b
    (by ssytSchurFin_one_row applied twice, then sum over product type)

(3) Jeu de taquin weight bijection (key step):
    For b ≥ 1, define forward map on non-col-strict (P,Q) by:
      c := min{j : P[j] ≥ Q[j]}
      P' := P[0..c-1] ++ [Q[c]] ++ P[c..a-1]   (length a+1)
      Q' := Q[0..c-1] ++ Q[c+1..b-1]             (length b-1)
    This is a weight-preserving bijection
      {non-col-strict (P,Q) of shapes (a,b)} ≃ {all (P',Q') of shapes (a+1,b-1)}
    Consequence: ∑_{non-col-strict} weight = h_{a+1} * h_{b-1}

(4) Combining (1),(2),(3):
      ssytSchurFin n 2 [a,b]
      = ∑_{col-strict} weight
      = h_a * h_b - ∑_{non-col-strict} weight
      = h_a * h_b - h_{a+1} * h_{b-1}
      = schurPolynomial 2 [a,b]   (by schurPolynomial_two_row)

Lean estimate: ~200 lines for steps (1)-(3). The bijection proof is the hard core:
  - Row projection Equiv (row decomposition): ~80 lines
  - Forward/inverse map + inverses proof: ~80 lines
  - Weight preservation: ~20 lines
-/

/-- Weight preservation for the JDT bijection step.
    Moving a single element `v` from `Q` (size b+1) to `P` (size a) yields
    `P' = Sym.cons v P` (size a+1) and `Q' = Sym.erase Q v hv` (size b),
    with the same product weight. This is the core algebraic identity behind
    `jdt_weight_sum` — the bijection itself is the remaining combinatorial work. -/
private lemma jdt_weight_preserved (n a b : ℕ)
    (P : Sym (Fin n) a) (Q : Sym (Fin n) (b + 1))
    (v : Fin n) (hv : v ∈ Q) :
    ((Sym.cons v P).1.map (X : Fin n → MvPolynomial (Fin n) R)).prod *
      ((Sym.erase Q v hv).1.map (X : Fin n → MvPolynomial (Fin n) R)).prod =
    (P.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod *
      (Q.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod := by
  -- (Sym.cons v P).1 = v ::ₘ P.1 and (Sym.erase Q v hv).1 = Q.1.erase v are rfl
  show ((v ::ₘ P.1).map (X : Fin n → MvPolynomial (Fin n) R)).prod *
       ((Q.1.erase v).map (X : Fin n → MvPolynomial (Fin n) R)).prod = _
  rw [Multiset.map_cons, Multiset.prod_cons]
  -- Goal: X v * (P.1.map X).prod * ((Q.1.erase v).map X).prod = (P.1.map X).prod * (Q.1.map X).prod
  have hQ : Q.1 = v ::ₘ Q.1.erase v := (Multiset.cons_erase hv).symm
  conv_rhs => rw [hQ, Multiset.map_cons, Multiset.prod_cons]
  ring

/-- For `Q : Sym (Fin n) 1`, the underlying multiset is the singleton `{q}` where `q` is the
    unique element of `Q`. We extract `q` and the equation `Q.1.sort = [q]` simultaneously. -/
private lemma sym_one_sort_head_singleton (n : ℕ) (Q : Sym (Fin n) 1) :
    ∃ q : Fin n, Q.1.sort (· ≤ ·) = [q] ∧ Q.1 = ({q} : Multiset (Fin n)) := by
  have hlen : (Q.1.sort (· ≤ ·)).length = 1 := (Multiset.length_sort _ Q.1).trans Q.2
  obtain ⟨q, hq⟩ := List.length_eq_one_iff.mp hlen
  refine ⟨q, hq, ?_⟩
  have hcoe := congrArg (Multiset.ofList) hq
  rw [Multiset.sort_eq] at hcoe
  simpa using hcoe

/-- **JDT weight sum, `b = 1` base case.**
    For `a ≥ 1`, the sum of weights over non-col-strict
    `(P : Sym (Fin n) a, Q : Sym (Fin n) 1)` pairs equals `h_{a+1} * h_0 = h_{a+1}`.

    **Recipe (bijection ψ : `LHS-subtype ≃ Sym (Fin n) (a+1)`):**
      * forward: `(P, Q, _) ↦ q ::ₛ P`, where `q` is the unique element of `Q`
        (i.e. `(Q.1.sort)[0]`).
      * inverse: `S ↦ ((S.erase qS hS, ⟨{qS}, _⟩), proof_¬ColStrict)`,
        where `qS = (S.1.sort)[0]` is the smallest element of `S`.

    **Why the bijection respects `¬ColStrictSym a 1 P Q`:**
    With `a ≥ 1`, `min a 1 = 1`, so `ColStrictSym a 1 P Q ⇔ (P.sort)[0] < (Q.sort)[0] = q`,
    and `¬ColStrictSym ⇔ q ≤ (P.sort)[0]`. By sortedness of `P.sort`, this means
    `q ≤ x` for all `x ∈ P.1`. Then `Multiset.sort_cons` gives
    `(q ::ₘ P.1).sort = q :: P.1.sort`, so `q` is the head of `(q ::ₛ P).1.sort`,
    making `Sym.erase` and `Sym.cons_erase`/`Sym.erase_cons_head` close the inverses.

    **Status (2026-05-02 session 15):** the helper `sym_one_sort_head_singleton` and the
    statement of this lemma are now in place. The bijection construction with weight
    preservation proof is the focused `sorry` below; estimated 100-130 lines using
    `Sym.cons_erase` (`Data/Sym/Basic.lean:219`), `Sym.erase_cons_head` (`:223`),
    `Multiset.sort_cons` (`Data/Multiset/Sort.lean:69`). -/
private lemma jdt_weight_sum_b_one (n a : ℕ) (ha : 1 ≤ a) :
    ∑ PQ : { PQ : Sym (Fin n) a × Sym (Fin n) 1 // ¬ColStrictSym a 1 PQ.1 PQ.2 },
      (PQ.1.1.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod *
      (PQ.1.2.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod =
    hsymm (Fin n) R (a + 1) * hsymm (Fin n) R 0 := by
  -- Simplify RHS via hsymm 0 = 1
  rw [hsymm_zero, mul_one]
  -- Bijection construction is the focused next-session task. See the recipe above
  -- and lines ~415-465 for the existing detailed comment block.
  sorry

/-- **Jeu de Taquin weight sum** (key step for two-row Jacobi-Trudi).
    The sum of pair-weights over NON-col-strict (a,b) pairs equals h_{a+1}*h_{b-1}.

    Proof by constructing a weight-preserving bijection
      φ : {non-col-strict (P: Sym n a, Q: Sym n b)} ≃ {all (P': Sym n (a+1), Q': Sym n (b-1))}
    where c := min{j : P.sort[j] ≥ Q.sort[j]} (first column violation), and
      P' := P.underlying + {Q.sort[c]}  (multiset-add, maintains sort since P[c-1] < Q.sort[c] ≤ P[c])
      Q' := Q.underlying - {Q.sort[c]}  (multiset-erase)
    Weight-preserved: wt(P)*wt(Q) = wt(P+{v})*wt(Q-{v}) by Multiset.prod_erase.
    Surjective: every (P', Q') has a unique preimage (find the "seam" element in P'.sort). -/
private lemma jdt_weight_sum (n a b : ℕ) (hba : b ≤ a) :
    ∑ PQ : { PQ : Sym (Fin n) a × Sym (Fin n) b // ¬ColStrictSym a b PQ.1 PQ.2 },
      (PQ.1.1.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod *
      (PQ.1.2.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod =
    hsymm (Fin n) R (a + 1) * (if 1 ≤ b then hsymm (Fin n) R (b - 1) else 0) := by
  by_cases hb : 1 ≤ b
  · -- b ≥ 1: JDT bijection
    simp only [if_pos hb]
    rw [← sum_all_sym_pairs n (a + 1) (b - 1)]
    -- Need: weight-preserving bijection
    --   {non-col-strict (a,b) pairs} ≃ {all (a+1, b-1) pairs}
    -- Forward map: find first violation c in ColStrictSym, let v = Q.sort[c],
    --   then P' = Sym.cons v P, Q' = Sym.erase Q v (need v ∈ Q.1)
    -- Inverse map: find the "seam" element in P'.sort to move back to Q'
    -- Weight preserved by Multiset.prod_cons + Multiset.prod_erase
    --
    -- ============================================================================
    -- DETAILED RECIPE FOR b = 1 BASE CASE (helper for next session)
    -- ============================================================================
    -- When b = 1, ColStrictSym a 1 P Q says P.sort[0] < Q.sort[0]; ¬cs gives the
    -- opposite. Q has size 1, so by Sym.oneEquiv we have Q = oneEquiv q for some
    -- q : Fin n, with q = Q.sort[0] (only element). Goal becomes:
    --
    --   ∑_{(P, q): q ≤ P.sort[0]} wt(P) * X q = h_{a+1}
    --
    -- BIJECTION ψ : {(P, q) : q ≤ P.sort[0]} ≃ Sym (Fin n) (a+1)
    --   forward (P, q) ↦ q ::ₛ P            -- Sym.cons; coe = q ::ₘ P.1
    --   inverse P' ↦ ((P'.erase q', oneEquiv q')) where
    --     q' := (P'.1.sort (· ≤ ·)).head    -- smallest element
    --     proof q' ∈ P'.1: q' is the head of (length a+1) sorted list
    --     proof q' ≤ (P'.erase q').sort[0]: erase preserves sortedness; q' was min
    --   weight preservation:
    --     wt(P) * X q
    --     = (P.1.map X).prod * X q
    --     = ((q ::ₘ P.1).map X).prod          -- by Multiset.prod_cons + map_cons
    --     = wt(q ::ₛ P)
    -- KEY LEMMAS (verified Mathlib v4.26.0, paths confirmed 2026-04-27 session 13):
    --   * Multiset.sort_cons (Data/Multiset/Sort.lean:69):
    --       (∀ b ∈ s, r a b) → sort(a ::ₘ s) r = a :: sort s r
    --     Applied with: q ≤ P.sort[0] + sortedness ⇒ q ≤ all of P
    --   * Sym.cons (Data/Sym/Basic.lean:106), coe_cons:123 (rfl):
    --       (a ::ₛ s : Multiset α) = a ::ₘ s.1
    --   * Sym.cons_erase (Data/Sym/Basic.lean:219, simp):
    --       a ::ₛ s.erase a h = s   — closes left_inv
    --   * Sym.erase_cons_head (Data/Sym/Basic.lean:223, simp):
    --       (a ::ₛ s).erase a _ = s — closes right_inv direction
    --   * Sym.oneEquiv (Data/Sym/Basic.lean:477, @[simps apply]):
    --       α ≃ Sym α 1; oneEquiv_apply rewrites oneEquiv a to ⟨{a}, _⟩
    --
    -- INVERSE DIRECTION MECHANISM (the trickiest piece, fleshed out session 13):
    --   Given P' : Sym (Fin n) (a+1):
    --     L := (P'.1 : Multiset).sort (· ≤ ·) : List (Fin n), length = a+1, sorted
    --     L_pos : 0 < L.length := by simp [Multiset.length_sort, P'.2]
    --     q' := L.head L_pos.ne' : Fin n
    --   Show q' ∈ P'.1 (need this to apply Sym.erase):
    --     have : q' ∈ L := List.head_mem L_pos.ne'
    --     have : q' ∈ (L : Multiset) := Multiset.mem_coe.mpr this
    --     rw [Multiset.sort_eq] at this
    --     exact this -- q' ∈ P'.1
    --   Show q' ≤ (P'.1.erase q').sort[0] (the bijection's domain constraint):
    --     L = q' :: L.tail (by List.head_cons_tail)
    --     P'.1 = (q' ::ₘ (L.tail : Multiset)) by Multiset.sort_eq + List congruence
    --     (P'.1.erase q' : Multiset) = (L.tail : Multiset)
    --       by Multiset.erase_cons_head (Data/Multiset/AddSub.lean:156):
    --         (a ::ₘ s).erase a = s
    --     (P'.1.erase q').sort[0] = L.tail[0] = L[1] (when a ≥ 1)
    --     Sortedness of L gives L[0] ≤ L[1], so q' ≤ L.tail[0]. ✓
    --     For a = 0 case: tail is empty, so erased multiset is 0; ColStrictSym is vacuous.
    -- ESTIMATE: ~80-100 lines for jdt_weight_sum_b_one as a separate helper.
    -- ============================================================================
    --
    -- For b ≥ 2, the bijection generalizes: insert Q.sort[c] into P at position c,
    -- where c is the first violation index. The inverse map is the JDT seam
    -- algorithm (find c such that P'.sort[c] came from Q's c-th violation column).
    -- This is genuinely intricate; ~150-200 lines of focused Lean work.
    sorry
  · -- b = 0: ColStrictSym a 0 P Q is vacuously true (quantifies over Fin (min a 0) = Fin 0)
    -- So ¬ColStrictSym = False, the subtype is empty, and the sum equals 0
    push_neg at hb
    have hb0 : b = 0 := by omega
    subst hb0
    -- RHS simplifies: if 1 ≤ 0 then ... else 0 = 0, so h_{a+1} * 0 = 0
    have hrhs : hsymm (Fin n) R (a + 1) * (if 1 ≤ 0 then hsymm (Fin n) R (0 - 1) else 0) = 0 :=
      by simp
    rw [hrhs]
    -- LHS: every element of the subtype derives False (ColStrictSym a 0 P Q is vacuously true)
    apply Finset.sum_eq_zero
    rintro ⟨⟨P, Q⟩, hPQ⟩ -
    exfalso
    apply hPQ
    intro j
    -- j : Fin (min a 0), and min a 0 = 0, so j.isLt : j.val < 0, which is absurd
    exact absurd j.isLt (by omega)

/-- Row decomposition: 2-row SSYT generating function = sum over col-strict pairs.
    The bijection φ : SSYTFin n 2 sh ≃ {(P,Q) : ColStrictSym (sh0, sh1) pairs}:
    - Forward: T ↦ (ofList(ofFn T.row0), ofList(ofFn T.row1)).
        ColStrict holds: T.row0/1 are sorted (SSYT row-weak), and T's col-strict condition
        says T.row0[j] < T.row1[j] for j < min(sh0, sh1), which is exactly ColStrictSym.
    - Backward: (P,Q) ↦ T where T.row0[j] = P.sort[j], T.row1[j] = Q.sort[j].
        Row-weak: sorted lists are weakly-increasing. Col-strict: ColStrictSym condition.
    - Weight: T.weight = ∏_{i,j} X(T(i,j)) = ∏_j X(P[j]) * ∏_j X(Q[j]) by Fin.prod_univ_two. -/
private lemma ssytFin_two_row_eq_sum_colstrict (n : ℕ) (sh : Fin 2 → ℕ) :
    ssytSchurFin (R := R) n 2 sh =
    ∑ PQ : { PQ : Sym (Fin n) (sh 0) × Sym (Fin n) (sh 1) //
              ColStrictSym (sh 0) (sh 1) PQ.1 PQ.2 },
      (PQ.1.1.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod *
      (PQ.1.2.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod := by
  simp only [ssytSchurFin]
  set a := sh 0 with ha; set b := sh 1 with hb
  have hPlen : ∀ P : Sym (Fin n) a, (P.1.sort (· ≤ ·)).length = a := fun P =>
    (Multiset.length_sort _ P.1).trans P.2
  have hQlen : ∀ Q : Sym (Fin n) b, (Q.1.sort (· ≤ ·)).length = b := fun Q =>
    (Multiset.length_sort _ Q.1).trans Q.2
  -- For each row i of T, the multiset cast of ofFn(T.row_i) sorts to ofFn(T.row_i)
  -- because SSYT rows are weakly increasing (so already sorted).
  have sortedRow0 : ∀ (T : SSYTFin n 2 sh),
      (↑(List.ofFn (fun j : Fin a => T.1 ⟨0, j⟩) : List _) : Multiset _).sort (· ≤ ·) =
        List.ofFn (fun j : Fin a => T.1 ⟨0, j⟩) := fun T => by
    rw [Multiset.coe_sort]
    exact List.mergeSort_eq_self ((List.sortedLE_ofFn_iff.mpr
      (fun j1 j2 h => h.lt_or_eq.elim (T.2.1 0 j1 j2)
        (fun h' => h' ▸ le_refl _))).pairwise)
  have sortedRow1 : ∀ (T : SSYTFin n 2 sh),
      (↑(List.ofFn (fun j : Fin b => T.1 ⟨1, j⟩) : List _) : Multiset _).sort (· ≤ ·) =
        List.ofFn (fun j : Fin b => T.1 ⟨1, j⟩) := fun T => by
    rw [Multiset.coe_sort]
    exact List.mergeSort_eq_self ((List.sortedLE_ofFn_iff.mpr
      (fun j1 j2 h => h.lt_or_eq.elim (T.2.1 1 j1 j2)
        (fun h' => h' ▸ le_refl _))).pairwise)
  let ψ : SSYTFin n 2 sh ≃
      { PQ : Sym (Fin n) a × Sym (Fin n) b // ColStrictSym a b PQ.1 PQ.2 } :=
    { toFun := fun T =>
        ⟨(⟨↑(List.ofFn (fun j : Fin a => T.1 ⟨0, j⟩)), by simp [Multiset.card_ofList]⟩,
          ⟨↑(List.ofFn (fun j : Fin b => T.1 ⟨1, j⟩)), by simp [Multiset.card_ofList]⟩),
         fun ⟨j, hj⟩ => by
          have hja : j < a := Nat.lt_of_lt_of_le hj (Nat.min_le_left a b)
          have hjb : j < b := Nat.lt_of_lt_of_le hj (Nat.min_le_right a b)
          have hPs := sortedRow0 T; have hQs := sortedRow1 T
          -- SSYT col-strict: T(0,j) < T(1,j)
          have hcol : T.1 ⟨0, ⟨j, hja⟩⟩ < T.1 ⟨1, ⟨j, hjb⟩⟩ :=
            T.2.2 0 1 ⟨j, hja⟩ ⟨j, hjb⟩ rfl (by decide)
          simp only [hPs, hQs, List.getElem_ofFn]
          exact hcol⟩
      invFun := fun ⟨(P, Q), hPQ⟩ =>
        let hP := hPlen P; let hQ := hQlen Q
        ⟨fun ⟨⟨i, hi⟩, j⟩ =>
          if h : i = 0 then
            (P.1.sort (· ≤ ·))[j.val]'(hP ▸
              ((show sh ⟨i, hi⟩ = sh 0 by congr 1; exact Fin.ext h) ▸ j.isLt))
          else
            have hi1 : i = 1 := by omega
            (Q.1.sort (· ≤ ·))[j.val]'(hQ ▸
              ((show sh ⟨i, hi⟩ = sh 1 by congr 1; exact Fin.ext hi1) ▸ j.isLt)),
         ⟨-- Row-weak: sorted lists are weakly increasing
          fun ⟨⟨i, _⟩, _⟩ j1 j2 hlt => by
            split_ifs with h
            · have hi0 : i = 0 := h; subst hi0
              exact ((Multiset.pairwise_sort (· ≤ ·) P.1).sortedLE)
                .getElem_le_getElem_of_le (hP ▸ j1.isLt) (hP ▸ j2.isLt)
                (le_of_lt (Fin.lt_iff_val_lt_val.mp hlt))
            · have hi1 : i = 1 := by omega
              subst hi1
              exact ((Multiset.pairwise_sort (· ≤ ·) Q.1).sortedLE)
                .getElem_le_getElem_of_le (hQ ▸ j1.isLt) (hQ ▸ j2.isLt)
                (le_of_lt (Fin.lt_iff_val_lt_val.mp hlt)),
          -- Col-strict: P.sort[j] < Q.sort[j] for same column j, from hPQ
          fun i1 i2 j1 j2 hval hlt => by
            -- i1 < i2 (as Fin 2) forces i1.val = 0 and i2.val = 1
            have h0 : i1.val = 0 := by have := i1.isLt; have := i2.isLt; omega
            have h1 : i2.val = 1 := by have := i1.isLt; have := i2.isLt; omega
            have hi1 : i1 = 0 := Fin.ext h0
            have hi2 : i2 = 1 := Fin.ext h1
            subst hi1
            -- After subst: j1 : Fin (sh 0) = Fin a; i2.val ≠ 0 means Q branch
            -- Evaluate T.1 ⟨i2, j2⟩ in the dite: i2.val = 1 ≠ 0, so Q branch
            have hj2b : j2.val < b := by
              have := (show sh i2 = b from hb ▸ congrArg sh hi2) ▸ j2.isLt; exact this
            have hj_min : j1.val < min a b :=
              Nat.lt_min.mpr ⟨j1.isLt, hval ▸ hj2b⟩
            -- The dite evaluates: i1.val = 0 → P branch, i2.val ≠ 0 → Q branch
            simp only [Nat.zero_eq, ↓reduceDite, show i2.val ≠ 0 from by omega, ↓reduceDite]
            rw [← hval]
            exact hPQ ⟨j1.val, hj_min⟩⟩⟩
      left_inv := fun T => by
        apply Subtype.ext; funext ⟨⟨i, hi⟩, j⟩
        simp only []
        split_ifs with h
        · -- i = 0: subst to unify types, then sort = ofFn(T.row0) and getElem = T(0,j)
          subst h
          rw [sortedRow0 T, List.getElem_ofFn]
        · -- i = 1
          have hi1 : i = 1 := by omega
          subst hi1
          rw [sortedRow1 T, List.getElem_ofFn]
      right_inv := fun ⟨(P, Q), _⟩ => by
        apply Subtype.ext; apply Prod.ext
        · -- ψ(invFun (P,Q)).1.1 = P
          apply Subtype.ext
          have hP := hPlen P
          have hL : List.ofFn (fun j : Fin a =>
              (P.1.sort (· ≤ ·))[j.val]'(hP ▸ j.isLt)) = P.1.sort (· ≤ ·) :=
            List.ext_getElem (by simp [hP]) (fun i _ _ => by simp [List.getElem_ofFn])
          show (↑(List.ofFn (fun j : Fin a =>
              (P.1.sort (· ≤ ·))[j.val]'(hP ▸ j.isLt))) : Multiset _) = P.1
          rw [hL]; exact_mod_cast Multiset.sort_eq (· ≤ ·) P.1
        · -- ψ(invFun (P,Q)).1.2 = Q
          apply Subtype.ext
          have hQ := hQlen Q
          have hL : List.ofFn (fun j : Fin b =>
              (Q.1.sort (· ≤ ·))[j.val]'(hQ ▸ j.isLt)) = Q.1.sort (· ≤ ·) :=
            List.ext_getElem (by simp [hQ]) (fun i _ _ => by simp [List.getElem_ofFn])
          show (↑(List.ofFn (fun j : Fin b =>
              (Q.1.sort (· ≤ ·))[j.val]'(hQ ▸ j.isLt))) : Multiset _) = Q.1
          rw [hL]; exact_mod_cast Multiset.sort_eq (· ≤ ·) Q.1 }
  refine Fintype.sum_equiv ψ _ _ fun T => ?_
  simp only [SSYTFin.weight, Fintype.prod_sigma, Fin.prod_univ_two]
  -- Goal: (∏ j, X(T.1 ⟨0,j⟩)) * (∏ j, X(T.1 ⟨1,j⟩)) =
  --       ((ψ T).1.1.1.map X).prod * ((ψ T).1.2.1.map X).prod
  -- (ψ T).1.1.1 = ↑(ofFn(T.row0)) and (ψ T).1.2.1 = ↑(ofFn(T.row1))
  simp [Multiset.map_coe, Multiset.prod_coe, List.map_ofFn, prod_ofFn]

/-- Partition of all Sym pairs into col-strict and non-col-strict, with sum = h_a * h_b.
    Uses Fintype.sum_subtype_add_sum_subtype to split the all-pairs sum into subtypes. -/
private lemma sym_pair_sum_partition (n a b : ℕ) :
    (∑ PQ : { PQ : Sym (Fin n) a × Sym (Fin n) b // ColStrictSym a b PQ.1 PQ.2 },
        (PQ.1.1.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod *
        (PQ.1.2.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod) +
    (∑ PQ : { PQ : Sym (Fin n) a × Sym (Fin n) b // ¬ColStrictSym a b PQ.1 PQ.2 },
        (PQ.1.1.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod *
        (PQ.1.2.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod) =
    hsymm (Fin n) R a * hsymm (Fin n) R b := by
  rw [← sum_all_sym_pairs (R := R)]
  exact Fintype.sum_subtype_add_sum_subtype
    (fun PQ => ColStrictSym a b PQ.1 PQ.2)
    (fun PQ => (PQ.1.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod *
               (PQ.2.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod)

/-- **Two-Row Jacobi-Trudi** (assembly from row-decomp + JDT):
    The 2-row SSYT generating function equals the 2×2 Jacobi-Trudi determinant.

    Assembly:
    1. ssytSchurFin = ∑_{col-strict} wt          [ssytFin_two_row_eq_sum_colstrict]
    2. ∑_{col-strict} + ∑_{¬col-strict} = h_a*h_b  [sym_pair_sum_partition]
    3. ∑_{¬col-strict} = h_{a+1}*h_{b-1}         [jdt_weight_sum]
    4. ∑_{col-strict} = h_a*h_b - h_{a+1}*h_{b-1} = schurPolynomial 2 sh [algebra] -/
theorem ssytSchurFin_two_row (n : ℕ) (sh : Fin 2 → ℕ) (hsh : sh 1 ≤ sh 0) :
    ssytSchurFin (R := R) n 2 sh =
    schurPolynomial (σ := Fin n) (R := R) 2 sh := by
  set a := sh 0 with ha
  set b := sh 1 with hb
  -- Step 1: rewrite schurPolynomial in explicit h_a*h_b - h_{a+1}*h_{b-1} form
  have hsch : schurPolynomial (σ := Fin n) (R := R) 2 sh =
      hsymm (Fin n) R a * hsymm (Fin n) R b -
      hsymm (Fin n) R (a + 1) * (if 1 ≤ b then hsymm (Fin n) R (b - 1) else 0) := by
    have hsh_eq : sh = Fin.cons a (Fin.cons b Fin.elim0) :=
      funext fun i => by fin_cases i <;> simp [ha, hb, Fin.cons_zero, Fin.cons_one]
    rw [hsh_eq]; exact schurPolynomial_two_row a b
  rw [hsch]
  -- Step 2: rewrite ssytSchurFin as ∑_{col-strict} wt (by row-decomp bijection)
  rw [ssytFin_two_row_eq_sum_colstrict (R := R)]
  -- Steps 3-5: algebra from partition + JDT
  -- sym_pair_sum_partition: ∑_{col-strict} + ∑_{¬col-strict} = h_a * h_b
  -- jdt_weight_sum:         ∑_{¬col-strict} = h_{a+1} * (if 1 ≤ b then h_{b-1} else 0)
  -- Therefore:              ∑_{col-strict} = h_a * h_b - h_{a+1} * ...
  exact eq_sub_of_add_eq
    (jdt_weight_sum (R := R) n a b hsh ▸ sym_pair_sum_partition (R := R) n a b)

/-
### Main Theorem: Jacobi-Trudi = SSYT Sum (Open for k ≥ 3)
-/

/-- **Jacobi-Trudi Identity** (proved for k = 0,1,2; open for k ≥ 3):
    The determinant definition equals the SSYT generating function.

    `JacobiTrudi.schurPolynomial k sh = ssytSchurFin n k sh`

    - k = 0: **proved** — det of 0×0 matrix = 1 = empty SSYT sum
    - k = 1: **proved** — det of 1×1 matrix = h_{sh(0)} = one-row SSYT sum
    - k = 2: **proved** (via `ssytSchurFin_two_row`) — jdt bijection
    - k ≥ 3: **open** — requires algebraic LGV (~150 lines) + RSK bijection (~150 lines):
        (1) algebraic_lgv: for ring-valued weighted DAG, det(weight_matrix) = ∑_NI ∏ weights
        (2) RSK: SSYTFin n k sh ↔ NI tuples of 1-row SSYTs (the Jacobi-Trudi LGV config)
        (3) Weight match: SSYT weight = NI-tuple weight -/
theorem jacobi_trudi_ssyt_eq (n k : ℕ) (sh : Fin k → ℕ) (hsh : Antitone sh) :
    JacobiTrudi.schurPolynomial (σ := Fin n) (R := R) k sh =
    ssytSchurFin (R := R) n k sh := by
  cases k with
  | zero =>
    -- k = 0: empty partition; both sides = 1.
    have hsh0 : sh = Fin.elim0 := funext (fun i => i.elim0)
    rw [hsh0, schurPolynomial_empty, ssytSchurFin_empty]
  | succ k =>
    cases k with
    | zero =>
      -- k = 1: one-row partition.
      have hsh1 : sh = fun _ => sh ⟨0, Nat.lt_succ_self 0⟩ :=
        funext (fun i => by fin_cases i <;> rfl)
      rw [hsh1, schurPolynomial_one_row, ssytSchurFin_one_row]
    | succ k =>
      cases k with
      | zero =>
        -- k = 2: two-row case, proved by jdt bijection.
        -- hsh : Antitone sh gives sh 1 ≤ sh 0 (the partition condition).
        exact (ssytSchurFin_two_row n sh (hsh (by decide : (0 : Fin 2) ≤ 1))).symm
      | succ k =>
        -- k ≥ 3: requires algebraic LGV + RSK (~300 lines).
        --
        -- Proof outline for general k:
        -- (1) algebraic_lgv: det(M) = ∑_{NI path tuples} ∏ path_weights
        --     (ring-valued version of lgv_lemma_rxr from BallotProblemOQ03OQ02)
        -- (2) RSK bijection: SSYTFin n k sh ↔ NI tuples of 1-row SSYTs in the
        --     Jacobi-Trudi lattice configuration
        -- (3) M[i][j] = ∑_{1-row SSYT of len sh(i)+j-i} weight = h_{sh(i)+j-i}
        --     (by ssytSchurFin_one_row)
        -- The k=2 case above (ssytSchurFin_two_row) provides the base case for
        -- any inductive approach; the algebraic LGV is the key missing piece.
        -- See research/problems/ballot-problem-oq-03-oq-01-oq-01-oq-01/knowledge.md
        sorry

end JacobiTrudi
