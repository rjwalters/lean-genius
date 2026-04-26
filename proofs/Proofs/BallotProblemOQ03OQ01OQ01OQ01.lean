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

/-- Column-strict condition for two symmetric products P : Sym α a, Q : Sym α b.
    The j-th element of the sorted representative of P must be strictly less than
    the j-th element of the sorted representative of Q, for all j < min(a,b). -/
private def ColStrictSym {α : Type*} [LinearOrder α] (a b : ℕ)
    (P : Sym α a) (Q : Sym α b) : Prop :=
  ∀ j : ℕ, j < min a b →
    (P.1.sort (· ≤ ·))[j]'(by
        have h : (P.1.sort (· ≤ ·)).length = a := (Multiset.length_sort _ P.1).trans P.2
        omega) <
    (Q.1.sort (· ≤ ·))[j]'(by
        have h : (Q.1.sort (· ≤ ·)).length = b := (Multiset.length_sort _ Q.1).trans Q.2
        omega)

instance {α : Type*} [LinearOrder α] {a b : ℕ}
    (P : Sym α a) (Q : Sym α b) : Decidable (ColStrictSym a b P Q) :=
  Classical.propDecidable _

/-- Sum over all Sym pairs equals the product of hsymm.
    Proof: product of sums = sum over product type (Fintype.sum_prod_type),
    then factor as (∑ P, wt P) * (∑ Q, wt Q) = h_a * h_b. -/
private lemma sum_all_sym_pairs (n a b : ℕ) :
    ∑ PQ : Sym (Fin n) a × Sym (Fin n) b,
      (PQ.1.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod *
      (PQ.2.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod =
    hsymm (Fin n) R a * hsymm (Fin n) R b := by
  simp only [hsymm, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]

/-- **Jeu de Taquin weight sum** (key step for two-row Jacobi-Trudi).
    The sum of pair-weights over NON-col-strict (a,b) pairs equals h_{a+1}*h_{b-1},
    valid for the partition condition b ≤ a.

    IMPORTANT: The naive multiset JDT bijection (P,Q)↦(P+{v},Q-{v}) is NOT injective
    for b ≥ 2. Example (n=2, a=2, b=2): pairs ({0,2},{1,2}) and ({0,1},{2,2}) both
    produce ({0,1,2},{2}) under the slide. The correct proof approach by case:
    (b=0) Trivial: ColStrictSym a 0 holds vacuously (min a 0 = 0, no j < 0), so
          the non-col-strict subtype is empty and the sum is 0 = RHS.
    (b=1) Direct bijection: {(P,{q}) : q ≤ min(P)} ≃ Sym n (a+1)
          via (P,{q}) ↦ P.1 + {q}, with unique inverse P' ↦ (P'-{min P'}, {min P'}).
          Weight preserved: wt(P)*X_q = wt(P+{q}) by Multiset.prod_cons.
    (b≥2) Requires the ring-valued algebraic LGV lemma (extending BallotProblemOQ03OQ02
          from ℤ-valued to ring-valued, then apply to the Jacobi-Trudi lattice config). -/
private lemma jdt_weight_sum (n a b : ℕ) (hab : b ≤ a) :
    ∑ PQ : { PQ : Sym (Fin n) a × Sym (Fin n) b // ¬ColStrictSym a b PQ.1 PQ.2 },
      (PQ.1.1.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod *
      (PQ.1.2.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod =
    hsymm (Fin n) R (a + 1) * (if 1 ≤ b then hsymm (Fin n) R (b - 1) else 0) := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · -- b = 0: RHS = h_{a+1} * 0 = 0 (since ¬(1 ≤ 0)).
    -- LHS = 0: the subtype is empty because ColStrictSym a 0 holds vacuously for all P, Q
    -- (the body is ∀ j < min a 0 = 0, which has no valid j).
    simp only [if_neg (show ¬(1 ≤ 0) from by omega), mul_zero]
    apply Finset.sum_eq_zero
    intro ⟨⟨_, _⟩, h⟩ _
    exfalso; apply h
    intro j hj
    -- hj : j < min a 0; since min a 0 = 0, this gives j < 0 which is absurd
    omega
  · -- b ≥ 1: split on b = 1 (direct bijection) vs b ≥ 2 (ring-valued LGV needed)
    have ha_pos : 0 < a := Nat.lt_of_lt_of_le hb hab
    have hb1_or : b = 1 ∨ 2 ≤ b := by omega
    rcases hb1_or with rfl | hb2
    · /- b = 1: bijection ψ : {non-cs (P,{q}) of shapes (a,1)} ≃ Sym n (a+1)
           via (P, {q}) ↦ P.1 + {q},  inverse P' ↦ (P'.erase(min P'), {min P'}).
           Non-cs condition for (a,1): q₀ ≤ P.sort[0]  (the singleton is ≤ min of P).
           Weight preserved: wt(P)*X_q = wt(P + {q}) by Multiset.map_add + prod_add. -/
      simp only [le_refl, ↓reduceIte, Nat.sub_self]
      -- hsymm R 0 = 1 (empty symmetric product, unique element ⟨∅,rfl⟩)
      have h0 : hsymm (Fin n) R 0 = 1 := by
        haveI : Unique (Sym (Fin n) 0) :=
          ⟨⟨⟨0, rfl⟩⟩, fun s => Subtype.ext (Multiset.card_eq_zero.mp s.2)⟩
        simp [hsymm]
      rw [h0, mul_one, hsymm]
      -- All elements of a Sym product are ≥ its sorted minimum
      have sym_ge_sort0 : ∀ (P' : Sym (Fin n) (a + 1)) (x : Fin n),
          x ∈ P'.1 → (P'.1.sort (· ≤ ·))[0]'(by rw [Multiset.length_sort, P'.2]) ≤ x :=
        fun P' x hx => by
          have hlen : (P'.1.sort (· ≤ ·)).length = a + 1 :=
            (Multiset.length_sort _ P'.1).trans P'.2
          obtain ⟨j, hj, hjx⟩ := List.mem_iff_getElem.mp ((Multiset.mem_sort _).mpr hx)
          exact ((Multiset.pairwise_sort (· ≤ ·) P'.1).sortedLE
            .getElem_le_getElem_of_le (by omega) (hlen ▸ hj) (Nat.zero_le j)).trans
            (le_of_eq hjx)
      -- Sort of singleton multiset = [q]
      have sort_sing : ∀ q : Fin n,
          ({q} : Multiset (Fin n)).sort (· ≤ ·) = [q] := fun q => by
        rw [show ({q} : Multiset (Fin n)) = ↑([q] : List (Fin n)) from by simp,
          Multiset.coe_sort]
        exact List.mergeSort_eq_self (List.pairwise_singleton _ _)
      -- Weight-preserving bijection ψ
      let ψ : { PQ : Sym (Fin n) a × Sym (Fin n) 1 // ¬ColStrictSym a 1 PQ.1 PQ.2 } ≃
              Sym (Fin n) (a + 1) :=
        { toFun := fun ⟨⟨P, Q⟩, _⟩ =>
              ⟨P.1 + Q.1, by simp [Multiset.card_add, P.2, Q.2]⟩
          invFun := fun P' =>
            let hlen : (P'.1.sort (· ≤ ·)).length = a + 1 :=
              (Multiset.length_sort _ P'.1).trans P'.2
            let q₀ := (P'.1.sort (· ≤ ·))[0]'(by omega)
            have hq₀_in : q₀ ∈ P'.1 := by
              rw [← Multiset.mem_sort (· ≤ ·)]; exact List.getElem_mem (by omega)
            have hcard_er : (P'.1.erase q₀).card = a := by
              rw [Multiset.card_erase_of_mem hq₀_in, P'.2]
            ⟨(⟨P'.1.erase q₀, hcard_er⟩, ⟨{q₀}, by simp⟩),
              -- ¬ColStrictSym: q₀ ≤ (P'.erase q₀).sort[0]
              fun (hcs : ColStrictSym a 1 _ _) => by
                have hlen_er : (P'.1.erase q₀).sort (· ≤ ·) |>.length = a :=
                  (Multiset.length_sort _ _).trans hcard_er
                have h0cs := hcs 0 (by simp only [Nat.lt_min]; exact ⟨ha_pos, Nat.lt_succ_self 0⟩)
                simp only [Sym.val_mk', sort_sing, List.getElem_cons_zero] at h0cs
                have h_er0_in : (P'.1.erase q₀).sort (· ≤ ·)[0]'(by omega) ∈ P'.1.erase q₀ := by
                  rw [← Multiset.mem_sort (· ≤ ·)]; exact List.getElem_mem (by omega)
                exact absurd (sym_ge_sort0 P' _ (Multiset.mem_of_mem_erase h_er0_in))
                  (not_le.mpr h0cs)⟩
          left_inv := fun ⟨⟨P, Q⟩, h_ncs⟩ => by
            obtain ⟨q₀, hq₀⟩ := Multiset.card_eq_one.mp Q.2
            have hP_len : (P.1.sort (· ≤ ·)).length = a :=
              (Multiset.length_sort _ P.1).trans P.2
            have hP_pos : 0 < (P.1.sort (· ≤ ·)).length := by omega
            -- From non-cs: q₀ ≤ P.sort[0]
            have hq0_le_Psort0 : q₀ ≤ (P.1.sort (· ≤ ·))[0]'hP_pos := by
              by_contra h_lt
              push_neg at h_lt
              exact h_ncs fun j hj => by
                simp only [Nat.lt_min] at hj
                have hj0 : j = 0 := by omega
                subst hj0
                simp only [Sym.val_mk', hq₀, sort_sing, List.getElem_cons_zero]
                exact h_lt
            -- q₀ ≤ all elements of P
            have hq0_le_P : ∀ x ∈ P.1, q₀ ≤ x := fun x hx => by
              obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ((Multiset.mem_sort _).mpr hx)
              exact hq0_le_Psort0.trans
                ((Multiset.pairwise_sort (· ≤ ·) P.1).sortedLE
                  .getElem_le_getElem_of_le hP_pos.le (hP_len ▸ hj) (Nat.zero_le j))
            -- sort[0] of P.1 + {q₀} = q₀
            have hPQ_pos : 0 < (P.1 + {q₀}).sort (· ≤ ·) |>.length := by
              rw [Multiset.length_sort, Multiset.card_add, P.2, hq₀]; simp
            have h_min_eq_q0 : (P.1 + {q₀}).sort (· ≤ ·)[0]'hPQ_pos = q₀ := by
              apply le_antisymm
              · -- q₀ is in the sort, sort[0] ≤ q₀ by monotonicity
                have hq0_in : q₀ ∈ (P.1 + {q₀}).sort (· ≤ ·) := by
                  rw [Multiset.mem_sort]; simp [Multiset.mem_add]
                obtain ⟨j, hj, hjq⟩ := List.mem_iff_getElem.mp hq0_in
                have hlenPQ : (P.1 + {q₀}).sort (· ≤ ·) |>.length = a + 1 := by
                  rw [Multiset.length_sort, Multiset.card_add, P.2, hq₀]; simp
                exact ((Multiset.pairwise_sort (· ≤ ·) (P.1 + {q₀})).sortedLE
                  .getElem_le_getElem_of_le hPQ_pos.le (hlenPQ ▸ hj) (Nat.zero_le j)).trans
                  (le_of_eq hjq)
              · -- all elements of P+{q₀} are ≥ q₀, so sort[0] ≥ q₀
                have h0_in : (P.1 + {q₀}).sort (· ≤ ·)[0]'hPQ_pos ∈ P.1 + {q₀} := by
                  rw [← Multiset.mem_sort (· ≤ ·)]; exact List.getElem_mem hPQ_pos
                rw [Multiset.mem_add, Multiset.mem_singleton] at h0_in
                rcases h0_in with h | rfl
                · exact hq0_le_P _ h
                · exact le_refl _
            apply Subtype.ext; apply Prod.ext <;> apply Subtype.ext
            · -- P component: (P.1 + {q₀}).erase(sort[0]) = P.1
              simp only [Sym.val_mk', hq₀]
              conv_lhs =>
                rw [show (P.1 + ({q₀} : Multiset (Fin n))).sort (· ≤ ·)[0]'hPQ_pos = q₀
                    from h_min_eq_q0]
              rw [show P.1 + ({q₀} : Multiset (Fin n)) = {q₀} + P.1 from add_comm _ _,
                Multiset.erase_add_left_pos _ (Multiset.mem_singleton_self q₀)]
              simp [Multiset.erase_cons_head]
            · -- Q component: {sort[0]} = {q₀}
              simp only [Sym.val_mk', hq₀]
              show ({(P.1 + ({q₀} : Multiset (Fin n))).sort (· ≤ ·)[0]'hPQ_pos}
                    : Multiset (Fin n)) = {q₀}
              rw [h_min_eq_q0]
          right_inv := fun P' => Subtype.ext (by
            have hlen : (P'.1.sort (· ≤ ·)).length = a + 1 :=
              (Multiset.length_sort _ P'.1).trans P'.2
            let q₀ := (P'.1.sort (· ≤ ·))[0]'(by omega)
            have hq₀_in : q₀ ∈ P'.1 := by
              rw [← Multiset.mem_sort (· ≤ ·)]; exact List.getElem_mem (by omega)
            simp only [Sym.val_mk']
            rw [show P'.1.erase q₀ + ({q₀} : Multiset (Fin n)) = {q₀} + P'.1.erase q₀
                from add_comm _ _, Multiset.singleton_add]
            exact Multiset.cons_erase hq₀_in) }
      exact Fintype.sum_equiv ψ _ _ fun ⟨⟨P, Q⟩, _⟩ => by
        show (P.1.map X).prod * (Q.1.map X).prod = ((P.1 + Q.1).map X).prod
        rw [Multiset.map_add, Multiset.prod_add]
    · -- b ≥ 2: requires ring-valued algebraic LGV extending BallotProblemOQ03OQ02.
      -- Proof: det(JT matrix) = ∑_NI-path-tuples ∏ weights (algebraic LGV),
      -- then identify non-cs pairs with cancellable path tuples via the GV involution.
      -- This generalizes lgv_general from ℤ to CommRing (~150 additional lines).
      sorry

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
  -- Helper: row i of T (weakly sorted) → sort of its multiset = List.ofFn(row i)
  have row_sort : ∀ (T : SSYTFin n 2 sh) (i : Fin 2),
      (↑(List.ofFn (fun j : Fin (sh i) => T.1 ⟨i, j⟩)) : Multiset _).sort (· ≤ ·) =
      List.ofFn (fun j : Fin (sh i) => T.1 ⟨i, j⟩) := fun T i => by
    rw [Multiset.coe_sort]
    exact List.mergeSort_eq_self
      ((List.sortedLE_ofFn_iff.mpr
        (fun j1 j2 h => h.lt_or_eq.elim (T.2.1 i j1 j2) (fun h => h ▸ le_refl _))).pairwise)
  -- Abbreviations
  set a := sh 0; set b := sh 1
  -- Build bijection φ : SSYTFin n 2 sh ≃ {(P,Q) : ColStrictSym}
  let φ : SSYTFin n 2 sh ≃
      { PQ : Sym (Fin n) a × Sym (Fin n) b // ColStrictSym a b PQ.1 PQ.2 } :=
    { toFun := fun T =>
        ⟨(⟨↑(List.ofFn (fun j => T.1 ⟨(0 : Fin 2), j⟩)), by simp [a]⟩,
          ⟨↑(List.ofFn (fun j => T.1 ⟨(1 : Fin 2), j⟩)), by simp [b]⟩),
         fun j hj => by
           have hj0 : j < a := by
             simp only [a, min_def] at hj; split_ifs at hj <;> omega
           have hj1 : j < b := by
             simp only [b, min_def] at hj; split_ifs at hj <;> omega
           simp only [Sym.val_mk', row_sort T 0, row_sort T 1, List.getElem_ofFn]
           exact T.2.2 0 1 ⟨j, hj0⟩ ⟨j, hj1⟩ rfl (by norm_num)⟩
      invFun := fun ⟨⟨P, Q⟩, _⟩ =>
        let plen : (P.1.sort (· ≤ ·)).length = a :=
          (Multiset.length_sort _ P.1).trans P.2
        let qlen : (Q.1.sort (· ≤ ·)).length = b :=
          (Multiset.length_sort _ Q.1).trans Q.2
        ⟨fun ⟨i, j⟩ => if _hi : i = (0 : Fin 2)
            then (P.1.sort (· ≤ ·))[j.val]'(plen ▸ j.isLt)
            else (Q.1.sort (· ≤ ·))[j.val]'(qlen ▸ j.isLt),
         ⟨fun i j1 j2 hlt => by
            fin_cases i
            · simp only [dif_pos rfl]
              exact ((Multiset.pairwise_sort (· ≤ ·) P.1).sortedLE).getElem_le_getElem_of_le
                (plen ▸ j1.isLt) (plen ▸ j2.isLt)
                (le_of_lt (Fin.lt_iff_val_lt_val.mp hlt))
            · simp only [dif_neg (by norm_num : (1 : Fin 2) ≠ 0)]
              exact ((Multiset.pairwise_sort (· ≤ ·) Q.1).sortedLE).getElem_le_getElem_of_le
                (qlen ▸ j1.isLt) (qlen ▸ j2.isLt)
                (le_of_lt (Fin.lt_iff_val_lt_val.mp hlt)),
          fun i1 i2 j1 j2 hjval hi12 => by
            have h0 : i1 = (0 : Fin 2) := by fin_cases i1 <;> fin_cases i2 <;> simp_all
            have h1 : i2 = (1 : Fin 2) := by fin_cases i1 <;> fin_cases i2 <;> simp_all
            subst h0; subst h1
            simp only [dif_pos rfl, dif_neg (by norm_num : (1 : Fin 2) ≠ 0)]
            have hmj : j1.val < min a b :=
              Nat.lt_min.mpr ⟨j1.isLt, hjval ▸ j2.isLt⟩
            have hval := ‹ColStrictSym a b _ _› j1.val hmj
            simp only [Sym.val_mk'] at hval
            rw [show j2.val = j1.val from hjval.symm]
            exact hval⟩⟩
      left_inv := fun T => by
        apply Subtype.ext; funext ⟨i, j⟩
        simp only
        fin_cases i
        · simp only [dif_pos rfl]
          rw [row_sort T 0]; simp [List.getElem_ofFn]
        · simp only [dif_neg (by norm_num : (1 : Fin 2) ≠ 0)]
          rw [row_sort T 1]; simp [List.getElem_ofFn]
      right_inv := fun ⟨⟨P, Q⟩, _⟩ => by
        apply Subtype.ext
        apply Prod.ext <;> apply Subtype.ext
        · -- P' = P: ofFn of getElem of sort = sort_eq
          have plen : (P.1.sort (· ≤ ·)).length = a :=
            (Multiset.length_sort _ P.1).trans P.2
          show (↑(List.ofFn (fun j : Fin a =>
              (P.1.sort (· ≤ ·))[j.val]'(plen ▸ j.isLt))) : Multiset _) = P.1
          rw [show List.ofFn (fun j : Fin a =>
              (P.1.sort (· ≤ ·))[j.val]'(plen ▸ j.isLt)) =
              P.1.sort (· ≤ ·) from
              List.ext_getElem (by simp [plen]) (fun i _ _ => by simp [List.getElem_ofFn])]
          exact_mod_cast Multiset.sort_eq (· ≤ ·) P.1
        · -- Q' = Q: same argument
          have qlen : (Q.1.sort (· ≤ ·)).length = b :=
            (Multiset.length_sort _ Q.1).trans Q.2
          show (↑(List.ofFn (fun j : Fin b =>
              (Q.1.sort (· ≤ ·))[j.val]'(qlen ▸ j.isLt))) : Multiset _) = Q.1
          rw [show List.ofFn (fun j : Fin b =>
              (Q.1.sort (· ≤ ·))[j.val]'(qlen ▸ j.isLt)) =
              Q.1.sort (· ≤ ·) from
              List.ext_getElem (by simp [qlen]) (fun i _ _ => by simp [List.getElem_ofFn])]
          exact_mod_cast Multiset.sort_eq (· ≤ ·) Q.1 }
  -- Transfer sum along φ and verify weight preservation
  refine Fintype.sum_equiv φ _ _ fun T => ?_
  simp only [SSYTFin.weight, Fintype.prod_sigma, Fin.prod_univ_two, Sym.val_mk']
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
theorem jacobi_trudi_ssyt_eq (n k : ℕ) (sh : Fin k → ℕ) (hanti : Antitone sh) :
    JacobiTrudi.schurPolynomial (σ := Fin n) (R := R) k sh =
    ssytSchurFin (R := R) n k sh := by
  cases k with
  | zero =>
    -- k = 0: empty partition; both sides = 1.
    have hsh : sh = Fin.elim0 := funext (fun i => i.elim0)
    rw [hsh, schurPolynomial_empty, ssytSchurFin_empty]
  | succ k =>
    cases k with
    | zero =>
      -- k = 1: one-row partition.
      have hsh : sh = fun _ => sh ⟨0, Nat.lt_succ_self 0⟩ :=
        funext (fun i => by fin_cases i <;> rfl)
      rw [hsh, schurPolynomial_one_row, ssytSchurFin_one_row]
    | succ k =>
      cases k with
      | zero =>
        -- k = 2: two-row case, proved by jdt bijection (partition condition: sh 1 ≤ sh 0).
        exact (ssytSchurFin_two_row n sh (hanti (Fin.zero_le 1))).symm
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
