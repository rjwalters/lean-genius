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
### Main Theorem: Jacobi-Trudi = SSYT Sum (Open for k ≥ 2)
-/

/-- **Jacobi-Trudi Identity** (proved for k = 0,1; open for k ≥ 2):
    The determinant definition equals the SSYT generating function.

    `JacobiTrudi.schurPolynomial k sh = ssytSchurFin n k sh`

    - k = 0: **proved** — det of 0×0 matrix = 1 = empty SSYT sum
      (`schurPolynomial_empty` + `ssytSchurFin_empty`)
    - k = 1: **proved** — det of 1×1 matrix = h_{sh(0)} = one-row SSYT sum
      (`schurPolynomial_one_row` + `ssytSchurFin_one_row`)
    - k ≥ 2: **open** — requires RSK correspondence (~300-400 lines):
        (1) RSK bijection: SSYTFin n k sh ↔ NI lattice path tuples
        (2) LGV: det[e(Aᵢ,Bⱼ)] = weighted NI-path-count (parent proof available)
        (3) Weight match: SSYT weight = product of path weights = hsymm entries -/
theorem jacobi_trudi_ssyt_eq (n k : ℕ) (sh : Fin k → ℕ) :
    JacobiTrudi.schurPolynomial (σ := Fin n) (R := R) k sh =
    ssytSchurFin (R := R) n k sh := by
  cases k with
  | zero =>
    -- k = 0: empty partition; both sides = 1.
    -- det of 0×0 matrix = 1 (schurPolynomial_empty);
    -- sum over unique empty SSYT = 1 (ssytSchurFin_empty).
    have hsh : sh = Fin.elim0 := funext (fun i => i.elim0)
    rw [hsh, schurPolynomial_empty, ssytSchurFin_empty]
  | succ k =>
    cases k with
    | zero =>
      -- k = 1: one-row partition [sh(0)].
      -- schurPolynomial_one_row: det of 1×1 matrix [[h_{sh(0)}]] = h_{sh(0)}.
      -- ssytSchurFin_one_row: SSYTFin n 1 (fun _ => sh(0)) ≃ Sym (Fin n) sh(0),
      --   so the SSYT sum = hsymm (Fin n) R (sh(0)).
      have hsh : sh = fun _ => sh ⟨0, Nat.lt_succ_self 0⟩ :=
        funext (fun i => by fin_cases i <;> rfl)
      rw [hsh, schurPolynomial_one_row, ssytSchurFin_one_row]
    | succ k =>
      -- k+2 rows: requires RSK correspondence (open; estimated ~300-400 lines).
      --
      -- Proof outline:
      -- (1) RSK bijection: SSYTFin n (k+2) sh ↔ tuples of NI lattice paths for
      --     the LGV configuration with sources sᵢ = i, targets tⱼ = sh(j) + j.
      -- (2) Weight identification: SSYT weight monomial ↦ product of hsymm entries,
      --     matching the Jacobi-Trudi matrix entry (i,j) = hsymm (sh(i) + j - i).
      -- (3) LGV lemma: det(path-weight-matrix) = weighted NI-path-count.
      -- (4) Path-weight-matrix = Jacobi-Trudi matrix (by hsymm path-count formula).
      --
      -- The k=0 and k=1 cases above close the induction base.
      -- See research/problems/ballot-problem-oq-03-oq-01-oq-01-oq-01/knowledge.md
      sorry

end JacobiTrudi
