import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic
import Proofs.MinpolyCharpoly

/-
# Diagonalizable Matrices via Squarefree Minimal Polynomial

## Open Question (minpoly-charpoly-oq-02)

> Can the diagonalizability characterisation
> `M ∈ Matₙ(F) diagonalizable ⇔ minpoly M ∈ F[X] is squarefree (and splits in F)`
> be formalized in Lean 4 using this infrastructure?

This is `conclusion.openQuestions[1]` of the parent gallery entry
`minpoly-charpoly` (Minimal Polynomial vs Characteristic Polynomial of
Matrices — 17 theorems, 0 axioms). Sibling open questions:

* OQ-01 (Jordan normal form — scaffolded in `MinpolyCharpolyOQ01.lean`)
* OQ-03 (rational canonical form — scaffolded in `MinpolyCharpolyOQ03.lean`)

## Resolution (S1 OBSERVE — affirmative, no Mathlib gap)

**Yes, the diagonalizability characterisation is formalizable in Lean 4**
directly via the Mathlib `Module.End.IsSemisimple` API. The "diagonalizable"
side decomposes into "semisimple + minpoly splits", and both halves of the
biconditional are already in Mathlib `v4.26.0`:

1. **`Module.End.IsSemisimple` ↔ `Squarefree (minpoly K f)`** for a finite
   `K`-module endomorphism `f` over a field `K` of characteristic 0
   (or, more generally, when `minpoly K f` is separable). The forward
   direction is `Module.End.isSemisimple_iff_squarefree_minpoly` in
   `Mathlib.LinearAlgebra.Semisimple`.

2. **`Module.End.IsSemisimple` + minpoly splits → diagonalizable.** Over an
   algebraically closed field this is automatic; over a general field one
   needs `Polynomial.Splits (algebraMap K K) (minpoly K f)`. The composite
   "splits-and-semisimple = diagonalizable" is the operator-theoretic
   characterisation: under both hypotheses, the eigenspace decomposition
   `⨁ λ, eigenspace f λ = ⊤` holds and gives an eigenbasis.

3. **Matrix ↔ endomorphism transport.** Identifying a matrix
   `M : Matrix n n K` with the endomorphism `Matrix.toLin' M` carries the
   minpoly across (`Matrix.minpoly_toLin'`) and lets us read the
   diagonalizability claim back in matrix language.

**No Mathlib gap is required.** The remaining work for OQ-02 is purely
*integrative*: assemble these three pieces into the headline matrix-level
statement.

## Decomposition into Sub-OQs (proposed)

| Sub-OQ        | Content                                                                   | Estimated lines |
|---------------|---------------------------------------------------------------------------|-----------------|
| **OQ-02-OQ-01** | Bridge `Module.End.IsSemisimple` ↔ `Squarefree (minpoly K f)` to matrices | ~100            |
| **OQ-02-OQ-02** | "Diagonalizable" predicate on matrices + alg-closed unconditional form    | ~150            |
| **OQ-02-OQ-03** | General-field form with explicit `splits` hypothesis                       | ~120            |
| **OQ-02-OQ-04** | Char-0 specialisation: minpoly is automatically separable                  | ~80             |

Total roadmap: ≈ 450 lines (smaller than OQ-01 / OQ-03; the
`Module.End.IsSemisimple` API absorbs most of the work).

## What This File Contributes (S1 scaffold)

* **`Matrix.IsDiagonalizable`** — the matrix-level predicate: `M` is similar
  to a diagonal matrix over `K`, i.e. `∃ (P : Matrix n n K), P.Invertible ∧
  IsDiag (P⁻¹ * M * P)`. Mirrors the structure of `Matrix.IsDiag` from
  Mathlib but as an existential over similarity transforms.
* **`diagonalizable_iff_squarefree_minpoly`** — the **main theorem
  statement**, guarded by a single `sorry`. Reads:
  `IsAlgClosed K → CharZero K → (M.IsDiagonalizable ↔ Squarefree (minpoly K M))`.
  The four sub-OQs above are designed to discharge it.
* **`Matrix.IsDiagonalizable.of_isDiag`** — sanity lemma (unconditional): any
  diagonal matrix is diagonalizable (take `P = 1`).
* **`Matrix.IsDiagonalizable.zero`** — sanity lemma (unconditional): the zero
  matrix is diagonalizable.

## Why this scaffold

We follow the same S1 OBSERVE pattern used in sibling files
`MinpolyCharpolyOQ01.lean` (JNF) and `MinpolyCharpolyOQ03.lean` (RCF):
state the headline theorem with a single `sorry`, document the resolution
strategy, and provide a couple of unconditional sanity helpers so the file
exposes a non-trivial public surface even before the discharge work
begins. The four sub-OQs are the natural follow-up iterations.
-/

namespace Proofs.MinpolyCharpolyOQ02

open Matrix Polynomial

variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

/-- A square matrix `M` is **diagonalizable** if it is similar to a diagonal
matrix: there is an invertible matrix `P` over `K` such that `P⁻¹ * M * P`
is a diagonal matrix.

This is the matrix-level predicate corresponding to
`Module.End.IsSemisimple ∧ Polynomial.Splits` for the associated
endomorphism. -/
def _root_.Matrix.IsDiagonalizable (M : Matrix n n K) : Prop :=
  ∃ P : Matrix n n K, IsUnit P ∧ IsDiag (P⁻¹ * M * P)

-- ============================================================
-- Forward direction (PROVED, unconditional over any field)
-- ============================================================

/-- Conjugation `x ↦ Q * x * P` by a two-sided-inverse pair `(P, Q)` as an
algebra automorphism of the matrix algebra. Used to transport the minimal
polynomial across a similarity transform. -/
def matConj (P Q : Matrix n n K) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    Matrix n n K ≃ₐ[K] Matrix n n K where
  toFun x := Q * x * P
  invFun x := P * x * Q
  left_inv x := by
    show P * (Q * x * P) * Q = x
    calc P * (Q * x * P) * Q
        = (P * Q) * x * (P * Q) := by simp only [mul_assoc]
      _ = x := by rw [hPQ]; simp
  right_inv x := by
    show Q * (P * x * Q) * P = x
    calc Q * (P * x * Q) * P
        = (Q * P) * x * (Q * P) := by simp only [mul_assoc]
      _ = x := by rw [hQP]; simp
  map_mul' x y := by
    show Q * (x * y) * P = Q * x * P * (Q * y * P)
    calc Q * (x * y) * P
        = Q * x * (P * Q) * y * P := by rw [hPQ]; simp only [mul_assoc, mul_one]
      _ = Q * x * P * (Q * y * P) := by simp only [mul_assoc]
  map_add' x y := by
    show Q * (x + y) * P = Q * x * P + Q * y * P
    rw [mul_add, add_mul]
  commutes' r := by
    show Q * (algebraMap K (Matrix n n K) r) * P = algebraMap K (Matrix n n K) r
    rw [mul_assoc, Algebra.commutes, ← mul_assoc, hQP, one_mul]

/-- A diagonal matrix has squarefree minimal polynomial. The minimal
polynomial divides `∏_{c ∈ image of the diagonal} (X - c)`, a product of
distinct linear factors, which is separable hence squarefree. Holds over any
field. -/
theorem squarefree_minpoly_of_isDiag {D : Matrix n n K} (hD : D.IsDiag) :
    Squarefree (minpoly K D) := by
  classical
  set v : n → K := Matrix.diag D with hv
  have hDdiag : D = diagonal v := (hD.diagonal_diag).symm
  set S : Finset K := Finset.image v Finset.univ with hS
  set p : K[X] := ∏ c ∈ S, (X - C c) with hp
  have key : (aeval (diagonal v)) p = diagonal (fun i => (aeval (v i)) p) := by
    have h1 : (diagonal v : Matrix n n K) = diagonalAlgHom K v := by
      simp [diagonalAlgHom_apply]
    rw [h1, aeval_algHom_apply, diagonalAlgHom_apply]
    congr 1
    funext i
    exact aeval_pi_apply₂ v p i
  have hentry : ∀ i, (aeval (v i)) p = 0 := by
    intro i
    have hvi : v i ∈ S := Finset.mem_image_of_mem v (Finset.mem_univ i)
    have : (aeval (v i)) p = ∏ c ∈ S, (v i - c) := by
      rw [hp, map_prod]
      refine Finset.prod_congr rfl ?_
      intro c _
      simp [map_sub, aeval_X, aeval_C]
    rw [this]
    exact Finset.prod_eq_zero hvi (by simp)
  have hann : (aeval D) p = 0 := by
    rw [hDdiag, key]
    ext i j
    by_cases h : i = j
    · subst h
      simp only [Matrix.diagonal_apply_eq, Matrix.zero_apply, hentry]
    · simp only [Matrix.diagonal_apply_ne _ h, Matrix.zero_apply]
  have hdvd : minpoly K D ∣ p := minpoly.dvd K D hann
  have hsep : p.Separable := by
    rw [hp]
    exact (separable_prod_X_sub_C_iff' (f := fun c : K => c) (s := S)).mpr
      (fun x _ y _ h => h)
  exact hsep.squarefree.squarefree_of_dvd hdvd

/-- **Forward direction of the headline biconditional (PROVED).** A
diagonalizable matrix has squarefree minimal polynomial. This holds over any
field — no algebraic-closure or characteristic-zero hypotheses are needed
(those are only required for the converse). -/
theorem _root_.Matrix.IsDiagonalizable.squarefree_minpoly {M : Matrix n n K}
    (h : M.IsDiagonalizable) : Squarefree (minpoly K M) := by
  obtain ⟨P, hP, hdiag⟩ := h
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPQ : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  have hQP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have hmeq : minpoly K (P⁻¹ * M * P) = minpoly K M :=
    minpoly.algEquiv_eq (matConj P P⁻¹ hPQ hQP) M
  rw [← hmeq]
  exact squarefree_minpoly_of_isDiag hdiag

/-- **S1 OBSERVE → S7 ACT main theorem.** Over an algebraically closed field
of characteristic zero, a matrix is diagonalizable iff its minimal polynomial
is squarefree.

The **forward** direction (`→`) is now fully proved and unconditional
(`Matrix.IsDiagonalizable.squarefree_minpoly`, any field). The **reverse**
direction (`←`, squarefree minpoly ⇒ diagonalizable) remains the single
`sorry`: over an algebraically closed field it follows from Bridge C
(`Module.End.isSemisimple_iff_squarefree_minpoly`) plus Bridge B
(`Module.End.iSup_eigenspace_eq_top_of_isSemisimple`) transported back through
`Matrix.toLin'`, and is the target of sub-OQ-02-OQ-02.

Note: the field hypotheses can be weakened to "perfect field + minpoly
splits", but the alg-closed-char-0 case is the headline textbook statement
and is what most callers (e.g. linear-algebra texts) expect. The general
form is the target of OQ-02-OQ-03. -/
theorem diagonalizable_iff_squarefree_minpoly
    [IsAlgClosed K] [CharZero K] (M : Matrix n n K) :
    M.IsDiagonalizable ↔ Squarefree (minpoly K M) := by
  refine ⟨fun h => h.squarefree_minpoly, ?_⟩
  sorry

/-- **Sanity lemma (unconditional).** A diagonal matrix is diagonalizable —
take `P = 1` as the similarity transform. -/
theorem _root_.Matrix.IsDiagonalizable.of_isDiag {M : Matrix n n K}
    (hM : Matrix.IsDiag M) : M.IsDiagonalizable := by
  refine ⟨1, isUnit_one, ?_⟩
  simpa using hM

/-- **Sanity lemma (unconditional).** The zero matrix is diagonalizable. -/
theorem _root_.Matrix.IsDiagonalizable.zero :
    (0 : Matrix n n K).IsDiagonalizable :=
  Matrix.IsDiagonalizable.of_isDiag Matrix.isDiag_zero

/-- **Sanity lemma (unconditional).** The identity matrix is diagonalizable. -/
theorem _root_.Matrix.IsDiagonalizable.one :
    (1 : Matrix n n K).IsDiagonalizable :=
  Matrix.IsDiagonalizable.of_isDiag Matrix.isDiag_one

/-- **Sanity lemma (unconditional).** Any explicitly diagonal matrix
`Matrix.diagonal d` is diagonalizable. -/
theorem _root_.Matrix.IsDiagonalizable.diagonal (d : n → K) :
    (Matrix.diagonal d).IsDiagonalizable :=
  Matrix.IsDiagonalizable.of_isDiag (Matrix.isDiag_diagonal d)

-- ============================================================
-- S7 ACT helpers: endomorphism-level bridges (Mathlib v4.26.0)
-- ============================================================

/-- **Bridge B forward** (per S4 PREP #18626 corrected 3-lemma chain).
Over an algebraically closed field in finite dimensions, semisimplicity
of an endomorphism implies that its eigenspaces span the whole space.

The chain is: `IsSemisimple → IsFinitelySemisimple → maxGenEigenspace μ =
eigenspace μ (per μ) → ⨆ eigenspace = ⨆ maxGenEigenspace = ⊤`. -/
lemma _root_.Module.End.iSup_eigenspace_eq_top_of_isSemisimple
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [IsAlgClosed K] {f : Module.End K V} (hss : f.IsSemisimple) :
    ⨆ μ : K, f.eigenspace μ = ⊤ := by
  have hfin : f.IsFinitelySemisimple := hss.isFinitelySemisimple
  have heq : ∀ μ : K, f.eigenspace μ = f.maxGenEigenspace μ :=
    fun μ => (hfin.maxGenEigenspace_eq_eigenspace μ).symm
  calc ⨆ μ : K, f.eigenspace μ
      = ⨆ μ, f.maxGenEigenspace μ := iSup_congr heq
    _ = ⊤ := Module.End.iSup_maxGenEigenspace_eq_top f

/-- **Bridge C** (endomorphism-level squarefree iff semisimple). Over a
finite-dimensional space, an endomorphism is semisimple iff its minimal
polynomial is squarefree. Forward: `Module.End.IsSemisimple.minpoly_squarefree`.
Reverse: `Module.End.isSemisimple_of_squarefree_aeval_eq_zero` applied to
`minpoly.aeval`. -/
theorem _root_.Module.End.isSemisimple_iff_squarefree_minpoly
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {f : Module.End K V} :
    f.IsSemisimple ↔ Squarefree (minpoly K f) :=
  ⟨Module.End.IsSemisimple.minpoly_squarefree,
   fun h => Module.End.isSemisimple_of_squarefree_aeval_eq_zero h (minpoly.aeval K f)⟩

end Proofs.MinpolyCharpolyOQ02
