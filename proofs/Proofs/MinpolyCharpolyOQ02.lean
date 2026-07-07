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

-- The headline biconditional `diagonalizable_iff_squarefree_minpoly` is stated
-- and PROVED (no sorry) at the end of this file, after the endomorphism-level
-- bridges (Bridge B/C) and the eigenbasis bridge it depends on.

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

-- ============================================================
-- Diagonalizability is a similarity invariant (PROVED, any field)
-- ============================================================

/-- **Diagonalizability is a similarity invariant.** If `M` is diagonalizable and
`P` is invertible, then the conjugate `P⁻¹ * M * P` is diagonalizable. If `M = Q⁻¹ D Q`
with `D` diagonal, then `P⁻¹ M P = (P⁻¹ Q)⁻¹ D (P⁻¹ Q)`, so `P⁻¹ Q` diagonalizes the
conjugate. This is the matrix-level counterpart of `minpoly.algEquiv_eq` (already used
for the forward direction via `matConj`) and the change-of-basis step the reverse
direction transports through `Matrix.toLin'`. Holds over any field. -/
theorem _root_.Matrix.IsDiagonalizable.conj {M : Matrix n n K}
    (h : M.IsDiagonalizable) {P : Matrix n n K} (hP : IsUnit P) :
    (P⁻¹ * M * P).IsDiagonalizable := by
  obtain ⟨Q, hQ, hdiag⟩ := h
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPinv : IsUnit P⁻¹ := (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_nonsing_inv_det P hPdet)
  refine ⟨P⁻¹ * Q, hPinv.mul hQ, ?_⟩
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPdet
  have hexpr : (P⁻¹ * Q)⁻¹ * (P⁻¹ * M * P) * (P⁻¹ * Q) = Q⁻¹ * M * Q := by
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv P hPdet,
      show Q⁻¹ * P * (P⁻¹ * M * P) * (P⁻¹ * Q)
        = Q⁻¹ * (P * P⁻¹) * M * (P * P⁻¹) * Q from by simp only [mul_assoc]]
    simp only [hPP, mul_one]
  rw [hexpr]
  exact hdiag

/-- **Similarity symmetry.** `P⁻¹ * M * P` is diagonalizable iff `M` is (for invertible
`P`). The forward implication is `Matrix.IsDiagonalizable.conj`; the converse conjugates
back by `P⁻¹` and rewrites `(P⁻¹)⁻¹ = P`. -/
theorem _root_.Matrix.isDiagonalizable_conj_iff {M P : Matrix n n K} (hP : IsUnit P) :
    (P⁻¹ * M * P).IsDiagonalizable ↔ M.IsDiagonalizable := by
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPdet
  have hPinv : IsUnit P⁻¹ := (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_nonsing_inv_det P hPdet)
  refine ⟨fun h => ?_, fun h => h.conj hP⟩
  have hback := h.conj (P := P⁻¹) hPinv
  have heq : (P⁻¹)⁻¹ * (P⁻¹ * M * P) * P⁻¹ = M := by
    rw [Matrix.nonsing_inv_nonsing_inv P hPdet,
      show P * (P⁻¹ * M * P) * P⁻¹ = (P * P⁻¹) * M * (P * P⁻¹) from by simp only [mul_assoc]]
    simp only [hPP, one_mul, mul_one]
  rwa [heq] at hback

-- ============================================================
-- Reverse direction: eigenbasis bridge + headline biconditional
-- ============================================================

/-- **Eigenbasis ⇒ diagonalizable (Bridge A reverse, PROVED, any field).**
If the space `n → K` admits a basis `b` of eigenvectors of `Matrix.toLin' M`
(with `toLin' M (b i) = μ i • b i`), then `M` is diagonalizable. The witnessing
similarity is the change-of-basis matrix `P = e.toMatrix b` (from the standard
basis `e` to `b`): in the eigenbasis the operator has matrix `diagonal μ`, and
the change-of-basis conjugation identity
`basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix` gives
`P⁻¹ * M * P = LinearMap.toMatrix b b (toLin' M) = diagonal μ`, which is
diagonal. This is the reusable core of the reverse direction; the remaining
work is to *produce* such an eigenbasis, done below from semisimplicity. -/
theorem isDiagonalizable_of_eigenbasis {M : Matrix n n K}
    (b : Module.Basis n K (n → K)) (μ : n → K)
    (hb : ∀ i, Matrix.toLin' M (b i) = μ i • b i) :
    M.IsDiagonalizable := by
  classical
  set e := Pi.basisFun K n with he
  have hdiag : LinearMap.toMatrix b b (Matrix.toLin' M) = Matrix.diagonal μ := by
    ext i j
    rw [LinearMap.toMatrix_apply, hb j, map_smul, Finsupp.smul_apply, Module.Basis.repr_self,
      Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  have hM : LinearMap.toMatrix e e (Matrix.toLin' M) = M := by
    rw [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  have hflip1 : e.toMatrix b * b.toMatrix e = 1 := Module.Basis.toMatrix_mul_toMatrix_flip e b
  haveI : Invertible (e.toMatrix b) := e.invertibleToMatrix b
  have hunit : IsUnit (e.toMatrix b) := isUnit_of_invertible _
  have hinv : (e.toMatrix b)⁻¹ = b.toMatrix e := Matrix.inv_eq_right_inv hflip1
  refine ⟨e.toMatrix b, hunit, ?_⟩
  rw [hinv]
  have h1 : b.toMatrix e * M * e.toMatrix b = LinearMap.toMatrix b b (Matrix.toLin' M) := by
    conv_lhs => rw [← hM]
    simp only [basis_toMatrix_mul_linearMap_toMatrix, linearMap_toMatrix_mul_basis_toMatrix]
  rw [h1, hdiag]
  exact Matrix.isDiag_diagonal μ

/-- **Headline biconditional (PROVED, no sorry).** Over an algebraically closed
field of characteristic zero, a matrix is diagonalizable iff its minimal
polynomial is squarefree.

The **forward** direction (`→`) is `Matrix.IsDiagonalizable.squarefree_minpoly`
(unconditional, any field). The **reverse** direction (`←`) is now discharged:
squarefree `minpoly` ⇒ the endomorphism `f = toLin' M` is semisimple (Bridge C),
hence over an algebraically closed field its eigenspaces span (`Bridge B`) and are
independent, so they form an internal direct sum. The collected per-eigenspace
bases give a basis of eigenvectors, which — after reindexing to `n` by equal
cardinality — is fed to `isDiagonalizable_of_eigenbasis`.

The field hypotheses can be weakened to "perfect field + minpoly splits", but the
alg-closed-char-0 case is the headline textbook statement (general form is the
target of OQ-02-OQ-03). -/
theorem diagonalizable_iff_squarefree_minpoly
    [IsAlgClosed K] [CharZero K] (M : Matrix n n K) :
    M.IsDiagonalizable ↔ Squarefree (minpoly K M) := by
  refine ⟨fun h => h.squarefree_minpoly, fun hsq => ?_⟩
  classical
  set f : Module.End K (n → K) := Matrix.toLin' M with hf
  have hmp : minpoly K f = minpoly K M := Matrix.minpoly_toLin' M
  have hss : f.IsSemisimple :=
    (Module.End.isSemisimple_iff_squarefree_minpoly).mpr (by rw [hmp]; exact hsq)
  have htop : ⨆ μ : K, f.eigenspace μ = ⊤ :=
    Module.End.iSup_eigenspace_eq_top_of_isSemisimple hss
  have hindep : iSupIndep (fun μ : K => f.eigenspace μ) :=
    Module.End.eigenspaces_iSupIndep f
  have hInt : DirectSum.IsInternal (fun μ : K => f.eigenspace μ) :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr ⟨hindep, htop⟩
  set B := hInt.collectedBasis (fun μ => Module.finBasis K (f.eigenspace μ)) with hB
  haveI : Fintype (Σ μ : K, Fin (Module.finrank K (f.eigenspace μ))) :=
    FiniteDimensional.fintypeBasisIndex B
  have hcard :
      Fintype.card (Σ μ : K, Fin (Module.finrank K (f.eigenspace μ))) = Fintype.card n := by
    rw [← Module.finrank_eq_card_basis B, ← Module.finrank_eq_card_basis (Pi.basisFun K n)]
  set ρ := Fintype.equivOfCardEq hcard with hρ
  refine isDiagonalizable_of_eigenbasis (B.reindex ρ) (fun i => (ρ.symm i).1) ?_
  intro i
  have hmem : B (ρ.symm i) ∈ f.eigenspace (ρ.symm i).1 :=
    hInt.collectedBasis_mem _ (ρ.symm i)
  have heig := Module.End.mem_eigenspace_iff.mp hmem
  rw [Module.Basis.reindex_apply, ← hf]
  exact heig

-- ============================================================
-- Recovered from PR #32451: standalone eigenbasis extraction and
-- the CharZero-free headline
-- ============================================================

omit [DecidableEq n] in
/-- **Reverse-direction eigenbasis construction (standalone).** Over an
algebraically closed field, a semisimple endomorphism of `n → K` admits a basis
of eigenvectors.

Semisimplicity gives `⨆ μ, eigenspace f μ = ⊤` (Bridge B); the eigenspaces are
always independent (`Module.End.eigenspaces_iSupIndep`), so the family is an
internal direct sum. Collecting a basis of each eigenspace yields a basis of
`n → K` indexed by a sigma type, reindexed onto `n` (both index a basis of the
same finite-dimensional space). Each collected vector lies in a single
eigenspace, hence is an eigenvector.

This factors the eigenbasis step of `diagonalizable_iff_squarefree_minpoly`
into a reusable lemma. -/
theorem _root_.Matrix.exists_eigenbasis_of_isSemisimple [IsAlgClosed K]
    {f : Module.End K (n → K)} (hss : f.IsSemisimple) :
    ∃ (b : Module.Basis n K (n → K)) (c : n → K), ∀ i, f (b i) = c i • b i := by
  classical
  have htop : ⨆ μ : K, f.eigenspace μ = ⊤ :=
    Module.End.iSup_eigenspace_eq_top_of_isSemisimple hss
  have hindep : iSupIndep (fun μ : K => f.eigenspace μ) :=
    Module.End.eigenspaces_iSupIndep f
  have hInt : DirectSum.IsInternal (fun μ : K => f.eigenspace μ) :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr ⟨hindep, htop⟩
  set B := hInt.collectedBasis (fun μ => Module.finBasis K (f.eigenspace μ)) with hB
  haveI : Fintype (Σ μ : K, Fin (Module.finrank K (f.eigenspace μ))) :=
    FiniteDimensional.fintypeBasisIndex B
  have hcard :
      Fintype.card (Σ μ : K, Fin (Module.finrank K (f.eigenspace μ))) = Fintype.card n := by
    rw [← Module.finrank_eq_card_basis B, ← Module.finrank_eq_card_basis (Pi.basisFun K n)]
  set ρ := Fintype.equivOfCardEq hcard with hρ
  refine ⟨B.reindex ρ, fun i => (ρ.symm i).1, fun i => ?_⟩
  rw [Module.Basis.reindex_apply]
  exact Module.End.mem_eigenspace_iff.mp (hInt.collectedBasis_mem _ (ρ.symm i))

/-- **Headline biconditional without `CharZero` (recovered from PR #32451).**
Over an algebraically closed field of *any* characteristic, a matrix is
diagonalizable iff its minimal polynomial is squarefree.

Only `[IsAlgClosed K]` is needed: over an algebraically closed field every
polynomial splits into linear factors, so a squarefree minimal polynomial is a
product of *distinct* linear factors and semisimplicity already forces an
eigenbasis — no separability (hence no characteristic-zero) hypothesis is
required. The textbook statement adds `[CharZero K]` (as
`diagonalizable_iff_squarefree_minpoly` above does), but that hypothesis is
redundant. The general-field form (with an explicit `Polynomial.Splits`
hypothesis) is the target of OQ-02-OQ-03. -/
theorem diagonalizable_iff_squarefree_minpoly'
    [IsAlgClosed K] (M : Matrix n n K) :
    M.IsDiagonalizable ↔ Squarefree (minpoly K M) := by
  refine ⟨fun h => h.squarefree_minpoly, fun hsq => ?_⟩
  have hsqf : Squarefree (minpoly K (Matrix.toLin' M : Module.End K (n → K))) := by
    rw [Matrix.minpoly_toLin']; exact hsq
  have hss : Module.End.IsSemisimple (Matrix.toLin' M : Module.End K (n → K)) :=
    Module.End.isSemisimple_iff_squarefree_minpoly.mpr hsqf
  obtain ⟨b, c, heig⟩ := Matrix.exists_eigenbasis_of_isSemisimple hss
  exact isDiagonalizable_of_eigenbasis b c heig

/- Axiom audit: expect only `propext`, `Classical.choice`, `Quot.sound`. -/
#print axioms Matrix.exists_eigenbasis_of_isSemisimple
#print axioms diagonalizable_iff_squarefree_minpoly'

end Proofs.MinpolyCharpolyOQ02
