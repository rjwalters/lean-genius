/-
# Diagonalizable Matrices — OQ-02 / closure properties of `Matrix.IsDiagonalizable`

The parent `MinpolyCharpolyOQ02` introduces the predicate

    `Matrix.IsDiagonalizable M := ∃ P, IsUnit P ∧ IsDiag (P⁻¹ * M * P)`

(`M` is similar to a diagonal matrix), proves the forward direction of the
diagonalizability characterisation, and records the trivial instances
(`zero`, `one`, `diagonal`, `of_isDiag`).  The substantive *reverse* direction
(squarefree minpoly ⇒ diagonalizable) is the parent's sole open obligation and is
not touched here.

This file fills in the **closure properties** of `IsDiagonalizable` — the
elementary algebraic stability laws that every textbook states immediately after
the definition but which the parent omits:

  * `IsDiagonalizable.conj`      — **similarity invariance**: if `M` is
    diagonalizable and `U` is invertible, so is the conjugate `U⁻¹ M U`.  This is
    the defining feature of diagonalizability as a property of the *operator*,
    not the matrix representative.
  * `IsDiagonalizable.smul`      — scalar multiples `c • M` stay diagonalizable
    (same diagonalizing `P`; the conjugate scales).
  * `IsDiagonalizable.neg`       — `-M` stays diagonalizable.
  * `IsDiagonalizable.transpose` — the transpose `Mᵀ` is diagonalizable, with
    diagonalizer `(Pᵀ)⁻¹` (eigenvalues are preserved under transpose).
  * `IsDiagonalizable.inv`       — the inverse `M⁻¹` is diagonalizable (same `P`),
    because `P⁻¹ M⁻¹ P = (P⁻¹ M P)⁻¹` and the inverse of a diagonal matrix is
    diagonal (`isDiag_inv`).
  * `IsDiagonalizable.pow`       — every power `Mᵏ` is diagonalizable (same `P`),
    because `P⁻¹ Mᵏ P = (P⁻¹ M P)ᵏ` (`conj_pow`) and powers of a diagonal matrix
    are diagonal (`isDiag_pow`, built on `isDiag_mul`).

All are fully machine-checked (0 axioms, 0 sorries) and reuse only the
parent's *definition* (not its open reverse-direction obligation).

Reference: Axler, *Linear Algebra Done Right* §5–8; Dummit–Foote §12.
-/

import Mathlib
import Proofs.MinpolyCharpoly
import Proofs.MinpolyCharpolyOQ02

namespace MinpolyCharpolyOQ02Incomplete01

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- **Similarity invariance.**  If `M` is diagonalizable and `U` is invertible,
    then the conjugate `U⁻¹ * M * U` is diagonalizable.  Diagonalizing `M` with
    `P` (so `P⁻¹ M P` is diagonal), the matrix `U⁻¹ P` diagonalizes `U⁻¹ M U`. -/
theorem IsDiagonalizable.conj {M : Matrix n n K} (hM : M.IsDiagonalizable)
    {U : Matrix n n K} (hU : IsUnit U) :
    (U⁻¹ * M * U).IsDiagonalizable := by
  obtain ⟨P, hP, hD⟩ := hM
  have hUdet : IsUnit U.det := (Matrix.isUnit_iff_isUnit_det U).mp hU
  have hUinv : IsUnit U⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hU
  refine ⟨U⁻¹ * P, hUinv.mul hP, ?_⟩
  have hQinv : (U⁻¹ * P)⁻¹ = P⁻¹ * U := by
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv U hUdet]
  have hUU : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U hUdet
  have hsimp : (U⁻¹ * P)⁻¹ * (U⁻¹ * M * U) * (U⁻¹ * P) = P⁻¹ * M * P := by
    rw [hQinv]
    calc P⁻¹ * U * (U⁻¹ * M * U) * (U⁻¹ * P)
        = P⁻¹ * (U * U⁻¹) * M * (U * U⁻¹) * P := by simp only [mul_assoc]
      _ = P⁻¹ * M * P := by rw [hUU]; simp only [mul_one]
  rw [hsimp]
  exact hD

/-- **Scalar multiples stay diagonalizable.**  The same `P` diagonalizes `c • M`,
    since `P⁻¹ (c • M) P = c • (P⁻¹ M P)` is again diagonal. -/
theorem IsDiagonalizable.smul {M : Matrix n n K} (hM : M.IsDiagonalizable) (c : K) :
    (c • M).IsDiagonalizable := by
  obtain ⟨P, hP, hD⟩ := hM
  refine ⟨P, hP, ?_⟩
  have h : P⁻¹ * (c • M) * P = c • (P⁻¹ * M * P) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [h]
  exact IsDiag.smul c hD

/-- **Negation stays diagonalizable.** -/
theorem IsDiagonalizable.neg {M : Matrix n n K} (hM : M.IsDiagonalizable) :
    (-M).IsDiagonalizable := by
  obtain ⟨P, hP, hD⟩ := hM
  refine ⟨P, hP, ?_⟩
  have h : P⁻¹ * (-M) * P = -(P⁻¹ * M * P) := by
    rw [Matrix.mul_neg, Matrix.neg_mul]
  rw [h]
  exact hD.neg

/-- **The transpose is diagonalizable.**  If `P⁻¹ M P` is diagonal then
    `((Pᵀ)⁻¹)⁻¹ Mᵀ (Pᵀ)⁻¹ = (P⁻¹ M P)ᵀ` is diagonal, so `(Pᵀ)⁻¹` diagonalizes
    `Mᵀ`. -/
theorem IsDiagonalizable.transpose {M : Matrix n n K} (hM : M.IsDiagonalizable) :
    (Mᵀ).IsDiagonalizable := by
  obtain ⟨P, hP, hD⟩ := hM
  have hPt : IsUnit (Pᵀ) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPtdet : IsUnit (Pᵀ).det := (Matrix.isUnit_iff_isUnit_det _).mp hPt
  refine ⟨(Pᵀ)⁻¹, Matrix.isUnit_nonsing_inv_iff.mpr hPt, ?_⟩
  have heq : (Pᵀ)⁻¹⁻¹ * Mᵀ * (Pᵀ)⁻¹ = (P⁻¹ * M * P)ᵀ := by
    rw [Matrix.nonsing_inv_nonsing_inv _ hPtdet, ← Matrix.transpose_nonsing_inv]
    simp only [Matrix.transpose_mul, mul_assoc]
  rw [heq]
  exact hD.transpose

/-- **The inverse of a diagonal matrix is diagonal.**  Writing `A = diagonal (diag A)`
    (valid because `A` is diagonal), `Matrix.inv_diagonal` gives
    `A⁻¹ = diagonal (Ring.inverse (diag A))`, which is again diagonal. -/
theorem isDiag_inv {A : Matrix n n K} (h : A.IsDiag) : A⁻¹.IsDiag := by
  rw [show A⁻¹ = (diagonal (diag A))⁻¹ by rw [h.diagonal_diag], Matrix.inv_diagonal]
  exact Matrix.isDiag_diagonal _

/-- **The inverse of a diagonalizable matrix is diagonalizable.**  The *same* `P`
    diagonalizes `M⁻¹`: since `P⁻¹ M⁻¹ P = (P⁻¹ M P)⁻¹` and the inverse of a diagonal
    matrix is diagonal (`isDiag_inv`), `P⁻¹ M⁻¹ P` is diagonal.  (No invertibility
    hypothesis on `M` is needed: if `M` is singular then `M⁻¹` is the junk value `0`,
    which is trivially diagonalizable, and the identity `P⁻¹ M⁻¹ P = (P⁻¹ M P)⁻¹`
    still holds for Mathlib's `nonsing_inv`.) -/
theorem IsDiagonalizable.inv {M : Matrix n n K} (hM : M.IsDiagonalizable) :
    M⁻¹.IsDiagonalizable := by
  obtain ⟨P, hP, hD⟩ := hM
  refine ⟨P, hP, ?_⟩
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have key : (P⁻¹ * M * P)⁻¹ = P⁻¹ * M⁻¹ * P := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv P hPdet,
      ← mul_assoc]
  rw [← key]
  exact isDiag_inv hD

/-- **The product of two diagonal matrices is diagonal.**  Off the diagonal
    (`i ≠ j`), every term `A i k * B k j` of `(A * B) i j = ∑ₖ A i k * B k j`
    vanishes: if `k ≠ i` then `A i k = 0`, and if `k = i` then `B k j = B i j = 0`
    (since `i ≠ j`). -/
theorem isDiag_mul {A B : Matrix n n K} (hA : A.IsDiag) (hB : B.IsDiag) :
    (A * B).IsDiag := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rcases eq_or_ne i k with rfl | hik
  · rw [hB hij, mul_zero]
  · rw [hA hik, zero_mul]

/-- **Powers of a diagonal matrix are diagonal.**  Immediate induction on the
    exponent: `A⁰ = 1` is diagonal and `Aᵏ⁺¹ = Aᵏ * A` is a product of diagonals. -/
theorem isDiag_pow {A : Matrix n n K} (h : A.IsDiag) (k : ℕ) : (A ^ k).IsDiag := by
  induction k with
  | zero => rw [pow_zero]; exact Matrix.isDiag_one
  | succ k ih => rw [pow_succ]; exact isDiag_mul ih h

/-- **Conjugation commutes with taking powers.**  For invertible `P`,
    `P⁻¹ Mᵏ P = (P⁻¹ M P)ᵏ`.  Proof by induction, cancelling the interior
    `P * P⁻¹ = 1` at each step. -/
theorem conj_pow {M P : Matrix n n K} (hP : IsUnit P.det) (k : ℕ) :
    P⁻¹ * M ^ k * P = (P⁻¹ * M * P) ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, mul_one, Matrix.nonsing_inv_mul P hP]
  | succ k ih =>
      have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
      rw [pow_succ, pow_succ, ← ih]
      have hcollapse : P⁻¹ * M ^ k * P * (P⁻¹ * M * P)
          = P⁻¹ * M ^ k * (P * P⁻¹) * (M * P) := by simp only [mul_assoc]
      rw [hcollapse, hPP]
      simp only [mul_one, mul_assoc]

/-- **Powers stay diagonalizable.**  The *same* `P` diagonalizes `Mᵏ`: since
    `P⁻¹ Mᵏ P = (P⁻¹ M P)ᵏ` (`conj_pow`) and powers of the diagonal matrix
    `P⁻¹ M P` are diagonal (`isDiag_pow`), `P⁻¹ Mᵏ P` is diagonal.  Completes the
    documented `nextSteps` item on powers of a diagonalizable matrix. -/
theorem IsDiagonalizable.pow {M : Matrix n n K} (hM : M.IsDiagonalizable) (k : ℕ) :
    (M ^ k).IsDiagonalizable := by
  obtain ⟨P, hP, hD⟩ := hM
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  refine ⟨P, hP, ?_⟩
  rw [conj_pow hPdet]
  exact isDiag_pow hD k

/-- **A finite sum of diagonal matrices is diagonal.**  Pointwise off the
    diagonal every summand vanishes, so does their sum. -/
theorem isDiag_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix n n K)
    (h : ∀ i ∈ s, (A i).IsDiag) : (∑ i ∈ s, A i).IsDiag := by
  intro r c hrc
  rw [Matrix.sum_apply]
  exact Finset.sum_eq_zero fun i hi => h i hi hrc

/-- **Polynomial closure — the capstone law.**  For *any* polynomial `q : K[X]`,
    the matrix `q(M) = aeval M q` is diagonalizable whenever `M` is, with the
    *same* diagonalizer `P`.  Indeed
    `P⁻¹ · q(M) · P = ∑ᵢ qᵢ · (P⁻¹ M P)ⁱ` (distributing the conjugation through
    the polynomial and applying `conj_pow` term-by-term), and each summand
    `qᵢ · (P⁻¹ M P)ⁱ` is diagonal (`isDiag_pow` + scaling), hence so is the sum.

    This subsumes the earlier `IsDiagonalizable.pow` (`q = Xᵏ`),
    `IsDiagonalizable.smul` (`q = C c · X`), `IsDiagonalizable.neg` (`q = -X`),
    and the spectral shift `M + c·1` (`q = X + C c`) in one statement. -/
theorem IsDiagonalizable.aeval {M : Matrix n n K} (hM : M.IsDiagonalizable)
    (q : Polynomial K) : ((Polynomial.aeval M) q).IsDiagonalizable := by
  obtain ⟨P, hP, hD⟩ := hM
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  refine ⟨P, hP, ?_⟩
  have hconj : P⁻¹ * ((Polynomial.aeval M) q) * P
      = ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i • (P⁻¹ * M * P) ^ i := by
    rw [Polynomial.aeval_eq_sum_range, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, conj_pow hPdet]
  rw [hconj]
  exact isDiag_sum _ _ fun i _ => IsDiag.smul (q.coeff i) (isDiag_pow hD i)

/-!
## Simultaneous diagonalization — the common-diagonalizer closure laws

The `aeval` capstone above closes `IsDiagonalizable` under polynomials of a
*single* matrix `M` (all sharing `M`'s diagonalizer `P`).  The remaining
documented `nextSteps` item — sums and products of *distinct* diagonalizable
matrices — is genuinely harder: in general `M + N` and `M * N` need NOT be
diagonalizable, and the classical sufficient condition (commuting matrices are
*simultaneously* diagonalizable) requires an eigenspace-decomposition argument.

The two laws below isolate the reusable, elementary half of that story: **once a
single invertible `P` is known to diagonalize both `M` and `N`, it diagonalizes
`M + N` and `M * N` as well.**  A future proof that commuting diagonalizable
matrices admit a common `P` would combine with these to conclude the commuting
sum/product is diagonalizable; here the hard eigenspace step is deliberately left
out and the algebraic consequence is recorded in full.
-/

/-- **Common diagonalizer ⟹ the sum is diagonalizable.**  If a single invertible
    `P` diagonalizes both `M` and `N` (so `P⁻¹ M P` and `P⁻¹ N P` are diagonal),
    then the same `P` diagonalizes `M + N`, since
    `P⁻¹ (M + N) P = P⁻¹ M P + P⁻¹ N P` is a sum of two diagonal matrices. -/
theorem IsDiagonalizable.add_of_commonDiagonalizer {M N P : Matrix n n K}
    (hP : IsUnit P) (hM : (P⁻¹ * M * P).IsDiag) (hN : (P⁻¹ * N * P).IsDiag) :
    (M + N).IsDiagonalizable := by
  refine ⟨P, hP, ?_⟩
  have h : P⁻¹ * (M + N) * P = (P⁻¹ * M * P) + (P⁻¹ * N * P) := by
    rw [Matrix.mul_add, Matrix.add_mul]
  rw [h]
  exact hM.add hN

/-- **Common diagonalizer ⟹ the product is diagonalizable.**  If a single
    invertible `P` diagonalizes both `M` and `N`, then the same `P` diagonalizes
    `M * N`, since `P⁻¹ (M * N) P = (P⁻¹ M P) (P⁻¹ N P)` (cancelling the interior
    `P * P⁻¹ = 1`) is a product of two diagonal matrices (`isDiag_mul`).  Unlike
    the general product of diagonalizable matrices, sharing a diagonalizer makes
    the product diagonalizable unconditionally. -/
theorem IsDiagonalizable.mul_of_commonDiagonalizer {M N P : Matrix n n K}
    (hP : IsUnit P) (hM : (P⁻¹ * M * P).IsDiag) (hN : (P⁻¹ * N * P).IsDiag) :
    (M * N).IsDiagonalizable := by
  refine ⟨P, hP, ?_⟩
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPdet
  have h : P⁻¹ * (M * N) * P = (P⁻¹ * M * P) * (P⁻¹ * N * P) := by
    calc P⁻¹ * (M * N) * P
        = P⁻¹ * M * (P * P⁻¹) * N * P := by rw [hPP]; simp only [mul_one, mul_assoc]
      _ = (P⁻¹ * M * P) * (P⁻¹ * N * P) := by simp only [mul_assoc]
  rw [h]
  exact isDiag_mul hM hN

/-- **Common diagonalizer ⟹ the difference is diagonalizable.**  Companion to
    `add_of_commonDiagonalizer`: if a single invertible `P` diagonalizes both `M`
    and `N`, the same `P` diagonalizes `M - N`, since
    `P⁻¹ (M - N) P = P⁻¹ M P - P⁻¹ N P` is a difference of two diagonal matrices. -/
theorem IsDiagonalizable.sub_of_commonDiagonalizer {M N P : Matrix n n K}
    (hP : IsUnit P) (hM : (P⁻¹ * M * P).IsDiag) (hN : (P⁻¹ * N * P).IsDiag) :
    (M - N).IsDiagonalizable := by
  refine ⟨P, hP, ?_⟩
  have h : P⁻¹ * (M - N) * P = (P⁻¹ * M * P) + (-(P⁻¹ * N * P)) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, sub_eq_add_neg]
  rw [h]
  exact hM.add hN.neg

/-- **Common diagonalizer ⟹ a whole finite family sum is diagonalizable.**  The
    `n`-ary generalization of `add_of_commonDiagonalizer`: if a single invertible
    `P` diagonalizes every `M i` (`i ∈ s`), it diagonalizes `∑ i ∈ s, M i`, since
    conjugation distributes over the sum (`Finset.mul_sum`/`Finset.sum_mul`) and a
    finite sum of diagonal matrices is diagonal (`isDiag_sum`). -/
theorem IsDiagonalizable.sum_of_commonDiagonalizer {ι : Type*} (s : Finset ι)
    (M : ι → Matrix n n K) {P : Matrix n n K} (hP : IsUnit P)
    (hM : ∀ i ∈ s, (P⁻¹ * M i * P).IsDiag) :
    (∑ i ∈ s, M i).IsDiagonalizable := by
  refine ⟨P, hP, ?_⟩
  have h : P⁻¹ * (∑ i ∈ s, M i) * P = ∑ i ∈ s, (P⁻¹ * M i * P) := by
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [h]
  exact isDiag_sum s _ hM

/-- **Common diagonalizer ⟹ the matrices commute.**  The (easy) *converse* half of
    the classical "commuting ⟺ simultaneously diagonalizable" theorem, complementing
    `mul_of_commonDiagonalizer`.  If a single invertible `P` diagonalizes both `M`
    and `N`, then `M` and `N` commute: their conjugates `P⁻¹ M P` and `P⁻¹ N P` are
    diagonal, hence commute (`diagonal_mul_diagonal` on both orders differ only by the
    pointwise `mul_comm`), and conjugation by the unit `P` is injective — undoing it
    (`P · (P⁻¹ · X · P) · P⁻¹ = X`) turns the equality of conjugates of `M N` and
    `N M` into `M * N = N * M`.  Together with the (hard, still open) fact that
    commuting diagonalizable matrices *admit* a common diagonalizer, this closes one
    direction of the simultaneous-diagonalization equivalence. -/
theorem commute_of_commonDiagonalizer {M N P : Matrix n n K}
    (hP : IsUnit P) (hM : (P⁻¹ * M * P).IsDiag) (hN : (P⁻¹ * N * P).IsDiag) :
    M * N = N * M := by
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPdet
  -- conjugation of a product splits by cancelling the interior `P * P⁻¹ = 1`
  have hMN : P⁻¹ * (M * N) * P = (P⁻¹ * M * P) * (P⁻¹ * N * P) := by
    calc P⁻¹ * (M * N) * P
        = P⁻¹ * M * (P * P⁻¹) * N * P := by rw [hPP]; simp only [mul_one, mul_assoc]
      _ = (P⁻¹ * M * P) * (P⁻¹ * N * P) := by simp only [mul_assoc]
  have hNM : P⁻¹ * (N * M) * P = (P⁻¹ * N * P) * (P⁻¹ * M * P) := by
    calc P⁻¹ * (N * M) * P
        = P⁻¹ * N * (P * P⁻¹) * M * P := by rw [hPP]; simp only [mul_one, mul_assoc]
      _ = (P⁻¹ * N * P) * (P⁻¹ * M * P) := by simp only [mul_assoc]
  -- diagonal matrices commute
  have hdcomm : (P⁻¹ * M * P) * (P⁻¹ * N * P) = (P⁻¹ * N * P) * (P⁻¹ * M * P) := by
    rw [← hM.diagonal_diag, ← hN.diagonal_diag, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  -- so the conjugates of `M * N` and `N * M` agree
  have hconj : P⁻¹ * (M * N) * P = P⁻¹ * (N * M) * P := by rw [hMN, hNM, hdcomm]
  -- undo the conjugation on both sides
  have hcancel : ∀ X : Matrix n n K, P * (P⁻¹ * X * P) * P⁻¹ = X := by
    intro X
    rw [show P * (P⁻¹ * X * P) * P⁻¹ = (P * P⁻¹) * X * (P * P⁻¹) by simp only [mul_assoc]]
    rw [hPP]; simp only [one_mul, mul_one]
  calc M * N = P * (P⁻¹ * (M * N) * P) * P⁻¹ := (hcancel _).symm
    _ = P * (P⁻¹ * (N * M) * P) * P⁻¹ := by rw [hconj]
    _ = N * M := hcancel _

/-- **A matrix commuting with a diagonal matrix of *distinct* entries is itself diagonal.**

    This is the combinatorial heart of the hard (still-open) converse
    "commuting diagonalizable ⟹ common diagonalizer": if `D` is diagonal with pairwise
    distinct diagonal entries and `A` commutes with `D`, then `A` must be diagonal.
    Entrywise, `(A*D)_{ij} = A_{ij}·D_{jj}` and `(D*A)_{ij} = D_{ii}·A_{ij}`, so
    `A_{ij}·(D_{jj} − D_{ii}) = 0`; for `i ≠ j` the distinctness `D_{jj} ≠ D_{ii}` forces
    `A_{ij} = 0`.

    Consequence (the reusable step a build-capable session can assemble into the converse):
    if `P` diagonalizes `M` (so `D = P⁻¹MP` is diagonal) with distinct eigenvalues and `N`
    commutes with `M`, then `P⁻¹NP` commutes with `D`, hence is diagonal — i.e. the *same*
    `P` diagonalizes `N`, giving a common diagonalizer. This settles the generic
    (distinct-eigenvalue) case of the classical theorem. -/
theorem isDiag_of_commute_diag_distinct {D A : Matrix n n K} (hD : D.IsDiag)
    (hdist : ∀ i j, i ≠ j → D i i ≠ D j j) (hcomm : A * D = D * A) :
    A.IsDiag := by
  intro i j hij
  -- `(A * D) i j = A i j * D j j` — only the `k = j` term of the row·column sum survives.
  have hAD : (A * D) i j = A i j * D j j := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_single j ?_ ?_
    · intro k _ hkj; rw [hD hkj, mul_zero]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  -- `(D * A) i j = D i i * A i j` — only the `k = i` term survives.
  have hDA : (D * A) i j = D i i * A i j := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_single i ?_ ?_
    · intro k _ hki; rw [hD (Ne.symm hki), zero_mul]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  -- commutativity equates the two entries
  have hkey : A i j * D j j = D i i * A i j := by rw [← hAD, ← hDA, hcomm]
  -- `A i j * (D j j - D i i) = 0`
  have hz : A i j * (D j j - D i i) = 0 := by
    rw [mul_sub, hkey, mul_comm (D i i) (A i j), sub_self]
  -- the second factor is nonzero, so `A i j = 0`
  have hne : D j j - D i i ≠ 0 := sub_ne_zero.mpr (hdist j i (Ne.symm hij))
  rcases mul_eq_zero.mp hz with h | h
  · exact h
  · exact absurd h hne

/-- **Distinct-eigenvalue case of the hard converse: a matrix commuting with a
    diagonalized matrix of distinct eigenvalues shares its diagonalizer.**
    If `P` diagonalizes `M` — `D = P⁻¹MP` is diagonal — with pairwise *distinct* diagonal
    entries (distinct eigenvalues), and `N` commutes with `M`, then the **same** `P`
    diagonalizes `N`: `P⁻¹NP` is diagonal.  This is the payoff of the crux
    `isDiag_of_commute_diag_distinct`: conjugating the commutation `MN = NM` by `P` (the
    same interior-`P·P⁻¹=1` cancellation as `commute_of_commonDiagonalizer`) shows `P⁻¹NP`
    commutes with the distinct-entry diagonal `D`, hence is diagonal.  It settles the generic
    (distinct-eigenvalue) case of the classical "commuting diagonalizable ⟹ common
    diagonalizer"; only the repeated-eigenvalue case (eigenspace decomposition) of the full
    converse remains open. -/
theorem commonDiagonalizer_of_commute_distinct {M N P : Matrix n n K}
    (hP : IsUnit P.det) (hMdiag : (P⁻¹ * M * P).IsDiag)
    (hdist : ∀ i j, i ≠ j → (P⁻¹ * M * P) i i ≠ (P⁻¹ * M * P) j j)
    (hcomm : M * N = N * M) :
    (P⁻¹ * N * P).IsDiag := by
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  -- Conjugation by `P` turns `NM = MN` into a commutation of `P⁻¹NP` with `D = P⁻¹MP`.
  have hAD : (P⁻¹ * N * P) * (P⁻¹ * M * P) = (P⁻¹ * M * P) * (P⁻¹ * N * P) := by
    have h1 : (P⁻¹ * N * P) * (P⁻¹ * M * P) = P⁻¹ * (N * M) * P := by
      calc (P⁻¹ * N * P) * (P⁻¹ * M * P)
          = P⁻¹ * N * (P * P⁻¹) * M * P := by simp only [mul_assoc]
        _ = P⁻¹ * (N * M) * P := by rw [hPP]; simp only [mul_one, mul_assoc]
    have h2 : (P⁻¹ * M * P) * (P⁻¹ * N * P) = P⁻¹ * (M * N) * P := by
      calc (P⁻¹ * M * P) * (P⁻¹ * N * P)
          = P⁻¹ * M * (P * P⁻¹) * N * P := by simp only [mul_assoc]
        _ = P⁻¹ * (M * N) * P := by rw [hPP]; simp only [mul_one, mul_assoc]
    rw [h1, h2, hcomm]
  exact isDiag_of_commute_diag_distinct hMdiag hdist hAD

/-!
### Simultaneous diagonalization — the distinct-eigenvalue payoff

`commonDiagonalizer_of_commute_distinct` supplies the hard half (commuting with a
distinct-spectrum diagonalizable `M` forces the same `P` to diagonalize `N`) and the
`*_of_commonDiagonalizer` laws supply the easy half (a shared `P` diagonalizes the
sum/product).  Composing them settles the **generic (distinct-eigenvalue) case of the
classical simultaneous-diagonalization theorem**: if `M` is diagonalizable with pairwise
distinct eigenvalues and `N` commutes with `M`, then `N` is itself diagonalizable and both
`M + N` and `M * N` are diagonalizable — *without any separate diagonalizability hypothesis
on `N`*, which comes for free.  Only the repeated-eigenvalue case (needing eigenspace
decomposition) of the full converse remains open.
-/

/-- **Distinct-eigenvalue case: a matrix commuting with a diagonalizable matrix of
    distinct eigenvalues is itself diagonalizable, sharing its diagonalizer.**  If `P`
    diagonalizes `M` (`P⁻¹MP` diagonal) with pairwise *distinct* diagonal entries and `N`
    commutes with `M`, then the same `P` diagonalizes `N`
    (`commonDiagonalizer_of_commute_distinct`), so `N` is diagonalizable.  No independent
    diagonalizability hypothesis on `N` is required — commuting with a distinct-spectrum
    diagonalizable matrix supplies it. -/
theorem IsDiagonalizable.of_commute_distinct {M N P : Matrix n n K}
    (hP : IsUnit P) (hMdiag : (P⁻¹ * M * P).IsDiag)
    (hdist : ∀ i j, i ≠ j → (P⁻¹ * M * P) i i ≠ (P⁻¹ * M * P) j j)
    (hcomm : M * N = N * M) :
    N.IsDiagonalizable := by
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  exact ⟨P, hP, commonDiagonalizer_of_commute_distinct hPdet hMdiag hdist hcomm⟩

/-- **Distinct-eigenvalue simultaneous diagonalization — the sum.**  If `P` diagonalizes
    `M` with pairwise distinct eigenvalues and `N` commutes with `M`, then `M + N` is
    diagonalizable.  Commuting with the distinct-spectrum `M` forces `N` to share `M`'s
    diagonalizer (`commonDiagonalizer_of_commute_distinct`), after which the shared-`P` sum
    law `add_of_commonDiagonalizer` applies.  The additive generic case of the classical
    "commuting diagonalizable ⟹ sum diagonalizable". -/
theorem IsDiagonalizable.add_of_commute_distinct {M N P : Matrix n n K}
    (hP : IsUnit P) (hMdiag : (P⁻¹ * M * P).IsDiag)
    (hdist : ∀ i j, i ≠ j → (P⁻¹ * M * P) i i ≠ (P⁻¹ * M * P) j j)
    (hcomm : M * N = N * M) :
    (M + N).IsDiagonalizable := by
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hNdiag := commonDiagonalizer_of_commute_distinct hPdet hMdiag hdist hcomm
  exact IsDiagonalizable.add_of_commonDiagonalizer hP hMdiag hNdiag

/-- **Distinct-eigenvalue simultaneous diagonalization — the product.**  If `P`
    diagonalizes `M` with pairwise distinct eigenvalues and `N` commutes with `M`, then
    `M * N` is diagonalizable.  As in the additive case, commuting with the distinct-spectrum
    `M` forces `N` to share `M`'s diagonalizer, so the shared-`P` product law
    `mul_of_commonDiagonalizer` applies.  This is the generic (distinct-eigenvalue) case of
    the classical theorem that commuting diagonalizable matrices have a diagonalizable
    product; the counterexample `exists_diagonalizable_mul_not_diagonalizable` shows the
    commuting hypothesis is essential (its witnesses do *not* commute). -/
theorem IsDiagonalizable.mul_of_commute_distinct {M N P : Matrix n n K}
    (hP : IsUnit P) (hMdiag : (P⁻¹ * M * P).IsDiag)
    (hdist : ∀ i j, i ≠ j → (P⁻¹ * M * P) i i ≠ (P⁻¹ * M * P) j j)
    (hcomm : M * N = N * M) :
    (M * N).IsDiagonalizable := by
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hNdiag := commonDiagonalizer_of_commute_distinct hPdet hMdiag hdist hcomm
  exact IsDiagonalizable.mul_of_commonDiagonalizer hP hMdiag hNdiag

/-- **The (ordered) product of a list of diagonal matrices is diagonal.**  The
    multiplicative companion of `isDiag_sum`.  Because matrix multiplication is
    *not* commutative, the product must be taken over an ordered `List` rather than
    a `Finset`; an immediate `List.prod` induction (base `1` diagonal, step
    `isDiag_mul`) gives the result. -/
theorem isDiag_listProd (L : List (Matrix n n K)) (h : ∀ A ∈ L, A.IsDiag) :
    L.prod.IsDiag := by
  induction L with
  | nil => rw [List.prod_nil]; exact Matrix.isDiag_one
  | cons a l ih =>
      rw [List.prod_cons]
      exact isDiag_mul (h a (List.mem_cons.mpr (Or.inl rfl)))
        (ih (fun A hA => h A (List.mem_cons.mpr (Or.inr hA))))

/-- **Conjugation distributes over an ordered product.**  For invertible `P`,
    `P⁻¹ · (∏ L) · P = ∏ (L.map (A ↦ P⁻¹ A P))`.  The list-valued analogue of
    `conj_pow`; the same interior `P * P⁻¹ = 1` cancellation is applied once per
    `cons` step. -/
theorem conj_listProd {P : Matrix n n K} (hP : IsUnit P.det) (L : List (Matrix n n K)) :
    P⁻¹ * L.prod * P = (L.map (fun A => P⁻¹ * A * P)).prod := by
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  induction L with
  | nil =>
      rw [List.prod_nil, List.map_nil, List.prod_nil, mul_one, Matrix.nonsing_inv_mul P hP]
  | cons a l ih =>
      rw [List.prod_cons, List.map_cons, List.prod_cons, ← ih]
      show P⁻¹ * (a * l.prod) * P = (P⁻¹ * a * P) * (P⁻¹ * l.prod * P)
      calc P⁻¹ * (a * l.prod) * P
          = P⁻¹ * a * (P * P⁻¹) * l.prod * P := by rw [hPP]; simp only [mul_one, mul_assoc]
        _ = (P⁻¹ * a * P) * (P⁻¹ * l.prod * P) := by simp only [mul_assoc]

/-- **Common diagonalizer ⟹ an ordered product of the family is diagonalizable.**
    The multiplicative, `List`-indexed generalization of both
    `mul_of_commonDiagonalizer` (a two-element product) and
    `sum_of_commonDiagonalizer` (the additive `Finset` version).  If a single
    invertible `P` diagonalizes every matrix in the list `L`, it diagonalizes the
    ordered product `L.prod`: conjugation distributes over the product
    (`conj_listProd`) and a list of diagonal matrices has a diagonal product
    (`isDiag_listProd`).  The ordering is essential — matrix multiplication is
    non-commutative — so unlike the sum this is genuinely a `List`, not a `Finset`,
    statement. -/
theorem IsDiagonalizable.prod_of_commonDiagonalizer {P : Matrix n n K} (hP : IsUnit P)
    (L : List (Matrix n n K)) (hM : ∀ A ∈ L, (P⁻¹ * A * P).IsDiag) :
    L.prod.IsDiagonalizable := by
  refine ⟨P, hP, ?_⟩
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  rw [conj_listProd hPdet]
  refine isDiag_listProd _ (fun A hA => ?_)
  rw [List.mem_map] at hA
  obtain ⟨B, hB, rfl⟩ := hA
  exact hM B hB

/-! ### Necessity of the common-diagonalizer hypothesis

`mul_of_commonDiagonalizer` requires `M` and `N` to share a single diagonalizer `P`;
mere diagonalizability of each is not enough.  Explicit witnesses over `ℚ`: the swap
`M = !![0,1;1,0]` (diagonalizable, eigenvalues `±1`) and the diagonal `N = !![1,0;0,-1]`.
They do not commute, so by `commute_of_commonDiagonalizer` they share no diagonalizer —
and indeed their product `M*N = !![0,-1;1,0]` is a rational `90°` rotation with
eigenvalues `±i ∉ ℚ`, hence not diagonalizable over `ℚ`.  (The proof needs no eigenvalue
theory: trace and determinant are similarity invariants, so a diagonal conjugate `D` of
`M*N` would satisfy `D₀₀ + D₁₁ = 0` and `D₀₀·D₁₁ = 1`, forcing `D₀₀² = -1`, impossible
over an ordered field.) -/
theorem exists_diagonalizable_mul_not_diagonalizable :
    ∃ M N : Matrix (Fin 2) (Fin 2) ℚ,
      M.IsDiagonalizable ∧ N.IsDiagonalizable ∧ ¬ (M * N).IsDiagonalizable := by
  refine ⟨!![0, 1; 1, 0], !![1, 0; 0, -1], ?_, ?_, ?_⟩
  · -- `M` (the swap) is diagonalized by `P = !![1,1;1,-1]`.
    refine ⟨!![1, 1; 1, -1], ?_, ?_⟩
    · rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two_of]; norm_num
    · have hinv : (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℚ)⁻¹ = !![1/2, 1/2; 1/2, -1/2] :=
        Matrix.inv_eq_right_inv (by rw [Matrix.one_fin_two]; norm_num [Matrix.mul_fin_two])
      rw [hinv, show
        (!![1/2, 1/2; 1/2, -1/2] : Matrix (Fin 2) (Fin 2) ℚ) * !![0, 1; 1, 0] * !![1, 1; 1, -1]
          = !![1, 0; 0, -1] by norm_num [Matrix.mul_fin_two]]
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
  · -- `N` is diagonal, hence diagonalizable.
    refine Matrix.IsDiagonalizable.of_isDiag ?_
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · -- `M*N = !![0,-1;1,0]` is not diagonalizable over `ℚ`.
    rintro ⟨P, hP, hdiag⟩
    have hMN : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ) * !![1, 0; 0, -1] = !![0, -1; 1, 0] := by
      norm_num [Matrix.mul_fin_two]
    rw [hMN] at hdiag
    set D := P⁻¹ * (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ) * P with hDdef
    have htr : Matrix.trace D = 0 := by
      rw [hDdef, Matrix.trace_conj' hP]; norm_num [Matrix.trace_fin_two_of]
    have hdet : Matrix.det D = 1 := by
      rw [hDdef, Matrix.det_conj' hP]; norm_num [Matrix.det_fin_two_of]
    have h01 : D 0 1 = 0 := hdiag (by decide)
    have h10 : D 1 0 = 0 := hdiag (by decide)
    rw [Matrix.trace_fin_two] at htr
    have hprod : D 0 0 * D 1 1 = 1 := by
      rw [Matrix.det_fin_two, h01, h10] at hdet; simpa using hdet
    have hD11 : D 1 1 = -D 0 0 := by linarith
    rw [hD11] at hprod
    nlinarith [sq_nonneg (D 0 0), hprod]

/-- **Necessity of a common diagonalizer for `add_of_commonDiagonalizer`.**
Diagonalizability of each summand is not enough to force the sum to be diagonalizable.
Explicit witnesses over `ℚ`: the diagonalizable `M = !![-2,-1;1,1/2]` (distinct rational
eigenvalues `0` and `-3/2`, diagonalized by `P = !![1,2;-2,-1]`) and the diagonal
`N = !![2,0;0,-1/2]`.  Their sum `M + N = !![0,-1;1,0]` is the rational `90°` rotation with
eigenvalues `±i ∉ ℚ`, hence not diagonalizable over `ℚ`.  So `M` and `N` cannot share a
diagonalizer, since otherwise `add_of_commonDiagonalizer` would diagonalize the sum.  The
non-diagonalizability proof reuses the trace/determinant argument of
`exists_diagonalizable_mul_not_diagonalizable`: a diagonal conjugate `D` of the rotation
would satisfy `D₀₀ + D₁₁ = 0` and `D₀₀·D₁₁ = 1`, forcing `D₀₀² = -1`. -/
theorem exists_diagonalizable_add_not_diagonalizable :
    ∃ M N : Matrix (Fin 2) (Fin 2) ℚ,
      M.IsDiagonalizable ∧ N.IsDiagonalizable ∧ ¬ (M + N).IsDiagonalizable := by
  refine ⟨!![-2, -1; 1, 1/2], !![2, 0; 0, -1/2], ?_, ?_, ?_⟩
  · -- `M` is diagonalized by `P = !![1,2;-2,-1]` (columns = eigenvectors for `0, -3/2`).
    refine ⟨!![1, 2; -2, -1], ?_, ?_⟩
    · rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two_of]; norm_num
    · have hinv : (!![1, 2; -2, -1] : Matrix (Fin 2) (Fin 2) ℚ)⁻¹ = !![-1/3, -2/3; 2/3, 1/3] :=
        Matrix.inv_eq_right_inv (by rw [Matrix.one_fin_two]; norm_num [Matrix.mul_fin_two])
      rw [hinv, show
        (!![-1/3, -2/3; 2/3, 1/3] : Matrix (Fin 2) (Fin 2) ℚ) * !![-2, -1; 1, 1/2]
            * !![1, 2; -2, -1]
          = !![0, 0; 0, -3/2] by ext i j; fin_cases i <;> fin_cases j <;>
            norm_num [Matrix.mul_fin_two]]
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
  · -- `N` is diagonal, hence diagonalizable.
    refine Matrix.IsDiagonalizable.of_isDiag ?_
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · -- `M + N = !![0,-1;1,0]` is not diagonalizable over `ℚ` (eigenvalues `±i`).
    rintro ⟨P, hP, hdiag⟩
    have hsum : (!![-2, -1; 1, 1/2] : Matrix (Fin 2) (Fin 2) ℚ) + !![2, 0; 0, -1/2]
        = !![0, -1; 1, 0] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.add_apply] <;> norm_num
    rw [hsum] at hdiag
    set D := P⁻¹ * (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ) * P with hDdef
    have htr : Matrix.trace D = 0 := by
      rw [hDdef, Matrix.trace_conj' hP]; norm_num [Matrix.trace_fin_two_of]
    have hdet : Matrix.det D = 1 := by
      rw [hDdef, Matrix.det_conj' hP]; norm_num [Matrix.det_fin_two_of]
    have h01 : D 0 1 = 0 := hdiag (by decide)
    have h10 : D 1 0 = 0 := hdiag (by decide)
    rw [Matrix.trace_fin_two] at htr
    have hprod : D 0 0 * D 1 1 = 1 := by
      rw [Matrix.det_fin_two, h01, h10] at hdet; simpa using hdet
    have hD11 : D 1 1 = -D 0 0 := by linarith
    rw [hD11] at hprod
    nlinarith [sq_nonneg (D 0 0), hprod]

/-- **Subtraction does not preserve diagonalizability.**  Diagonalizable matrices
    `M`, `N` can have a non-diagonalizable *difference* `M − N`, so the
    common-diagonalizer hypothesis of `sub_of_commonDiagonalizer` is genuinely
    necessary (not merely for products and sums).  Reduces to the additive
    counterexample `exists_diagonalizable_add_not_diagonalizable`: negation
    preserves diagonalizability (`IsDiagonalizable.neg`), so from diagonalizable
    `M`, `N` with `M + N` non-diagonalizable we obtain diagonalizable `M`, `−N`
    with `M − (−N) = M + N` non-diagonalizable.  Completes the trio of
    binary-operation counterexamples (product, sum, difference). -/
theorem exists_diagonalizable_sub_not_diagonalizable :
    ∃ M N : Matrix (Fin 2) (Fin 2) ℚ,
      M.IsDiagonalizable ∧ N.IsDiagonalizable ∧ ¬ (M - N).IsDiagonalizable := by
  obtain ⟨M, N, hM, hN, hMN⟩ := exists_diagonalizable_add_not_diagonalizable
  exact ⟨M, -N, hM, IsDiagonalizable.neg hN, by rwa [sub_neg_eq_add]⟩

end MinpolyCharpolyOQ02Incomplete01
