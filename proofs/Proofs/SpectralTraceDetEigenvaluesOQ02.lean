import Mathlib

/-!
# Cyclic invariance of the trace: `tr(A·B) = tr(B·A)`

The trace of a product is unchanged by cyclically permuting the factors.  This is the
workhorse behind similarity-invariance of the trace, the fact that the trace is a
conjugacy class function (and hence well defined on endomorphisms of a vector space, not
just on their matrices), the Killing/trace form in Lie theory, and the vanishing of the
trace of any commutator.

Mathlib proves the headline identities, so they carry the `mathlib` badge:

* `Matrix.trace_mul_comm` — `tr(A·B) = tr(B·A)`, even for **rectangular** `A : Matrix m n`
  and `B : Matrix n m` (the two products live in different matrix algebras!);
* `Matrix.trace_mul_cycle` — `tr(A·B·C) = tr(C·A·B)`.

We re-export those under self-documenting names and then add the content that the gallery
(and, in the case of the commutator identity, Mathlib's *elementary* surface) lacks:

* `trace_commutator_eq_zero` — `tr(A·B − B·A) = 0` written with an honest subtraction.
  Mathlib states this only through the Lie bracket (`matrix_trace_commutator_zero` for
  `⁅X, Y⁆`); the explicit `A·B − B·A` form is the one most calculations actually want;
* `trace_conj_of_isUnit_det` — **similarity invariance**: `tr(P⁻¹·A·P) = tr(A)` whenever
  `P` is invertible, stated with the *determinant* hypothesis `IsUnit P.det` and the
  Mathlib nonsingular inverse `P⁻¹`.  (Mathlib's `trace_conj'` asks for `IsUnit P` as a
  matrix; `IsUnit P.det` is the form one verifies in practice, and it ties this file to the
  spectral picture of [oq-01], where `det = 0` detects singularity.)
* `trace_eq_of_conj` — packaging the above as a class-function statement: similar matrices
  have equal trace.

Finally we connect cyclic invariance back to the **eigenvalue** picture of the companion
entry [oq-01] (`trace = Σ λ`, `det = Π λ`).  Conjugation leaves the characteristic
polynomial unchanged (`Matrix.charpoly_units_conj`), so over **any** field similar matrices
share their *entire eigenvalue multiset* — a strictly stronger statement than sharing trace
and determinant:

* `eigenvalues_units_conj` — `B = P⁻¹·A·P ⟹` `A` and `B` have the same multiset of
  eigenvalues (roots of the characteristic polynomial, counted with multiplicity);
* `sum_eigenvalues_units_conj`, `prod_eigenvalues_units_conj` — its trace-side and
  determinant-side specialisations, the eigenvalue-sum and eigenvalue-product invariance
  that recover `tr(P⁻¹·A·P) = tr(A)` and `det(P⁻¹·A·P) = det(A)` through the [oq-01]
  identities.

The closing examples illustrate the phenomena concretely over `ℤ`:

* a **cross-dimension** witness where `A·B` is `1×1` and `B·A` is `2×2`, yet both traces
  equal `11` — the cleanest demonstration that cyclic invariance is *not* about
  rearranging diagonal entries of a fixed matrix;
* a **non-commuting** pair with `A·B ≠ B·A` but `tr(A·B) = tr(B·A) = 3`;
* the commutator of that pair, whose trace is `0`.

All results are fully machine-checked with no `sorry` and no extra axioms.
-/

namespace SpectralTraceDetEigenvaluesOQ02

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R]

/-! ### The headline identities (re-exported from Mathlib) -/

/-- **Cyclic invariance of the trace**, `tr(A·B) = tr(B·A)`, including the rectangular case
`A : Matrix m n R` and `B : Matrix n m R` where the two products `A·B : Matrix m m R` and
`B·A : Matrix n n R` need not even have the same size.  This is `Matrix.trace_mul_comm`. -/
theorem trace_mul_comm {m l : Type*} [Fintype m] [Fintype l]
    (A : Matrix m l R) (B : Matrix l m R) :
    (A * B).trace = (B * A).trace :=
  Matrix.trace_mul_comm A B

/-- **Three-factor cyclic invariance**, `tr(A·B·C) = tr(C·A·B)`.  This is
`Matrix.trace_mul_cycle`. -/
theorem trace_mul_cycle {m l p : Type*} [Fintype m] [Fintype l] [Fintype p]
    (A : Matrix m l R) (B : Matrix l p R) (C : Matrix p m R) :
    (A * B * C).trace = (C * A * B).trace :=
  Matrix.trace_mul_cycle A B C

/-! ### Genuine content beyond Mathlib's elementary surface -/

/-- **The trace of a commutator vanishes**, `tr(A·B − B·A) = 0`, written with an explicit
subtraction (over any commutative ring).  Mathlib proves this only via the Lie bracket
`⁅X, Y⁆`; here it is the immediate consequence of cyclic invariance. -/
theorem trace_commutator_eq_zero (A B : Matrix n n R) :
    (A * B - B * A).trace = 0 := by
  rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

/-- **Similarity invariance of the trace** (determinant form).  If `P` is invertible — that
is, `IsUnit P.det` — then conjugating `A` by `P` (using the Mathlib nonsingular inverse
`P⁻¹`) leaves the trace unchanged: `tr(P⁻¹·A·P) = tr(A)`.

This is the practically usable companion of Mathlib's `Matrix.trace_conj'`, which asks for
`IsUnit P` as an element of the matrix ring.  The determinant hypothesis is the one checked
in computations, and it connects cyclic invariance to the spectral picture in which
`det = 0` precisely detects a singular matrix. -/
theorem trace_conj_of_isUnit_det (A P : Matrix n n R) (hP : IsUnit P.det) :
    (P⁻¹ * A * P).trace = A.trace := by
  rw [Matrix.trace_mul_cycle, Matrix.mul_nonsing_inv P hP, Matrix.one_mul]

/-- **The trace is a conjugacy class function.**  Similar matrices have equal trace: if
`B = P⁻¹·A·P` with `P` invertible (`IsUnit P.det`), then `tr(B) = tr(A)`.  In particular
the trace descends to a well-defined invariant of a linear endomorphism, independent of the
chosen basis. -/
theorem trace_eq_of_conj {A B P : Matrix n n R} (hP : IsUnit P.det)
    (h : B = P⁻¹ * A * P) : B.trace = A.trace := by
  rw [h]; exact trace_conj_of_isUnit_det A P hP

/-! ### From cyclic invariance to the eigenvalues (bridge to [oq-01])

Conjugation preserves the characteristic polynomial, so similar matrices share the *whole*
multiset of eigenvalues — not merely their sum (the trace) and product (the determinant).
We phrase this over a field, where `Polynomial.roots` is the eigenvalue multiset used in
[oq-01]. -/

section Eigenvalues

variable {K : Type*} [Field K]

/-- The eigenvalues of `A`, counted with algebraic multiplicity: the multiset of roots of
the characteristic polynomial (matching the convention of [oq-01]). -/
noncomputable abbrev eigenvalues (A : Matrix n n K) : Multiset K := A.charpoly.roots

/-- **Similar matrices have the same eigenvalues.**  For an invertible `P : (Matrix n n K)ˣ`
the conjugate `P⁻¹·A·P` has exactly the same multiset of eigenvalues as `A`, over any field.
This refines similarity-invariance of the trace and determinant (which are only the sum and
product of these eigenvalues) to the full spectrum with multiplicities, via Mathlib's
`Matrix.charpoly_units_conj`. -/
theorem eigenvalues_units_conj (P : (Matrix n n K)ˣ) (A : Matrix n n K) :
    eigenvalues (P⁻¹.val * A * P.val) = eigenvalues A := by
  unfold eigenvalues
  rw [Matrix.charpoly_units_conj']

/-- **Eigenvalue-sum invariance.**  The sum of the eigenvalues is a similarity invariant —
the trace-side shadow of `eigenvalues_units_conj`.  Combined with `trace = Σ λ` from
[oq-01] this re-derives `tr(P⁻¹·A·P) = tr(A)`. -/
theorem sum_eigenvalues_units_conj (P : (Matrix n n K)ˣ) (A : Matrix n n K) :
    (eigenvalues (P⁻¹.val * A * P.val)).sum = (eigenvalues A).sum := by
  rw [eigenvalues_units_conj]

/-- **Eigenvalue-product invariance.**  The product of the eigenvalues is a similarity
invariant — the determinant-side shadow of `eigenvalues_units_conj`.  Combined with
`det = Π λ` from [oq-01] this re-derives `det(P⁻¹·A·P) = det(A)`. -/
theorem prod_eigenvalues_units_conj (P : (Matrix n n K)ˣ) (A : Matrix n n K) :
    (eigenvalues (P⁻¹.val * A * P.val)).prod = (eigenvalues A).prod := by
  rw [eigenvalues_units_conj]

end Eigenvalues

/-! ### Concrete illustrations over `ℤ`

The first example is the conceptual heart of cyclic invariance: the two products do not
even have the same dimension. -/

/-- **Cross-dimension witness.**  With `A : Matrix (Fin 1) (Fin 2) ℤ` and
`B : Matrix (Fin 2) (Fin 1) ℤ`, the product `A·B` is the `1×1` matrix `[11]` while `B·A` is
the `2×2` matrix `!![3, 6; 4, 8]`.  Their traces — computed in different matrix algebras —
both equal `11`. -/
theorem trace_mul_comm_cross_dim :
    ((!![(1 : ℤ), 2] : Matrix (Fin 1) (Fin 2) ℤ) * (!![3; 4] : Matrix (Fin 2) (Fin 1) ℤ)).trace
      = ((!![(3 : ℤ); 4] : Matrix (Fin 2) (Fin 1) ℤ) * (!![1, 2] : Matrix (Fin 1) (Fin 2) ℤ)).trace := by
  rw [trace_mul_comm]

/-- The common value of both traces in the cross-dimension example is `11`. -/
theorem trace_mul_comm_cross_dim_value :
    ((!![(1 : ℤ), 2] : Matrix (Fin 1) (Fin 2) ℤ) * (!![3; 4] : Matrix (Fin 2) (Fin 1) ℤ)).trace = 11 := by
  rw [Matrix.trace_fin_one]
  norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- **A non-commuting pair with equal traces of the two products.**  For
`A = !![1, 2; 3, 4]` and `B = !![0, 1; 0, 0]` we have `A·B = !![0, 1; 0, 3]` and
`B·A = !![3, 4; 0, 0]`, so `A·B ≠ B·A`, yet `tr(A·B) = tr(B·A) = 3`. -/
theorem trace_mul_comm_noncomm_example :
    ((!![(1 : ℤ), 2; 3, 4]) * !![0, 1; 0, 0]).trace
      = ((!![(0 : ℤ), 1; 0, 0]) * !![1, 2; 3, 4]).trace := by
  rw [trace_mul_comm]

/-- The two products in the non-commuting example are genuinely different matrices, so the
equality of traces is not an accident of `A·B = B·A`. -/
theorem mul_comm_noncomm_example_ne :
    (!![(1 : ℤ), 2; 3, 4]) * !![0, 1; 0, 0] ≠ (!![(0 : ℤ), 1; 0, 0]) * !![1, 2; 3, 4] := by
  decide

/-- The common trace of both products in the non-commuting example is `3`. -/
theorem trace_mul_comm_noncomm_value :
    ((!![(1 : ℤ), 2; 3, 4]) * !![0, 1; 0, 0]).trace = 3 := by
  rw [Matrix.trace_fin_two]
  norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- **The commutator of the non-commuting pair has trace zero**, as guaranteed by
`trace_commutator_eq_zero`. -/
theorem trace_commutator_example :
    ((!![(1 : ℤ), 2; 3, 4]) * !![0, 1; 0, 0]
        - (!![(0 : ℤ), 1; 0, 0]) * !![1, 2; 3, 4]).trace = 0 :=
  trace_commutator_eq_zero _ _

end SpectralTraceDetEigenvaluesOQ02

#print axioms SpectralTraceDetEigenvaluesOQ02.trace_commutator_eq_zero
#print axioms SpectralTraceDetEigenvaluesOQ02.trace_conj_of_isUnit_det
#print axioms SpectralTraceDetEigenvaluesOQ02.trace_eq_of_conj
#print axioms SpectralTraceDetEigenvaluesOQ02.eigenvalues_units_conj
#print axioms SpectralTraceDetEigenvaluesOQ02.trace_mul_comm_cross_dim_value
#print axioms SpectralTraceDetEigenvaluesOQ02.mul_comm_noncomm_example_ne
