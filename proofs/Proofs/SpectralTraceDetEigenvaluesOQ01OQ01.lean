import Mathlib

/-
# Power sums of the eigenvalues: `det(Aᵏ)` and `tr(Aᵏ)` spectrally

Continuing [oq-01] (`SpectralTraceDetEigenvaluesOQ01`), where the trace and determinant of a
square matrix `A : Matrix n n K` were read off from its **eigenvalue multiset**
`eigenvalues A := A.charpoly.roots` (the roots of the characteristic polynomial, counted with
algebraic multiplicity):

* `trace = Σ λᵢ`  (`trace_eq_sum_eigenvalues`)
* `det   = Π λᵢ`  (`det_eq_prod_eigenvalues`)

this entry studies what happens to those symmetric functions under **matrix powers** `A ^ k`.

## The determinant power identity (the clean half)

For the determinant there is no obstruction: `det` is multiplicative, so `det (Aᵏ) = (det A)ᵏ`,
and a product of `k`-th powers is the `k`-th power of the product. Hence

* `det_pow_eq_prod_pow_eigenvalues` — `det (Aᵏ) = Π (λᵢ ᵏ)`: the determinant of `Aᵏ` is the
  product of the `k`-th powers of the eigenvalues of `A`.

This is the determinant instance of the **spectral mapping theorem** `spec(p(A)) = p(spec(A))`
specialised to `p(X) = Xᵏ`, and it needs nothing beyond multiplicativity of the determinant —
in particular it holds over **any** algebraically closed field with no triangularisation.

## The trace power identity (Newton's power sums)

For the trace the analogous statement `tr (Aᵏ) = Σ (λᵢ ᵏ)` is the genuinely spectral fact: the
`k`-th **power sum** of the eigenvalues. Unlike the determinant it does *not* reduce to a
one-line algebraic identity in `A`; it is the trace half of the spectral mapping theorem and is
equivalent to the eigenvalue multiset of `Aᵏ` being `(eigenvalues A).map (· ^ k)`. What *is*
available cleanly from [oq-01] is the tautological reading

* `trace_pow_eq_sum_eigenvalues_pow_self` — `tr (Aᵏ) = Σ μⱼ` where `μⱼ = eigenvalues (Aᵏ)`,
  i.e. the trace of `Aᵏ` is the sum of the eigenvalues *of `Aᵏ`*.

Identifying those `μⱼ` with `λᵢ ᵏ` (the multiset spectral mapping for the full characteristic
polynomial) is the remaining content; see the closing note.

All results below are fully machine-checked with no `sorry` and no extra axioms.
-/

namespace SpectralTraceDetEigenvaluesOQ01OQ01

open Matrix Polynomial

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {K : Type*} [Field K]

/-- The eigenvalue multiset of `A`, as in [oq-01]: the roots of the characteristic polynomial,
counted with algebraic multiplicity.  A reducible alias for `A.charpoly.roots`. -/
noncomputable abbrev eigenvalues (A : Matrix n n K) : Multiset K := A.charpoly.roots

/-! ### The determinant power identity -/

/-- **Determinant of a power, multiplicatively.**  Over any commutative ring,
`det (Aᵏ) = (det A)ᵏ`. -/
theorem det_pow (A : Matrix n n K) (k : ℕ) : (A ^ k).det = A.det ^ k :=
  Matrix.det_pow A k

/-- A product of `k`-th powers is the `k`-th power of the product, at the level of the
eigenvalue multiset: `Π (λᵢ ᵏ) = (Π λᵢ) ᵏ`. -/
theorem prod_map_pow_eigenvalues (A : Matrix n n K) (k : ℕ) :
    ((eigenvalues A).map (· ^ k)).prod = (eigenvalues A).prod ^ k := by
  simpa using Multiset.prod_hom (eigenvalues A) (powMonoidHom k)

/-- **Determinant power identity (spectral form).**  Over an algebraically closed field, the
determinant of `Aᵏ` is the product of the `k`-th powers of the eigenvalues of `A`:
`det (Aᵏ) = Π (λᵢ ᵏ)`.  This is the determinant instance of the spectral mapping theorem for
`p(X) = Xᵏ`; it follows purely from multiplicativity of the determinant and the [oq-01]
identity `det A = Π λᵢ`, with no triangularisation. -/
theorem det_pow_eq_prod_pow_eigenvalues [IsAlgClosed K] (A : Matrix n n K) (k : ℕ) :
    (A ^ k).det = ((eigenvalues A).map (· ^ k)).prod := by
  rw [det_pow, prod_map_pow_eigenvalues, eigenvalues, ← A.det_eq_prod_roots_charpoly]

/-! ### The trace of a power as a sum of eigenvalues -/

/-- **Trace of a power as a sum of its own eigenvalues.**  Over an algebraically closed field,
the trace of `Aᵏ` is the sum of the eigenvalues of `Aᵏ` (the [oq-01] identity `trace = Σ λ`
applied to the matrix `Aᵏ`).  Identifying `eigenvalues (Aᵏ)` with `(eigenvalues A).map (· ^ k)`
upgrades this to the power-sum statement `tr (Aᵏ) = Σ (λᵢ ᵏ)`; see the closing note. -/
theorem trace_pow_eq_sum_eigenvalues_pow_self [IsAlgClosed K] (A : Matrix n n K) (k : ℕ) :
    (A ^ k).trace = (eigenvalues (A ^ k)).sum :=
  (A ^ k).trace_eq_sum_roots_charpoly

/-- The two extreme cases tie back to [oq-01]: the determinant power identity at `k = 1` is just
`det A = Π λᵢ`. -/
theorem det_pow_one [IsAlgClosed K] (A : Matrix n n K) :
    (A ^ 1).det = ((eigenvalues A).map (· ^ 1)).prod :=
  det_pow_eq_prod_pow_eigenvalues A 1

/-! ### The trace power sum `tr(A²) = Σ λᵢ²` for `2 × 2` matrices (first Newton identity)

For `1 × 1` and `2 × 2` matrices the trace power sum is reachable without the general spectral
mapping, via **Newton's identity** `p₂ = e₁² − 2 e₂`: the second power sum is determined by the
first two elementary symmetric functions, which [oq-01] already identifies as the trace and the
determinant. This is the genuinely spectral statement `tr(A²) = λ₁² + λ₂²` in the first
nontrivial dimension. -/

/-- **Newton's identity for a two-element multiset.**  The sum of squares of two numbers is the
square of their sum minus twice their product: `Σ xᵢ² = (Σ xᵢ)² − 2 ∏ xᵢ`. -/
theorem sum_sq_of_card_eq_two (s : Multiset K) (h : Multiset.card s = 2) :
    (s.map (· ^ 2)).sum = s.sum ^ 2 - 2 * s.prod := by
  obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.1 h
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.sum_cons, Multiset.sum_singleton, Multiset.prod_cons, Multiset.prod_singleton]
  ring

/-- The eigenvalue multiset of a `2 × 2` matrix over an algebraically closed field has exactly
two elements. -/
theorem card_eigenvalues_fin_two [IsAlgClosed K] (A : Matrix (Fin 2) (Fin 2) K) :
    Multiset.card (eigenvalues A) = 2 := by
  rw [eigenvalues, (Polynomial.splits_iff_card_roots).1 (IsAlgClosed.splits A.charpoly),
    Matrix.charpoly_natDegree_eq_dim]
  simp

/-- **Trace power sum in dimension two.**  Over an algebraically closed field, the trace of `A²`
is the sum of the squares of the eigenvalues of the `2 × 2` matrix `A`: `tr(A²) = λ₁² + λ₂²`.
The proof is Newton's identity `p₂ = e₁² − 2 e₂` with `e₁ = tr A = Σ λᵢ` and `e₂ = det A = ∏ λᵢ`
from [oq-01]; the matrix side `tr(A²) = (tr A)² − 2 det A` is the `2 × 2` Cayley–Hamilton
identity in disguise. -/
theorem trace_sq_eq_sum_sq_eigenvalues [IsAlgClosed K] (A : Matrix (Fin 2) (Fin 2) K) :
    (A ^ 2).trace = ((eigenvalues A).map (· ^ 2)).sum := by
  rw [sum_sq_of_card_eq_two (eigenvalues A) (card_eigenvalues_fin_two A), eigenvalues,
    ← A.trace_eq_sum_roots_charpoly, ← A.det_eq_prod_roots_charpoly, pow_two,
    Matrix.trace_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-! ### A concrete `2 × 2` illustration over `ℂ`

For `A = !![1, 2; 3, 4]` (eigenvalues `(5 ± √33)/2`, irrational) the determinant power identity
gives `det (A²) = (det A)² = (-2)² = 4` — equivalently the product of the squared eigenvalues —
without ever computing the eigenvalues. -/

/-- `det (A²) = 4` for `A = !![1, 2; 3, 4]`, equal to the product of the squared eigenvalues. -/
theorem det_sq_example :
    (!![(1 : ℂ), 2; 3, 4] ^ 2).det = ((eigenvalues (!![(1 : ℂ), 2; 3, 4])).map (· ^ 2)).prod := by
  rw [← det_pow_eq_prod_pow_eigenvalues]

/-- `tr (A²) = 29` for `A = !![1, 2; 3, 4]`, equal to the sum of the squared eigenvalues
`((5 + √33)/2)² + ((5 − √33)/2)² = 29` — obtained without computing the irrational eigenvalues. -/
theorem trace_sq_example :
    (!![(1 : ℂ), 2; 3, 4] ^ 2).trace
      = ((eigenvalues (!![(1 : ℂ), 2; 3, 4])).map (· ^ 2)).sum := by
  rw [trace_sq_eq_sum_sq_eigenvalues]

end SpectralTraceDetEigenvaluesOQ01OQ01

#print axioms SpectralTraceDetEigenvaluesOQ01OQ01.det_pow_eq_prod_pow_eigenvalues
#print axioms SpectralTraceDetEigenvaluesOQ01OQ01.trace_pow_eq_sum_eigenvalues_pow_self
#print axioms SpectralTraceDetEigenvaluesOQ01OQ01.prod_map_pow_eigenvalues
#print axioms SpectralTraceDetEigenvaluesOQ01OQ01.trace_sq_eq_sum_sq_eigenvalues
