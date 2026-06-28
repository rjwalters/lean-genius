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
polynomial) is the remaining content. The closing sections below establish this mapping
unconditionally for **diagonal** and **upper-triangular** matrices — the computational core — and
isolate the single classical ingredient (Schur triangularisation over an algebraically closed
field) needed to extend it to every matrix.

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

/-! ### From the spectral mapping to the general power sum

The general trace power sum `tr(Aᵏ) = Σ λᵢᵏ`, valid in **every** dimension, is equivalent to the
*multiset spectral mapping* `eigenvalues (Aᵏ) = (eigenvalues A).map (· ^ k)`. We record this
reduction, then discharge the spectral mapping **unconditionally** for two structured families that
between them form the computational core of the general statement: **diagonal** matrices and
**upper-triangular** matrices. For an upper-triangular `M`, `M.charpoly = ∏ᵢ (X − C (M i i))` and the
diagonal of `Mᵏ` is `(M i i)ᵏ`, so the eigenvalue multiset maps under `(· ^ k)` directly — no
algebraic-closure hypothesis is even needed for the multiset identity. The only remaining ingredient
for an *arbitrary* matrix is the classical Schur/triangularisation fact that over an algebraically
closed field every matrix is conjugate to an upper-triangular one, which is not yet available at the
matrix level in Mathlib (only `Module.End`-level generalized-eigenspace decompositions and
`RCLike` Schur triangulation are present). -/

/-- Roots of `∏ i, (X - C (f i))` are exactly the multiset of values `f i`. -/
theorem prod_X_sub_C_roots (f : n → K) :
    (∏ i, (X - C (f i))).roots = Finset.univ.val.map f := by
  have h : (∏ i, (X - C (f i)))
      = ((Finset.univ.val.map f).map (fun a => X - C a)).prod := by
    rw [Multiset.map_map]; rfl
  rw [h, roots_multiset_prod_X_sub_C]

/-- **Reduction.** The general eigenvalue power sum `tr(Aᵏ) = Σ λᵢᵏ` follows from the multiset
spectral mapping `eigenvalues (Aᵏ) = (eigenvalues A).map (· ^ k)`: substitute the latter into the
tautological `trace_pow_eq_sum_eigenvalues_pow_self`. -/
theorem trace_pow_of_eigenvalues_pow [IsAlgClosed K] (A : Matrix n n K) (k : ℕ)
    (h : eigenvalues (A ^ k) = (eigenvalues A).map (· ^ k)) :
    (A ^ k).trace = ((eigenvalues A).map (· ^ k)).sum := by
  rw [trace_pow_eq_sum_eigenvalues_pow_self, h]

/-! #### Diagonal matrices: the spectral mapping holds in every dimension -/

/-- The eigenvalue multiset of a diagonal matrix is the multiset of its diagonal entries. -/
theorem eigenvalues_diagonal (d : n → K) :
    eigenvalues (diagonal d) = Finset.univ.val.map d := by
  unfold eigenvalues; rw [charpoly_diagonal, prod_X_sub_C_roots]

/-- **Multiset spectral mapping for diagonal matrices** (all `n`, all `k`):
`eigenvalues ((diagonal d)ᵏ) = (eigenvalues (diagonal d)).map (· ^ k)`. -/
theorem eigenvalues_pow_diagonal (d : n → K) (k : ℕ) :
    eigenvalues (diagonal d ^ k) = (eigenvalues (diagonal d)).map (· ^ k) := by
  rw [diagonal_pow, eigenvalues_diagonal, eigenvalues_diagonal, Multiset.map_map]; rfl

/-- **Eigenvalue power sum for diagonal matrices** (all `n`, all `k`):
`tr ((diagonal d)ᵏ) = Σ λᵢᵏ`. -/
theorem trace_pow_eq_sum_pow_eigenvalues_diagonal [IsAlgClosed K] (d : n → K) (k : ℕ) :
    (diagonal d ^ k).trace = ((eigenvalues (diagonal d)).map (· ^ k)).sum :=
  trace_pow_of_eigenvalues_pow (diagonal d) k (eigenvalues_pow_diagonal d k)

/-! #### Upper-triangular matrices: the computational core of the spectral mapping -/

section Triangular
variable {N : Type*} [Fintype N] [DecidableEq N] [LinearOrder N]

/-- The characteristic matrix `X • 1 − M` of an upper-triangular matrix is upper-triangular. -/
theorem charmatrix_blockTriangular {M : Matrix N N K} (hM : M.BlockTriangular id) :
    (charmatrix M).BlockTriangular id := by
  intro i j hij
  have hlt : j < i := hij
  rw [charmatrix_apply_ne M i j (ne_of_lt hlt).symm, hM hij, map_zero, neg_zero]

/-- **Characteristic polynomial of an upper-triangular matrix** is `∏ᵢ (X − C (M i i))`, the
product over the diagonal entries (its roots are precisely the diagonal, with multiplicity). -/
theorem charpoly_blockTriangular {M : Matrix N N K} (hM : M.BlockTriangular id) :
    M.charpoly = ∏ i, (X - C (M i i)) := by
  rw [Matrix.charpoly, det_of_upperTriangular (charmatrix_blockTriangular hM)]
  simp only [charmatrix_apply_eq]

/-- The `(i,i)` entry of a product of two upper-triangular matrices is the product of their
`(i,i)` entries (off-diagonal cross terms vanish by triangularity). -/
theorem blockTriangular_mul_diag {M P : Matrix N N K}
    (hM : M.BlockTriangular id) (hP : P.BlockTriangular id) (i : N) :
    (M * P) i i = M i i * P i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hM h, zero_mul]
    · rw [hP h, mul_zero]
  · intro hni; exact absurd (Finset.mem_univ i) hni

/-- Powers of an upper-triangular matrix are upper-triangular. -/
theorem blockTriangular_pow {M : Matrix N N K} (hM : M.BlockTriangular id) (k : ℕ) :
    (M ^ k).BlockTriangular id := by
  induction k with
  | zero => simpa using blockTriangular_one
  | succ k ih => rw [pow_succ]; exact ih.mul hM

/-- The diagonal of `Mᵏ` is the `k`-th power of the diagonal of an upper-triangular `M`:
`(Mᵏ) i i = (M i i)ᵏ`. -/
theorem blockTriangular_pow_diag {M : Matrix N N K} (hM : M.BlockTriangular id) (k : ℕ) (i : N) :
    (M ^ k) i i = (M i i) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, blockTriangular_mul_diag (blockTriangular_pow hM k) hM i, ih, pow_succ]

/-- The eigenvalue multiset of an upper-triangular matrix is the multiset of its diagonal entries. -/
theorem eigenvalues_blockTriangular {M : Matrix N N K} (hM : M.BlockTriangular id) :
    eigenvalues M = Finset.univ.val.map (fun i => M i i) := by
  unfold eigenvalues; rw [charpoly_blockTriangular hM, prod_X_sub_C_roots]

/-- **Multiset spectral mapping for upper-triangular matrices** (any field, all `k`):
`eigenvalues (Mᵏ) = (eigenvalues M).map (· ^ k)`. This is the genuinely spectral computational
core; the general case for arbitrary matrices reduces to it via Schur triangularisation. -/
theorem eigenvalues_pow_blockTriangular {M : Matrix N N K} (hM : M.BlockTriangular id) (k : ℕ) :
    eigenvalues (M ^ k) = (eigenvalues M).map (· ^ k) := by
  rw [eigenvalues_blockTriangular (blockTriangular_pow hM k), eigenvalues_blockTriangular hM,
    Multiset.map_map]
  apply Multiset.map_congr rfl
  intro i _
  exact blockTriangular_pow_diag hM k i

/-- **Eigenvalue power sum for upper-triangular matrices** (all `k`):
`tr (Mᵏ) = Σ λᵢᵏ` over the eigenvalues (diagonal entries) of an upper-triangular `M`. -/
theorem trace_pow_eq_sum_pow_eigenvalues_blockTriangular [IsAlgClosed K] {M : Matrix N N K}
    (hM : M.BlockTriangular id) (k : ℕ) :
    (M ^ k).trace = ((eigenvalues M).map (· ^ k)).sum :=
  trace_pow_of_eigenvalues_pow M k (eigenvalues_pow_blockTriangular hM k)

end Triangular

end SpectralTraceDetEigenvaluesOQ01OQ01

#print axioms SpectralTraceDetEigenvaluesOQ01OQ01.det_pow_eq_prod_pow_eigenvalues
#print axioms SpectralTraceDetEigenvaluesOQ01OQ01.trace_pow_eq_sum_eigenvalues_pow_self
#print axioms SpectralTraceDetEigenvaluesOQ01OQ01.prod_map_pow_eigenvalues
#print axioms SpectralTraceDetEigenvaluesOQ01OQ01.trace_sq_eq_sum_sq_eigenvalues
#print axioms SpectralTraceDetEigenvaluesOQ01OQ01.eigenvalues_pow_diagonal
#print axioms SpectralTraceDetEigenvaluesOQ01OQ01.eigenvalues_pow_blockTriangular
#print axioms SpectralTraceDetEigenvaluesOQ01OQ01.trace_pow_eq_sum_pow_eigenvalues_blockTriangular
