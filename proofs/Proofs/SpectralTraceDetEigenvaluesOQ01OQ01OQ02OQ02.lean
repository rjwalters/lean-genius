import Mathlib
import Proofs.SpectralTraceDetEigenvaluesOQ01

/-
# Spectral trace, OQ-01 → OQ-01 → OQ-02 → OQ-02: the trace power sum `tr(Aᵏ) = Σ λᵢᵏ`
in **all dimensions** and for **all powers**, via the spectral-mapping technique

## Background and what is new

The parent line proved Newton's power-sum identity one dimension at a time:

* `spectral-trace-det-eigenvalues-oq-01-oq-01` — `tr(A²) = λ₁² + λ₂²` for `2 × 2` matrices,
* `spectral-trace-det-eigenvalues-oq-01-oq-01-oq-02` — `tr(A³) = λ₁³ + λ₂³ + λ₃³` for `3 × 3`.

Each step matched a **dimension-specific** matrix Newton identity (closed by `ring` on the
entries) against the corresponding multiset identity, using Vieta to identify the elementary
symmetric functions.  That route is intrinsically bounded: the `ring` identity has to be
rewritten by hand for every new `(k, n)`.

This file removes both restrictions at once for **diagonalizable** matrices, replacing the
per-dimension `ring` computations by the dimension-free **spectral-mapping** mechanism:

      A = M · diag(d) · M⁻¹     ⟹     Aᵏ = M · diag(d)ᵏ · M⁻¹ = M · diag(dᵏ) · M⁻¹,

so the trace is conjugation-invariant and reads off the diagonal:

      tr(Aᵏ) = tr(diag(d)ᵏ) = Σᵢ (dᵢ)ᵏ,

while the eigenvalue multiset (the roots of the characteristic polynomial) is the multiset
`{dᵢ}` — *with multiplicity* — because `charpoly(diag d) = ∏ᵢ (X − dᵢ)`.  Combining the two:

      tr(Aᵏ) = Σ_{λ ∈ eigenvalues A} λᵏ          for every `k` and every dimension.

## Results

* `trace_diagonal_pow` — for any diagonal matrix and any `k`, `tr(diag(d)ᵏ) = Σᵢ (dᵢ)ᵏ`
  (over any commutative ring).
* `units_conj_pow` / `trace_pow_units_conj` — conjugation by a unit commutes with powers, hence
  the trace of a power is conjugation-invariant: `tr((M A M⁻¹)ᵏ) = tr(Aᵏ)`.
* `roots_charpoly_diagonal` — the eigenvalue multiset of a diagonal matrix is exactly its
  diagonal (with multiplicity): `(diag d).charpoly.roots = (univ : Finset n).val.map d`.
* `trace_pow_eq_sum_pow_eigenvalues` — **the headline spectral identity**, in all dimensions and
  for all powers, for any matrix `A = M · diag(d) · M⁻¹`:

        tr(Aᵏ) = ((eigenvalues A).map (· ^ k)).sum.

  Specialising `k = 1` recovers the parent headline `trace_eq_sum_eigenvalues`; the genuinely new
  content is uniformity in both `k` and the dimension.
* `card_eigenvalues_diagonalizable` — such an `A` has exactly `Fintype.card n` eigenvalues counted
  with multiplicity, over *any* field (no algebraic closure needed: the characteristic polynomial
  already splits).

## Honesty / scope

The theorem is stated for **diagonalizable** matrices (`A = M · diag(d) · M⁻¹`).  This is the
dense/generic case and the natural reach of an elementary spectral-mapping argument that uses only
conjugation invariance and `charpoly_diagonal`.  The fully general statement (every matrix over an
algebraically closed field) additionally needs **triangularization** — similarity to an
upper-triangular matrix with the eigenvalues on the diagonal — which Mathlib does not currently
expose at the matrix level (only the endomorphism generalized-eigenspace decomposition).  That
extension is recorded as the open follow-up.  No `native_decide`; `#print axioms` confirms only the
standard foundational axioms.
-/

namespace SpectralTraceDetEigenvaluesOQ01OQ01OQ02OQ02

open Matrix Polynomial
open SpectralTraceDetEigenvaluesOQ01 (eigenvalues)

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Part I: the diagonal power sum and conjugation invariance (over any commutative ring) -/

variable {R : Type*} [CommRing R]

/-- **Trace of a power of a diagonal matrix is the power sum of its diagonal entries.**
`tr(diag(d)ᵏ) = Σᵢ (dᵢ)ᵏ`, over any commutative ring.  The single fact behind every diagonal
power-sum: `diag(d)ᵏ = diag(dᵏ)` and the trace of a diagonal matrix is the sum of its entries. -/
theorem trace_diagonal_pow (d : n → R) (k : ℕ) :
    ((diagonal d) ^ k).trace = ∑ i, (d i) ^ k := by
  rw [diagonal_pow, trace_diagonal]
  simp only [Pi.pow_apply]

/-- **Conjugation by a unit commutes with taking powers.**
`(M · N · M⁻¹)ᵏ = M · Nᵏ · M⁻¹`. -/
theorem units_conj_pow (M : (Matrix n n R)ˣ) (N : Matrix n n R) (k : ℕ) :
    ((M : Matrix n n R) * N * (↑M⁻¹ : Matrix n n R)) ^ k
      = (M : Matrix n n R) * N ^ k * (↑M⁻¹ : Matrix n n R) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (↑M⁻¹ : Matrix n n R) (↑M : Matrix n n R), Units.inv_mul, one_mul]

/-- **The trace of a power is conjugation-invariant.** `tr((M · N · M⁻¹)ᵏ) = tr(Nᵏ)`. -/
theorem trace_pow_units_conj (M : (Matrix n n R)ˣ) (N : Matrix n n R) (k : ℕ) :
    (((M : Matrix n n R) * N * (↑M⁻¹ : Matrix n n R)) ^ k).trace = (N ^ k).trace := by
  rw [units_conj_pow, trace_units_conj]

/-! ## Part II: eigenvalues of a diagonal matrix (over a field) -/

variable {K : Type*} [Field K]

/-- **The eigenvalue multiset of a diagonal matrix is its diagonal, with multiplicity.**
`(diag d).charpoly.roots = (univ : Finset n).val.map d`.  Repeated diagonal entries appear with
the correct multiplicity because we use the *multiset* form of `roots (∏ (X − aᵢ)) = {aᵢ}`. -/
theorem roots_charpoly_diagonal (d : n → K) :
    (diagonal d).charpoly.roots = (Finset.univ : Finset n).val.map d := by
  rw [charpoly_diagonal, ← roots_multiset_prod_X_sub_C ((Finset.univ : Finset n).val.map d)]
  congr 1
  rw [Multiset.map_map]
  rfl

/-! ## Part III: the spectral trace power sum in all dimensions and all powers -/

/-- **The trace power sum `tr(Aᵏ) = Σ λᵢᵏ`, uniformly in the power `k` and the dimension `n`,**
for a diagonalizable matrix `A = M · diag(d) · M⁻¹`.

Over *any* field, the trace of the `k`-th power is the `k`-th power sum of the eigenvalues of `A`
(the roots of its characteristic polynomial, counted with multiplicity):

      tr(Aᵏ) = ((eigenvalues A).map (· ^ k)).sum.

The trace side is conjugation invariance + the diagonal power sum (`trace_pow_units_conj`,
`trace_diagonal_pow`); the eigenvalue side is conjugation invariance of the characteristic
polynomial (`charpoly_units_conj`) + `roots_charpoly_diagonal`.  No algebraic closure is needed:
the characteristic polynomial of a diagonalizable matrix already splits. -/
theorem trace_pow_eq_sum_pow_eigenvalues (A : Matrix n n K) (M : (Matrix n n K)ˣ) (d : n → K)
    (hA : A = (M : Matrix n n K) * diagonal d * (↑M⁻¹ : Matrix n n K)) (k : ℕ) :
    (A ^ k).trace = ((eigenvalues A).map (· ^ k)).sum := by
  have htrace : (A ^ k).trace = ∑ i, (d i) ^ k := by
    rw [hA, trace_pow_units_conj, trace_diagonal_pow]
  have hroots : eigenvalues A = (Finset.univ : Finset n).val.map d := by
    show A.charpoly.roots = _
    rw [hA, charpoly_units_conj]
    exact roots_charpoly_diagonal d
  rw [htrace, hroots, Multiset.map_map]
  rfl

/-- A diagonalizable matrix `A = M · diag(d) · M⁻¹` has exactly `Fintype.card n` eigenvalues counted
with multiplicity, over *any* field — no algebraic closure required, since its characteristic
polynomial splits. -/
theorem card_eigenvalues_diagonalizable (A : Matrix n n K) (M : (Matrix n n K)ˣ) (d : n → K)
    (hA : A = (M : Matrix n n K) * diagonal d * (↑M⁻¹ : Matrix n n K)) :
    Multiset.card (eigenvalues A) = Fintype.card n := by
  have hroots : eigenvalues A = (Finset.univ : Finset n).val.map d := by
    show A.charpoly.roots = _
    rw [hA, charpoly_units_conj]
    exact roots_charpoly_diagonal d
  rw [hroots, Multiset.card_map, ← Finset.card_def, Finset.card_univ]

/-! ## Part IV: concrete illustrations -/

/-- For the diagonal matrix `diag(2, 3)` the power sum identity gives `tr(A³) = 2³ + 3³ = 35`,
read directly off the (already diagonal) eigenvalues — with `k = 3` and no `ring` computation. -/
theorem trace_pow_diagonal_example :
    ((diagonal ![(2 : ℚ), 3]) ^ 3).trace = 35 := by
  rw [trace_diagonal_pow]
  norm_num [Fin.sum_univ_two]

/-- The same diagonal matrix has two eigenvalues `{2, 3}`, and their cubes sum to `35`, matching
`tr(A³)`. -/
theorem sum_pow_eigenvalues_example :
    ((eigenvalues (diagonal ![(2 : ℚ), 3])).map (· ^ 3)).sum = 35 := by
  show (((diagonal ![(2 : ℚ), 3]).charpoly.roots).map (· ^ 3)).sum = 35
  rw [roots_charpoly_diagonal, Multiset.map_map]
  show (∑ i, (![(2 : ℚ), 3] i) ^ 3) = 35
  norm_num [Fin.sum_univ_two]

end SpectralTraceDetEigenvaluesOQ01OQ01OQ02OQ02

-- Axiom audit: only the standard foundational axioms — no `Lean.ofReduceBool`
-- (no `native_decide`) and no `sorryAx`.
#print axioms SpectralTraceDetEigenvaluesOQ01OQ01OQ02OQ02.trace_pow_eq_sum_pow_eigenvalues
#print axioms SpectralTraceDetEigenvaluesOQ01OQ01OQ02OQ02.roots_charpoly_diagonal
#print axioms SpectralTraceDetEigenvaluesOQ01OQ01OQ02OQ02.card_eigenvalues_diagonalizable
