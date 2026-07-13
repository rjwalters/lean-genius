import Mathlib

/-
# Cauchy Interlacing Theorem — statement of record (ORIENT)

For a Hermitian matrix `A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ` and the principal
`n × n` submatrix `B` obtained by deleting the last row and column, the sorted
eigenvalues of `B` interlace those of `A`.

## Convention

Mathlib provides `Matrix.IsHermitian.eigenvalues₀ : Fin (Fintype.card …) → ℝ`,
the eigenvalues listed in **descending** (antitone) order
(`Matrix.IsHermitian.eigenvalues₀_antitone`). Note the ordinary
`Matrix.IsHermitian.eigenvalues : n → ℝ` is reindexed by the matrix's index type
and is *not* sorted, so it cannot express "the k-th eigenvalue". We therefore
build everything on top of `eigenvalues₀`.

With the descending convention `λ₀ ≥ λ₁ ≥ … ≥ λₙ` for `A` and
`μ₀ ≥ … ≥ μ_{n-1}` for `B`, Cauchy interlacing reads

  `λ i ≥ μ i ≥ λ (i+1)`   for every `i : Fin n`,

equivalently `μ i ≤ λ i.castSucc` and `λ i.succ ≤ μ i`.

(Under the more common *ascending* textbook convention `λ_k ≤ μ_k ≤ λ_{k+1}` the
inequalities flip; the two are equivalent under `i ↦ n - i`.)

## Status

ORIENT / statement of record. The mathematical keystone is the Courant–Fischer
max–min variational characterisation of the descending k-th eigenvalue, which is
**not currently in Mathlib** (only the extreme cases — top/bottom eigenvalue as a
Rayleigh-quotient sup/inf — are available, via the inner-product Rayleigh API).
Given that characterisation, interlacing is a short subspace-inclusion argument:
the test subspaces available to `B` are exactly those contained in the
codimension-one coordinate subspace `span {e₀,…,e_{n-1}}`, a subset of those
available to `A`, which sandwiches each `μ i` between `λ i` and `λ (i+1)`.

The main theorem and the keystone lemma are left as `sorry`. This file is a
research skeleton and is intentionally **not** registered in `Proofs.lean`.
-/

open Matrix

namespace CauchyInterlacing

variable {N n : ℕ}

/-- Descending sorted eigenvalues of a Hermitian matrix on `Fin N`, indexed
naturally by `Fin N` (composing `eigenvalues₀` with the canonical
`Fin N ≃ Fin (Fintype.card (Fin N))`). -/
noncomputable def sortedEigs {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian) :
    Fin N → ℝ :=
  fun i => hA.eigenvalues₀ (Fin.cast (Fintype.card_fin N).symm i)

/-- `sortedEigs` is antitone (descending), inherited from `eigenvalues₀_antitone`
through the order-preserving reindexing `Fin.cast`. -/
lemma sortedEigs_antitone {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian) :
    Antitone (sortedEigs hA) := by
  intro i j hij
  refine hA.eigenvalues₀_antitone ?_
  simpa [Fin.le_iff_val_le_val] using hij

/-- The principal `n × n` submatrix of an `(n+1) × (n+1)` matrix obtained by
deleting the last row and the last column (keeping coordinates `0,…,n-1`). -/
noncomputable def principalDrop (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  A.submatrix Fin.castSucc Fin.castSucc

/-- A principal submatrix of a Hermitian matrix is Hermitian. -/
lemma principalDrop_isHermitian {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hA : A.IsHermitian) : (principalDrop A).IsHermitian :=
  hA.submatrix Fin.castSucc

/-- **Courant–Fischer keystone (Mathlib gap).** The descending k-th eigenvalue of
a Hermitian matrix is the max over all `(k+1)`-dimensional subspaces of the
minimum Rayleigh quotient on that subspace (equivalently the min over
codimension-`k` subspaces of the maximum). This variational characterisation is
the single missing ingredient; once available the interlacing proof below is
immediate from subspace inclusion.

Stated here only as a documented placeholder; the precise inner-product-space
formulation (over `Submodule ℂ (EuclideanSpace ℂ (Fin N))` with the Rayleigh
quotient) is the object that must be built or ported. -/
theorem courant_fischer_placeholder : True := trivial

/-- **Cauchy interlacing theorem** (one deleted index, descending convention):
for the principal submatrix `principalDrop A` of a Hermitian `A` on `Fin (n+1)`,
each eigenvalue `μ i` of the submatrix is sandwiched as `λ (i+1) ≤ μ i ≤ λ i`. -/
theorem cauchy_interlacing {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hA : A.IsHermitian) (i : Fin n) :
    sortedEigs hA i.succ ≤ sortedEigs (principalDrop_isHermitian hA) i ∧
      sortedEigs (principalDrop_isHermitian hA) i ≤ sortedEigs hA i.castSucc := by
  sorry

end CauchyInterlacing
