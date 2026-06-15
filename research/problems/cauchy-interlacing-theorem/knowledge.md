# Knowledge Base: cauchy-interlacing-theorem

Insights accumulated during research on this problem.

---

## Problem Understanding

Cauchy interlacing: if `B` is the principal `(n-1)×(n-1)` submatrix of a Hermitian
`A ∈ ℂ^{n×n}` (delete one matching row/column), the sorted eigenvalues interlace:
`λ_k ≤ μ_k ≤ λ_{k+1}` (ascending convention). The proof of record is the
Courant–Fischer min-max variational characterisation restricted to the
codimension-one coordinate subspace.

---

## Insights

### Session 2026-06-15 (s01, FRESH → ORIENT)

- **Mathlib API correction (vs. older notes).** Mathlib now ships
  `Matrix.IsHermitian.eigenvalues₀ : Fin (Fintype.card n) → ℝ`, the eigenvalues
  in **descending** order, with `Matrix.IsHermitian.eigenvalues₀_antitone`. This
  is the sorted enumeration earlier sessions thought was absent. It makes a clean
  statement of "the k-th eigenvalue" possible — the plain
  `Matrix.IsHermitian.eigenvalues : n → ℝ` is reindexed by the matrix index type
  and is **not** sorted, so it cannot express interlacing directly.
- **Statement of record written** using `eigenvalues₀`. With the descending
  convention the theorem reads `λ i ≥ μ i ≥ λ (i+1)` for `i : Fin n` (the
  ascending textbook convention flips the inequalities under `i ↦ n - i`).
- **Reusable helper `sortedEigs`**: composes `eigenvalues₀` with the canonical
  `Fin N ≃ Fin (Fintype.card (Fin N))` so eigenvalues are indexed naturally by
  `Fin N`; `sortedEigs_antitone` carries the descending order across.
- **Principal submatrix** modelled as `A.submatrix Fin.castSucc Fin.castSucc`
  (delete the last index); Hermitian-ness is inherited via
  `Matrix.IsHermitian.submatrix`.

---

## Dead Ends

(none yet)

---

## Mathlib Gap (keystone)

The single missing ingredient is the **Courant–Fischer max–min characterisation**
of the descending k-th eigenvalue:

  `λ_k = max_{dim S = k+1} min_{0 ≠ x ∈ S} ⟨x, A x⟩ / ⟨x, x⟩`
       `= min_{dim S = n-k} max_{0 ≠ x ∈ S} ⟨x, A x⟩ / ⟨x, x⟩`.

Mathlib has only the **extreme cases** (top/bottom eigenvalue as a Rayleigh
quotient sup/inf via the inner-product Rayleigh API). The general k-th min-max is
absent. Estimated effort: a self-contained min-max over
`Submodule ℂ (EuclideanSpace ℂ (Fin N))` with the Rayleigh quotient — a few
hundred lines, the natural next build target (or a Mathlib contribution).

Once the min-max lemma exists, interlacing is a short subspace-inclusion argument:
the `(k+1)`-dimensional test subspaces available to `B` are exactly those
contained in the codimension-one coordinate subspace `span{e₀,…,e_{n-1}}`, a
subset of those available to `A`. The inclusion sandwiches `μ_k` between `λ_k`
(more subspaces can only raise the max) and `λ_{k+1}` (the deleted dimension
contributes at most one to the min-max index).

---

## Next Steps

1. State the Courant–Fischer min-max lemma precisely over
   `Submodule ℂ (EuclideanSpace ℂ (Fin N))` using the existing Rayleigh API; prove
   the two extreme cases (`k = 0` top, `k = N-1` bottom) directly from Mathlib.
2. Build the general k-th min-max (induction / orthogonal-complement dimension
   counting). This is the keystone; consider an Aristotle submission once the
   backend is reachable (currently 404).
3. Discharge `cauchy_interlacing` from the min-max lemma via the subspace
   inclusion `span{e₀,…,e_{n-1}}`.
4. Build & register only after `lake`/Docker capacity is free (this session both
   Aristotle (404) and Docker (saturated at 3 containers) were unavailable, so the
   skeleton is build-pending and deliberately unregistered).
