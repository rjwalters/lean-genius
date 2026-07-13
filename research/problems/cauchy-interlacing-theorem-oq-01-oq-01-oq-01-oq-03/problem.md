# Problem: Poincaré Separation — Eigenvalue Bounds for m×m Principal Submatrices

**Slug**: cauchy-interlacing-theorem-oq-01-oq-01-oq-01-oq-03
**Created**: 2026-06-30
**Status**: Active
**Source**: gallery-gap (open-question child of `cauchy-interlacing-theorem-oq-01-oq-01-oq-01`)

## Problem Statement

### Formal Statement

Let `A : Matrix (Fin n) (Fin n) 𝕜` be Hermitian (`hA : A.IsHermitian`) over an `RCLike`
field `𝕜` (so `ℝ` or `ℂ`), with sorted eigenvalues `hA.eigenvalues₀ : Fin n → ℝ`
(the concrete Mathlib tuple from `Mathlib.Analysis.Matrix.Spectrum`, antitone by
`Matrix.IsHermitian.eigenvalues₀_antitone`). Fix an index set `I ⊆ Fin n` of size `m`,
realized as an injection `g : Fin m ↪ Fin n` (or `g : Fin m → Fin n` injective), and form
the `m × m` principal submatrix

```
A^{(I)} := A.submatrix g g          -- (A.submatrix g g) i j = A (g i) (g j)
```

which is again Hermitian (`(hA.submatrix g).?` — Hermitianness of a principal submatrix is
immediate: `(A.submatrix g g)ᴴ = Aᴴ.submatrix g g = A.submatrix g g`). Write
`μ := (submatrix_isHermitian).eigenvalues₀ : Fin m → ℝ` for its sorted eigenvalue tuple.

**Poincaré separation theorem.** For every `k` with `1 ≤ k ≤ m` (0-indexed: `k : Fin m`),

```
λ_k(A)  ≤  λ_k(A^{(I)})  ≤  λ_{k + (n − m)}(A).
```

Because Mathlib's `eigenvalues₀` are sorted in **decreasing** (antitone) order, the same
statement in Mathlib's convention becomes the "opposite ordering" form flagged in the parent's
open question:

```
λ_{k + (n − m)}(A)  ≤  λ_k(A^{(I)})  ≤  λ_k(A)      -- antitone/decreasing indexing
```

i.e. with `hA.eigenvalues₀` and `μ` both decreasing, `k : Fin m`, and the shift
`k ↦ ⟨k + (n − m), _⟩ : Fin n` on the lower bound. The parent single-deletion result is the
special case `m = n − 1`, which reads `λ_{k+1}(A) ≤ λ_k(A^{(j)}) ≤ λ_k(A)`.

**Lean theorem shape (decreasing convention):**

```lean
theorem poincare_separation
    {n m : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian)
    (g : Fin m → Fin n) (hg : Function.Injective g)
    (hAI : (A.submatrix g g).IsHermitian)      -- from hA and injectivity
    (k : Fin m) (hkn : (k : ℕ) + (n - m) < n) :
    hA.eigenvalues₀ ⟨(k : ℕ) + (n - m), hkn⟩
      ≤ hAI.eigenvalues₀ k
    ∧ hAI.eigenvalues₀ k
      ≤ hA.eigenvalues₀ ⟨(k : ℕ), by omega⟩ := by
  sorry
```

**Compression viewpoint.** Let `P_I : EuclideanSpace 𝕜 (Fin n) → EuclideanSpace 𝕜 (Fin n)` be
the orthogonal projection onto `span 𝕜 {e_i : i ∈ I}` (the coordinate subspace `ℝ^I`, an
`m`-dimensional coordinate subspace). Then `A^{(I)}` is the **compression** `P_I A P_I`
restricted to that subspace: identifying the coordinate subspace `span {e_{g i}}` with
`EuclideanSpace 𝕜 (Fin m)` via the isometry sending `e_{g i} ↦ e_i`, the operator
`toEuclideanLin (A.submatrix g g)` is unitarily conjugate to `P_I ∘ toEuclideanLin A ∘ P_I`
on that subspace. This is exactly the sesquilinear-form identification the parent chain proves:
the entry `#27917` (`cauchy-interlacing-theorem-oq-01-oq-01`) supplies
`compress_inner_eq_principalSubmatrix`, and this entry's parent
(`cauchy-interlacing-theorem-oq-01-oq-01-oq-01`) supplies `eigenvalues_eq_of_eigenbasis` /
the unitary-conjugation invariance that lets one read the compressed operator's sorted spectrum
off as `A^{(I)}`'s.

### Plain Language

Take a Hermitian matrix `A` and throw away all but `m` chosen rows and the matching `m`
columns, keeping an `m × m` diagonal block `A^{(I)}`. The eigenvalues of that block cannot
stray arbitrarily from those of `A`: sorted the same way, each eigenvalue of the block is
squeezed between the corresponding eigenvalue of `A` and the one shifted by `n − m` positions.
The classic **Cauchy interlacing** theorem is the case where you delete a single row/column
(`m = n − 1`); the eigenvalues of the `(n−1)×(n−1)` block then strictly interlace those of `A`.
Poincaré separation is the general statement, obtained either by **iterating** single-row
deletion `n − m` times, or **in one shot** via the min–max (Courant–Fischer) description of
eigenvalues restricted to test subspaces that live inside the coordinate subspace `ℝ^I`.

### Why This Matters

- **General form of interlacing.** Cauchy interlacing (`m = n − 1`) is the workhorse special
  case; Poincaré separation is the full statement for any principal submatrix. Having it makes
  the whole gallery Cauchy-interlacing chain "complete at the top."
- **Reusable spectral infrastructure.** The compression / restriction-to-a-coordinate-subspace
  identification, and the sorted-eigenvalue-is-a-unitary-invariant lemma proved by the parent,
  are exactly the tools needed for a family of monotonicity results.
- **Foundation for majorization and min–max.** Poincaré separation is the standard route into
  the **Schur–Horn** theorem (diagonal entries are majorized by eigenvalues), **Weyl's
  inequalities** for eigenvalues of sums, and numerical eigenvalue bounds (deflation, Rayleigh–
  Ritz, Sturm sequences). None of these are in Mathlib yet; this is a natural first brick.

### Known Results

- **Parent bridge lemma (verified, this gallery).**
  `CauchyInterlacingOQ01OQ01OQ01.eigenvalues_eq_of_eigenbasis`: for a self-adjoint
  `T : E →ₗ[𝕜] E` with `hT : T.IsSymmetric`, any orthonormal eigenbasis `(b, f)` with
  `T (b i) = (f i : 𝕜) • b i` and `f` antitone satisfies `hT.eigenvalues hn = f`. Corollary:
  the sorted spectrum is invariant under linear isometry equivalence (unitary conjugation).
- **Compression identity (verified, `#27917`).** `compress_inner_eq_principalSubmatrix`:
  the sesquilinear form of the compressed operator on the coordinate subspace equals that of
  `toEuclideanLin (A.submatrix …)`.
- **Courant–Fischer min–max (classical, NOT yet in Mathlib for the k-th eigenvalue).**
  `λ_k(A) = min_{dim V = k} max_{0 ≠ x ∈ V} ⟨Ax, x⟩ / ⟨x, x⟩` (increasing convention). Mathlib
  currently has only the **extremal** Rayleigh cases (largest/smallest eigenvalue), not the
  general k-dimensional subspace min–max. See "Suggested Approach" for exactly what is missing.
- **Coordinate-subspace restriction.** Restricting the Rayleigh quotient of `A` to test vectors
  supported on `I` yields the Rayleigh quotient of `A^{(I)}`; combined with min–max this gives
  the two-sided bound directly.

### Suggested Approach

Two routes; the iterated-parent route is the tractable one given current Mathlib.

**(a) Iterated single-deletion (recommended).**
Assemble the parent's single-deletion principal-submatrix interlacing
`λ_{k+1}(A) ≤ λ_k(A^{(j)}) ≤ λ_k(A)` (the parent's second open question — building the explicit
coordinate-hyperplane isometry and feeding `compress_inner_eq_principalSubmatrix` into the
conjugation corollary), then induct on `n − m`: delete indices in `Fin n \ I` one at a time,
each step applying single-deletion and composing the index shifts (`k+1` accumulates to
`k + (n − m)`). Pros: reuses the parent lemma directly; each step is a known result. Cons:
requires (i) finishing the parent's own single-deletion assembly first, and (ii) careful
bookkeeping of the `Fin`-index arithmetic across `n − m` deletions and of Hermitianness of each
intermediate submatrix. This is the lower-risk path because it does not need any new min–max
machinery.

**(b) Direct Courant–Fischer min–max.**
Prove the general k-th-eigenvalue min–max characterization first, then restrict the test
subspaces to lie inside the `m`-dimensional coordinate subspace `ℝ^I`: the upper bound
`λ_k(A^{(I)}) ≤ λ_k(A)` uses that `A^{(I)}`'s optimal `k`-dim subspace is a valid (smaller-
ambient) competitor for `A`; the lower bound `λ_{k+(n−m)}(A) ≤ λ_k(A^{(I)})` uses the max–min
form with the codimension bookkeeping. Pros: one shot, no induction, conceptually clean. Cons:
**the general k-dimensional min–max theorem is absent from Mathlib** — only the extremal cases
exist (see verified names below). Building it (a `sInf`/`sSup` over subspaces of a given
`finrank`, plus existence of an optimizer via the spectral theorem) is itself a substantial
lemma. So route (b) is more work unless one first upstreams Courant–Fischer.

**Verified Mathlib names to build on** (spelling + module confirmed):
- `Matrix.IsHermitian` — `Mathlib.LinearAlgebra.Matrix.Hermitian` (`Aᴴ = A`).
- `Matrix.IsHermitian.eigenvalues₀`, `Matrix.IsHermitian.eigenvalues`,
  `Matrix.IsHermitian.eigenvalues₀_antitone`, `Matrix.IsHermitian.eigenvectorBasis`
  — `Mathlib.Analysis.Matrix.Spectrum`.
- `Matrix.toEuclideanLin`, `Matrix.submatrix` — core Mathlib.
- `LinearMap.IsSymmetric.eigenvalues`, `.eigenvalues_antitone`, `.eigenvectorBasis`,
  `.apply_eigenvectorBasis` — `Mathlib.Analysis.InnerProductSpace.Spectrum`.
- `ContinuousLinearMap.rayleighQuotient`,
  `LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional`,
  `LinearMap.IsSymmetric.hasEigenvalue_iInf_of_finiteDimensional`
  — `Mathlib.Analysis.InnerProductSpace.Rayleigh` (extremal Rayleigh only — the largest/smallest
  eigenvalue; **no k-th-eigenvalue min–max**).
- `Submodule.subtype`, `OrthonormalBasis`, linear isometry equivalences `≃ₗᵢ` — for the
  coordinate-subspace restriction / conjugation, exactly as the parent uses them.

**Do NOT cite (searched, not present in Mathlib):** `LinearMap.IsSymmetric.rayleigh`, any
`iSup_rayleigh_eq_iInf…` on `LinearMap.IsSymmetric`, a general Courant–Fischer k-th eigenvalue
min–max theorem, or any `interlac`/`Poincare` eigenvalue lemma. These would be original
contributions.

**Recommendation.** Pursue route (a): it inherits the parent's verified charpoly-based
invariance lemma and only needs the single-deletion assembly (already scoped as the parent's
open question) plus an induction on `n − m`. Route (b) is mathematically cleaner but is gated on
first formalizing Courant–Fischer, which is a larger independent target.

### Classification

```yaml
tier: B
significance: 7
tractability: 5
tags:
  - linear-algebra
  - spectral
  - hermitian
  - eigenvalues
  - cauchy-interlacing
  - spectral-theorem
```

Rationale: significance 7 — Poincaré separation is a named, textbook-standard generalization
underpinning Schur–Horn, Weyl, and numerical spectral bounds, and it completes the gallery's
Cauchy-interlacing chain. Tractability 5 — the iterated route reuses the parent's verified
bridge lemma, but depends on first completing the parent's own single-deletion assembly and on
nontrivial `Fin`-index bookkeeping across `n − m` deletions; the clean min–max route needs a
Courant–Fischer theorem that Mathlib does not yet have.

### Related Gallery Proofs

- **`cauchy-interlacing-theorem-oq-01-oq-01-oq-01`** (direct parent, verified, 0 axioms) —
  proves `eigenvalues_eq_of_eigenbasis`: a self-adjoint operator's sorted eigenvalues are
  determined by any orthonormal eigenbasis, i.e. invariant under unitary conjugation. Its third
  listed open question is exactly this Poincaré-separation generalization.
- **`cauchy-interlacing-theorem-oq-01-oq-01`** (grandparent, `#27917`) — the principal-submatrix
  identification supplying `compress_inner_eq_principalSubmatrix`, the sesquilinear-form bridge
  between the compressed operator and `toEuclideanLin (A.submatrix …)`.
- **`cauchy-interlacing-theorem`** (root) — the single-deletion Cauchy interlacing keystone,
  `λ_{k+1}(A) ≤ λ_k(A^{(j)}) ≤ λ_k(A)`, the `m = n − 1` special case of this problem.
