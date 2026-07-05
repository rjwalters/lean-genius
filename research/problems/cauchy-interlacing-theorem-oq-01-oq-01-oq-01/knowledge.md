# Knowledge Base: cauchy-interlacing-theorem-oq-01-oq-01-oq-01

Candidate goal (Seeker-generated): *"Assemble the matrix-level eigenvalue
corollary for Cauchy interlacing: principal submatrix eigenvalues interlace A's."*

---

## Problem Understanding

The parent chain builds Cauchy interlacing from the Courant–Fischer keystone up
to concrete matrices. The candidate asks for the final corollary: for a
Hermitian matrix `A`, the eigenvalues of a principal submatrix interlace those
of `A`, `λ_{k+1} ≤ μ_k ≤ λ_k`.

---

## Insights

### FINDING (2026-07-04, Session 2): the candidate is ALREADY COMPLETE.

The requested corollary already exists in the tracked codebase, sorry-free and
axiom-free, in two forms. The candidate reproduces an open question that a prior
session already answered.

**Literal matrix statement, codimension one (the exact ask):**
`proofs/Proofs/CauchyInterlacingOQ01OQ01OQ02.lean` —
`eigenvalues₀_principalSubmatrix_interlacing` (line 273):

```
hA.eigenvalues₀ (k+1) ≤ (hA.submatrix j.succAbove).eigenvalues₀ k
                       ≤ hA.eigenvalues₀ k
```

for a Hermitian `(n+1)×(n+1)` matrix `A`, deleted index `j : Fin (n+1)`,
principal submatrix `A.submatrix j.succAbove j.succAbove`, and every `k : Fin n`
(read through the `Fin (n+1) ≃ Fin card` / `Fin n ≃ Fin card` index casts). Its
docstring quotes the parent's open question verbatim and states "This file
answers it."

**Literal matrix statement, arbitrary codimension (Poincaré separation):**
`proofs/Proofs/CauchyInterlacingOQ01OQ01OQ01OQ03.lean` —
`eigenvalues₀_principalSubmatrix_poincare` (line 324): for injective
`ι : Fin n → Fin (n+m)`,
`A.eigenvalues₀ ⟨k+m⟩ ≤ (A.submatrix ι ι).eigenvalues₀ k ≤ A.eigenvalues₀ ⟨k⟩`.
The codim-one file is the special case `m = 1`, `ι = j.succAbove`.

**The bridge that powers both** (the genuine content the candidate names):
- `compress_inner_eq_submatrix` / `compress_inner_eq_principalSubmatrix`: the
  orthogonal compression of `toEuclideanLin A` to the coordinate subspace
  `H = span {e_{ι i}}`, read on the natural basis, is exactly `A.submatrix ι ι`.
- `coordEquiv : EuclideanSpace 𝕜 (Fin n) ≃ₗᵢ H`, `e_i ↦ e_{ι i}`, the coordinate
  isometry, and `compress_intertwine`: under `coordEquiv` the compression *is*
  the submatrix operator, so pushing the submatrix's spectral eigenbasis through
  `coordEquiv` yields an eigenbasis of the compression with the *same* antitone
  eigenvalues (no eigenvalue-uniqueness lemma needed).
- `interlacing_poincare_of_intertwine` / `interlacing_of_intertwine` feed this
  into the abstract `poincare_separation` / `cauchy_interlacing`.
- `eigenvalues_finrank_congr` bridges the `finrank_euclideanSpace_fin` indexing
  used in the operator statements to `Matrix.IsHermitian.eigenvalues₀`.

Over any `RCLike` field `𝕜` (so both `ℝ` and `ℂ`). Absent from Mathlib.

### Whole-chain status
`grep`-verified 0 real `sorry` / 0 `axiom` across the dependency chain:
Keystone, Assembly, Compression, Poincare, PoincareSubmatrix,
PoincareCompression, OQ01OQ01, OQ01OQ01OQ01, OQ01OQ01OQ01OQ01,
OQ01OQ01OQ01OQ03, OQ01OQ01OQ02. (The `sorry=1` that a naive grep reports for
Keystone/Assembly/Compression/Poincare is the token "0-sorry" inside their
docstrings, not a real hole.)

---

## The one genuine remaining gap (build-dependent — currently blocked)

None of the CauchyInterlacing files are registered in `proofs/Proofs.lean`
(`grep -c CauchyInterlacing proofs/Proofs.lean` → 0). Each carries the header
"Research file — intentionally NOT registered in `Proofs.lean`." Consequences:

- The results are never machine-checked in CI, only asserted.
- There is no dedicated gallery entry for the matrix corollary; the dir
  `cauchy-interlacing-theorem-oq-01-oq-01-oq-01/` holds the *parent* entry
  ("Sorted Eigenvalues Are Determined by Any Orthonormal Eigenbasis").

So the mathematics is complete; the outstanding work is **integration**:
register the leaf files (at minimum `CauchyInterlacingOQ01OQ01OQ02` and
`CauchyInterlacingOQ01OQ01OQ01OQ03` with their transitive deps) in
`Proofs.lean`, build via `./proofs/scripts/docker-build.sh`, and add a gallery
`meta.json` for the matrix corollary. This is build-dependent and cannot be
done under the current Docker/containerd blackout (blob I/O error) — it is the
concrete next action once the build toolchain recovers.

---

## Dead Ends / Do-Not-Repeat

- Do NOT re-prove the matrix corollary — it exists twice (codim-1 and
  arbitrary-codim), sorry-free. Any new attempt is duplicated work.

---

## Suggested follow-up (not injected into the pool)

- **Fan–Pall converse (inverse problem):** every real sequence `μ` interlacing
  `λ` (`λ_{k+1} ≤ μ_k ≤ λ_k`) is realised as the spectrum of *some* principal
  submatrix / codim-one compression of a Hermitian `A` with spectrum `λ`. This
  is a genuinely distinct, deeper result (sharpness of interlacing), not a
  cosmetic variant. Left as a note rather than a pool candidate to avoid
  bloating the already dense cauchy-interlacing sub-tree.
