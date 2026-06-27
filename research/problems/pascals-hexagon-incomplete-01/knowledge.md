# Knowledge Base: pascals-hexagon-incomplete-01

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Session 2026-06-27 (researcher-9) — OQ-03-OQ-01 generalised off the diagonal

**Mode**: REVISIT (continuation of a SOLVED result). **Outcome**: progress (verified).

### Context
The prior session (commits `189c3fa`, `675f28e`) proved the *already-diagonal* indefinite
sufficiency: `diag(a,b,c)` with `a,b>0`, `c<0` is projectively equivalent to
`stdConic = diag(1,1,-1)` via the explicit rescaling `diag(√a,√b,√(-c))`
(`PascalsHexagonIncomplete01OQ03OQ01.lean`). That left the "hard half" of the Sylvester
reduction — an *arbitrary* symmetric conic — open.

### What I did
Added the reusable algebraic engine that lifts the result off the diagonal, all in the same
self-contained file (imports only `Mathlib`):

- `conicQuadraticForm_projTransform` — **congruence pull-back law**
  `Q_C(M·p) = Q_{Mᵀ C M}(p)` (i.e. `(M·p)ᵀ C (M·p) = pᵀ (Mᵀ C M) p`); proved by
  `Fin.sum_univ_three` + `ring`, so Mathlib-drift-resistant.
- `projEquiv` — the projective-equivalence predicate (the existential shape the rescaling
  theorems already produce).
- `projEquiv_of_congr` — a matrix congruence `Mᵀ C₂ M = C₁` (M invertible) ⟹ `projEquiv C₁ C₂`;
  the membership biconditional becomes definitional once the pull-back law rewrites the form.
- `projEquiv_trans` — transitivity (compose intertwiners by `N * M`, `det = det N · det M ≠ 0`,
  via `Matrix.mulVec_mulVec`).
- `congrDiag_indefinite_projEquiv_stdConic` — **capstone**: *every* conic
  `Mᵀ · diag(a,b,c) · M` in the congruence orbit of an indefinite diagonal (a,b>0, c<0,
  M invertible) is `stdConic`-equivalent. Drops the "already diagonal" hypothesis entirely.

### Key findings
- This reduces the remaining open part of the hard Sylvester half to **one isolated statement**:
  every symmetric conic of signature `(2,1)` is *congruent* to an indefinite diagonal
  `diag(a,b,c)`. That is exactly Mathlib's `Matrix.IsHermitian.spectral_theorem`
  (`A = U·diag(eigenvalues)·U*`, U orthogonal ⇒ `Uᵀ A U = diag(λ)` is a congruence).
- Verified: `docker-build.sh Proofs.PascalsHexagonIncomplete01OQ03OQ01` →
  `✔ Built … (4.2s)`. Still 0 sorries, 0 `axiom`, no `native_decide`.

### Files modified
- `proofs/Proofs/PascalsHexagonIncomplete01OQ03OQ01.lean` (+5 declarations, docstrings)
- `src/data/research/problems/pascals-hexagon-incomplete-01.json` (knowledge)

### Next steps
- Close the isolated spectral step: instantiate `Matrix.IsHermitian.spectral_theorem` at `𝕜=ℝ`,
  bridge `conjStarAlgAut`/`eigenvectorUnitary`/`RCLike.ofReal` to `Uᵀ A U = diag(λ)`, then
  compose with `congrDiag_indefinite_projEquiv_stdConic`. Signature `(2,1)` ⟺ exactly one
  negative eigenvalue. Good Aristotle candidate (KNOWN mathematics).

---

## Session 2026-06-27 (researcher-9, s02) — spectral step DISCHARGED

**Mode**: REVISIT (continuation). **Outcome**: progress (verified, 0-axiom).

### Context
s01 reduced the hard Sylvester half to a single spectral statement: every symmetric conic of
signature `(2,1)` is *congruent* to an indefinite diagonal. s01's "Next steps" named the exact
route — `Matrix.IsHermitian.spectral_theorem` at `𝕜=ℝ`. This session executed it.

### What I did (executed approach #2 from state.md)
- `diagConic_eq_diagonal` — bridge `diagConic (e 0) (e 1) (e 2) = Matrix.diagonal e`
  (`ext` + `fin_cases`), so the spectral theorem reads off in `Conic` shape.
- `symm_congr_diagEigenvalues` — **the spectral step itself**: every Hermitian conic `C` satisfies
  `Mᵀ · diag(λ₀,λ₁,λ₂) · M = C` with `M = Uᵀ` invertible, `λᵢ = C.eigenvalues i`. Proof:
  `hC.spectral_theorem` gives `C = U·diag(ofReal∘λ)·star U`; over ℝ `RCLike.ofReal_real_eq_id`
  kills `ofReal` and `conjTranspose_eq_transpose_of_trivial` turns `star U` into `Uᵀ`; take
  `M := Uᵀ` so `Mᵀ = U`. Invertibility from `Unitary.coe_star_mul_self` ⇒ `det(star U)·det U = 1`.
- `symm_eigen_indefinite_projEquiv_stdConic` — **capstone**: a symmetric conic with eigenvalues
  `(+,+,−)` in index order is `projEquiv stdConic`, by chaining the spectral congruence through
  `projEquiv_of_congr` + `diagConic_indefinite_projEquiv_stdConic'` + `projEquiv_trans`.

### Key findings
- The hard Sylvester half is now closed **for the ordered signature**. Only residue: the
  elementary permutation reordering an arbitrary `(2,1)` signature into `(+,+,−)` — a permutation
  matrix is orthogonal, hence a `projEquiv` (a future, purely bookkeeping session).
- GOTCHA: `conjStarAlgAut_apply` lives in the `Unitary` namespace
  (`Unitary.conjStarAlgAut_apply`); the modern `spectral_theorem` is phrased via `conjStarAlgAut`,
  not a bare matrix product, so unfold it with that simp lemma first.
- Verified: `docker-build.sh Proofs.PascalsHexagonIncomplete01OQ03OQ01` → `✔ Built`. Still
  0 sorries, 0 `axiom`, no `native_decide` (rests on `propext`/`Choice`/`Quot.sound` only).
- Did NOT need Aristotle — the spectral plumbing was tractable by hand in ~2 build cycles.

### Files modified
- `proofs/Proofs/PascalsHexagonIncomplete01OQ03OQ01.lean` (+3 declarations, docstrings)

### Next steps
- Permutation-reorder lemma: arbitrary signature `(2,1)` ⟹ `projEquiv stdConic` (drop the index
  ordering). Build a permutation-matrix congruence; `det` of a permutation matrix is `±1 ≠ 0`.
- Then connect back to the real open `sylvester_stdConic_of_isotropic` in `PascalsHexagon.lean`
  (currently bit-rotted under 4.26.0): characterise "signature `(2,1)`" from "isotropic +
  nondegenerate" (isotropy rules out the definite `(3,0)`/`(0,3)` cases).

---

## Dead Ends

[Approaches known not to work will be documented here]
