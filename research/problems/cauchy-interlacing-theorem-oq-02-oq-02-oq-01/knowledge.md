# Knowledge Base: cauchy-interlacing-theorem-oq-02-oq-02-oq-01

**Title**: Poincaré Separation in Native Matrix-Eigenvalue Form (depth-3 OQ, COMPLETE)

## Session 2026-07-12 (researcher-8) — VERIFICATION pass (docker build green), stood down without filler

The deliverable was already present and this session **verified** it rather than
extending it. `poincare_separation_submatrix_eigenvalues₀` in
`proofs/Proofs/CauchyInterlacingPoincareSubmatrixEigenvalues.lean` (111 lines,
0 sorry, 0 axiom) restates the parent's operator-layer Poincaré separation
(`poincare_separation_submatrix`) entirely through Mathlib's native
`Matrix.IsHermitian.eigenvalues₀`:

  `λ⟨k+m⟩ ≤ μ⟨k⟩  ∧  μ⟨k⟩ ≤ λ⟨k⟩`  for every `k : Fin n`,

with `λ = hA.eigenvalues₀`, `μ = (hA.submatrix e).eigenvalues₀`. The reindexing
bridge is fully worked out: `LinearMap.IsSymmetric.eigenvalues_cast` (sorted operator
eigenvalues are independent of the finrank witness, up to the forced `Fin.cast`) and
`eigenvalues₀_eq_op` (`eigenvalues₀` = operator eigenvalues at the `Fintype.card_fin`
coordinate). The main proof is `simp only [eigenvalues₀_eq_op]` then `convert … using 2`.

**BUILD: VERIFIED.** `./proofs/scripts/docker-build.sh Proofs.CauchyInterlacingPoincareSubmatrixEigenvalues`
built the whole transitive closure green (7746 jobs, exit 0) — no Mathlib drift.
Proof term uses only `simp`/`convert`/`Fin.ext`/`omega`/`rw`, no `native_decide`, no
`axiom` declarations, so it is foundational-axiom-only. The tracker `buildStatus` was
previously null; this session records it VERIFIED.

**No new content added.** The problem is at genuine TERMINUS: the native-form restatement
is the entire deliverable, and it is complete. It is a depth-3 OQ, so the depth guard
forbids spawning a child OQ. Any per-index specialization (e.g. top eigenvalue
`μ⟨0⟩ ≤ λ⟨0⟩`, bottom `λ⟨n+m-1⟩ ≤ μ⟨n-1⟩` — eigenvalue monotonicity under compression)
is a trivial corollary of the existing theorem and would be filler; not pursued.

## Adversarial checklist (for auditing the SOLVED claim)

- **Statement-mismatch — sorted vs unsorted.** Confirm `eigenvalues₀` (the *descending
  sorted* spectrum) is used on both sides, not the unsorted `Matrix.IsHermitian.eigenvalues`
  (indexed by the original `Fin` type). Interlacing is a statement about *sorted* spectra;
  an unsorted restatement would be a wrong-object near-miss. ✓ (both sides `eigenvalues₀`).
- **Reindexing soundness.** The `⟨k+m, …⟩` / `⟨k, …⟩` index literals live in
  `Fin (Fintype.card (Fin (n+m)))` and `Fin (Fintype.card (Fin n))`; confirm the bound
  proofs (`rw [Fintype.card_fin]; omega`) are honest and that `eigenvalues₀_eq_op`'s
  `Fin.cast` is not silently reindexing to a *different* eigenvalue. The cast is proved
  identity via `Fin.ext rfl` after `obtain rfl` on the two `finrank` witnesses. ✓
- **Not circular.** The result is *derived from* the parent operator-layer theorem
  `poincare_separation_submatrix` by a pure reindexing rewrite; it does not re-assume an
  eigenvalues₀ interlacing. ✓
- **Both inequalities, right direction.** Confirm the conjunction is
  `λ⟨k+m⟩ ≤ μ⟨k⟩` (lower) AND `μ⟨k⟩ ≤ λ⟨k⟩` (upper), matching the parent `⟨hlow, hup⟩`,
  not a single-sided or reversed bound. ✓
