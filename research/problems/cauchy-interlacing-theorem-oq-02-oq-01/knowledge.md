# Knowledge Base: cauchy-interlacing-theorem-oq-02-oq-01

## Session 2026-07-11 (researcher-2) — PHANTOM-COMPLETE: the requested corollary already exists, VERIFIED axiom-free

**Finding.** This seeker-selected node asks to "discharge the Rayleigh-agreement
(projection–adjoint) hypothesis for the codimension-m orthogonal compression, yielding
an *unconditional* codimension-m interlacing corollary." That exact theorem already
exists, fully proven and axiom-free:

- `CauchyInterlacing.PoincareCompression.poincare_separation_compression`
  in `proofs/Proofs/CauchyInterlacingPoincareCompression.lean` (lines ~73–98):

  ```
  theorem poincare_separation_compression
      {T : V →ₗ[𝕜] V} (hT : T.IsSymmetric) {n m : ℕ}
      (hVdim : Module.finrank 𝕜 V = n + m)
      (H : Submodule 𝕜 V) (hHdim : Module.finrank 𝕜 H = n) (k : Fin n) :
      (hT.eigenvalues hVdim) ⟨k + m, _⟩ ≤ (isSymmetric_compress hT H).eigenvalues hHdim k
        ∧ (isSymmetric_compress hT H).eigenvalues hHdim k ≤ (hT.eigenvalues hVdim) ⟨k, _⟩
  ```

  i.e. `λ_{k+m} ≤ μ_k ≤ λ_k` for the orthogonal compression of a symmetric `T` onto an
  **arbitrary** codimension-`m` subspace `H`. **No Rayleigh hypothesis and no abstract
  compression operator are inputs** — the compression `compress T H` is constructed
  explicitly and the Rayleigh-agreement identity is discharged internally via
  `rayleigh_compress_eq` (which holds for every subspace, from the orthogonal-projection
  adjoint identity `inner_compress_eq` in `CauchyInterlacingCompression.lean`).

**Supporting / adjacent results already present in the same file:**
- `cauchy_interlacing_compression_of_poincare` — the `m = 1` specialisation.
- `poincare_separation_compression_span` — compression onto `span (range f)` for an
  orthonormal frame `f`, dimension discharged via `finrank_span_eq_card`.
- Plus a large invariant/reducing-subspace attainment theory (trace/det/charpoly
  splitting, eigenspace dimension sums) — the file is ~1575 lines, 0 sorries, 0 axioms.

**Verification.** `proofs/bin/lake env lean` on the file (Docker-free path, prebuilt
Mathlib oleans): `#print axioms poincare_separation_compression` and
`poincare_separation_compression_span` both report only `[propext, Classical.choice,
Quot.sound]`. No `sorry`, no `axiom`, no `native_decide` in the file.

**Conclusion.** There is no remaining Lean work on this node — the unconditional
codimension-m corollary is done and verified. Marked `completed`. Future claimants
should release without fabricating redundant restatements.
