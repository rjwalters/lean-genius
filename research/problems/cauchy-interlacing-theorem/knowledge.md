# Knowledge Base: cauchy-interlacing-theorem

Insights accumulated during research on this problem.

---

## Problem Understanding

- One-step interlacing: deleting row/col `i` from Hermitian `A` gives `B` whose
  sorted spectrum interlaces `A`'s: `λ_k ≤ μ_k ≤ λ_{k+1}`. Codim-1 case only;
  delete-`m` version is a stretch goal.
- The math is classical (Courant–Fischer + dimension count); the entire
  difficulty is missing Mathlib scaffolding, not depth.

---

## Insights

- **Keystone gap**: Mathlib has only EXTREME-eigenvalue Rayleigh
  (`iSup`/`iInf` in `Analysis.InnerProductSpace.Rayleigh`), NOT a k-th
  Courant–Fischer min-max. Building the k-th min-max lemma is the bulk of the
  work and is independently reusable (Weyl, Lidskii).
- **~~Sorting gap~~ RETRACTED (iter 3, verified vs Mathlib master)**: Mathlib
  DOES ship sorted eigenvalues. Matrix-native:
  `Matrix.IsHermitian.eigenvalues₀ : Fin (Fintype.card n) → ℝ` is sorted
  DESCENDING with `eigenvalues₀_antitone` (`Mathlib.LinearAlgebra.Matrix.Spectrum`).
  (`.eigenvalues` reuses index type `n` and is unsorted — that is what the stale
  note conflated.) Operator-level twin:
  `LinearMap.IsSymmetric.eigenvalues : Fin n → ℝ` antitone, with
  `hasEigenvalue_eigenvalues`, `eigenvectorBasis`. So state interlacing directly
  over `eigenvalues₀`; no abstract-monotone-tuple workaround, no sorting
  obligation. The keystone min-max gap above is REAL and still stands.
- **Verified extreme Rayleigh signatures (iter 3)**:
  `LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional` /
  `_iInf_of_finiteDimensional` — `⨆`/`⨅` of `⟪Tx,x⟫/‖x‖²` over `{x≠0}` IS the
  top/bottom eigenvalue. Bridging extremum→`eigenvalues₀ 0/last` is a small
  lemma. (Spot-checked against master via GitHub docs/source — `.lake` is still
  an ELOOP symlink and the build image carries only oleans, so no local grep;
  re-confirm against pin v4.26.0 at build time.)
- **Free wins available now**: the two EXTREME cases (k=0 lower `λ₀≤μ₀`,
  k=n-2 upper `μ_{n-2}≤λ_{n-1}`) follow from the existing extreme-eigenvalue
  Rayleigh API by domain-restriction to the hyperplane `H_i = {x : x i = 0}`,
  WITHOUT the general min-max lemma. Best first PR / Aristotle target.
- **Dimension-count lemma** (upper bound): a `(k+2)`-dim subspace meets the
  codim-1 hyperplane `H_i` in `≥ k+1` dims — Mathlib
  `Submodule.finrank_sup_add_finrank_inf_eq` + `finrank H_i = n-1`.

Full decomposition + DRAFT (unverified) Lean statement:
`approaches/orient-min-max-scaffolding.md`.

---

## Sessions

### 2026-06-15 (iter 3, researcher-11) — API spot-check / ORIENT

**Mode**: REVISIT (depth-first on owned MODERATE-tier problem). **Outcome**: progress (orientation corrected, no Lean shipped — both backends down).

- Backends: Aristotle `prove` → 404; Docker pool saturated (3 `lean-build` on 7.65 GiB VM). Build-free session.
- `.lake` is a self-referential (ELOOP) symlink and the `lean4-arm64:v4.26.0` image ships only oleans (no Mathlib source) → spot-checked the API against **Mathlib master via GitHub docs/source** instead.
- **Retracted** the iter-2 "no sorted eigenvalues" gap: `Matrix.IsHermitian.eigenvalues₀` (antitone) and `LinearMap.IsSymmetric.eigenvalues` (antitone) both exist. Re-pinned the statement to the matrix-native `eigenvalues₀` (memo §5-revised).
- Pinned exact extreme-Rayleigh signatures (memo §4-verified) and the minimal residual-lemma list for the extreme-case PR.
- Confirmed the **keystone gap stands**: no k-th Courant–Fischer min-max in Mathlib.
- Brought the previously-untracked `src/data/research/problems/cauchy-interlacing-theorem.json` under version control (was not on origin/main); corrected an inaccurate `builtItems` entry that claimed a non-existent `CauchyInterlacing.lean`.

**Next**: formalize the two extreme cases over `eigenvalues₀` when a backend returns; then build the k-th min-max keystone.

---

## Dead Ends

[Approaches known not to work will be documented here]
