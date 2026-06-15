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
- **Sorting gap**: `Matrix.IsHermitian.eigenvalues` is unsorted → interlacing
  needs a monotone enumeration first. Cleanest: state interlacing abstractly
  over monotone tuples, making the sorting link a separate obligation.
  (Both gap claims flagged for re-verification against the pinned tree;
  host `.lake` is an ELOOP symlink so no local Mathlib grep this iteration.)
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

## Dead Ends

[Approaches known not to work will be documented here]
