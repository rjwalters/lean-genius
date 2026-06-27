# Knowledge Base: cayley-hamilton-minpoly-oq-01-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

Parent `cayley-hamilton-minpoly-oq-01` ("Jordan Canonical Form and the Minimal
Polynomial") axiomatizes the full JCF–minpoly product formula

    minpoly K f = ∏_{μ} (X - μ)^{e_μ},   e_μ = maxGenEigenspaceIndex f μ

as the axiom `minpoly_product_formula`, on the stated grounds that Mathlib 4.26.0
lacks the explicit Jordan block matrix decomposition with labeled basis vectors.

Key realization: the **forward divisibility** direction

    minpoly K f  ∣  ∏_{μ eigenvalue} (X - μ)^{e_μ}

does NOT need Jordan block matrices at all. It follows purely from Mathlib's
generalized-eigenspace machinery. Only the reverse divisibility (equivalently the
exactness `maxGenEigenspaceIndex_exact`) needs the largest-Jordan-block witness.

---

## Insights

- `Module.End.iSup_maxGenEigenspace_eq_top` (Axler 8.21) gives, over an
  algebraically closed field in finite dimensions, `⨆ μ, maxGenEigenspace μ = ⊤`.
  This is the entire engine for the forward direction.
- Proof that the product polynomial `p = ∏ (X - μ)^{e_μ}` annihilates `f`:
  show `LinearMap.ker (aeval f p) = ⊤` by checking each maximal generalized
  eigenspace lies in the kernel. On the `ν`-summand, factor `p` (in the
  *commutative* ring `K[X]`) as `q * (X - C ν)^{e_ν}`; then
  `aeval f p = aeval f q * (f - ν•1)^{e_ν}`, and `(f - ν•1)^{e_ν}` already kills
  every vector of `maxGenEigenspace ν` (= `genEigenspace ν (maxGenEigenspaceIndex ν)`
  = `ker ((f - ν•1)^{e_ν})`). The remaining factor maps `0 ↦ 0`.
- `maxGenEigenspace_eq` : `maxGenEigenspace f μ = genEigenspace f μ (maxGenEigenspaceIndex f μ)`
  (needs `[IsNoetherian]`, supplied by `FiniteDimensional`).
- `genEigenspace_nat` : `genEigenspace f μ k = ker ((f - μ•1)^k)`.
- A non-eigenvalue `ν` has `maxGenEigenspace ν = ⊥`
  (contrapositive of `hasEigenvalue_of_hasGenEigenvalue ∘ hasGenEigenvalue_iff.mpr`),
  so the spanning iSup over all `μ : K` reduces to the finite eigenvalue set
  `(finite_hasEigenvalue f).toFinset`.
- `minpoly.dvd K f hp` converts "p annihilates f" into "minpoly ∣ p".
- GOTCHA: `Finset.erase` / `Finset.prod_erase_mul` require `DecidableEq K`; a
  `classical` at the top of the proof supplies it (a field is not `DecidableEq` by
  default).

## Result this session

New file `proofs/Proofs/CayleyHamiltonMinpolyOQ01OQ01.lean` proves:
- `minpoly_dvd_maxGenEigenspace_product` — the forward divisibility above.
- supporting: `maxGenEigenspace_eq_bot_of_not_hasEigenvalue`,
  `aeval_linear_factor_pow`.
0 sorries, 0 axioms by construction.

This converts the parent's `minpoly_product_formula` axiom into a one-sided gap:
only `∏ ∣ minpoly` (the exactness side) remains unproved.

## BUILD STATUS — verification pending (infrastructure)

The first Docker build run reported exactly two file errors (`DecidableEq K`
synthesis at the `Finset.erase` sites); both fixed by adding `classical`.
Subsequent build attempts failed at the *infrastructure* level only: the host
disk is at 100% (`/System/Volumes/Data`, ~2.7 GiB free), which corrupted the
Mathlib olean cache (`Mathlib/GroupTheory/Perm/Cycle/Basic.olean.private`,
invalid header) and then prevented Docker from writing its containerd metadata
DB at all. A clean machine-check is required once disk pressure is relieved.
The proof is logically complete and the only code-level issue was already
resolved.

---

## Dead Ends

- None yet. The reverse direction (`∏ ∣ minpoly`) was deliberately not attempted:
  it requires exhibiting a vector `v` with `(f - μ)^{e_μ - 1} v ≠ 0`
  (strictness of the generalized-eigenspace chain at the index), which is the
  genuine content of `maxGenEigenspaceIndex_exact` and likely needs more
  infrastructure than one session.
