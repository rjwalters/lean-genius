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

## Result — FULL PRODUCT FORMULA PROVED (parent axiom eliminated)

`proofs/Proofs/CayleyHamiltonMinpolyOQ01OQ01.lean` now proves the *complete*
identity that the parent file only axiomatized as `minpoly_product_formula`:

    minpoly_eq_prod_pow_maxGenEigenspaceIndex :
      minpoly K f = ∏_{μ eigenvalue} (X - μ)^{maxGenEigenspaceIndex f μ}
    [IsAlgClosed K] [FiniteDimensional K V].

Both divisibilities + monicity:
- `minpoly_dvd_maxGenEigenspace_product` — forward `minpoly ∣ ∏` (needs alg.closed,
  from `iSup_maxGenEigenspace_eq_top`).
- `pow_maxGenEigenspaceIndex_dvd_minpoly` — single-factor reverse `(X-μ)^{e_μ} ∣ minpoly`
  (needs only `FiniteDimensional`).
- `prod_pow_maxGenEigenspaceIndex_dvd_minpoly` — full reverse `∏ ∣ minpoly`
  via pairwise coprimality (`pairwise_coprime_X_sub_C`, `Finset.prod_dvd_of_coprime`).
- equality via `eq_of_monic_of_associated` + `associated_of_dvd_dvd`.
0 sorries, 0 axioms.

### Reverse-direction proof skeleton (the genuine new content)
For an eigenvalue μ with index `e>0`: factor `minpoly = (X-μ)^m·g`,
`m = rootMultiplicity μ`, `(X-μ) ∤ g` (`exists_eq_pow_rootMultiplicity_mul_and_not_dvd`).
`X-μ` prime ⇒ `IsCoprime (X-μ) g` (`(prime_X_sub_C μ).coprime_iff_not_dvd`), so
`IsCoprime ((X-μ)^e) g` (`.pow_left`). Bézout `a·(X-μ)^e + b·g = 1`; take exactness
witness `v` (`(f-μ)^e v = 0`, `(f-μ)^{e-1} v ≠ 0`); evaluating Bézout at `v` kills the
first term ⇒ `v = b(f)(g(f) v)`. `minpoly` annihilates ⇒ `(f-μ)^m (g(f) v) = 0`;
`b(f)` commutes with `(f-μ)^m` ⇒ `(f-μ)^m v = 0`; exactness ⇒ `e ≤ m` ⇒
`(X-μ)^e ∣ (X-μ)^m ∣ minpoly`.

## BUILD STATUS — VERIFIED offline (0-axiom)

Docker is dead (containerd-corrupt, disk 100% / ~3.7 GiB free), but the file
machine-checks **green offline** from the main repo:
`LAKE_UNSAFE=1 ./bin/lake env lean <worktree-file>` → EXIT 0.
`#print axioms minpoly_eq_prod_pow_maxGenEigenspaceIndex` (and the two divisibility
lemmas) lists only `[propext, Classical.choice, Quot.sound]` — genuinely 0-axiom,
no `sorryAx`/`ofReduceBool`. The earlier `DecidableEq K` `Finset.erase` errors were
already fixed with `classical`.

---

## Dead Ends

- None. The reverse direction (`∏ ∣ minpoly`) — previously flagged as needing more
  infrastructure than one session — was completed this session via the per-eigenvalue
  coprimality + Bézout argument above, requiring only `FiniteDimensional` (no algebraic
  closure) for each factor. The exactness witness from the prior session was the key
  enabler.
