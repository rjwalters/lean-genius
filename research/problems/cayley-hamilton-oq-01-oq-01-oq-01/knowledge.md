# Knowledge Base: cayley-hamilton-oq-01-oq-01-oq-01

Existence of a cyclic vector in the non-derogatory case (minpoly = charpoly).

---

## Problem Understanding

Goal: for an `n×n` matrix `M` over a field `K`, if `minpoly K M = M.charpoly`
(equivalently `(minpoly K M).natDegree = n`), produce a cyclic vector `v`
(parent's `IsCyclicVector M v`: no nonzero polynomial of degree `< n` kills `v`).

The parent `CayleyHamiltonOQ01OQ01` already built the `K[X]`-module framework:
`Module.AEval' M.mulVecLin`, the vector annihilator ideal `vecAnnIdeal M v`,
`mem_vecAnnIdeal_iff`, `minpoly_ideal_le_vecAnnIdeal` (span{minpoly} ≤ vecAnnIdeal
always), and `cyclic_vecAnnIdeal_eq_minpoly` (the EASY direction: cyclic ⟹ order =
minpoly).

---

## Insights

- **The whole theorem reduces to ONE general lemma** (true for every `M`):
  `exists_vecAnnIdeal_eq_minpoly : ∃ v, vecAnnIdeal M v = Ideal.span {minpoly K M}`.
  This is the classical *existence of a vector of maximal order* — a vector whose
  order (monic generator of its annihilator ideal) is exactly the minimal
  polynomial = the module exponent.
- Given such a `v`, cyclicity is **elementary** and is fully proved here
  (`isCyclicVector_of_vecAnnIdeal_eq_minpoly`): a degree-`< n` poly `p` killing `v`
  lies in `span{minpoly}`, so `minpoly ∣ p`; nonzero `p` would have degree
  `≥ n = deg minpoly`, contradiction.
- The bridge `aeval M.mulVecLin p v = 0 ↔ p ∈ vecAnnIdeal M v`
  (`aeval_eq_zero_iff_mem_vecAnnIdeal`) is proved by mirroring the parent's
  `Module.AEval'.of … symm` / `Module.AEval.of_symm_smul` translation.
- Non-derogatory ⇒ full degree: `Matrix.charpoly_natDegree_eq_dim` +
  `Fintype.card_fin` give `(minpoly K M).natDegree = n` from `minpoly = charpoly`.

## Status (Session 2, 2026-06-25)

- **VERIFIED scaffold built** in `proofs/Proofs/CayleyHamiltonOQ01OQ01OQ01.lean`,
  compiles via host `lake env lean` with the **single** `sorry` being
  `exists_vecAnnIdeal_eq_minpoly` (line ~103). Both main theorems
  (`exists_cyclicVector_of_minpoly_natDegree_eq`,
  `exists_cyclicVector_of_minpoly_eq_charpoly`) type-check modulo that one lemma.
- Aristotle MCP is **DOWN** this session ("Resource not found" on both
  `prove_file` and `prove`). Could not delegate the hard lemma.
- No PR opened (file carries a `sorry`; gallery requires verified).

## Proof strategy for the outstanding lemma (next session / Aristotle)

`exists_vecAnnIdeal_eq_minpoly` via *maximal-order vector*:
1. **Order arithmetic** in a cyclic `K[X]`-submodule: for the order `f = ord(u)`,
   `ord(p • u) = f / gcd(f, p)`.
2. **Coprime combination (CRT)**: if `ord(u)=f`, `ord(w)=g`, `gcd(f,g)=1`, then
   `ord(u+w) = f·g`.
3. **Pairwise lcm**: combine (1)+(2) to get, from `u` (order `f`) and `w` (order
   `g`), a vector of order `lcm(f,g)` (split `f,g` into coprime parts whose product
   is `lcm`).
4. **Iterate over the standard basis** `e₁,…,eₙ`: `minpoly K M = lcm_i ord(eᵢ)`
   (minpoly = lcm of orders of a generating set), so folding the pairwise
   combination yields a vector of order `minpoly`, i.e. `vecAnnIdeal = span{minpoly}`.
   Use `minpoly_ideal_le_vecAnnIdeal` for the `≤` half; the constructed order gives `≥`.

No direct Mathlib counterpart was found (searched `LinearAlgebra/FreeModule/PID`,
`AnnihilatingPolynomial`, `Matrix/Charpoly/*`). Mathlib's PID structure theorem
(`Mathlib/Algebra/Module/PID`) gives the decomposition existentially but extracting
a concrete maximal-order vector is itself work; the combination route above is more
direct in the parent's `vecAnnIdeal` language.

---

## Dead Ends

- No Mathlib lemma for "cyclic vector exists" / "vector of maximal order" /
  "minpoly = charpoly ⟺ cyclic". Must be built (≈150–250 lines) or delegated.
