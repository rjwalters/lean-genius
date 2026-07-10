# Knowledge Base: cayley-hamilton-cyclic-vector-all-fields-oq-02-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

## Session 2026-07-09 (researcher-5) - Scalar matrix = maximally-derogatory extreme

**Mode**: FRESH (built on merged sibling OQ02OQ02 headline `dim C(M)=n`)
**Outcome**: progress (0-sorry/0-axiom; UNVERIFIED — env-blocked, see below)

### What I Did
- Created `proofs/Proofs/CayleyHamiltonCyclicVectorAllFieldsOQ02OQ02Scalar.lean` (4 decls).
- Pinned the OTHER end of the Frobenius range `n ≤ dim_K C(M) ≤ n²`: the scalar
  matrix `c•I` realises the maximum `n²` (nonderogatory realises the minimum `n`).

### Key Findings
- `centralizer_scalar_eq_top`: `C(c•I)=⊤` (scalars central; `smul_mul_assoc`+`mul_smul_comm`).
- `adjoin_scalar_eq_bot`: `K[c•I]=⊥` (`c•I=algebraMap K Mₙ c ∈ ⊥`; `Algebra.mem_bot`+`algebraMap_eq_smul_one`).
- `finrank_centralizer_scalar`: `dim_K C(c•I)=n²` via `Subalgebra.topEquiv.toLinearEquiv`
  + `LinearEquiv.finrank_eq` + `Module.finrank_matrix`+`Fintype.card_fin`+`Module.finrank_self`.
- `scalar_derogatory` (n≥2): `minpoly≠charpoly`, derived from the sibling headline —
  nonderogatory would force dim=n but dim=n²; `Nat.mul_le_mul hn (le_refl n)`+omega.

### Blocker (env, not logic)
Docker build blocked by poisoned shared cache: dep `OQ02OQ01.setup.json` in
`lean-mathlib-cache` volume has `"isModule": true` (source is clean `/-`), aborting the
whole Cayley chain with `` `module` keyword experimental ``. Deleting the artifact
regenerates it as `true` (deterministic; see reference-docker-ismodule-poison). Did NOT
`--nuke` shared volume (live fleet). Shipped UNVERIFIED — same blocker hit sibling
PR #36663 which merged & CI-verified fine.

### Files Modified
- `proofs/Proofs/CayleyHamiltonCyclicVectorAllFieldsOQ02OQ02Scalar.lean` (new)

### Next Steps
- General Frobenius formula `dim C(M)=Σ(2i−1)dᵢ` (needs RCF/invariant-factor infra, hard).
- Clean-cache rebuild to flip this PR VERIFIED.
