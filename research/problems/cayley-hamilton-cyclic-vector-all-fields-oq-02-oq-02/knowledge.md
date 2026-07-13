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

## Session 2026-07-12 (researcher-1) - Symmetries: similarity + transpose invariance of dim C(M)

**Mode**: FRESH (built on the pinned Frobenius range n ≤ dim C(M) ≤ n²)
**Outcome**: progress (0-sorry / 0-axiom, VERIFIED via `lake env lean` against built Mathlib;
`#print axioms` = [propext, Classical.choice, Quot.sound] on all three headline theorems)

### What I Did
- Created `proofs/Proofs/CayleyHamiltonCyclicVectorAllFieldsOQ02OQ02Symmetry.lean` (7 decls).
- Established *why* the whole commutant-dimension analysis is an invariant of the
  rational-canonical / invariant-factor data: `dim_K C(M)` is unchanged under
  **similarity** and **transpose**.

### Key Findings
- `conjLinearEquiv u` : `X ↦ u X u⁻¹` for a unit `u : Mₙ(K)ˣ`, packaged as a K-linear
  automorphism of Mₙ(K) (inverse `X ↦ u⁻¹ X u`). Built by hand; left/right inverse via
  `Units.inv_mul_cancel_left/right`, `Units.mul_inv_cancel_left/right`.
- `conj_mul` : `(uAu⁻¹)(uBu⁻¹) = u(AB)u⁻¹` — `simp only [mul_assoc]; rw [Units.inv_mul_cancel_left]`.
- `map_conj_centralizer` : the automorphism maps `C(M)` submodule ONTO `C(uMu⁻¹)` submodule
  (Submodule.map equality by ext + membership; both directions reduce to `M Y = Y M`).
- `finrank_centralizer_conj` : **similarity invariance** `dim_K C(uMu⁻¹) = dim_K C(M)`,
  via `Subalgebra.finrank_toSubmodule` + `LinearEquiv.finrank_eq ((conjLinearEquiv u).submoduleMap _)`.
- `map_transpose_centralizer` / `finrank_centralizer_transpose` : **transpose invariance**
  `dim_K C(Mᵀ) = dim_K C(M)` (transpose is a linear anti-automorphism; `transpose_mul`,
  `transpose_transpose`).
- `finrank_centralizer_conj_transpose` : combined `dim_K C((uMu⁻¹)ᵀ) = dim_K C(M)`.

### Gotchas
- ★ Bare `↑u⁻¹` MIS-PARSES (leaves `u⁻¹ : Mₙˣ` uncoerced → `HMul Matrix Matrixˣ` synth fail).
  Use `.val` form: `u.val` / `(u⁻¹).val`, which are defeq to the coercions in the
  `Units.*_cancel_*` lemmas so `rw` still matches.
- ★ `transposeLinearEquiv` coercion reduces to `(transposeAddEquiv ..).toFun Y`, which
  `transposeLinearEquiv_apply`/`LinearEquiv.coe_coe` do NOT rewrite in the goal; discharge
  the `e y = X` obligation by `show ... Yᵀ ...` (defeq) then `rw`.
- Env: loom worktree `.loom/worktrees/researcher-1` was reclaimed by the janitor mid-session
  (no commits yet ⇒ "clean" ⇒ removed). Recovered by `git worktree add -b … origin/main
  .loom/tmp/r1-cayley-sym`; typecheck via `cd proofs && LAKE_UNSAFE=1 ./bin/lake env lean <abs-file>`.

### Files Modified
- `proofs/Proofs/CayleyHamiltonCyclicVectorAllFieldsOQ02OQ02Symmetry.lean` (new)

### Next Steps
- General Frobenius formula `dim C(M)=Σ(2i−1)dᵢ` (needs RCF/invariant-factor infra, hard).
- Block-diagonal subadditivity `dim C(M⊕N) ≥ dim C(M)+dim C(N)` (clean next target).
