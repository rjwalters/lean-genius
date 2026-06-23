# cayley-hamilton-oq-01-oq-01
## Module Annihilator = Minpoly Ideal — IN PROGRESS (1 sorry: cyclic vector characterization)

**Status: IN PROGRESS** — 3 theorems proved, 1 sorry (cyclic_vecAnnIdeal_eq_minpoly).

---

## Summary

`CayleyHamiltonOQ01OQ01.lean` (~114 lines) formalizes the K[X]-module annihilator theory
for n×n matrices over a field K.

**Proved theorems (0 sorries)**:
- `minpoly_matrix_eq_mulVecLin`: minpoly K M = minpoly K M.mulVecLin (private helper)
- `kn_module_annihilator_eq_minpoly`: annihilator K[X] (AEval' M.mulVecLin) = span {minpoly K M}
- `mem_vecAnnIdeal_iff`: f ∈ vecAnnIdeal M v ↔ f • (AEval'.of M.mulVecLin v) = 0
- `minpoly_mem_vecAnnIdeal`: minpoly K M ∈ vecAnnIdeal M v (for all v)
- `minpoly_ideal_le_vecAnnIdeal`: span {minpoly K M} ≤ vecAnnIdeal M v

**Sorry theorems (1)**:
- `cyclic_vecAnnIdeal_eq_minpoly`: For a cyclic vector v (IsCyclicVector), vecAnnIdeal M v = span {minpoly K M}

**PR**: #9097

---

## Session Log

### Session 2026-04-03 (Session 1)
**Mode**: FRESH
**Outcome**: progress — 3 theorems proved, 1 sorry

**What Was Done**:
1. Surveyed Mathlib for K[X]-module structure on K^n and annihilator ideal theory
2. Found `Polynomial.span_minpoly_eq_annihilator` in `AnnihilatingPolynomial.lean`
3. Found `Matrix.minpoly_toLin'` and `Matrix.toLin'_apply'` for matrix-to-endomorphism connection
4. Created `CayleyHamiltonOQ01OQ01.lean` with full module annihilator theory
5. Built cleanly: 0 errors, 1 sorry warning

**Key Lean Fixes**:
1. `Polynomial.span_minpoly_eq_annihilator` takes `𝕜` as an EXPLICIT argument (not implicit).
   In Mathlib's `AnnihilatingPolynomial.lean`, `variable (𝕜)` at line 139 makes the field explicit.
   Must call as `Polynomial.span_minpoly_eq_annihilator K f`, NOT `span_minpoly_eq_annihilator f`.
   Error without explicit K: "Application type mismatch: The argument φ has type ... →ₗ[K] ... of sort
   Type u_1 but is expected to have type Type ?u.2685 of sort Type (?u.2685 + 1)".

2. `Polynomial.dvd_iff_modByMonic_eq_zero` does NOT exist in Mathlib.
   The correct lemma for "p | q ↔ q %ₘ p = 0" needs to be found (Polynomial.modByMonic_eq_zero_iff_isRoot?
   or Polynomial.dvd_iff_isRoot? — check for monic divisibility lemmas).

3. `Module.AEval'.of_symm_smul`: `(AEval'.of φ).symm (f • m) = aeval φ f • (AEval'.of φ).symm m`
   Used to prove minpoly_mem_vecAnnIdeal via apply_fun + simp.

**Files Created**:
- `proofs/Proofs/CayleyHamiltonOQ01OQ01.lean` (114 lines)

**Next Steps**:
1. Prove `cyclic_vecAnnIdeal_eq_minpoly`:
   - Search Mathlib for the correct name for "p | q ↔ q modByMonic p = 0"
   - Candidates: `Polynomial.dvd_iff_modByMonic`, `Polynomial.modByMonic_eq_zero_iff_dvd`
   - Use `Polynomial.modByMonic_eq_zero_iff_isRoot` is wrong (that's for linear factors)
   - Try `Polynomial.EuclideanDomain.dvd_iff_modByMonic_eq_zero` or just search
2. Once cyclic_vecAnnIdeal is proved, consider the full invariant factor decomposition
   (needs f.g. torsion K[X]-module structure theorem — likely needs Mathlib's Smith Normal Form)

---

## Key Mathematical Insights

1. **AEval' bridge**: `Module.AEval' φ` is the K[X]-module on M where X acts as φ. The
   annihilator of this module as a K[X]-module equals `Ideal.span {minpoly K φ}`.

2. **Matrix vs endomorphism**: Matrices need `mulVecLin` to become K[X]-module endomorphisms.
   The bridge: `M.mulVecLin = Matrix.toLin' M`, and `minpoly K M = minpoly K (Matrix.toLin' M)`.

3. **vecAnnIdeal**: The annihilator of the cyclic submodule span {v} equals span {minpoly K M}
   IFF v is a cyclic vector. This is the key to invariant factor decomposition.

4. **Explicit field argument in Mathlib**: When a `section` uses `variable (𝕜)`, theorems
   in that section have 𝕜 as an explicit argument. Always check `variable` declarations
   before calling theorems from Mathlib sections.
