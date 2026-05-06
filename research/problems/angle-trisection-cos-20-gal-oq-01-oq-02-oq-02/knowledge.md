# angle-trisection-cos-20-gal-oq-01-oq-02-oq-02

## Problem Summary

**Question**: Can `gal_order_eq_totient_div2_general` be proved using IsCyclotomicExtension?

**Short answer**: YES.

**Target**: For n ≥ 3, |Gal(minpoly ℚ (cos(π/n)))| = φ(2n)/2.

---

## Session 2026-05-06 (Session 2) — Eliminate cos_pi_splitting_finrank sorry

**Mode**: REVISIT
**Outcome**: completed

### What I Did

1. Read the 1 remaining sorry in `cos_pi_splitting_finrank`
2. Identified proof route: conjSubgroup(2n) normal → IsGalois ℚ maxRealSubfield → splits → bounds
3. Wrote complete proof using:
   - `IsCyclotomicExtension.autEquivPow` for abelianness → `aep.injective + mul_comm` for normality
   - `inferInstance` to get `IsGalois ℚ ↥(maxRealSubfield (2*n))` after `H.Normal`
   - `IsNormal.splits acos_in_K` for upper bound splits
   - `IsSplittingField.lift _ _ hsplits` for `SplittingField →ₐ maxRealSubfield`
   - `LinearMap.finrank_le_finrank_of_injective hlift.injective` for upper bound
   - `minpoly.eq_of_irreducible_of_monic h_irr hr_root` for lower bound
4. File now has 0 sorries, 0 axioms, 305 lines

### Key Findings

- `inferInstance` gives `IsGalois ℚ ↥(maxRealSubfield (2*n))` once `H.Normal` is established
- The normality proof is 3 lines: `aep.injective (by rw [map_mul, map_mul, mul_comm])`
- Pattern mirrors `InverseGalois.lean:994-1005` exactly
- `minpoly.eq_of_irreducible_of_monic` is the right lemma for the lower bound root argument

### Files Modified

- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ02OQ02.lean` (305 lines, 0 sorries)
- `src/data/proofs/angle-trisection-cos-20-gal-oq-01-oq-02-oq-02/meta.json` (status: verified)

---

## Session 2026-05-05 (Session 1) — General Formula via IsCyclotomicExtension

**Mode**: FRESH
**Outcome**: progress

### What I Did

1. Surveyed AngleTrisectionCos20GalOQ01OQ02 — found tautological placeholder for `gal_order_eq_totient_div2_general`
2. Surveyed AngleTrisectionOQ02OQ03OQ01 — found complete cyclotomic machinery for cos(2π/m) case
3. Identified key reduction: cos(π/n) = cos(2π/(2n)), allowing n → 2n substitution
4. Wrote `AngleTrisectionCos20GalOQ01OQ02OQ02.lean` with:
   - `cos_pi_minpoly_natDegree`: natDegree = φ(2n)/2 — SORRY-FREE
   - `cos_pi_extension_degree`: intermediate field of degree φ(2n)/2 — SORRY-FREE
   - `cos_pi_gal_card`: |Gal| = φ(2n)/2 — 1 sorry on splitting field degree
   - Consistency checks for n=5,7,9
5. Created gallery data (meta.json, index.ts, annotations.json)
6. Submitted Docker build

### Key Findings

- **Central reduction**: cos(π/n) = cos(2π/(2n)) is the key arithmetic identity
- The IsCyclotomicExtension machinery in OQ02OQ03OQ01 works for cos(2π/m); substituting m=2n gives our result
- Degree theorem is FULLY PROVED (0 sorries)
- The Gal card theorem has 1 sorry on: finrank ℚ SplittingField = φ(2n)/2
- This sorry is well-understood: follows from normality of ℚ(cos(π/n))/ℚ

### The Sorry Analysis

**Sorry**: `cos_pi_splitting_finrank n hn`

**Proof sketch**:
1. Lower bound: SplittingField ⊇ ℚ(root), so finrank ≥ natDegree = φ(2n)/2
2. Upper bound: ℚ(cos(π/n)) = maxRealSubfield(2n) is Galois over ℚ
   - conjSubgroup = ⟨σ⟩ is a subgroup of (ℤ/2nℤ)× (abelian group)
   - Every subgroup of an abelian group is normal
   - Fixed field of a normal subgroup of a Galois group is Galois
3. By normality, minpoly(cos(π/n)) splits over ℚ(cos(π/n))
4. Polynomial.SplittingField.lift: SplittingField ↪ ℚ(cos(π/n)), so finrank ≤ φ(2n)/2

**Estimated effort to eliminate**: ~80 lines
- Need: `Subgroup.isNormal_of_subgroup_of_abelian`
- Need: `IntermediateField.isGalois_of_fixedField_of_normal_subgroup`
- Need: `IsGalois.splits` → `Polynomial.SplittingField.lift`

### Files Created

- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ02OQ02.lean` (175 lines, 1 sorry)
- `src/data/proofs/angle-trisection-cos-20-gal-oq-01-oq-02-oq-02/meta.json`
- `src/data/proofs/angle-trisection-cos-20-gal-oq-01-oq-02-oq-02/index.ts`
- `src/data/proofs/angle-trisection-cos-20-gal-oq-01-oq-02-oq-02/annotations.json`

### Next Steps

1. Eliminate the sorry: prove conjSubgroup(2n) is normal → maxRealSubfield(2n) is Galois
2. Use Polynomial.SplittingField.lift or similar to bound finrank SplittingField
3. Combine bounds to get finrank = φ(2n)/2 exactly
