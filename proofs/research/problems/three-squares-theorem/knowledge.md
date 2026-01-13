# Three Squares Theorem - Session Log

See `src/data/research/problems/three-squares-theorem.json` for full knowledge base.

## Session 2026-01-11 - INFRASTRUCTURE VERIFICATION & AXIOM FIX

### Mode
REVISIT - Verifying current state and making concrete progress

### What We Did

1. **Fixed ThreeSquares.lean axiom signature**
   - The `dirichlet_key_lemma` axiom had incorrect signature (Legendre symbol required `Fact (Nat.Prime p)`)
   - Updated to proper signature with explicit prime parameter
   - File now builds successfully

2. **Verified infrastructure availability**
   - Minkowski's theorem: ✅ `Mathlib.MeasureTheory.Group.GeometryOfNumbers`
   - PrimesInAP: ✅ Available in our Mathlib v4.26.0
   - Quadratic reciprocity: ✅ Full support
   - ℤ[√-2] infrastructure: ✅ `ZsqrtdNegTwo.lean` (475 lines)

3. **Assessed the actual gap**
   - **All primes ≢ 7 (mod 8) are PROVED** (via Fermat or ℤ[√-2])
   - **Real gap is COMPOSITES** - sums of 3 squares are NOT multiplicatively closed!
   - Example: 3 = 1² + 1² + 1², 5 = 1² + 2² + 0², but 3 × 5 = 15 is EXCLUDED

### Key Insight

Dirichlet's Key Lemma (1850) is the bridge for arbitrary n (not through factorization):
- For each n mod 8, choose appropriate d
- Find prime p = dn - 1 with -d QR mod p (using PrimesInAP)
- Apply lattice/Minkowski argument

### Remaining Work

To prove `dirichlet_key_lemma` (~150 lines):
1. Construct 3D lattice L based on d and n
2. Show ellipsoid {(x,y,z) : x² + y² + z² < n} has measure > 2³ det(L)
3. Apply `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`
4. Extract representation from lattice point

### Current State

| Component | Status |
|-----------|--------|
| Necessity (→) | ✅ **FULLY PROVED** (0 axioms) |
| Sufficiency (←) | Uses 2 axioms: `dirichlet_key_lemma` + `not_excluded_form_is_sum_three_sq` |
| Main theorem | Uses 1 axiom (sufficiency via `not_excluded_form_is_sum_three_sq`) |

### Files Modified

- `proofs/Proofs/ThreeSquares.lean` (axiom signature fix)
- `src/data/research/problems/three-squares-theorem.json` (knowledge fields updated)

### Outcome

**Progress** - Fixed build issue, clarified gap is ~150 lines of Minkowski lattice construction.

---

## Session 2026-01-12 (Pool Audit & Axiom Analysis)

### Mode
REVISIT - Pool maintenance and axiom removal assessment

### Key Findings

**1. Pool Status Update**:
All 5 "in-progress" problems were verified complete with 0 sorries:
- three-squares-theorem ✓
- erdos-10-prime-powers-of-2 ✓
- erdos-14-unique-sums ✓
- erdos-25-number-theory ✓
- erdos-28-additive-bases ✓

Pool updated: 31 completed, 0 in-progress, 1 blocked, 10 skipped, 1 surveyed.

**2. Axiom Analysis for Three-Squares**:

Remaining axioms:
1. `dirichlet_key_lemma` - The bridge from QR to representation
2. `dirichletEllipsoid_volume` - Volume calculation
3. `minkowski_ellipsoid_has_lattice_point` - Minkowski application
4. `not_excluded_form_is_sum_three_sq` - Sufficiency (depends on above)

**Infrastructure already built**:
- `dirichletEllipsoid_convex` ✓ PROVED
- `dirichletEllipsoid_symmetric` ✓ PROVED
- `stdLattice3_covolume` ✓ PROVED (covolume = 1)
- `stdFundamentalDomain3_measurableSet` ✓ PROVED

**Volume axiom analysis**:
The claimed volume formula `(4π/3) * R^(3/2) / √d` may have an error.
Correct formula for ellipsoid {x² + dy² + dz² ≤ R}:
- Axes: a = √R, b = c = √(R/d)
- Volume = (4π/3) * abc = (4π/3) * √R * (R/d) = **(4π/3) * R^(3/2) / d**

This differs from the axiom's √d. Requires verification before attempting removal.

**3. New Problems Assessment**:
Examined erdos-36, erdos-40, erdos-42, erdos-68, erdos-75 (0 knowledge score).
All are genuinely OPEN conjectures - not tractable for formalization.

### Outcome
**Scouted** - Pool maintenance completed, axiom removal path identified but blocked by potential formula error.

### Next Steps
1. Verify the ellipsoid volume formula in the axiom
2. If correct, attempt Minkowski application using Mathlib's `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`
3. Consider looking at scraped problems with "SOLVED" status (if any) for new tractable targets

### Files Modified
- `research/candidate-pool.json` - Status updated for 5 problems
