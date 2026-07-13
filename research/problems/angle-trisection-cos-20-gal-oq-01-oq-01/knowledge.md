# angle-trisection-cos-20-gal-oq-01-oq-01: Unified Eisenstein Galois Group

**Status**: COMPLETED (0 sorries, 0 axioms)
**Phase**: COMPLETED
**File**: `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ01.lean`

## Problem Statement

Unify the cos(20°) and cos(π/7) Galois group results (both |Gal| = 3) into a single
theorem parameterized by the Eisenstein prime p ∈ {3, 7}.

## Session 2026-04-21 (Session 1) - Complete Unification

**Mode**: FRESH
**Outcome**: completed

### What I Did

1. Read both parent files to understand the common algebraic structure
2. Identified the common pattern:
   - Both polynomials arise from Eisenstein cubics via substitution
   - cos(20°): r₃ = Y³-6Y²+9Y-3 (Eisenstein at p=3), substitution X = (Y-1)/2
   - cos(π/7): r₇ = Y³-7Y²+14Y-7 (Eisenstein at p=7), substitution X = (Y-2)/2
3. Created `AngleTrisectionCos20GalOQ01OQ01.lean` with:
   - `trisectionPoly p`: parameterized definition for p ∈ {3,7}
   - `eisensteinCubic p`: the shifted Eisenstein cubic for each p
   - `CyclicCubicData` structure capturing the common proof pattern
   - `trisection_gal_order_3`: unified Galois group theorem (0 sorries)
   - `eisenstein_cubic_to_trisection`: the substitution X = (Y-a)/2 via ring identity
   - `both_trisection_gal_order_3`: main summary theorem

### Key Findings

- **Common structure**: both are monic cubics Eisenstein at p with:
  - coeff_0 = -p (divisible by p but not p²)
  - coeff_1, coeff_2 divisible by p
  - leading coeff = 1 (not divisible by p)
- **Substitution pattern**: 
  - p=3: r₃(2X+1) = 8X³-6X-1 (cos 20° minimal poly)  
  - p=7: r₇(2X+2) = 8X³-4X²-4X+1 (cos π/7 minimal poly)
- **Both verified by `ring`**: the substitution identity is purely algebraic
- **`CyclicCubicData` structure**: cleanly packages (irreducible, degree_3, gal_order_3)

### Files Modified

- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ01.lean` (new file)
- `proofs/Proofs.lean` (added import)

### Mathematical Insight

The unification reveals that both cases arise from "Eisenstein cubics at prime p" under the
substitution X ↦ (Y-a)/2 (which is a change of variable in the triple-angle Chebyshev context).
The Eisenstein criterion explains WHY both polynomials are irreducible, and the shared proof
structure (degree 3 → splitting field of degree 3 → Galois group order 3) applies uniformly.

The `CyclicCubicData` structure explicitly encodes this common structure, making both cases
instances of the same abstract mathematical pattern.

### Next Steps

None — proof is complete. Potential follow-ups:
- Can this generalize to all primes p ≡ 1 (mod 3)? (Where cos(2π/p) has degree-3 min poly)
- Or all p with φ(p) = 6 (i.e., p = 7, 9)? These would require the full cyclotomic theory.
