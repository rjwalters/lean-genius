# angle-trisection-cos-20-gal-oq-01-oq-02

**Problem**: |Gal(minpoly(cos(π/n))/ℚ)| for general n — the φ(2n)/2 formula

## Problem Summary

The general formula for the Galois group order of the minimal polynomial of cos(π/n) is:
  |Gal(minpoly(cos(π/n))/ℚ)| = φ(2n)/2

This follows from cyclotomic field theory: cos(π/n) generates the maximal real subfield
of ℚ(ζ_{2n}) where ζ_{2n} = e^{iπ/n}.

## Mathematical Background

**General formula**: For n ≥ 3, Gal(ℚ(cos(π/n))/ℚ) ≅ (ℤ/2nℤ)^× / ⟨-1⟩, of order φ(2n)/2.

**Known cases in the gallery**:
| n  | cos(π/n)   | minpoly               | deg | |Gal| | φ(2n)/2 |
|----|------------|----------------------|-----|------|---------|
|  5 | cos(36°)   | 4X² - 2X - 1        |  2  |   2  |   2     |
|  7 | cos(π/7)   | 8X³ - 4X²- 4X + 1  |  3  |   3  |   3     |
|  9 | cos(20°)   | 8X³ - 6X - 1        |  3  |   3  |   3     |

## Session 1 (2026-04-26) — n=5 Case Proved; General Formula Stated

**Mode**: FRESH (claimed from pool)
**Outcome**: PROGRESS — n=5 case proved (1 sorry for irreducibility), general formula stated

### What I Did
- Created `AngleTrisectionCos20GalOQ01OQ02.lean`
- Proved the n=5 case: |Gal(4X²-2X-1/ℚ)| = 2 = φ(10)/2
- Key insight: 4(1/2-a)²-2(1/2-a)-1 = 4a²-2a-1 (by ring), so β = 1/2-α is the second root
- This is the Vieta identity: sum of roots = 2/4 = 1/2, so β = 1/2-α ∈ ℚ(α)
- Proved all theorems sorry-free except `pCos5_irreducible`
- Computed φ(2n)/2 for n=5,7,9 by `decide` and cross-verified with sibling proofs

### Key Insights
- The n=5 case is simpler than n=7,9 because the second root is β = 1/2-α (linear in α)
- The cubic cases require more complex algebraic identities (quadratic expressions in α)
- The polynomial 4(1/2-a)²-2(1/2-a)-1 = 4a²-2a-1 (not the negative!) — verified by ring
- `1/2 ∈ ℚ(α)` requires casting: `algebraMap ℚ SplittingField (1/2 : ℚ) ∈ S`
- The linter warning on `map_div₀, map_one` in simp: these can be simplified away

### Remaining Sorry
- **`pCos5_irreducible`**: 4X²-2X-1 is irreducible over ℚ
  - Proof strategy: rational root theorem candidates ±1, ±1/2, ±1/4 all non-roots (norm_num)
  - Then: degree 2 + no roots → irreducible (needs Lean lemma for "degree 2 irreducible iff no roots over field")
  - Alternative: 4X²-2X-1 mod 3 = X²+X+2, no roots mod 3 → irreducible mod 3 → irreducible over ℚ
  - Alternative: use `Nat.sqrt_lt_self` or similar for "√5 ∉ ℚ"
  - **Submit to Aristotle** for automated proof

### Files Created
- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ02.lean` (310 lines, 1 sorry)
- `src/data/proofs/angle-trisection-cos-20-gal-oq-01-oq-02/meta.json`

### Next Steps
1. Submit `pCos5_irreducible` to Aristotle for automated proof
2. For general formula: research `IsCyclotomicExtension` in Mathlib
   - `IsCyclotomicExtension.Gal_equiv_totient` or similar
   - Connection between cos(π/n) and ζ_{2n} in Lean types
3. Consider n=4 case: cos(π/4) = √2/2, minpoly 2X²-1, |Gal|=2, φ(8)/2=2
