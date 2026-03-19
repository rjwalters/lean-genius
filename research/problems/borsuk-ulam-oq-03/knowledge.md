# borsuk-ulam-oq-03: Constructive (Intuitionistic) Borsuk-Ulam

## Problem Summary

**Open Question**: Can the 1D Borsuk-Ulam theorem be proved constructively
(without full classical logic)? What is the constructive status of
higher-dimensional Borsuk-Ulam?

**Status**: 157 proved theorems, 4 axioms (2 independent), 0 sorries (3680 lines).

**Answer**:
- 1D: YES, proved via IVT on antisymmetric difference
- n≥2: Requires algebraic topology (axiomized); no known constructive proof

## Session 2026-03-19 (researcher-2, Session 6) - Axiom Reduction

**Mode**: REVISIT (RICH knowledge from 5 prior sessions)
**Outcome**: progress (major axiom reduction)

### What I Did

1. **Proved Brouwer FP → No-Retraction (General)** (Section LXIII):
   - Elegant proof: Given retraction r, define F(x)=-r(x). F maps B→S⊂B.
   - By Brouwer FP, F has fixed point x₀=-r(x₀). Then ‖x₀‖=‖r(x₀)‖=1.
   - So x₀∈S^n, r(x₀)=x₀, but x₀=-r(x₀)=-x₀, giving x₀=0∈S^n. Contradiction.

2. **Proved No-Retraction → Brouwer FP (General)** (Section LXIII):
   - Key construction: ray-sphere intersection via quadratic formula.
   - Extend f to f̃=f∘ballProj on all of ℝ^(n+1).
   - For each x, ray from f̃(x) through x exits S^n at t*=(-B+√Δ)/A.
   - Proved retraction maps to sphere (quadratic root property).
   - Proved retraction fixes sphere (t*=1 when ‖x‖=1, via AM-GM bound).
   - Proved continuity (explicit composition chain using Continuous.* API).

3. **Established full equivalence** `brouwer_fp_iff_no_retraction`:
   - Both directions proved, so the two axioms are interchangeable.
   - Reduced independent axiom count from 3 to 2.

4. **Removed ~2000 lines of duplicate code**:
   - Sections XLII-LIX appeared three times due to merge artifacts.
   - Cleaned to single copy, reducing file from 5393 to 3680 lines.

### Key Findings

- AM-GM inequality `2⟨p,x⟩ ≤ ‖p‖²+‖x‖²` avoids Cauchy-Schwarz for the A+B≥0 bound
- The quadratic root identity: `(-B+√Δ)²+2B(-B+√Δ)+A(S-1)=0` reduces to `Δ-B²+A(S-1)=0`
- Ball projection `ballProj(x) = x/max(1,‖x‖)` cleanly extends f to all of ℝ^(n+1)
- For sphere points: t*=1 follows from `A+2B+S = ∑x²=1` and `√(A+B)² = A+B`

### Files Modified

- `proofs/Proofs/BorsukUlamOQ03.lean` (5393 → 3680 lines, deduplicated + 7 new theorems)

### Next Steps

- Prove BU → no_retraction (would reduce to 1 independent axiom)
- Extend discrete BU to integer labels (Tucker complementary edge)
- Add topological degree for S¹ maps
- Prove BU → Brouwer FP directly

## Session 2026-03-19 (researcher-6, Session 7) - BU → No-Retraction

**Mode**: REVISIT (RICH knowledge from 6 prior sessions)
**Outcome**: progress (key theorem added)

### What I Did

1. **Proved `no_odd_map_sphere`** (Section LXV, fully proved, 0 sorries):
   - Borsuk's odd mapping theorem: no continuous odd map S^n → S^{n-1}.
   - Direct from BU: f(x₀)=f(-x₀)=-f(x₀) → f(x₀)=0 ∉ S^{n-1}.

2. **Added `bu_implies_no_retraction`** (Section LXV, 1 sorry):
   - Key theorem reducing independent axioms from 2 to 1.
   - Proof strategy: hemisphere pasting + radial extension + no_odd_map_sphere.
   - Given retraction r, construct odd map g: S^{n+1} → S^n (dimension shift!).
   - Upper hemisphere: g(x) = r(projInit x).
   - Lower hemisphere: g(x) = -r(-projInit x).
   - Branches agree on equator (where projInit ∈ S^n, r = identity).
   - Radial extension to ℝ^{n+2} for BU application.
   - Sorry: continuity of radial extension (standard analysis, not a math gap).

3. **Added infrastructure**: projInit, lastCoord, fin_sum_split, related lemmas.

### Key Insights

- The proof uses BU for S^{n+1} (one dimension HIGHER), not S^n.
  This is the crucial "dimension shift" that makes the argument work.
- The naive approach (difference map r(y)-r(-y)) fails because it vanishes
  at the poles. The pasting construction avoids this.
- The max/min scaling approach G(x)=max(t,0)*r(y)+min(t,0)*r(-y) fails
  because it vanishes on the equator (scaling by t kills the signal).
- The correct pasting g(x) = r(y) or -r(-y) maps S^{n+1} to S^n
  (always ‖g(x)‖=1), enabling the oddness contradiction.

### Files Modified

- `proofs/Proofs/BorsukUlamOQ03.lean` (3680 → 3833 lines)

### Remaining Work

- Close the 1 sorry in `bu_implies_no_retraction` (radial extension continuity)
- This requires showing the piecewise-defined function
  F̃(x) = ‖x‖·g(x/‖x‖) is continuous, where g is the hemisphere pasting.
  Standard analysis argument using pasting lemma + radial cone construction.
