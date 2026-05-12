# Current State

**Phase**: ACT (boundary case + structural sign lemma added; general proof still open)
**Since**: 2026-05-12T05:00:00Z
**Iteration**: 3

## Current Focus

S3 ACT — Boundary case + structural sign-pattern lemma on top of S2 Level-2:
- Extended `r : ℕ → ℤ[X]` to include p = 3 with `r 3 = X − 3`
  (degenerate degree-1 base case since cos(π/3) = 1/2, so 2 + 2cos(π/3) = 3).
- Added five p = 3 theorems: `r_3_eq`, `r_3_natDegree`, `r_3_degree`,
  `r_3_monic`, `r_3_isEisensteinAt`.
- Extended `eisenstein_verified_small_primes` from four primes to five
  (p ∈ {3, 5, 7, 11, 13}).
- Added structural lemma `r_constantCoeff_eq_signed_p`: for each verified
  prime p, `(r p).coeff 0 = (-1)^((p-1)/2) · p`. This packages the sign
  pattern uniformly and matches the cyclotomic prediction
  `N_{ℚ(θ_p)/ℚ}(2 + θ_p) = (-1)^((p-1)/2) · Φ_{2p}(-1) = (-1)^((p-1)/2) · p`.
- File grows: 301 → 404 lines, 24 → 30 theorems, 1 definition (unchanged).
- Sorries: 1 (unchanged — the general conjecture).

## Active Approach

**Unified cyclotomic-ramification proof** of the conjecture (unchanged from S1):

> For every odd prime p ≥ 3, the minimal polynomial of 2 + 2cos(π/p) over ℚ is Eisenstein at p.

Proof strategy:
1. Show 2 + θ_p = (1+ζ)(1+ζ⁻¹) where ζ = ζ_{2p} and θ_p = 2cos(π/p).
2. Show N_{ℚ(ζ_{2p})/ℚ}(1 + ζ) = Φ_{2p}(−1) = Φ_p(1) = p.
3. Conclude N_{ℚ(θ_p)/ℚ}(2 + θ_p) = p, giving the constant-term-of-min-poly = ±p.
4. Show 2 + θ_p is a uniformizer of the unique prime 𝔭_θ above p in ℤ[θ_p].
5. Quote: uniformizer of totally ramified extension ⇒ min poly is Eisenstein at p.

## Blockers

None firm. Mathlib's `Polynomial.cyclotomic` API provides the value Φ_{2p}(−1) = p
via the relation `Polynomial.cyclotomic_two_mul_odd_eq_cyclotomic_neg` (or its equivalent)
plus `Polynomial.cyclotomic_prime_eval_one`. The local-field uniformizer ⇒ Eisenstein
theorem may need to be built locally (~200–400 lines) or replaced with a direct
Newton-identity argument.

## Next Action

**S4 next action**: Resume the cyclotomic-ramification approach toward the
general conjecture, now with the sign-pattern fingerprint in hand.

Two paths:

### Path A: Cyclotomic-ramification proof
Build the missing local-field uniformizer ⇒ Eisenstein theorem in Mathlib style.
Estimated: 200–400 lines. High leverage if completed (proves the conjecture for all p).

### Path B: Direct Chebyshev/cyclotomic computation
Define `r_p : ℕ → ℤ[X]` parametrically using `Polynomial.cyclotomic` and the
real-subfield trace. Prove each Eisenstein clause:
- Constant term: `Polynomial.cyclotomic_prime_eval_one` gives Φ_p(1) = p, hence
  Φ_{2p}(−1) = p, hence N(2 + θ_p) = p.
- Sub-leading divisibility: each elementary symmetric polynomial in the conjugates
  lies in p·Z by ramification.
- Constant ∉ p²: from the totally-ramified structure.

Estimated: similar (~300 lines), but more grounded in the existing Mathlib cyclotomic API.

**Recommend Path B for S3**, with the local-field framework as a fallback if direct
computation hits Mathlib gaps.

### Followup: Extend explicit verification

Add `r 17, r 19, r 23` to the parametric definition and verify Eisenstein. Each adds
~30 lines. Useful for testing edge cases (e.g., degree-8 and degree-9 polynomials).

## Attempt Counts

- Total attempts: 3 (S1 OBSERVE, S2 ACT Level-2 per-prime + statement, S3 ACT base case + sign lemma)
- Current approach attempts: 2 (Level-2 implementation; S3 boundary extension)
- Approaches tried:
  - S1: cyclotomic ramification, surveyed only.
  - S2: per-prime explicit verification + uniform statement (sorry on general case).
  - S3: p = 3 boundary case + `r_constantCoeff_eq_signed_p` sign pattern (structural).

## Key Files

- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean` — **extended in S3** (404 lines, +103 vs S2).
  Parametric `r : ℕ → ℤ[X]` now covers p ∈ {3, 5, 7, 11, 13} (added boundary p = 3).
  Eisenstein verification for all five primes. Irreducibility for p ∈ {11, 13}.
  Structural sign-pattern lemma `r_constantCoeff_eq_signed_p`. General conjecture sorry.
- `src/data/proofs/angle-trisection-cos-20-gal-oq-01-oq-03/` — **new in S2**.
  Gallery entry: meta.json (status: axiomatized, sorries: 1), annotations.json, index.ts.
- `proofs/Proofs/AngleTrisectionCos20Gal.lean` — cos(20°) case, p=3 via cos(π/9); Eisenstein at 3.
- `proofs/Proofs/AngleTrisectionCos20GalOQ01.lean` — cos(π/7); Eisenstein at 7.
- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ01.lean` — unified cos(20°) ⊕ cos(π/7) for p ∈ {3, 7}.
- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ02.lean` — cos(π/5); Eisenstein at 5.
