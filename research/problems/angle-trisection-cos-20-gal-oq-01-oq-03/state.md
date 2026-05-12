# Current State

**Phase**: ACT (per-prime verification done; general proof open)
**Since**: 2026-05-12T03:00:00Z
**Iteration**: 2

## Current Focus

S2 ACT — Level 2 implementation per S1 plan:
- Parametric `r : ℕ → ℤ[X]` with explicit values for p ∈ {5, 7, 11, 13}.
- IsEisensteinAt verification for each of the four primes.
- Irreducibility for the new primes (p=11, p=13).
- General conjecture stated as `eisenstein_conjecture_cos_pi_p` (sorry).

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

**S3 next action**: Begin discharging the `eisenstein_conjecture_cos_pi_p` sorry.

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

- Total attempts: 2 (S1 OBSERVE, S2 ACT Level-2 per-prime + statement)
- Current approach attempts: 1 (Level-2 implementation)
- Approaches tried:
  - S1: cyclotomic ramification, surveyed only.
  - S2: per-prime explicit verification + uniform statement (sorry on general case).

## Key Files

- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean` — **new in S2** (301 lines).
  Parametric `r : ℕ → ℤ[X]`, Eisenstein verification for p ∈ {5, 7, 11, 13},
  irreducibility for p ∈ {11, 13}, general conjecture sorry.
- `src/data/proofs/angle-trisection-cos-20-gal-oq-01-oq-03/` — **new in S2**.
  Gallery entry: meta.json (status: axiomatized, sorries: 1), annotations.json, index.ts.
- `proofs/Proofs/AngleTrisectionCos20Gal.lean` — cos(20°) case, p=3 via cos(π/9); Eisenstein at 3.
- `proofs/Proofs/AngleTrisectionCos20GalOQ01.lean` — cos(π/7); Eisenstein at 7.
- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ01.lean` — unified cos(20°) ⊕ cos(π/7) for p ∈ {3, 7}.
- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ02.lean` — cos(π/5); Eisenstein at 5.
