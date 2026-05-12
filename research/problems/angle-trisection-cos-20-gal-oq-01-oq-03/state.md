# Current State

**Phase**: ACT (cyclotomic anchor verified per-prime; general lift pending)
**Since**: 2026-05-12T08:00:00Z
**Iteration**: 5

## Current Focus

S5 ACT — Cyclotomic anchor connecting the S3 norm fingerprint to Mathlib's
cyclotomic-polynomial API for p ∈ {3, 5, 7}:

- **Explicit cyclotomic forms** via `eq_cyclotomic_iff` + divisor expansion:
  - `cyclotomic_5_eq`: Φ_5 = X⁴+X³+X²+X+1
  - `cyclotomic_7_eq`: Φ_7 = X⁶+X⁵+X⁴+X³+X²+X+1
  - `cyclotomic_six_eq`: Φ_6 = X²−X+1
  - `cyclotomic_ten_eq`: Φ_10 = X⁴−X³+X²−X+1
  - `cyclotomic_fourteen_eq`: Φ_14 = X⁶−X⁵+X⁴−X³+X²−X+1
  Each closes by `ring` after substituting `cyclotomic_one/two/three`.

- **Numerical anchors** Φ_{2p}(-1) = p for p ∈ {3, 5, 7}:
  - `cyclotomic_six_eval_neg_one`: Φ_6(-1) = 3
  - `cyclotomic_ten_eval_neg_one`: Φ_10(-1) = 5
  - `cyclotomic_fourteen_eval_neg_one`: Φ_14(-1) = 7
  These verify the cyclotomic side of the norm prediction
  `N(2 + θ_p) = (-1)^((p-1)/2) · Φ_{2p}(-1)` directly from Mathlib.

- **Bridge to gallery's r_p**:
  - `r_3_constantCoeff_eq_cyclotomic`: `(r 3).coeff 0 = (-1)^1 · Φ_6(-1)`
  - `r_5_constantCoeff_eq_cyclotomic`: `(r 5).coeff 0 = (-1)^2 · Φ_10(-1)`
  - `r_7_constantCoeff_eq_cyclotomic`: `(r 7).coeff 0 = (-1)^3 · Φ_14(-1)`
  - `r_constantCoeff_eq_cyclotomic_small`: packaged 3-prime bridge.
  Each follows by rewriting with the cyclotomic eval and the matching
  `r_constantCoeff_eq_signed_p.X` projection from S3.

- File grows: 470 → 617 lines (+147), 32 → 44 theorems (+12),
  1 definition (unchanged). Sorries: 1 (unchanged — the general conjecture).

## Active Approach

**Unified cyclotomic-ramification proof** of the conjecture (unchanged from S1):

> For every odd prime p ≥ 3, the minimal polynomial of 2 + 2cos(π/p) over ℚ is Eisenstein at p.

Proof strategy:
1. Show 2 + θ_p = (1+ζ)(1+ζ⁻¹) where ζ = ζ_{2p} and θ_p = 2cos(π/p).
2. Show N_{ℚ(ζ_{2p})/ℚ}(1 + ζ) = Φ_{2p}(−1) = Φ_p(1) = p.
3. Show Tr_{ℚ(θ_p)/ℚ}(2 + θ_p) = p (from the cyclotomic identity
   `∑_{k odd, 1 ≤ k ≤ p−2} 2cos(kπ/p) = 1` plus the (p−1)/2 contributions
   of `+2` per conjugate).
4. Conclude `(r_p)_0 = (-1)^((p-1)/2) · p` and `(r_p)_{n-1} = -p` where
   n = (p-1)/2 — the two Vieta fingerprints already established for
   p ∈ {3, 5, 7, 11, 13} in the file.
5. Show 2 + θ_p is a uniformizer of the unique prime 𝔭_θ above p in ℤ[θ_p].
6. Quote: uniformizer of totally ramified extension ⇒ min poly is Eisenstein at p.

## Blockers

None firm. Mathlib v4.26.0 lacks the uniform bridge `Φ_{2p}(X) = Φ_p(-X)`
(or equivalently `Φ_{2p}(X)·(X+1) = X^p + 1` for odd prime p ≥ 3).
S5 derived the cyclotomic anchor per-prime for p ∈ {3, 5, 7} via
`eq_cyclotomic_iff` and explicit divisor unfolding. Lifting to all odd
primes (S6 target) requires the general bridge identity. The local-field
uniformizer ⇒ Eisenstein theorem (for the sub-leading divisibility half)
remains the deeper gap (~200–400 lines).

## Next Action

**S6 next action**: Build the uniform cyclotomic bridge for odd primes.

### Tactic A1 (primary): The (X+1) factorization identity
Prove the general identity
  `(cyclotomic (2 * p) ℤ) * (X + 1) = X^p + 1`
for odd prime p ≥ 3. Derivation:
1. `prod_cyclotomic_eq_X_pow_sub_one` at n = 2p gives
   `Φ_1 · Φ_2 · Φ_p · Φ_{2p} = X^{2p} - 1`.
2. Substitute `Φ_1·Φ_p = (X-1)·Φ_p = X^p - 1`
   (`cyclotomic_prime_mul_X_sub_one`).
3. Result: `(X+1) · Φ_{2p} · (X^p - 1) = (X^p-1)(X^p+1)`.
4. Cancel (X^p - 1) (monic, nonzero in ℤ[X], an ID).

This needs `Nat.divisors (2*p) = {1, 2, p, 2*p}` for p odd prime,
provable via `Nat.divisors_mul_of_coprime` (gcd(2,p)=1 for odd p)
plus `Nat.divisors_prime`. Estimated ~50–80 lines.

### Tactic A2 (fallback): Per-prime extension to {11, 13}
Add `cyclotomic_twentytwo_eq`, `cyclotomic_twentysix_eq` and the
matching eval-at-(-1) and r_p-bridge lemmas. The `ring`-proofs would
involve degree-22 and degree-26 polynomial identities; performance is
the only risk. Lower mathematical interest than A1 but lower formal risk.

### Tactic B (further followup): Lift trace fingerprint
After the norm bridge lands, attack `r_subLeadingCoeff_eq_neg_p`
uniformly using `Polynomial.coeff_natDegree_sub_one_of_monic` plus the
cyclotomic-sum identity `Σ primitive 2p-th roots = 1` (or Möbius value
μ(2p) = -μ(p) = 1 for p prime odd).

### Followup: Discharge the HARD half (sub-leading divisibility)
Sub-leading-coefficient divisibility for *all* indices `0 ≤ k < (p-1)/2`
(not just the two extreme endpoints). Requires the ramification
calculation or the local-field uniformizer theorem.

## Attempt Counts

- Total attempts: 5 (S1 OBSERVE, S2 ACT Level-2, S3 ACT norm-Vieta, S4 ACT trace-Vieta, S5 ACT cyclotomic anchor)
- Current approach attempts: 4 (Level-2 + S3 norm + S4 trace + S5 cyclotomic anchor)
- Approaches tried:
  - S1: cyclotomic ramification, surveyed only.
  - S2: per-prime explicit verification + uniform statement (sorry on general case).
  - S3: p = 3 boundary case + `r_constantCoeff_eq_signed_p` sign pattern (norm-Vieta).
  - S4: `r_subLeadingCoeff_eq_neg_p` + `r_3_traceCoeff` (trace-Vieta).
  - S5: cyclotomic anchor Φ_{2p}(-1) = p for p ∈ {3, 5, 7} (per-prime) + bridge to `r p` constant.

## Key Files

- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean` — **extended in S5** (617 lines, +147 vs S4).
  Parametric `r : ℕ → ℤ[X]` covers p ∈ {3, 5, 7, 11, 13}.
  Eisenstein verification for all five primes. Irreducibility for p ∈ {11, 13}.
  Two structural Vieta lemmas (`r_constantCoeff_eq_signed_p` for the norm,
  `r_subLeadingCoeff_eq_neg_p` + `r_3_traceCoeff` for the trace).
  **S5**: cyclotomic anchor Φ_{2p}(-1) = p for p ∈ {3, 5, 7} via explicit
  `cyclotomic_{6,10,14}_eq` + `cyclotomic_{6,10,14}_eval_neg_one`, plus
  bridge `r_{3,5,7}_constantCoeff_eq_cyclotomic` to gallery's `r p`.
  General conjecture sorry (unchanged).
- `src/data/proofs/angle-trisection-cos-20-gal-oq-01-oq-03/` — **refreshed in S5**.
  Gallery entry: meta.json (status: axiomatized, sorries: 1, lineCount 617, theoremCount 44,
  13 sections), annotations.json, index.ts.
- `proofs/Proofs/AngleTrisectionCos20Gal.lean` — cos(20°) case, p=3 via cos(π/9); Eisenstein at 3.
- `proofs/Proofs/AngleTrisectionCos20GalOQ01.lean` — cos(π/7); Eisenstein at 7.
- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ01.lean` — unified cos(20°) ⊕ cos(π/7) for p ∈ {3, 7}.
- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ02.lean` — cos(π/5); Eisenstein at 5.
