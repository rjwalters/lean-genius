# Current State

**Phase**: ACT (norm + trace Vieta fingerprints established; general proof still open)
**Since**: 2026-05-12T06:30:00Z
**Iteration**: 4

## Current Focus

S4 ACT-prep — Trace-pattern structural lemma on top of S3:
- Added structural lemma `r_subLeadingCoeff_eq_neg_p` for p ∈ {5, 7, 11, 13}:
  `(r p).coeff ((p-1)/2 - 1) = -p`. This is the trace half of Vieta,
  encoding `Tr_{ℚ(θ_p)/ℚ}(2 + 2cos(π/p)) = p`.
- Added boundary lemma `r_3_traceCoeff : (r 3).coeff 0 = -3` to record
  the p = 3 case explicitly (degree 1 collapses the sub-leading index
  onto the constant term, where it already overlaps with
  `r_constantCoeff_eq_signed_p`).
- Together with the S3 lemma `r_constantCoeff_eq_signed_p` (norm half),
  this fixes BOTH Vieta endpoints of `r p`:
  - Constant   = `(-1)^((p-1)/2) · p`  (norm fingerprint)
  - Sub-leading = `-p`                  (trace fingerprint)
  Any general cyclotomic-ramification proof must reproduce both.
- File grows: 404 → 470 lines, 30 → 32 theorems, 1 definition (unchanged).
- Sorries: 1 (unchanged — the general conjecture).

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

None firm. Mathlib's `Polynomial.cyclotomic` API provides the value Φ_{2p}(−1) = p
via the relation `Polynomial.cyclotomic_two_mul_odd_eq_cyclotomic_neg` (or its equivalent)
plus `Polynomial.cyclotomic_prime_eval_one`. The local-field uniformizer ⇒ Eisenstein
theorem may need to be built locally (~200–400 lines) or replaced with a direct
Newton-identity argument.

## Next Action

**S5 next action**: Lift one of the two Vieta fingerprints to all odd primes
via the Mathlib cyclotomic API. Two concrete tactics:

### Tactic A: Norm half via cyclotomic_prime_eval_one
Prove `(cyclotomic (2*p) ℤ).eval (-1) = p` for every odd prime p ≥ 3 by
combining `Polynomial.eval_one_cyclotomic_prime` with the identity
`cyclotomic (2*p) X = cyclotomic p (-X)` (the second is not yet in
Mathlib in this exact form; a clean proof goes via primitive roots and
`Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots`). Once established,
discharge `r_constantCoeff_eq_signed_p` for *all* odd primes p ≥ 3 (not
just the five enumerated ones).

### Tactic B: Trace half via cyclotomic sum identity
Use `Polynomial.coeff_natDegree_sub_one_of_monic` (or rederive via
`coeff_X_pow + coeff_C_mul`) to convert the trace condition into a sum
over primitive 2p-th roots of unity, then apply Mathlib's
`PrimitiveRoots.sum_eq_zero` and the residue at `X = 1` of `Φ_{2p}` to
extract `Tr(2 + θ_p) = p` uniformly.

**Recommend Tactic A for S5** — `eval_one_cyclotomic_prime` is already
in Mathlib and the `cyclotomic_two_mul_odd` bridge is a self-contained
lemma (~30 lines via primitive roots).

### Followup: Discharge the HARD half
Sub-leading-coefficient divisibility for *all* indices `0 ≤ k < (p-1)/2`
(not just the constant and trace endpoints). This is the genuine hard
core of the conjecture — requires showing each elementary symmetric
polynomial of the conjugates lies in `p · ℤ`, which in turn requires
the ramification calculation (or the local-field uniformizer theorem).

## Attempt Counts

- Total attempts: 4 (S1 OBSERVE, S2 ACT Level-2, S3 ACT boundary + norm lemma, S4 ACT trace lemma)
- Current approach attempts: 3 (Level-2 implementation; S3 boundary; S4 trace fingerprint)
- Approaches tried:
  - S1: cyclotomic ramification, surveyed only.
  - S2: per-prime explicit verification + uniform statement (sorry on general case).
  - S3: p = 3 boundary case + `r_constantCoeff_eq_signed_p` sign pattern (norm-Vieta).
  - S4: `r_subLeadingCoeff_eq_neg_p` + `r_3_traceCoeff` (trace-Vieta).

## Key Files

- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean` — **extended in S4** (470 lines, +66 vs S3).
  Parametric `r : ℕ → ℤ[X]` covers p ∈ {3, 5, 7, 11, 13}.
  Eisenstein verification for all five primes. Irreducibility for p ∈ {11, 13}.
  Two structural Vieta lemmas (`r_constantCoeff_eq_signed_p` for the norm,
  `r_subLeadingCoeff_eq_neg_p` + `r_3_traceCoeff` for the trace).
  General conjecture sorry.
- `src/data/proofs/angle-trisection-cos-20-gal-oq-01-oq-03/` — **new in S2, refreshed in S4**.
  Gallery entry: meta.json (status: axiomatized, sorries: 1, lineCount 470, theoremCount 32),
  annotations.json, index.ts.
- `proofs/Proofs/AngleTrisectionCos20Gal.lean` — cos(20°) case, p=3 via cos(π/9); Eisenstein at 3.
- `proofs/Proofs/AngleTrisectionCos20GalOQ01.lean` — cos(π/7); Eisenstein at 7.
- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ01.lean` — unified cos(20°) ⊕ cos(π/7) for p ∈ {3, 7}.
- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ02.lean` — cos(π/5); Eisenstein at 5.
