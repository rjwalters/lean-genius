# Current State

**Phase**: ACT (S7 SCAFFOLD landed — divisor enumeration for uniform bridge)
**Since**: 2026-05-12T10:55:00Z
**Iteration**: 7

## Current Focus

S7 SCAFFOLD — Combinatorial backbone (step 1 of 6) for the uniform
cyclotomic bridge identity `cyclotomic (2 * p) ℤ * (X + 1) = X ^ p + 1`
(odd prime `p`). Lands `divisors_two_mul_odd_prime`:

  `Nat.divisors (2 * p) = {1, 2, p, 2 * p}` for `p` odd prime, 0 sorries.

Proof: `ext k`, parity-split on `k`. Even branch: `k = 2 * m`, cancel `2`
via `Nat.eq_of_mul_eq_mul_left` to extract `m ∣ p`, then primality
(`Nat.Prime.eq_one_or_self_of_dvd`) gives `m ∈ {1, p}` hence `k ∈ {2, 2*p}`.
Odd branch: `Nat.Coprime k 2` (from `¬ 2 ∣ k`), then
`Nat.Coprime.dvd_of_dvd_mul_left` extracts `k ∣ p`, primality closes.

This enables the next session (S8) to apply
`Polynomial.prod_cyclotomic_eq_X_pow_sub_one` at `n = 2 * p` and substitute
the divisor enumeration, completing steps 2–6 of the uniform bridge:

  3. `Φ_1 = X - 1`, `Φ_2 = X + 1` ⇒ product becomes
     `(X-1)(X+1) Φ_p Φ_{2p} = X^{2p} - 1`.
  4. `prod_cyclotomic_eq_X_pow_sub_one` at `n = p` ⇒
     `(X-1) Φ_p = X^p - 1`.
  5. Algebraic identity `X^{2p} - 1 = (X^p-1)(X^p+1)`.
  6. Cancel `(X-1) Φ_p` (monic, nonzero in ℤ[X], an ID).

File grows: 750 → 835 lines (+85), 55 → 56 theorems (+1 lemma).
Sorries: 1 (unchanged — the general conjecture).
Axioms: 0 (unchanged).

## Previous focus (S6 — `cyclotomic_{22,26}_eq` + 5-prime bridge)

S6 ACT — Cyclotomic anchor extension via Tactic A2 (per-prime). S5 covered
p ∈ {3, 5, 7}; S6 extends the same template to p ∈ {11, 13}, giving the
full verified gallery set coverage for the cyclotomic side of the norm
fingerprint:

- **Explicit Φ_p forms** for the two remaining primes via `eq_cyclotomic_iff`
  (`properDivisors p = {1}`, `cyclotomic_one`, `ring`):
  - `cyclotomic_11_eq`: Φ_11 = X^10 + X^9 + ⋯ + X + 1
  - `cyclotomic_13_eq`: Φ_13 = X^12 + X^11 + ⋯ + X + 1

- **Explicit Φ_{2p} forms** via `eq_cyclotomic_iff` with
  `properDivisors (2p) = {1, 2, p}`, `cyclotomic_one`/`cyclotomic_two`,
  and the step-(1) Φ_p lemma; closed by `ring`:
  - `cyclotomic_22_eq`: Φ_22 = X^10 - X^9 + X^8 - X^7 + ⋯ - X + 1
  - `cyclotomic_26_eq`: Φ_26 = X^12 - X^11 + X^10 - X^9 + ⋯ - X + 1

- **Numerical anchors** Φ_{2p}(-1) = p for p ∈ {11, 13}:
  - `cyclotomic_twentytwo_eval_neg_one`: Φ_22(-1) = 11
  - `cyclotomic_twentysix_eval_neg_one`: Φ_26(-1) = 13

- **Bridge to gallery's r_p** for p ∈ {11, 13}:
  - `r_11_constantCoeff_eq_cyclotomic`: `(r 11).coeff 0 = (-1)^5 · Φ_22(-1)`
  - `r_13_constantCoeff_eq_cyclotomic`: `(r 13).coeff 0 = (-1)^6 · Φ_26(-1)`
  Each follows by rewriting with the cyclotomic eval and the matching
  `r_constantCoeff_eq_signed_p.2.2.2.{1,2}` projection.

- **Packaged 5-prime bridge** `r_constantCoeff_eq_cyclotomic_full`
  upgrades the S5 `r_constantCoeff_eq_cyclotomic_small` (3-prime
  conjunction) to the full p ∈ {3, 5, 7, 11, 13} set. The S5 version
  remains in the file for compatibility.

- File grows: 617 → 750 lines (+133), 44 → 55 theorems (+11),
  1 definition (unchanged). Sorries: 1 (unchanged — the general conjecture).
  Axioms: 0 (unchanged).

## Previous focus (S5 — `r_{3,5,7}_constantCoeff_eq_cyclotomic`)

S5 ACT closed the cyclotomic-side norm fingerprint for the three smallest
primes p ∈ {3, 5, 7} via explicit Φ_{6,10,14} forms plus the bridge
`r_constantCoeff_eq_cyclotomic_small`. S6 now extends the bridge to
p ∈ {11, 13}, matching the per-prime range of `r_constantCoeff_eq_signed_p`
(which already covered all five primes).

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
S5+S6 jointly verified the cyclotomic anchor per-prime for the full
gallery set p ∈ {3, 5, 7, 11, 13} via `eq_cyclotomic_iff` and explicit
divisor unfolding. Lifting to all odd primes (S7 target) still requires
the general bridge identity (Tactic A1 below). The local-field
uniformizer ⇒ Eisenstein theorem (for the sub-leading divisibility half)
remains the deeper gap (~200–400 lines).

## Next Action

**S8 next action**: Finish the uniform cyclotomic bridge using
`divisors_two_mul_odd_prime` (S7) as the combinatorial input.

### Tactic A1 (primary): The (X+1) factorization identity — S8
Prove the general identity
  `(cyclotomic (2 * p) ℤ) * (X + 1) = X^p + 1`
for odd prime p ≥ 3. Derivation now uses the S7 helper directly:
1. `Polynomial.prod_cyclotomic_eq_X_pow_sub_one` at n = 2p gives
   `∏ d ∈ Nat.divisors (2*p), Φ_d = X^{2p} - 1`.
2. Rewrite using `divisors_two_mul_odd_prime` (S7) to get the four-term
   product `Φ_1 · Φ_2 · Φ_p · Φ_{2p} = X^{2p} - 1`.
3. Substitute `Φ_1 = X - 1`, `Φ_2 = X + 1`, then
   `(X-1) · Φ_p = X^p - 1` (via `prod_cyclotomic_eq_X_pow_sub_one` at
   n = p, using `Nat.divisors_prime hp = {1, p}`).
4. Result: `(X+1) · Φ_{2p} · (X^p - 1) = X^{2p} - 1 = (X^p - 1)(X^p + 1)`.
5. Cancel `(X^p - 1)` (monic, nonzero in ℤ[X], an ID).

Estimated ~50 lines on top of the S7 SCAFFOLD.

### S7 DONE: Combinatorial backbone
Lemma `divisors_two_mul_odd_prime : Nat.divisors (2*p) = {1, 2, p, 2*p}`
for `p` odd prime. Parity-split proof, 0 sorries.

### Tactic A2 (DONE in S6): Per-prime extension to {11, 13}
Completed. Both `cyclotomic_22_eq` (degree-22 ring identity) and
`cyclotomic_26_eq` (degree-26 ring identity) close. Bridge lemmas
`r_{11,13}_constantCoeff_eq_cyclotomic` plus packaged
`r_constantCoeff_eq_cyclotomic_full` ship in PR.

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

- Total attempts: 7 (S1 OBSERVE, S2 ACT Level-2, S3 ACT norm-Vieta,
  S4 ACT trace-Vieta, S5 ACT cyclotomic anchor {3,5,7},
  S6 ACT cyclotomic anchor extension {11,13},
  S7 SCAFFOLD divisor enumeration for uniform bridge).
- Current approach attempts: 6 (Level-2 + S3 norm + S4 trace +
  S5 cyclotomic anchor + S6 cyclotomic extension + S7 SCAFFOLD).
- Approaches tried:
  - S1: cyclotomic ramification, surveyed only.
  - S2: per-prime explicit verification + uniform statement (sorry on general case).
  - S3: p = 3 boundary case + `r_constantCoeff_eq_signed_p` sign pattern (norm-Vieta).
  - S4: `r_subLeadingCoeff_eq_neg_p` + `r_3_traceCoeff` (trace-Vieta).
  - S5: cyclotomic anchor Φ_{2p}(-1) = p for p ∈ {3, 5, 7} (per-prime) + bridge to `r p` constant.
  - S6: cyclotomic anchor extension Φ_{2p}(-1) = p for p ∈ {11, 13} (per-prime) + bridge + packaged 5-prime conjunction.
  - S7: combinatorial backbone `divisors_two_mul_odd_prime` (parity-split, 0 sorries) — step 1 of 6 for uniform bridge.

## Key Files

- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean` — **extended in S7** (835 lines, +85 vs S6).
  Parametric `r : ℕ → ℤ[X]` covers p ∈ {3, 5, 7, 11, 13}.
  Eisenstein verification for all five primes. Irreducibility for p ∈ {11, 13}.
  Two structural Vieta lemmas (`r_constantCoeff_eq_signed_p` for the norm,
  `r_subLeadingCoeff_eq_neg_p` + `r_3_traceCoeff` for the trace).
  **S5**: cyclotomic anchor Φ_{2p}(-1) = p for p ∈ {3, 5, 7} via explicit
  `cyclotomic_{6,10,14}_eq` + `cyclotomic_{6,10,14}_eval_neg_one`, plus
  bridge `r_{3,5,7}_constantCoeff_eq_cyclotomic` to gallery's `r p`.
  **S6**: cyclotomic anchor extension Φ_{2p}(-1) = p for p ∈ {11, 13}
  via explicit `cyclotomic_{11,13,22,26}_eq` + `cyclotomic_{twentytwo,twentysix}_eval_neg_one`,
  plus bridge `r_{11,13}_constantCoeff_eq_cyclotomic` and packaged
  5-prime conjunction `r_constantCoeff_eq_cyclotomic_full`.
  **S7**: combinatorial backbone `divisors_two_mul_odd_prime`
  (`Nat.divisors (2*p) = {1, 2, p, 2*p}` for `p` odd prime; 0 sorries)
  — step 1 of 6 for the uniform bridge identity. Detailed proof outline
  in module docstring for the S7 section.
  General conjecture sorry (unchanged).
- `src/data/proofs/angle-trisection-cos-20-gal-oq-01-oq-03/` — **refreshed in S6**.
  Gallery entry: meta.json (status: axiomatized, sorries: 1, lineCount 750, theoremCount 55,
  14 sections), annotations.json, index.ts.
- `proofs/Proofs/AngleTrisectionCos20Gal.lean` — cos(20°) case, p=3 via cos(π/9); Eisenstein at 3.
- `proofs/Proofs/AngleTrisectionCos20GalOQ01.lean` — cos(π/7); Eisenstein at 7.
- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ01.lean` — unified cos(20°) ⊕ cos(π/7) for p ∈ {3, 7}.
- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ02.lean` — cos(π/5); Eisenstein at 5.
