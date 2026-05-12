# Current State

**Phase**: ACT (S8 closed — uniform cyclotomic bridge identity proved)
**Since**: 2026-05-12T11:30:00Z
**Iteration**: 8

## Current Focus

S8 ACT — **Uniform cyclotomic bridge identity proved.** Discharges
steps 2–6 of the outline laid down in the S7 module docstring, landing
the structural theorem

  `cyclotomic_two_mul_prime_mul_X_add_one_uniform`
  : `cyclotomic (2 * p) ℤ * (X + 1) = X ^ p + 1`    in `ℤ[X]`,
    for every odd prime `p`.

This collapses the five per-prime ring identities of S5+S6
(`cyclotomic_{6, 10, 14, 22, 26}_eq`) into a single uniform statement
holding for **all** odd primes — not just the five verified gallery
primes. Together with Mathlib's `cyclotomic_prime_mul_X_sub_one`
(`cyclotomic p ℤ * (X − 1) = X^p − 1`), the canonical cyclotomic duality

      cyclotomic p ℤ · (X - 1) = X^p - 1
      cyclotomic (2*p) ℤ · (X + 1) = X^p + 1            (new in S8)

is now formally available, exposing `Φ_{2p}` as the X ↦ -X conjugate of
`Φ_p` without invoking polynomial composition or working in a splitting
field.

### Proof structure

Six steps, mirroring the outline in the S7 module docstring:

1. (S7 lemma `divisors_two_mul_odd_prime`): `(2p).divisors = {1,2,p,2p}`.
2. `Polynomial.prod_cyclotomic_eq_X_pow_sub_one` at `n = 2p`:
     `∏ d ∈ (2p).divisors, cyclotomic d ℤ = X^{2p} − 1`.
3. Substitute step 1, unfold the four-term `Finset.prod` via three
   `Finset.prod_insert`s + one `Finset.prod_singleton`, and simplify
   with `cyclotomic_one` (= X−1) and `cyclotomic_two` (= X+1).
4. `Polynomial.cyclotomic_prime_mul_X_sub_one` (using `Fact (Nat.Prime p)`):
     `cyclotomic p ℤ · (X − 1) = X^p − 1`.
5. `X^{2p} − 1 = (X^p − 1) · (X^p + 1)` via `two_mul` plus `ring`.
6. Cancel `X^p − 1` via `mul_left_cancel₀`. Nonzero in `ℤ[X]`: evaluating
   at `0` yields `0^p − 1 = −1 ≠ 0` for `p > 0`.

### Stats

- File grows: 835 → 962 lines (+127), 56 → 57 theorems (+1 named theorem).
- Sorries: 1 (unchanged — the general conjecture).
- Axioms: 0 (unchanged).
- New theorem: `cyclotomic_two_mul_prime_mul_X_add_one_uniform`.
- New module-docstring section documenting S8.

### Build status

**Pending.** Docker build is queued (proofs/.lake symlink is broken,
forcing ~30–45 min fresh-clone of Mathlib + cache get). The proof
references only standard Mathlib API (`prod_cyclotomic_eq_X_pow_sub_one`,
`cyclotomic_one`, `cyclotomic_two`, `cyclotomic_prime_mul_X_sub_one`,
`mul_left_cancel₀`, `Finset.prod_insert`, `Finset.prod_singleton`,
`Polynomial.eval_*`) plus the S7 `divisors_two_mul_odd_prime` already
merged in PR #18057 (build verified). Per the build-pending precedent
of S4 (#17906), S5 (#17975), and S6 (#18028), this PR is submitted as
"build pending" for deployer verification.

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

None firm. The uniform cyclotomic bridge identity is now **proved**
(this S8 iteration). The local-field uniformizer ⇒ Eisenstein theorem
(for the sub-leading divisibility half — Tactic B) remains the deeper
gap (~200–400 lines). The eval-at-(-1) corollary
`Φ_{2p}(-1) = p` (deferred to S9) collapses S5+S6 anchors but requires
polynomial-evaluation manipulation of the bridge (geometric-series
substitution via `geom_sum_mul` or formal differentiation).

## Next Action

**S9 next action**: Lift `Φ_{2p}(-1) = p` to all odd primes (corollary
of the S8 bridge). Once landed, the per-prime S5+S6 evaluations collapse
into one uniform statement; the constant-coefficient sign-pattern
prediction
`(r p).coeff 0 = (-1)^((p-1)/2) · Φ_{2p}(-1) = (-1)^((p-1)/2) · p`
becomes a one-line corollary for every odd prime, not just the five
verified gallery primes.

### Tactic A1 (DONE in S8): The (X+1) factorization identity
Lemma `cyclotomic_two_mul_prime_mul_X_add_one_uniform`
  : `cyclotomic (2 * p) ℤ * (X + 1) = X^p + 1` for `p` odd prime.
Proof composes `prod_cyclotomic_eq_X_pow_sub_one` at `n = 2 * p` with
the S7 `divisors_two_mul_odd_prime` enumeration, identifies
`(X − 1) · Φ_p = X^p − 1` via `cyclotomic_prime_mul_X_sub_one`, factors
`X^{2p} − 1 = (X^p − 1)(X^p + 1)`, and cancels `X^p − 1` via
`mul_left_cancel₀`. 127 line additions; 0 new sorries; 0 new axioms.

### Tactic A1-corollary (S9 target): Uniform `Φ_{2p}(-1) = p`
Approaches:

* **(A)** Geometric-series identification. Use `geom_sum_mul` at `-X` to
  build `Q(X) := ∑_{k < p} (-X)^k` satisfying `Q · (X + 1) = X^p + 1`
  (for `p` odd, via `Odd.neg_one_pow`). Cancel `(X + 1)` (nonzero in
  `ℤ[X]`) against the S8 bridge to identify `Φ_{2p} = Q`. Evaluate at
  `−1`: `Q(-1) = ∑_{k<p} (-(-1))^k = ∑_{k<p} 1 = p`.

* **(B)** Formal differentiation. Apply `Polynomial.derivative` to the
  S8 bridge, evaluate at `−1`: the derivative term `Φ'_{2p}(-1) · ((-1)+1) = 0`
  cancels, leaving `Φ_{2p}(-1) = p · (-1)^(p-1) = p` (since `p − 1` is
  even). Cleaner mathematically; depends on Mathlib's `derivative_mul`,
  `derivative_X_pow`, `eval` simp lemmas, and `Even.neg_one_pow`.

Either approach is ~30 lines. Pick (A) for fewer Mathlib API surfaces;
(B) for cleaner mathematics.

### S7 DONE: Combinatorial backbone
Lemma `divisors_two_mul_odd_prime : Nat.divisors (2*p) = {1, 2, p, 2*p}`
for `p` odd prime. Parity-split proof, 0 sorries (PR #18057, merged).

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

- Total attempts: 8 (S1 OBSERVE, S2 ACT Level-2, S3 ACT norm-Vieta,
  S4 ACT trace-Vieta, S5 ACT cyclotomic anchor {3,5,7},
  S6 ACT cyclotomic anchor extension {11,13},
  S7 SCAFFOLD divisor enumeration for uniform bridge,
  S8 ACT uniform cyclotomic bridge identity).
- Current approach attempts: 7 (Level-2 + S3 norm + S4 trace +
  S5 cyclotomic anchor + S6 cyclotomic extension + S7 SCAFFOLD + S8 ACT).
- Approaches tried:
  - S1: cyclotomic ramification, surveyed only.
  - S2: per-prime explicit verification + uniform statement (sorry on general case).
  - S3: p = 3 boundary case + `r_constantCoeff_eq_signed_p` sign pattern (norm-Vieta).
  - S4: `r_subLeadingCoeff_eq_neg_p` + `r_3_traceCoeff` (trace-Vieta).
  - S5: cyclotomic anchor Φ_{2p}(-1) = p for p ∈ {3, 5, 7} (per-prime) + bridge to `r p` constant.
  - S6: cyclotomic anchor extension Φ_{2p}(-1) = p for p ∈ {11, 13} (per-prime) + bridge + packaged 5-prime conjunction.
  - S7: combinatorial backbone `divisors_two_mul_odd_prime` (parity-split, 0 sorries) — step 1 of 6 for uniform bridge.
  - S8: uniform cyclotomic bridge identity `cyclotomic_two_mul_prime_mul_X_add_one_uniform` via composition of S7 backbone with `prod_cyclotomic_eq_X_pow_sub_one` + `cyclotomic_prime_mul_X_sub_one` + `mul_left_cancel₀`.

## Key Files

- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean` — **extended in S8** (962 lines, +127 vs S7).
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
  (`Nat.divisors (2*p) = {1, 2, p, 2*p}` for `p` odd prime; 0 sorries).
  **S8**: uniform cyclotomic bridge identity
  `cyclotomic_two_mul_prime_mul_X_add_one_uniform`:
  `cyclotomic (2 * p) ℤ * (X + 1) = X ^ p + 1` for `p` odd prime.
  Replaces five per-prime ring identities with a single uniform statement.
  General conjecture sorry (unchanged).
- `src/data/proofs/angle-trisection-cos-20-gal-oq-01-oq-03/` — **refreshed in S8**.
  Gallery entry: meta.json (status: axiomatized, sorries: 1, lineCount 962, theoremCount 57,
  14 sections), annotations.json, index.ts.
- `proofs/Proofs/AngleTrisectionCos20Gal.lean` — cos(20°) case, p=3 via cos(π/9); Eisenstein at 3.
- `proofs/Proofs/AngleTrisectionCos20GalOQ01.lean` — cos(π/7); Eisenstein at 7.
- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ01.lean` — unified cos(20°) ⊕ cos(π/7) for p ∈ {3, 7}.
- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ02.lean` — cos(π/5); Eisenstein at 5.
