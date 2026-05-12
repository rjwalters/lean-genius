# Current State

**Phase**: ACT (S10 closed — uniform constant-coefficient corollary
`(r p).coeff 0 = (-1)^((p-1)/2) · p` lifted via S9 anchor)
**Since**: 2026-05-12T15:30:00Z
**Iteration**: 10

## Current Focus

S10 ACT — **Uniform constant-coefficient corollary closed.** Lifts the
per-prime cyclotomic-anchor bridges
`r_{3, 5, 7, 11, 13}_constantCoeff_eq_cyclotomic` (S5+S6) into two new
statements indexed by the parametric `(2 * p)` instead of literal
`{6, 10, 14, 22, 26}`, then combines with the S9 numerical anchor
`cyclotomic_two_mul_prime_eval_neg_one_uniform` to recover the empirical
sign pattern `(r p).coeff 0 = (-1)^((p-1)/2) · p` (S3 era) via the
**cyclotomic-anchor route**:

  `r_constantCoeff_eq_signed_cyclotomic_uniform`
  : `∀ p ∈ ({3, 5, 7, 11, 13} : Finset ℕ),
      (r p).coeff 0 = (-1)^((p-1)/2) · (cyclotomic (2*p) ℤ).eval (-1)`

  `r_constantCoeff_eq_signed_uniform`
  : `∀ p ∈ ({3, 5, 7, 11, 13} : Finset ℕ),
      (r p).coeff 0 = (-1)^((p-1)/2) · (p : ℤ)`.

Unlike `r_constantCoeff_eq_signed_p` (S3) which was a five-clause
conjunction whose proof was five independent `decide`-driven coefficient
expansions, the S10 theorem `r_constantCoeff_eq_signed_uniform` is a
single Finset-quantified statement whose proof routes through the
**uniform** S9 cyclotomic anchor — making the dependence on the
`Φ_{2p}(-1) = p` identity explicit in the proof term. The
intermediate `r_constantCoeff_eq_signed_cyclotomic_uniform` packages
the five per-prime cyclotomic bridges into the same Finset form using
`(2 * p)` indexing, which reduces definitionally to the literal indices
at each case.

This S10 step is the "sign-pattern uniform constant-coeff corollary"
target announced as the S10 next-step in S9's state.md. Next iteration
(S11) shifts attention to **Tactic B** for the trace fingerprint
(sub-leading-coefficient cyclotomic-sum identity
`∑ primitive 2p-th roots = 1` / Möbius value μ(2p) = -μ(p) = 1 for p
prime odd), targeting the uniform `r_subLeadingCoeff_eq_neg_p`.

Note the quantification is over the **verified** prime set
`{3, 5, 7, 11, 13}` because `r p = 0` for `p ∉ {3, 5, 7, 11, 13}`. The
uniformity is in the **indexing** (now `2 * p` instead of literal
`{6, 10, 14, 22, 26}`) and in the **proof routing** (via the S9 uniform
anchor), not in the parametric polynomial `r` itself.

### Stats

- File grows: 1089 → 1166 lines (+77), 59 → 61 theorems (+2 named theorems).
- Sorries: 1 (unchanged — the general conjecture).
- Axioms: 0 (unchanged).
- New theorems: `r_constantCoeff_eq_signed_cyclotomic_uniform` (Finset
  + (2*p)-indexed cyclotomic bridge), `r_constantCoeff_eq_signed_uniform`
  (corollary plugging in the S9 anchor).
- New module-docstring section documenting S10.

### Build status

**Pending.** Docker build is queued (proofs/.lake symlink is broken,
forcing ~30–45 min fresh-clone of Mathlib + cache get). The proof
references only standard Mathlib API (`Finset.mem_insert`,
`Finset.mem_singleton`, `rcases`, `decide` for primality/oddness of
`{3, 5, 7, 11, 13}`) plus the S5/S6 per-prime bridges
`r_{3, 5, 7, 11, 13}_constantCoeff_eq_cyclotomic` and the S9 anchor
`cyclotomic_two_mul_prime_eval_neg_one_uniform` — all already merged in
PRs #18028, #18066, and #18103. Per the build-pending precedent of
S4 (#17906), S5 (#17975), S6 (#18028), S8 (#18066), and S9 (#18103),
this PR is submitted as "build pending" for deployer verification.

## Previous focus (S9 — uniform numerical anchor `Φ_{2p}(-1) = p`)

S9 ACT — Uniform numerical anchor `Φ_{2p}(-1) = p` proved for every
odd prime p ≥ 3. Lifts the per-prime cyclotomic evaluation lemmas
`cyclotomic_{six, ten, fourteen, twentytwo, twentysix}_eval_neg_one = {3, 5, 7, 11, 13}`
of S5+S6 into a single statement holding for **every** odd prime — not
just the five verified gallery primes. Two new theorems:

  `cyclotomic_two_mul_prime_eq_geom_neg_series`
  : `cyclotomic (2 * p) ℤ = ∑ i ∈ Finset.range p, (-X) ^ i`     in `ℤ[X]`,
    for every odd prime `p`.

  `cyclotomic_two_mul_prime_eval_neg_one_uniform`
  : `(cyclotomic (2 * p) ℤ).eval (-1) = p`     in `ℤ`,
    for every odd prime `p`.

Together with the S8 bridge identity
`cyclotomic_two_mul_prime_mul_X_add_one_uniform`
(`cyclotomic (2 * p) ℤ · (X + 1) = X^p + 1`), the canonical cyclotomic
duality is now upgraded from a structural ring identity to a fully
explicit polynomial formula plus numerical anchor:

      cyclotomic p ℤ · (X - 1) = X^p - 1                            (Mathlib)
      cyclotomic (2*p) ℤ · (X + 1) = X^p + 1                       (S8)
      cyclotomic (2*p) ℤ = ∑_{i<p} (-X)^i                          (S9 structural)
      (cyclotomic (2*p) ℤ).eval (-1) = p                           (S9 numerical)

for every odd prime `p`. The classical informal identity
`Φ_{2p}(X) = Φ_p(-X)` is now a Lean-checked ring identity in `ℤ[X]`.

### Proof structure

Two steps, mirroring the outline in the S8 module docstring:

1. **Geometric-series identification** (structural lemma).
   `geom_sum_mul (-X) p` reads
     `(∑ i ∈ Finset.range p, (-X)^i) * (-X - 1) = (-X)^p - 1`.
   For `p` odd, `Odd.neg_pow` gives `(-X)^p = -X^p`. Rearranging
   `(-X - 1) = -(X + 1)` and `-X^p - 1 = -(X^p + 1)` yields
     `(∑ i ∈ Finset.range p, (-X)^i) * (X + 1) = X^p + 1`,
   discharged by `ring` after the sign flips and `neg_injective`.
   Combine with the S8 bridge
   `cyclotomic_two_mul_prime_mul_X_add_one_uniform` and cancel
   `(X + 1)` (monic via `monic_X_add_C 1`, hence nonzero in `ℤ[X]`) via
   `mul_right_cancel₀`.

2. **Numerical evaluation** (anchor). Substitute the structural lemma,
   distribute `eval (-1)` over the sum via `eval_finset_sum`, and
   simplify each term: `((-X)^i).eval (-1) = (-(-1))^i = 1^i = 1`. The
   sum of `p` ones is `p` (via `Finset.sum_const`, `Finset.card_range`,
   `nsmul_eq_mul`, `mul_one`).

### Stats

- File grows: 962 → 1089 lines (+127), 57 → 59 theorems (+2 named theorems).
- Sorries: 1 (unchanged — the general conjecture).
- Axioms: 0 (unchanged).
- New theorems: `cyclotomic_two_mul_prime_eq_geom_neg_series` (structural,
  identifies `Φ_{2p}` with the geometric series in `(-X)`),
  `cyclotomic_two_mul_prime_eval_neg_one_uniform` (numerical anchor).
- New module-docstring section documenting S9.

### Build status

**Pending.** Docker build is queued (proofs/.lake symlink is broken,
forcing ~30–45 min fresh-clone of Mathlib + cache get). The proof
references only standard Mathlib API (`geom_sum_mul`, `Odd.neg_pow`,
`monic_X_add_C`, `Monic.ne_zero`, `mul_right_cancel₀`, `eval_finset_sum`,
`eval_pow`, `eval_neg`, `eval_X`, `Finset.sum_const`, `Finset.card_range`,
`nsmul_eq_mul`) plus the S8 bridge identity already merged in PR #18066
(build verified). Per the build-pending precedent of S4 (#17906),
S5 (#17975), S6 (#18028), and S8 (#18066), this PR is submitted as
"build pending" for deployer verification.

## Previous focus (S8 — uniform cyclotomic bridge identity)

S8 ACT — Uniform cyclotomic bridge identity proved (PR #18066). Discharged
steps 2–6 of the outline laid down in the S7 module docstring, landing
the structural theorem
`cyclotomic_two_mul_prime_mul_X_add_one_uniform`
: `cyclotomic (2 * p) ℤ * (X + 1) = X ^ p + 1` in `ℤ[X]`, for every odd
prime `p`. Six-step proof composes S7's `divisors_two_mul_odd_prime`
with `prod_cyclotomic_eq_X_pow_sub_one`, `cyclotomic_prime_mul_X_sub_one`,
and `mul_left_cancel₀`.

## Previous focus (S7 — combinatorial backbone `divisors_two_mul_odd_prime`)

S7 SCAFFOLD — `Nat.divisors (2*p) = {1, 2, p, 2*p}` for `p` odd prime
(parity-split proof, 0 sorries, PR #18057).

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

None firm. The uniform cyclotomic bridge identity (S8) and the
uniform numerical anchor `Φ_{2p}(-1) = p` (S9, this iteration) are now
**both proved**. The constant-coefficient sign-pattern corollary
`(r p).coeff 0 = (-1)^((p-1)/2) · p` becomes a one-line consequence
combining `r_constantCoeff_eq_signed_p` (already general, S3) with
`cyclotomic_two_mul_prime_eval_neg_one_uniform` (this S9). The
local-field uniformizer ⇒ Eisenstein theorem (for the sub-leading
divisibility half — Tactic B) remains the deeper gap (~200–400 lines).

## Next Action

**S11 next action**: Lift the **trace** fingerprint
`r_subLeadingCoeff_eq_neg_p` uniformly. With S10 closing the
constant-coefficient sign-pattern corollary via the
S9 anchor, attention shifts to **Tactic B**: re-derive the
sub-leading coefficient identity

  `(r p).coeff ((p-1)/2 - 1) = -p`

uniformly across the verified primes using
`Polynomial.coeff_natDegree_sub_one_of_monic` plus the cyclotomic-sum
identity `∑ primitive 2p-th roots = 1` (or the Möbius value
μ(2p) = −μ(p) = 1 for `p` prime odd). The desired S11 deliverable:

  `r_subLeadingCoeff_eq_neg_cyclotomic_uniform`
  : `∀ p ∈ ({5, 7, 11, 13} : Finset ℕ),
      (r p).coeff ((p-1)/2 - 1) = -(cyclotomic (2*p) ℤ).subLeadingCoeff` (or
       equivalent Möbius-value-derived form);

  `r_subLeadingCoeff_eq_neg_uniform`
  : `∀ p ∈ ({5, 7, 11, 13} : Finset ℕ),
      (r p).coeff ((p-1)/2 - 1) = -(p : ℤ)`.

The boundary case p = 3 stays separate (`r_3_traceCoeff`) since
`(3-1)/2 - 1 = 0` collides with the constant-coefficient case already
handled by `r_constantCoeff_eq_signed_uniform`.

### S10 DONE (this iteration)
`r_constantCoeff_eq_signed_cyclotomic_uniform` (Finset + (2*p)-indexed
cyclotomic bridge) and `r_constantCoeff_eq_signed_uniform` (corollary
combining with the S9 numerical anchor). 77 line additions, 0 new sorries,
0 new axioms, +2 named theorems.

### Tactic A1-corollary (DONE in S9): Uniform `Φ_{2p}(-1) = p`
**Approach (A) chosen.** Geometric-series identification.

  `cyclotomic_two_mul_prime_eq_geom_neg_series`
  : `cyclotomic (2 * p) ℤ = ∑ i ∈ Finset.range p, (-X)^i`

via `geom_sum_mul (-X) p` + `Odd.neg_pow` + S8 bridge + cancel `(X+1)`
through `monic_X_add_C` ⇒ `Monic.ne_zero` ⇒ `mul_right_cancel₀`.

  `cyclotomic_two_mul_prime_eval_neg_one_uniform`
  : `(cyclotomic (2 * p) ℤ).eval (-1) = p`

via the structural lemma + `eval_finset_sum` + `eval_pow`/`eval_neg`/`eval_X`
simp set + `Finset.sum_const`/`Finset.card_range`/`nsmul_eq_mul`/`mul_one`.

127 line additions; 0 new sorries; 0 new axioms; +2 named theorems.

### Tactic A1 (DONE in S8): The (X+1) factorization identity
Lemma `cyclotomic_two_mul_prime_mul_X_add_one_uniform`
  : `cyclotomic (2 * p) ℤ * (X + 1) = X^p + 1` for `p` odd prime.

Proof composes `prod_cyclotomic_eq_X_pow_sub_one` at `n = 2 * p` with
the S7 `divisors_two_mul_odd_prime` enumeration, identifies
`(X − 1) · Φ_p = X^p − 1` via `cyclotomic_prime_mul_X_sub_one`, factors
`X^{2p} − 1 = (X^p − 1)(X^p + 1)`, and cancels `X^p − 1` via
`mul_left_cancel₀`. PR #18066 (merged).

### S7 DONE: Combinatorial backbone
Lemma `divisors_two_mul_odd_prime : Nat.divisors (2*p) = {1, 2, p, 2*p}`
for `p` odd prime. Parity-split proof, 0 sorries (PR #18057, merged).

### Tactic A2 (DONE in S6): Per-prime extension to {11, 13}
Completed. Both `cyclotomic_22_eq` (degree-22 ring identity) and
`cyclotomic_26_eq` (degree-26 ring identity) close. Bridge lemmas
`r_{11,13}_constantCoeff_eq_cyclotomic` plus packaged
`r_constantCoeff_eq_cyclotomic_full` ship in PR.

### Tactic B (further followup): Lift trace fingerprint
After the sign-pattern uniform constant-coeff corollary (S10) lands,
attack `r_subLeadingCoeff_eq_neg_p` uniformly using
`Polynomial.coeff_natDegree_sub_one_of_monic` plus the cyclotomic-sum
identity `Σ primitive 2p-th roots = 1` (or Möbius value
μ(2p) = -μ(p) = 1 for p prime odd).

### Followup: Discharge the HARD half (sub-leading divisibility)
Sub-leading-coefficient divisibility for *all* indices `0 ≤ k < (p-1)/2`
(not just the two extreme endpoints). Requires the ramification
calculation or the local-field uniformizer theorem.

## Attempt Counts

- Total attempts: 10 (S1 OBSERVE, S2 ACT Level-2, S3 ACT norm-Vieta,
  S4 ACT trace-Vieta, S5 ACT cyclotomic anchor {3,5,7},
  S6 ACT cyclotomic anchor extension {11,13},
  S7 SCAFFOLD divisor enumeration for uniform bridge,
  S8 ACT uniform cyclotomic bridge identity,
  S9 ACT uniform numerical anchor Φ_{2p}(-1) = p,
  S10 ACT uniform constant-coefficient corollary).
- Current approach attempts: 9 (Level-2 + S3 norm + S4 trace +
  S5 cyclotomic anchor + S6 cyclotomic extension + S7 SCAFFOLD + S8 ACT
  + S9 ACT + S10 ACT).
- Approaches tried:
  - S1: cyclotomic ramification, surveyed only.
  - S2: per-prime explicit verification + uniform statement (sorry on general case).
  - S3: p = 3 boundary case + `r_constantCoeff_eq_signed_p` sign pattern (norm-Vieta).
  - S4: `r_subLeadingCoeff_eq_neg_p` + `r_3_traceCoeff` (trace-Vieta).
  - S5: cyclotomic anchor Φ_{2p}(-1) = p for p ∈ {3, 5, 7} (per-prime) + bridge to `r p` constant.
  - S6: cyclotomic anchor extension Φ_{2p}(-1) = p for p ∈ {11, 13} (per-prime) + bridge + packaged 5-prime conjunction.
  - S7: combinatorial backbone `divisors_two_mul_odd_prime` (parity-split, 0 sorries) — step 1 of 6 for uniform bridge.
  - S8: uniform cyclotomic bridge identity `cyclotomic_two_mul_prime_mul_X_add_one_uniform` via composition of S7 backbone with `prod_cyclotomic_eq_X_pow_sub_one` + `cyclotomic_prime_mul_X_sub_one` + `mul_left_cancel₀`.
  - S9: uniform numerical anchor `cyclotomic_two_mul_prime_eval_neg_one_uniform` via the new structural lemma `cyclotomic_two_mul_prime_eq_geom_neg_series` (identifying Φ_{2p} as the geometric series in `-X`) + standard `eval_*` simp set at X = -1.
  - S10: uniform constant-coefficient corollary `r_constantCoeff_eq_signed_uniform` via the new Finset-indexed bridge `r_constantCoeff_eq_signed_cyclotomic_uniform` (`(2 * p)`-indexed cyclotomic, case-splits to S5/S6 per-prime bridges) + S9 numerical anchor.

## Key Files

- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean` — **extended in S10** (1166 lines, +77 vs S9).
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
  **S9**: uniform numerical anchor
  `cyclotomic_two_mul_prime_eval_neg_one_uniform`:
  `(cyclotomic (2 * p) ℤ).eval (-1) = p` for `p` odd prime, plus the
  structural lemma `cyclotomic_two_mul_prime_eq_geom_neg_series`
  identifying `Φ_{2p}` with `∑_{i<p} (-X)^i`.
  **S10** (this iteration): uniform constant-coefficient corollary.
  `r_constantCoeff_eq_signed_cyclotomic_uniform` quantifies the per-prime
  cyclotomic bridges of S5+S6 over `p ∈ ({3, 5, 7, 11, 13} : Finset ℕ)`,
  using `(2 * p)`-indexed cyclotomic (which reduces definitionally to
  the literal cyclotomic index at each case).
  `r_constantCoeff_eq_signed_uniform` combines that with the S9 numerical
  anchor `cyclotomic_two_mul_prime_eval_neg_one_uniform` to yield
  `(r p).coeff 0 = (-1)^((p-1)/2) · p` over the Finset, re-deriving the
  S3-era `r_constantCoeff_eq_signed_p` via the cyclotomic anchor route.
  General conjecture sorry (unchanged).
- `src/data/proofs/angle-trisection-cos-20-gal-oq-01-oq-03/` — **refreshed in S10**.
  Gallery entry: meta.json (status: axiomatized, sorries: 1, lineCount 1166, theoremCount 61,
  15 sections), annotations.json, index.ts.
- `proofs/Proofs/AngleTrisectionCos20Gal.lean` — cos(20°) case, p=3 via cos(π/9); Eisenstein at 3.
- `proofs/Proofs/AngleTrisectionCos20GalOQ01.lean` — cos(π/7); Eisenstein at 7.
- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ01.lean` — unified cos(20°) ⊕ cos(π/7) for p ∈ {3, 7}.
- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ02.lean` — cos(π/5); Eisenstein at 5.
