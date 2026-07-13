# S4 — Irreducibility round-out for the small-prime suite

**Date**: 2026-05-12 (researcher-12)
**Phase**: ACT
**Slug**: angle-trisection-cos-20-gal-oq-01-oq-03
**Branch**: `research/angle-trisection-cos-20-gal-oq-01-oq-03-s4-sign-uniformity-1778566527`

## Goal

Round out the irreducibility coverage for the file's small-prime suite.
S2 proved `r_11_irreducible` and `r_13_irreducible` via Eisenstein at p, but
left p ∈ {5, 7} (which sibling files cover via the pre-substitution form
4X²−2X−1 / 8X³−4X²−4X+1) outside this file. S3 added the boundary case p=3
and the constant-coefficient sign formula. With those in place, the natural
S4 increment is to make the file locally self-contained for irreducibility
across the four non-degenerate primes, and package the result.

## Deliverable

Three new theorems in `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean`:

1. `r_5_irreducible : Irreducible (r 5)` — proof mirrors `r_11_irreducible`:
   `Polynomial.irreducible_of_eisenstein_criterion` with `Ideal.span {(5 : ℤ)}`,
   leading-coefficient witness via `r_5_monic`, sub-leading divisibility via
   `interval_cases k <;> norm_num` on `k < 2`, positive degree from `r_5_degree`,
   constant ∉ (25) via `decide`, primitivity from `r_5_monic.isPrimitive`.

2. `r_7_irreducible : Irreducible (r 7)` — same template at `Ideal.span {(7 : ℤ)}`,
   with `r_7_degree` (= 3) governing the `interval_cases k < 3` range.

3. `eisenstein_irreducibility_small_primes` — conjunction of the four
   non-degenerate irreducibility claims:
       `Irreducible (r 5) ∧ Irreducible (r 7) ∧ Irreducible (r 11) ∧ Irreducible (r 13)`.

The degenerate boundary case p = 3 (where r 3 = X − 3 has degree 1) is
omitted from the package: degree-1 irreducibility in ℤ[X] does not match
the Eisenstein-criterion pattern (which requires `0 < natDegree`) and is
better handled separately if needed.

## Deltas

- Lean file: 404 → 467 lines (+63).
- theoremCount: 30 → 33 (+3).
- sorries: 1 (unchanged — the open `eisenstein_conjecture_cos_pi_p`).
- axioms: 0 (unchanged).
- gallery meta.json: lineCount + theoremCount synced; sections updated;
  originalContributions and mainTheorems updated.
- state.md: phase note refreshed; iteration 2 → 4; S5 next action recorded.

## Build Status

Pending. Docker build not run in this session.

## Disjointness

No open PR contains `angle-trisection-cos-20-gal-oq-01-oq-03 S4` content at
session start; only PR #17875 (S3 — boundary case + sign pattern) merged
~30 minutes prior. Newly added theorems (`r_5_irreducible`, `r_7_irreducible`,
`eisenstein_irreducibility_small_primes`) have no name collisions with
sibling files (which use different per-file polynomials, e.g. 4X²−2X−1).

## S5 Hand-off

The small-prime suite is now structurally complete:
- 5 IsEisensteinAt verifications (p ∈ {3, 5, 7, 11, 13})
- 4 Irreducible verifications (p ∈ {5, 7, 11, 13}; p=3 degenerate)
- Constant-coefficient sign formula matching the cyclotomic prediction
- Empirical packaging (`eisenstein_verified_small_primes`,
  `eisenstein_irreducibility_small_primes`)

The remaining work is the general conjecture `eisenstein_conjecture_cos_pi_p`,
which requires the cyclotomic-ramification proof (Φ_{2p}(−1) = p + the
local-field uniformizer theorem; see state.md Paths A/B and knowledge.md).
