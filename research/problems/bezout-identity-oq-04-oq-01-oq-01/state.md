# Current State

**Phase**: COMPLETED
**Since**: 2026-05-06T06:28:26Z
**Iteration**: 1

## Current Focus

`snf_1x2_invariant_factor_pid` proved in
`proofs/Proofs/BezoutIdentityOQ04OQ01OQ01.lean`: for any
`CommRing R` with `IsDomain R` and `GCDMonoid R`, the 1×2 invariant
factor of a Smith Normal Form decomposition is associated to
`gcd(a, b)`. This generalizes the ℤ-specific
`BezoutIdentityOQ04OQ01` to arbitrary GCD-domains. File: 206 lines,
2 axioms, 0 sorries, 6 theorems.

## Active Approach

None — work is in maintenance mode.

## Built Items

- `snf_1x2_invariant_factor_pid` — the main theorem; both directions of
  the associated-to-gcd argument generalized from ℤ to `GCDMonoid R`.
- Direction `d ∣ gcd(a, b)`: from `A = U·D·V`, extract
  `a = u · d · V 0 0` and `b = u · d · V 0 1`, then `dvd_gcd`.
- Direction `gcd(a, b) ∣ d`: `det V = ±1` gives
  `a · V 1 1 − b · V 1 0 = ±u·d`, so `gcd(a, b) ∣ uval · d`, then
  `dvd_iff` (via `IsUnit uval`) yields `gcd(a, b) ∣ d`.
- Entry-extraction technique: `congr_fun (congr_fun hsnf 0) j` +
  `Matrix.mul_apply` + `Fin.sum_univ_succ`.
- `linear_combination` replaces ℤ-specific `linarith` for the
  `CommRing` setting.

## Axioms (2)

Both inherited from the parent SNF-existence axiomatization
(`lines 158-170 in BezoutIdentityOQ04OQ01OQ01.lean`):

- `snf_pid_exists` — every matrix over a PID admits a Smith Normal
  Form decomposition. Routine to provide from
  `Mathlib.LinearAlgebra.FreeModule.PID.SmithNormalForm`; flagged in
  `nextSteps` as OQ-01.
- `snf_pid_solvability` — the linear system `A x = b` is solvable iff
  the SNF invariant factors satisfy the standard divisibility +
  zero-row conditions. Flagged as OQ-02 (structure theorem
  consequence).

## Blockers

None for the main theorem. Axiom elimination from Mathlib is the
natural next direction but is a separate OQ.

## Next Action

Gallery entry already correct: `status: "axiomatized"`,
`badge: "axiom"`, `axiomCount: 2`, `sorries: 0`, `lineCount: 206`,
`theoremCount: 6`. Top-level `phase` in
`src/data/research/problems/bezout-identity-oq-04-oq-01-oq-01.json`
still reads `"OBSERVE"` while `currentState.phase` reads `"COMPLETED"`
— a candidate JSON drift fix, but out of scope for this state.md
sync.

Future work threads: OQ-01 (Mathlib `FreeModule.PID` to discharge
`snf_pid_exists`), OQ-02 (structure theorem for f.g. modules over
PIDs).

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (entry-extraction via `congr_fun` +
  `Matrix.mul_apply`, ±1 case split via `unit.inv_val`)
