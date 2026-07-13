# Knowledge: erdos-727-incomplete-01

## Overview

Completion problem for Erdős #727. The sorry in `main_implies_egrs` is now **PROVED**.

## Gallery Proof Summary

- Gallery: `erdos-727`
- Lean: `proofs/Proofs/Erdos727Problem.lean`
- Sorries: 0 (was 1), Axioms: multiple (open problem axiomatized)

## Session 2026-04-13 — PROVED

**Mode**: REVISIT
**Outcome**: `main_implies_egrs` sorry eliminated

### What I Did

Replaced the sorry in `main_implies_egrs` with a case split on `k = 0` vs `k ≥ 1`:

**k = 0 case**: `n! * (n+1)! = (n+1) * n!²` (via `Nat.factorial_succ` + `ring`),
then `(2n)! = centralBinom n * n!²` (via `factorial_2n_eq`), and
`(n+1) ∣ centralBinom n` (via `catalan_divisibility n`, proved using `Nat.succ_mul_catalan_eq`).

**k ≥ 1 case**: Clean chain via `Nat.factorial_dvd_factorial` (gives `(n+1)! ∣ (n+k)!`),
then `Nat.mul_dvd_mul_left` (gives `(n+k)!*(n+1)! ∣ (n+k)!²`), then `dvd_trans`.

### Key Lemmas Used
- `catalan_divisibility n : (n+1) ∣ centralBinom n` (already proved in file, line 129)
- `factorial_2n_eq n : (2*n)! = centralBinom n * n!²` (proved in file, line 42)
- `Nat.factorial_dvd_factorial : m ≤ n → m! ∣ n!`
- `Nat.mul_dvd_mul_left`

### Files Modified
- `proofs/Proofs/Erdos727Problem.lean` lines 183-200: replaced sorry with rcases proof

## Key References

- Gallery: `src/data/proofs/erdos-727/`
