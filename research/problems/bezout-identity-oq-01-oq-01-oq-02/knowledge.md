# Binary GCD Extended to Integers

**Problem ID**: bezout-identity-oq-01-oq-01-oq-02
**Parent**: bezout-identity-oq-01-oq-01 (Stein's binary GCD for ℕ)

## Problem Statement

Can Stein's binary GCD algorithm, which computes `gcd(a, b)` for natural numbers
using only subtraction, halving, and parity tests, be extended to integers?

## Session 2026-05-07 (Session 1) — Complete Proof

**Mode**: FRESH
**Outcome**: completed — full proof written, Docker build confirmed

### What I Did

1. Claimed problem; surveyed parent proof `BezoutIdentityOQ01OQ01`
2. Defined `intBinaryGcd (a b : ℤ) : ℤ := ↑(binaryGcd a.natAbs b.natAbs)` — reduces to ℕ algorithm via `Int.natAbs`
3. Proved 10 theorems + 5 computational examples, 0 sorries, 0 axioms:
   - `intBinaryGcd_eq_gcd`: equals `Int.gcd` (Mathlib's integer GCD)
   - `intBinaryGcd_dvd_left/right`: divisibility in ℤ via `▸ Int.gcd_dvd_left/right`
   - `intBinaryGcd_comm`: symmetry (from `binaryGcd_comm`)
   - `intBinaryGcd_neg_left/right`: sign invariance (natAbs strips signs)
   - `intBinaryGcd_zero_left/right`: boundary cases (= |b| and |a|)
   - `bezout_via_intBinaryGcd`: ∃ u v, u*a + v*b = intBinaryGcd a b
   - `dvd_intBinaryGcd`: any common divisor divides intBinaryGcd (via Bézout)
4. Fixed `AmgmInequalityOQ03.lean` trailing docstring bug (needed for build to succeed)

### Key Findings

- The extension is trivial mathematically: `Int.gcd a b = Nat.gcd a.natAbs b.natAbs` definitionally, so `intBinaryGcd` just reduces to the ℕ algorithm.
- Lean 4.26 API issues:
  - `Int.gcd_dvd_left` requires explicit arguments and uses `↑(a.gcd b)` dot notation — use `▸` for the dvd proofs
  - `linear_combination` for Bézout produces residual `binaryGcd a.natAbs = binaryGcd |a|.natAbs` goals — use explicit `rw [heq, hbez]; ring` instead
  - `dvd_intBinaryGcd` better proved via Bézout (d ∣ a ∧ d ∣ b → d ∣ u*a+v*b) than via `Int.dvd_gcd` (API changed)
- Build: 3059 jobs, 0 errors — confirmed via Docker build

### Files Created

- `proofs/Proofs/BezoutIdentityOQ01OQ01OQ02.lean` (146 lines)
- `src/data/proofs/bezout-identity-oq-01-oq-01-oq-02/meta.json`
- `research/problems/bezout-identity-oq-01-oq-01-oq-02/knowledge.md` (this file)
- Also fixed `proofs/Proofs/AmgmInequalityOQ03.lean` (trailing `/--` docstring bug)

### Phase: COMPLETED
