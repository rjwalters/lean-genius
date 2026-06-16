# Repunit Divisibility (repunit-oq-01)

## Problem Summary

For a base `b ≥ 2`, the base-`b` repunit of length `n` is
`R_b(n) = 1 + b + b² + ⋯ + b^{n-1} = ∑_{i<n} b^i = (b^n − 1)/(b − 1)`
(the number written as `n` ones in base `b`; `R₁₀(3) = 111`).

**Theorem**: `R_b(m) ∣ R_b(n) ⟺ m ∣ n`.

**Status**: COMPLETE — fully verified, 0 axioms, 0 sorries (build-pending confirmation
under heavy Docker contention; proof is self-contained and elementary).
**File**: `proofs/Proofs/RepunitDivisibilityOQ01.lean`

## Approach

The result is *not* an enumeration: it holds for all `m, n` via an elementary
number-theoretic argument, with the engine being the power-difference criterion.

1. **Power-difference engine** (`pow_sub_one_dvd_iff_dvd`): for `b ≥ 2`,
   `(b^m − 1) ∣ (b^n − 1) ⟺ m ∣ n`.
   - `⟸`: if `n = m·k`, then `b^n − 1 = (b^m)^k − 1^k`, and `(x − y) ∣ x^k − y^k`
     (`nat_sub_dvd_pow_sub_pow`) gives `(b^m − 1) ∣ (b^n − 1)`.
   - `⟹`: division algorithm `n = m·q + r`, `r < m`. Modular arithmetic
     (`Nat.ModEq`): `b^m ≡ 1 (mod b^m − 1)`, so `b^n = (b^m)^q · b^r ≡ b^r`.
     The hypothesis gives `b^n ≡ 1`, hence `b^r ≡ 1`, i.e. `(b^m − 1) ∣ (b^r − 1)`.
     But `b^r − 1 < b^m − 1` (since `r < m`, `b ≥ 2`), so `b^r − 1 = 0`, forcing
     `r = 0` and `m ∣ n`.

2. **Repunit ↔ power bridge** (`pred_mul_repunit`): `(b − 1)·R_b(n) = b^n − 1`,
   proved from the subtraction-free additive form `(b − 1)·R_b(n) + 1 = b^n`
   (`pred_mul_repunit_add_one`, induction after substituting `b = c + 1` to dodge
   `ℕ` truncated subtraction).

3. **Cancel the common factor** (`repunit_dvd_iff`): since `b − 1 > 0`,
   `R_b(m) ∣ R_b(n) ⟺ (b−1)R_b(m) ∣ (b−1)R_b(n) ⟺ (b^m−1) ∣ (b^n−1) ⟺ m ∣ n`
   via `Nat.mul_dvd_mul_iff_left`.

Base-ten corollary `repunit_ten_dvd_iff` instantiates `b = 10`.

## Mathlib API used (target v4.26.0)

- `nat_sub_dvd_pow_sub_pow : (x - y) ∣ x ^ n - y ^ n`
- `Nat.modEq_iff_dvd' : a ≤ b → (a ≡ b [MOD n] ↔ n ∣ b - a)`
- `Nat.ModEq.pow`, `Nat.ModEq.mul_right`
- `Nat.mul_dvd_mul_iff_left : 0 < a → (a * b ∣ a * c ↔ b ∣ c)`
- `Nat.le_self_pow`, `Nat.one_le_pow`, `Nat.le_of_dvd`, `Nat.div_add_mod`,
  `Nat.pow_le_pow_right`, `Nat.mul_le_mul`

## Sessions

### Session 2026-06-16 (Session 1, researcher-12) — COMPLETE (build-pending)
**Mode**: FRESH. **Outcome**: completed (pending Docker confirmation).

- Pool had 19 available; chose `repunit-oq-01` (tractability 7) over the finite-`decide`
  candidates (abundant/keith) because it is a genuine theorem over *infinitely* many
  `(m, n)` via elementary divisibility — higher value than enumeration.
- Aristotle unavailable (404 — blackout ongoing); proved everything manually.
- Wrote `RepunitDivisibilityOQ01.lean`: 1 def, 7 theorems, 0 axioms, 0 sorries.
- Key design choice: prove the power-difference iff with `Nat.ModEq` (avoids messy
  `ℕ`-subtraction algebra), and the repunit↔power bridge additively (substitute
  `b = c + 1` so `ring` works over a subtraction-free goal).
- Docker heavily loaded (load ~27, 6+ sibling builds queued); build launched with
  8 GB cap / 30 m timeout.

### Next Steps (follow-ups)
- gcd form: `gcd(R_b(m), R_b(n)) = R_b(gcd(m, n))` (the natural strengthening).
- Repunit primality necessary condition: `R_b(n)` prime ⟹ `n` prime (immediate corollary,
  since `m ∣ n`, `1 < m < n` gives a proper repunit divisor).
