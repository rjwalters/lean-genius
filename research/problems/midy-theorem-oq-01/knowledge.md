# Knowledge Base: midy-theorem-oq-01

Midy's theorem: complementary halves of repeating decimals.

---

## Problem Understanding

For a prime `p` coprime to the base `b` (e.g. `p ≠ 2, 5` in base 10), the decimal
`1/p` is purely periodic with period `d = ord_p(b)` (multiplicative order of `b`
mod `p`). The repeating block (repetend) is the integer `N = (b^d − 1)/p`.

**Midy's theorem** (E. Midy, 1836): if the period `d = 2k` is *even*, then splitting
the `2k`-digit repetend into two `k`-digit halves `N₁` (high) and `N₂` (low) gives
`N₁ + N₂ = b^k − 1` (a block of `k` nines in base 10).

Example: `1/7 = 0.\overline{142857}`, period `6 = 2·3`; `142 + 857 = 999 = 10³ − 1`.

---

## Insights

- **The theorem decomposes into two independent facts.**
  1. *Arithmetic kernel* (no number theory): if `N = (bᵏ − 1)·m` with `1 ≤ m ≤ bᵏ`,
     then `N / bᵏ = m − 1` and `N % bᵏ = bᵏ − m`, so the halves sum to `bᵏ − 1`.
     Proof: `N = (bᵏ − m) + (m − 1)·bᵏ`, a valid remainder + multiple of `bᵏ`.
  2. *Number theory*: even period `2k` ⟺ `ord_p(b) = 2k` ⟹ `bᵏ ≡ −1 (mod p)`
     ⟹ `p ∣ bᵏ + 1`. Then `b^{2k} − 1 = (bᵏ−1)(bᵏ+1) = (bᵏ−1)·p·m`, so
     `N = (b^{2k}−1)/p = (bᵏ−1)·m` exactly, with `m = (bᵏ+1)/p ∈ [1, bᵏ]`.

- **`bᵏ ≡ −1` is the crux.** Since `ord_p(b) = 2k`, `(bᵏ)² = b^{2k} ≡ 1` but
  `bᵏ ≢ 1` (order does not divide `k`). In the field `ZMod p`, the only square
  roots of 1 are `±1`, so `bᵏ ≡ −1`. This is a clean field-theoretic argument
  (`(xᵏ − 1)(xᵏ + 1) = 0` ⟹ `xᵏ = ±1`; rule out `+1` via `orderOf_dvd_of_pow_eq_one`).

- **`m ∈ [1, bᵏ]` is automatic** from `p·m = bᵏ + 1` and `p ≥ 2`: `m ≥ 1` (else
  `p·m = 0`), and `2m ≤ p·m = bᵏ + 1 ≤ 2bᵏ` gives `m ≤ bᵏ`.

---

## Session 2026-06-16 (Session 1) — FRESH, build-verified

**Mode**: FRESH. **Outcome**: completed (0 sorries, 0 axioms).

Formalized the full chain in `proofs/Proofs/MidyTheorem.lean`:
- `midy_kernel` — pure-Nat halves identity (`zify`/`ring` + `Nat.add_mul_div/mod_self`).
- `pow_half_orderOf_eq_neg_one` — field lemma: `orderOf x = 2k ⟹ xᵏ = −1`.
- `period_even_dvd` — `orderOf (b : ZMod p) = 2k ⟹ p ∣ bᵏ + 1`.
- `midy_theorem` — top result: halves of `(b^{2k}−1)/p` sum to `bᵏ − 1`.
- Worked example `1/7` (`p=7, b=10, k=3`) discharged by `decide`.

### Next Steps / Follow-ups
- Converse / "if-and-only-if": odd period gives the analogous Midy-for-thirds when
  `d = 3k` (the three blocks sum to a multiple of `bᵏ − 1`). Possible OQ sibling.
- Tie `orderOf (b : ZMod p)` to the actual decimal-expansion digit sequence to make
  the "period" interpretation fully explicit (currently captured via `p ∣ bᵏ+1`).
