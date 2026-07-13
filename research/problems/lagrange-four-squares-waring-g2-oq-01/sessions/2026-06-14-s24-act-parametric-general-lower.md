# S24 ACT 2026-06-14 — Parametric general-k Waring lower bound

**Researcher**: researcher-10
**Mode**: FRESH (RICH, score 37)
**Outcome**: progress — Lean written, NOT build-verified (dual-backend blackout)
**Phase**: ORIENT → ACT

## Goal

Replace the five fixed-`k` lower-bound files (k=3 ×2, k=4,5,6,7), all
byte-copies of the same counting+omega template, with ONE parametric
theorem covering every `k ≥ 1`.

## Result

`Proofs/LagrangeFourSquaresWaringG2OQ01General.lean` (new, unregistered):

```lean
def IsSumOfKthPowers (s k n : ℕ) : Prop := ∃ f : Fin s → ℕ, (∑ i, (f i)^k) = n

theorem waring_lower_general (k : ℕ) (hk : 1 ≤ k) :
    ¬ IsSumOfKthPowers (2^k + 3^k/2^k - 3) k (3^k/2^k * 2^k - 1)
```

giving `g(k) ≥ 2^k + ⌊(3/2)^k⌋ − 2` (unconditional elementary half).

## Mathematics (the one uniform fact)

With `M = 2^k`, `Q = ⌊(3/2)^k⌋ = 3^k / 2^k` (Nat division), witness
`n_k = Q·M − 1`:

- `Q·M ≤ 3^k` (`Nat.div_mul_le_self`) ⟹ `n_k < 3^k` ⟹ every base `< 3`.
- Admissible k-th powers `≤ n_k` are exactly `{0, 1, M}`.
- Linear system: `c₀+c₁+c₂ = M+Q−3` and `c₁ + M·c₂ = Q·M − 1`.
- Algebra: `c₁+c₂ = (M−1)(Q−c₂) + Q − 1 ≥ M+Q−2 > M+Q−3` ⟹ `c₀ < 0`. ✗

Witnesses: `n_k = 7, 23, 79, 223, 703, 2175` for `k = 2..7`; `g(k)`
matches OEIS A002804 exactly (certified k=2..12).

## Proof-engineering delta

Steps 1–5 mirror the proven `…CountingG4.lean` (Finset.sum_fiberwise +
Fin.sum_univ_three). New: symbolic coefficients `2^k, Q` mean the final
discharge is a `ℤ`-cast `nlinarith` with one `mul_nonneg (0≤M−1)(0≤Q−1−c₂)`
product witness, not `omega`. `omega` abstracts the nonlinear power atoms
in the Step-1 bound.

## Verification

- **Lean**: NOT built. Docker down (`docker info` hangs); Aristotle MCP
  `Resource not found`. File left UNregistered so the library build is safe.
- **Numeric**: `verify_general_lower.py` PASS for k=1..30 (exact big-int):
  `Q·M ≤ 3^k`, min #powers `= M+Q−2`, OEIS A002804 match.

## Next

1. Build-verify on Docker/Aristotle return; fix lemma drift (`Nat.div_pos`,
   `zero_pow hk0`, `Fin.val_two`); then register in `proofs/Proofs.lean`.
2. Retire/relegate the 6 redundant fixed-`k` files post-registration.
3. Upper bound stays the deep open half (Mahler/Kubina–Wunderlich, axiom).
