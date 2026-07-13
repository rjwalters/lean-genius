# Knowledge: basel-problem-oq-01-oq-01-oq-02-oq-03

Hanson's bound `lcm(1,...,n) ≤ 3^n` (1972), Apéry's ζ(3) integer-squeeze constant.

## Key Definitions / Lemmas (in `Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean`)

| Name | Type | Source |
|------|------|--------|
| `lcmRange` | def | Iteration 1 |
| `lcmRange_zero/one/pos` | basic | Iteration 1 |
| `dvd_lcmRange` | k ∈ {1..n} → k ∣ lcmRange n | Iteration 1 |
| `pow_dvd_lcmRange` | 0 < b → b^k ≤ n → b^k ∣ lcmRange n | Iteration 3 (#16772) |
| `prime_pow_dvd_lcmRange` | p prime → 1 ≤ n → p^(Nat.log p n) ∣ lcmRange n | **Iteration 5** (this PR) |
| `lcmRange_succ` | recursion | Iteration 2 (#16704) |
| `lcmRange_dvd_lcmRange_of_le` | divisibility monotonicity | Iteration 2 |
| `lcmRange_monotone` | numerical monotonicity | Iteration 2 |
| `lcmRange_dvd_factorial`, `lcmRange_le_factorial`, `lcmRange_le_self_pow` | trivial bounds | Iteration 1 |
| `hanson_n1..n20`, `lcmRange_5/10/15/20_eq` | numerical verification | Iteration 1 |
| `axiom hanson_bound` | the OPEN target | Iteration 1 |
| `hanson_strictly_stronger_than_factorial` | 3^n < n^n for n ≥ 4 | Iteration 1 |

## Iteration 5 (2026-05-08, researcher-1) — `prime_pow_dvd_lcmRange`

**Theorem statement**:

```lean
theorem prime_pow_dvd_lcmRange {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) :
    p ^ Nat.log p n ∣ lcmRange n :=
  pow_dvd_lcmRange hp.pos (Nat.pow_log_le_self p (by omega))
```

**Why this is the right next lemma after `pow_dvd_lcmRange`** (Iteration 3):

`pow_dvd_lcmRange` is generic over the base `b`; the *prime-power* case
is the one Hanson-style proofs actually need, because Chebyshev's
decomposition

  `lcm(1,...,n) = ∏_{p prime, p ≤ n} p ^ ⌊log_p n⌋`

requires precisely: (a) every maximal prime-power `p^⌊log_p n⌋` divides
the LHS — proved by this lemma; (b) no larger prime power can divide
the LHS — follows from unique factorization.

Direction (a) is now a **library entry point**, available as
`prime_pow_dvd_lcmRange hp hn` for any downstream proof that needs to
extract a prime-power factor from `lcmRange n`.

**New imports introduced**: `Mathlib.Data.Nat.Log` (for `Nat.log`,
`Nat.pow_log_le_self`), `Mathlib.Data.Nat.Prime.Basic` (for `Nat.Prime.pos`).

**Proof technique**: literal three-call composition.
`hp.pos` discharges `0 < p`; `Nat.pow_log_le_self p (n.ne')`
(massaged from `1 ≤ n` via `omega`) discharges `p ^ Nat.log p n ≤ n`;
`pow_dvd_lcmRange` does the rest. No new mathematics; just connects
two existing pieces.

**Mathlib precedent for the technique**: the same
`Nat.pow_log_le_self` + `b ^ Nat.log b n ≤ n` pattern appears in
`Erdos123Problem.lean:166`, `BaselProblemOQ01OQ01OQ02Aristotle.lean:82`,
`ChebyshevBounds.lean:315`, etc. — 17+ files in this repository use it.
The lemma name `prime_pow_dvd_lcmRange` is consistent with Mathlib
naming for divisibility lemmas (`Nat.Prime.dvd_lcm`, etc.).

## Next Iteration (Iteration 6 candidate): `lcmRange_eq_prod_prime_powers`

The full Chebyshev decomposition:

```lean
theorem lcmRange_eq_prod_prime_powers (n : ℕ) :
    lcmRange n = ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime,
                  p ^ Nat.log p n := sorry
```

- **Forward `RHS ∣ LHS`**: use `prime_pow_dvd_lcmRange` for each prime
  factor + pairwise-coprimality of distinct primes
  (`Nat.Coprime.prime_pow_pow`) + `Finset.prod_dvd` for coprime factors.

- **Reverse `LHS ∣ RHS`**: every `k ∈ {1,...,n}` factors as
  `∏_p p^(k.factorization p)` with each exponent `≤ Nat.log p n`. Use
  Mathlib's `Nat.factorization` framework + `Nat.eq_pow_of_factorization_eq`.

Once proven, the bound `lcmRange n ≤ ∏_{p ≤ n} n = n^{π(n)}` is
immediate from `Finset.prod_le_prod` (each factor ≤ `n` since
`p ^ Nat.log p n ≤ n`). This is a strictly weaker bound than Hanson's
3^n but is the first non-trivial named LCM-bound theorem in Lean.

## Long-Term Blockers (unchanged)

1. **Mathlib Beta-integral over ℚ**: `(n+1)·C(n,k)·∫₀¹ x^k(1-x)^(n-k) dx = 1`
   not yet available in usable rational-denominator form.
2. **Mathlib `primorial → lcm` bridge**: missing. NB: the naive form
   `lcm(1..n) ≤ n · primorial(n)` is FALSE (counterexample at n=9);
   correct bridge uses Chebyshev's prime-power decomposition.
3. **Mathlib LCM-specific bounds**: none — this OQ is contributing
   them.

## Cross-References

- Parent: `basel-problem-oq-01-oq-01-oq-02` (Apéry ζ(3) irrationality
  scaffold; uses `lcm_hanson_bound` axiom that this OQ targets).
- Sibling: `basel-problem-oq-01-oq-01-oq-02-oq-02` (separate axiom in
  the same parent's chain).
- Mathlib gap: `Mathlib.NumberTheory.Primorial.primorial_le_4_pow`
  exists but the `primorial → lcmRange` bridge does not.

## References

- Hanson, *Canad. Math. Bull.* 15 (1972) 33–37.
- Nair, *Amer. Math. Monthly* 89 (1982) 126–129 (alternative central-binomial-coefficient route).
- Apéry, *Astérisque* 61 (1979) (the canonical application of `lcm ≤ 3^n`).
- OEIS A003418: `lcm(1,...,n)`.
