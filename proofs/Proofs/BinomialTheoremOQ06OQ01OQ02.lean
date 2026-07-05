import Mathlib

/-
# The Alternating Squared-Binomial Sum Vanishes for Odd `n` — Involution Proof

## Open Question OQ-06-OQ-01-OQ-02 (from `binomial-theorem-oq-06-oq-01`)

The parent entry `binomial-theorem-oq-06-oq-01` proves

  `∑_{k=0}^{n} (-1)^k C(n,k)^2 = 0`  for odd `n`

as a *corollary of the signed Vandermonde convolution*, i.e. by extracting the
coefficient `[x^n] (1 - X^2)^n` in `ℤ[X]`.  That route is powerful (it also
gives the even closed form `(-1)^{n/2} C(n, n/2)`) but it is heavy machinery for
the odd-`n` vanishing, which is really a **pairing phenomenon**.

This entry gives the *second, elementary proof*: the map `k ↦ n - k` is a
**fixed-point-free, sign-reversing involution** on `{0, …, n}` when `n` is odd.
Since `C(n, n-k) = C(n, k)` and, for odd `n`, `(-1)^{n-k} = -(-1)^k`, each term
is sent to its own negative, so the whole sum equals its own negative and hence
vanishes.  No polynomials, generating functions, or Vandermonde identity are
used — only `Finset.sum_range_reflect`, `Nat.choose_symm`, and parity of `-1`
powers.

## Results

* `neg_one_pow_sub`             — for odd `n` and `k ≤ n`, `(-1)^{n-k} = -(-1)^k` over `ℤ`;
* `alternating_choose_sq_odd_reflect` — `∑_k (-1)^k C(n,k)^2 = 0` for odd `n`,
  proved purely by reflection `k ↦ n - k`.

## Comparison of the two proofs

| Route | Engine | Also yields even case? | Machinery |
|-------|--------|------------------------|-----------|
| Parent (`…-oq-06-oq-01`) | `[x^n] (1-X^2)^n` in `ℤ[X]` | yes, `(-1)^{n/2} C(n,n/2)` | `Polynomial.coeff_mul`, binomial expansion |
| This entry | involution `k ↦ n-k` on `range (n+1)` | no (odd only) | `Finset.sum_range_reflect`, parity |

The reflection proof is strictly shorter and more transparent for the odd case,
but is genuinely specific to it: the involution has a fixed point `k = n/2` when
`n` is even, and there the pairing argument breaks down (the fixed term
`(-1)^{n/2} C(n, n/2)^2` survives), which is exactly why the even sum is
generally nonzero.

## References

- Sign-reversing involutions / the "reflection" evaluation of alternating sums.
- Parent `binomial-theorem-oq-06-oq-01` (generating-function proof, closed form).

## Axioms: 0 | Sorries: 0
-/

namespace BinomialTheoremOQ06OQ01OQ02

open Finset

/-! ## The parity sign identity -/

/-- For odd `n` and `k ≤ n`, `(-1)^{n-k} = -(-1)^k` over `ℤ`.

This is the "sign-reversing" heart of the involution: reflecting the exponent
across an odd total flips the sign, because `(n-k)` and `k` then have opposite
parities. -/
theorem neg_one_pow_sub (n k : ℕ) (hn : Odd n) (hk : k ≤ n) :
    (-1 : ℤ) ^ (n - k) = -((-1) ^ k) := by
  -- `(-1)^k` is a square root of `1`.
  have hb : ((-1 : ℤ) ^ k) * ((-1) ^ k) = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨k, rfl⟩
  -- The two exponents sum to the odd number `n`, so the powers multiply to `-1`.
  have hprod : (-1 : ℤ) ^ (n - k) * (-1) ^ k = -1 := by
    rw [← pow_add, Nat.sub_add_cancel hk, hn.neg_one_pow]
  calc (-1 : ℤ) ^ (n - k)
      = (-1 : ℤ) ^ (n - k) * ((-1) ^ k * (-1) ^ k) := by rw [hb, mul_one]
    _ = ((-1 : ℤ) ^ (n - k) * (-1) ^ k) * (-1) ^ k := by ring
    _ = (-1) * (-1) ^ k := by rw [hprod]
    _ = -((-1) ^ k) := by ring

/-! ## The vanishing theorem via reflection -/

/-- **Odd alternating squared-binomial sum, involution proof.**
For odd `n`, `∑_{k=0}^{n} (-1)^k C(n,k)^2 = 0`, proved by the fixed-point-free
sign-reversing involution `k ↦ n - k` on `range (n+1)`. -/
theorem alternating_choose_sq_odd_reflect (n : ℕ) (hn : Odd n) :
    ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (n.choose k : ℤ) ^ 2 = 0 := by
  -- Each reflected term is the negative of the original term.
  have key : ∀ k ∈ range (n + 1),
      (-1 : ℤ) ^ (n - k) * (n.choose (n - k) : ℤ) ^ 2
        = (-1) * ((-1 : ℤ) ^ k * (n.choose k : ℤ) ^ 2) := by
    intro k hk
    rw [mem_range, Nat.lt_succ_iff] at hk
    rw [Nat.choose_symm hk, neg_one_pow_sub n k hn hk]
    ring
  -- Reflect the sum, apply `key` termwise, pull out the sign: `S = -S`.
  have hSS :
      (∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (n.choose k : ℤ) ^ 2)
        = -(∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (n.choose k : ℤ) ^ 2) := by
    calc (∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (n.choose k : ℤ) ^ 2)
        = ∑ k ∈ range (n + 1), (-1 : ℤ) ^ (n - k) * (n.choose (n - k) : ℤ) ^ 2 := by
          rw [← Finset.sum_range_reflect
            (fun k => (-1 : ℤ) ^ k * (n.choose k : ℤ) ^ 2) (n + 1)]
          apply Finset.sum_congr rfl
          intro j _
          simp only [Nat.add_sub_cancel]
      _ = ∑ k ∈ range (n + 1), (-1) * ((-1 : ℤ) ^ k * (n.choose k : ℤ) ^ 2) :=
          Finset.sum_congr rfl key
      _ = (-1) * ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (n.choose k : ℤ) ^ 2 := by
          rw [← Finset.mul_sum]
      _ = -(∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (n.choose k : ℤ) ^ 2) := by
          rw [neg_one_mul]
  linarith [hSS]

/-! ## Numerical sanity checks -/

/-- `∑_{k=0}^{3} (-1)^k C(3,k)^2 = 1 - 9 + 9 - 1 = 0`. -/
theorem check_three :
    ∑ k ∈ range 4, (-1 : ℤ) ^ k * ((3).choose k : ℤ) ^ 2 = 0 := by decide

/-- `∑_{k=0}^{5} (-1)^k C(5,k)^2 = 1 - 25 + 100 - 100 + 25 - 1 = 0`. -/
theorem check_five :
    ∑ k ∈ range 6, (-1 : ℤ) ^ k * ((5).choose k : ℤ) ^ 2 = 0 := by decide

#print axioms alternating_choose_sq_odd_reflect

end BinomialTheoremOQ06OQ01OQ02
