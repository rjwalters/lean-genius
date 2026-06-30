import Mathlib
import Proofs.FibonacciIdentitiesOQ04OQ01

/-
# The Gibonacci Gelin–Cesàro identity

The Fibonacci **Gelin–Cesàro identity**

  `F(n−2)·F(n−1)·F(n+1)·F(n+2) − F n⁴ = −1`

was established in `Proofs/FibonacciIdentitiesOQ04OQ01.lean` (open question 3 of
oq-04) as a difference of squares: Cassini gives
`F(n−1)·F(n+1) = F n² + (−1)^|n|` and the Catalan `r = 2` instance gives
`F(n−2)·F(n+2) = F n² − (−1)^|n|`, whose product is
`(F n²)² − ((−1)^|n|)² = F n⁴ − 1`.

This entry lifts that identity to the **full two–parameter Gibonacci family**
`G a b n = a·F n + b·F(n−1)` with characteristic discriminant
`μ = a² − a·b − b²`.  The same difference-of-squares mechanism, now driven by the
Gibonacci Cassini and Gibonacci Catalan identities of the parent file, yields

  `G(n−2)·G(n−1)·G(n+1)·G(n+2) − G n⁴ = −μ²`.

The `(−1)^|n|` sign factor — which is *odd* in `n` and would obstruct a naive
generalisation — is annihilated by the difference of squares, leaving the clean
index-independent constant `−μ²`.  The result is strictly stronger than the
Fibonacci case and specialises:

* `(a, b) = (1, 0)` ⟹ `μ = 1`  ⟹ the Fibonacci identity `… = −1`;
* `(a, b) = (1, 2)` ⟹ `μ = −5` ⟹ the Lucas identity `… = −25`.

Both corollaries are recorded below.  No axioms, no `sorry`, no `native_decide`.
-/

namespace FibonacciIdentitiesOQ04OQ03

open Int FibonacciIdentitiesOQ04OQ01

/-- **Gibonacci Gelin–Cesàro identity.**  For every Gibonacci sequence
`G a b n = a·F n + b·F(n−1)` with discriminant `μ = a² − a·b − b²`,

`G(n−2)·G(n−1)·G(n+1)·G(n+2) − G n⁴ = −μ²`.

The sign factor `(−1)^|n|` from the underlying Cassini/Catalan identities cancels
in the difference of squares, so the right-hand side is the index-independent
constant `−μ²`. -/
theorem gib_gelin_cesaro (a b n : ℤ) :
    gib a b (n - 2) * gib a b (n - 1) * gib a b (n + 1) * gib a b (n + 2)
      - gib a b n ^ 4 = -(a ^ 2 - a * b - b ^ 2) ^ 2 := by
  -- Gibonacci Cassini, recentred so the middle index is `n` (base `m = n − 1`)
  have hA := gib_cassini a b (n - 1)
  rw [show (n - 1) + 1 = n by ring, show (n - 1) + 2 = n + 1 by ring] at hA
  -- Gibonacci Catalan, `r = 2`, base `x = n − 2`
  have hB := gib_catalan a b (n - 2) 2
  rw [show (n - 2) + 2 = n by ring, show (n - 2) + 2 * 2 = n + 2 by ring] at hB
  have hf2 : Int.fib 2 = 1 := by decide
  -- the two sign normalisations: `|n−1|` flips, `|n−2|` returns to `|n|`
  have hs1 : (-1 : ℤ) ^ (n - 1).natAbs = -(-1) ^ n.natAbs := sign_flip n
  have hs2 : (-1 : ℤ) ^ (n - 2).natAbs = (-1) ^ n.natAbs := by
    rw [show (n : ℤ) - 2 = (n - 1) - 1 by ring, sign_flip (n - 1), sign_flip n]; ring
  rw [hs1] at hA
  rw [hf2, hs2] at hB
  -- the two "outer product" forms, symmetric about `G n²`
  have hP : gib a b (n - 1) * gib a b (n + 1)
      = gib a b n ^ 2 + (-1) ^ n.natAbs * (a ^ 2 - a * b - b ^ 2) := by
    linear_combination -hA
  have hQ : gib a b (n - 2) * gib a b (n + 2)
      = gib a b n ^ 2 - (-1) ^ n.natAbs * (a ^ 2 - a * b - b ^ 2) := by
    linear_combination -hB
  -- the sign squares away
  have he2 : ((-1 : ℤ) ^ n.natAbs * (a ^ 2 - a * b - b ^ 2)) ^ 2
      = (a ^ 2 - a * b - b ^ 2) ^ 2 := by
    have h1 : ((-1 : ℤ) ^ n.natAbs) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [mul_pow, h1, one_mul]
  calc
    gib a b (n - 2) * gib a b (n - 1) * gib a b (n + 1) * gib a b (n + 2) - gib a b n ^ 4
        = (gib a b (n - 2) * gib a b (n + 2)) * (gib a b (n - 1) * gib a b (n + 1))
            - gib a b n ^ 4 := by ring
      _ = (gib a b n ^ 2 - (-1) ^ n.natAbs * (a ^ 2 - a * b - b ^ 2))
            * (gib a b n ^ 2 + (-1) ^ n.natAbs * (a ^ 2 - a * b - b ^ 2))
            - gib a b n ^ 4 := by rw [hP, hQ]
      _ = -(a ^ 2 - a * b - b ^ 2) ^ 2 := by linear_combination -he2

/-- **Fibonacci Gelin–Cesàro** recovered as the seed `(a, b) = (1, 0)`
(`μ = 1`).  Matches `FibonacciIdentitiesOQ04OQ01.fib_gelin_cesaro`. -/
theorem fib_gelin_cesaro (n : ℤ) :
    Int.fib (n - 2) * Int.fib (n - 1) * Int.fib (n + 1) * Int.fib (n + 2)
      - Int.fib n ^ 4 = -1 := by
  have h := gib_gelin_cesaro 1 0 n
  simpa using h

/-- **Lucas Gelin–Cesàro**: the seed `(a, b) = (1, 2)` has discriminant
`μ = −5`, so `L(n−2)·L(n−1)·L(n+1)·L(n+2) − L n⁴ = −25`. -/
theorem lucas_gelin_cesaro (n : ℤ) :
    lucas (n - 2) * lucas (n - 1) * lucas (n + 1) * lucas (n + 2)
      - lucas n ^ 4 = -25 := by
  have h := gib_gelin_cesaro 1 2 n
  norm_num at h
  simpa [lucas] using h

end FibonacciIdentitiesOQ04OQ03
