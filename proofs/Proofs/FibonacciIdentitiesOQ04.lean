import Mathlib

/-
# Vajda's identity and d'Ocagne's identity for the Fibonacci numbers

Mathlib's integer Fibonacci file `Mathlib/Data/Int/Fib/Lemmas.lean` (Monica Omar,
2025) records two of the classical *product* identities:

* **Cassini's identity** `Int.fib_succ_mul_fib_pred_sub_fib_sq` —
  `fib (n + 1) * fib (n - 1) - fib n ^ 2 = (-1) ^ |n|`, and
* **Catalan's identity** `Int.fib_add_sq_sub_fib_mul_fib_add_two_mul` —
  `fib (x + a) ^ 2 - fib x * fib (x + 2 * a) = (-1) ^ |x| * fib a ^ 2`.

Catalan is the one–parameter (`i = j`) specialisation of the *two*-parameter
**Vajda identity**

  `fib (x + i) * fib (x + j) - fib x * fib (x + i + j) = (-1) ^ |x| * (fib i * fib j)`,

which is the genuine master identity of this family: Cassini (`i = j = 1`),
Catalan (`i = j`) and d'Ocagne all fall out of it.  Vajda's identity itself is
**absent from Mathlib**, as is **d'Ocagne's identity**

  `fib m * fib (n + 1) - fib (m + 1) * fib n = (-1) ^ |n| * fib (m - n)`.

This entry supplies both.  The proof of Vajda mirrors Mathlib's own Catalan
proof: expand the three "shifted" Fibonacci numbers `fib (x + i)`, `fib (x + j)`,
`fib (x + (i + j))` with the integer addition formula `Int.fib_add`, expand the
inner `fib (i + j)` and `fib (i + (j + 1))` the same way, and the whole expression
collapses — by `ring`-level algebra together with Cassini's identity for `x` — to
`(-1) ^ |x| * (fib i * fib j)`.  d'Ocagne and a fresh derivation of Catalan and
Cassini are then immediate `Int`-arithmetic corollaries.

Everything is over `Int.fib` (the Fibonacci sequence extended to all integer
indices), so the statements hold for negative indices as well.  No axioms, no
`sorry`, no `native_decide`.
-/

namespace FibonacciIdentitiesOQ04

open Int

/-- **Vajda's identity** for the integer Fibonacci numbers:
`fib (x + i) · fib (x + j) − fib x · fib (x + i + j) = (−1)^|x| · fib i · fib j`.

This is the two–parameter master identity of the Fibonacci product family.
Setting `i = j` recovers Catalan's identity, `i = j = 1` recovers Cassini's
identity, and `i = m - n, j = 1, x = n` recovers d'Ocagne's identity. -/
theorem fib_vajda (x i j : ℤ) :
    Int.fib (x + i) * Int.fib (x + j) - Int.fib x * Int.fib (x + i + j)
      = (-1) ^ x.natAbs * (Int.fib i * Int.fib j) := by
  -- expand the three shifted Fibonacci numbers with the integer addition formula
  have e1 := Int.fib_add x i                 -- fib (x+i) = fib (x-1)·fib i + fib x·fib (i+1)
  have e2 := Int.fib_add x j                 -- fib (x+j) = fib (x-1)·fib j + fib x·fib (j+1)
  have e3 := Int.fib_add x (i + j)           -- fib (x+(i+j)) = fib (x-1)·fib (i+j) + fib x·fib (i+j+1)
  have e4 := Int.fib_add i j                 -- fib (i+j) = fib (i-1)·fib j + fib i·fib (j+1)
  have e5 := Int.fib_add i (j + 1)           -- fib (i+(j+1)) = fib (i-1)·fib (j+1) + fib i·fib (j+2)
  -- the recurrence in the form we need (no Nat subtraction; indices normalised)
  have rx : Int.fib (x + 1) = Int.fib (x - 1) + Int.fib x := by
    rw [show (x : ℤ) + 1 = (x - 1) + 2 by ring, Int.fib_add_two, show (x : ℤ) - 1 + 1 = x by ring]
  have ri : Int.fib (i + 1) = Int.fib (i - 1) + Int.fib i := by
    rw [show (i : ℤ) + 1 = (i - 1) + 2 by ring, Int.fib_add_two, show (i : ℤ) - 1 + 1 = i by ring]
  -- the `fib_add` expansion of `fib (i + (j + 1))` produces the index `j + 1 + 1`
  have rj : Int.fib (j + 1 + 1) = Int.fib j + Int.fib (j + 1) := by
    rw [show (j : ℤ) + 1 + 1 = j + 2 by ring]; exact Int.fib_add_two j
  -- Cassini's identity isolates the sign `(-1)^|x|`
  have hc := Int.fib_succ_mul_fib_pred_sub_fib_sq x
  -- normalise the compound index, then expand every shifted Fibonacci number
  rw [show x + i + j = x + (i + j) by ring, e1, e2, e3, e4,
      show i + j + 1 = i + (j + 1) by ring, e5]
  -- replace the sign by its Cassini value, then it is a pure ring identity
  rw [← hc, rx, ri, rj]
  ring

/-- **d'Ocagne's identity** for the integer Fibonacci numbers:
`fib m · fib (n + 1) − fib (m + 1) · fib n = (−1)^|n| · fib (m − n)`. -/
theorem fib_dOcagne (m n : ℤ) :
    Int.fib m * Int.fib (n + 1) - Int.fib (m + 1) * Int.fib n
      = (-1) ^ n.natAbs * Int.fib (m - n) := by
  have h := fib_vajda n (m - n) 1
  -- `n + (m - n)` rewrites to `m`, which also turns `n + (m - n) + 1` into `m + 1`
  rw [show n + (m - n) = m by ring] at h
  simp only [Int.fib_one, mul_one] at h
  linear_combination h

/-- **Catalan's identity** recovered as the `i = j = a` case of Vajda
(matching Mathlib's `Int.fib_add_sq_sub_fib_mul_fib_add_two_mul`). -/
theorem fib_catalan (x a : ℤ) :
    Int.fib (x + a) ^ 2 - Int.fib x * Int.fib (x + 2 * a)
      = (-1) ^ x.natAbs * Int.fib a ^ 2 := by
  have h := fib_vajda x a a
  rw [show x + a + a = x + 2 * a by ring] at h
  linear_combination h

/-- **Cassini's identity** recovered as the `i = j = 1` case of Vajda. -/
theorem fib_cassini (x : ℤ) :
    Int.fib (x + 1) ^ 2 - Int.fib x * Int.fib (x + 2) = (-1) ^ x.natAbs := by
  have h := fib_vajda x 1 1
  rw [show x + 1 + 1 = x + 2 by ring] at h
  simp only [Int.fib_one, mul_one] at h
  linear_combination h

end FibonacciIdentitiesOQ04
