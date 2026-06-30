import Mathlib

/-
# Vajda's identity for Gibonacci (Horadam) sequences, with the discriminant constant

`fibonacci-identities-oq-04` proved **Vajda's identity** for the integer Fibonacci
numbers,

  `F (x+i)·F (x+j) − F x·F (x+i+j) = (−1)^|x| · F i · F j`,

and recovered Cassini, Catalan and d'Ocagne as one-line corollaries.  Its first
open question asks to *replace the sign constant by a discriminant* and prove the
analogue for the Lucas numbers and the general Gibonacci (Horadam) sequences.
Its third open question asks for the **Gelin–Cesàro identity**
`F(n−2)·F(n−1)·F(n+1)·F(n+2) − F n⁴ = −1`.  This entry supplies both.

A **Gibonacci sequence** is any solution of the Fibonacci recurrence
`G(n+2) = G(n+1) + G n`.  Over the integers every such sequence has the closed form

  `G n = a · F n + b · F (n−1)`,    where `a = G 1`, `b = G 0`,

so it is parametrised by its two seeds.  The headline result is the
**Gibonacci Vajda identity**

  `G(x+i)·G(x+j) − G x·G(x+i+j) = (−1)^|x| · (a² − a·b − b²) · F i · F j`,

in which the Fibonacci sign constant `(−1)^|x|` is multiplied by the
**characteristic** `μ = a² − a·b − b² = G 1² − G 0·G 1 − G 0²`.  This `μ` is
exactly the "discriminant" the open question refers to:

* the **Fibonacci** numbers are `G = gib 1 0`, with `μ = 1` — Vajda is recovered;
* the **Lucas** numbers are `G = gib 1 2` (`L 0 = 2`, `L 1 = 1`), with
  `μ = 1 − 2 − 4 = −5` — the Lucas discriminant `5` appears with a sign.

The proof reduces the Gibonacci identity to four instances of the Fibonacci Vajda
identity (at base points `x` and `x−1`), a parity sign-flip lemma
`(−1)^|x−1| = −(−1)^|x|`, and the basic recurrence `F(j+1) = F(j−1) + F j`.
Everything is over `Int.fib`, so the statements hold for all integer indices.
No axioms, no `sorry`, no `native_decide`.
-/

namespace FibonacciIdentitiesOQ04OQ01

open Int

/-! ## Fibonacci Vajda identity (restated locally for a self-contained file)

This is the verified headline of `fibonacci-identities-oq-04`, reproduced here so
that this file depends only on Mathlib. -/

/-- **Vajda's identity** for the integer Fibonacci numbers. -/
theorem fib_vajda (x i j : ℤ) :
    Int.fib (x + i) * Int.fib (x + j) - Int.fib x * Int.fib (x + i + j)
      = (-1) ^ x.natAbs * (Int.fib i * Int.fib j) := by
  have e1 := Int.fib_add x i
  have e2 := Int.fib_add x j
  have e3 := Int.fib_add x (i + j)
  have e4 := Int.fib_add i j
  have e5 := Int.fib_add i (j + 1)
  have rx : Int.fib (x + 1) = Int.fib (x - 1) + Int.fib x := by
    rw [show (x : ℤ) + 1 = (x - 1) + 2 by ring, Int.fib_add_two, show (x : ℤ) - 1 + 1 = x by ring]
  have ri : Int.fib (i + 1) = Int.fib (i - 1) + Int.fib i := by
    rw [show (i : ℤ) + 1 = (i - 1) + 2 by ring, Int.fib_add_two, show (i : ℤ) - 1 + 1 = i by ring]
  have rj : Int.fib (j + 1 + 1) = Int.fib j + Int.fib (j + 1) := by
    rw [show (j : ℤ) + 1 + 1 = j + 2 by ring]; exact Int.fib_add_two j
  have hc := Int.fib_succ_mul_fib_pred_sub_fib_sq x
  rw [show x + i + j = x + (i + j) by ring, e1, e2, e3, e4,
      show i + j + 1 = i + (j + 1) by ring, e5]
  rw [← hc, rx, ri, rj]
  ring

/-- Parity sign-flip: `(−1)^|y−1| = −(−1)^|y|`, since consecutive integers have
opposite parity (and `|n|` has the same parity as `n`). -/
theorem sign_flip (y : ℤ) : (-1 : ℤ) ^ (y - 1).natAbs = -(-1 : ℤ) ^ y.natAbs := by
  rcases Int.even_or_odd y with he | ho
  · have h1 : Even y.natAbs := Int.natAbs_even.mpr he
    have h2 : Odd (y - 1).natAbs := Int.natAbs_odd.mpr (by simpa using he.sub_odd odd_one)
    rw [h1.neg_one_pow, h2.neg_one_pow]
  · have h1 : Odd y.natAbs := Int.natAbs_odd.mpr ho
    have h2 : Even (y - 1).natAbs := Int.natAbs_even.mpr (by simpa using ho.sub_odd odd_one)
    rw [h1.neg_one_pow, h2.neg_one_pow]; norm_num

/-! ## Gibonacci sequences -/

/-- The Gibonacci (Horadam) sequence with seeds `G 0 = b`, `G 1 = a`, given in
closed form by `G n = a · F n + b · F (n−1)`. -/
def gib (a b n : ℤ) : ℤ := a * Int.fib n + b * Int.fib (n - 1)

@[simp] theorem gib_one (a b : ℤ) : gib a b 1 = a := by simp [gib]

@[simp] theorem gib_two (a b : ℤ) : gib a b 2 = a + b := by
  simp [gib]

theorem gib_zero (a b : ℤ) : gib a b 0 = b := by
  simp [gib]

/-- `gib` really is a Gibonacci sequence: it satisfies the Fibonacci recurrence. -/
theorem gib_recurrence (a b n : ℤ) : gib a b (n + 2) = gib a b (n + 1) + gib a b n := by
  have h1 : Int.fib (n + 2) = Int.fib n + Int.fib (n + 1) := Int.fib_add_two n
  have h2 : Int.fib (n + 1) = Int.fib (n - 1) + Int.fib n := by
    rw [show (n : ℤ) + 1 = (n - 1) + 2 by ring, Int.fib_add_two, show (n : ℤ) - 1 + 1 = n by ring]
  simp only [gib, show (n : ℤ) + 2 - 1 = n + 1 by ring, show (n : ℤ) + 1 - 1 = n by ring]
  rw [h1, h2]; ring

/-- The Fibonacci numbers are the Gibonacci sequence with seeds `(a, b) = (1, 0)`. -/
@[simp] theorem gib_one_zero (n : ℤ) : gib 1 0 n = Int.fib n := by simp [gib]

/-! ## The master identity -/

/-- **Vajda's identity for Gibonacci sequences.**  With characteristic
`μ = a² − a·b − b²`,

  `G(x+i)·G(x+j) − G x·G(x+i+j) = (−1)^|x| · μ · F i · F j`. -/
theorem gib_vajda (a b x i j : ℤ) :
    gib a b (x + i) * gib a b (x + j) - gib a b x * gib a b (x + i + j)
      = (-1) ^ x.natAbs * (a ^ 2 - a * b - b ^ 2) * (Int.fib i * Int.fib j) := by
  have V1 := fib_vajda x i j
  have V2 := fib_vajda (x - 1) i j
  have V3 := fib_vajda x i (j - 1)
  have V4 := fib_vajda (x - 1) i (j + 1)
  rw [show x - 1 + i = x + i - 1 by ring, show x - 1 + j = x + j - 1 by ring,
      show x + i - 1 + j = x + i + j - 1 by ring, sign_flip x] at V2
  rw [show x + (j - 1) = x + j - 1 by ring, show x + i + (j - 1) = x + i + j - 1 by ring] at V3
  rw [show x - 1 + i = x + i - 1 by ring, show x - 1 + (j + 1) = x + j by ring,
      show x + i - 1 + (j + 1) = x + i + j by ring, sign_flip x] at V4
  have hj : Int.fib (j + 1) = Int.fib (j - 1) + Int.fib j := by
    rw [show (j : ℤ) + 1 = (j - 1) + 2 by ring, Int.fib_add_two, show (j : ℤ) - 1 + 1 = j by ring]
  unfold gib
  linear_combination a ^ 2 * V1 + b ^ 2 * V2 + a * b * V3 + a * b * V4
    - a * b * (-1) ^ x.natAbs * Int.fib i * hj

/-- **Gibonacci Cassini** (the `i = j = 1` case): `G(n+1)² − G n·G(n+2) = (−1)^|n|·μ`. -/
theorem gib_cassini (a b n : ℤ) :
    gib a b (n + 1) ^ 2 - gib a b n * gib a b (n + 2)
      = (-1) ^ n.natAbs * (a ^ 2 - a * b - b ^ 2) := by
  have h := gib_vajda a b n 1 1
  rw [show n + 1 + 1 = n + 2 by ring] at h
  simp only [Int.fib_one, mul_one] at h
  linear_combination h

/-- **Gibonacci Catalan** (the `i = j = r` case):
`G(x+r)² − G x·G(x+2r) = (−1)^|x|·μ·F r²`. -/
theorem gib_catalan (a b x r : ℤ) :
    gib a b (x + r) ^ 2 - gib a b x * gib a b (x + 2 * r)
      = (-1) ^ x.natAbs * (a ^ 2 - a * b - b ^ 2) * Int.fib r ^ 2 := by
  have h := gib_vajda a b x r r
  rw [show x + r + r = x + 2 * r by ring] at h
  linear_combination h

/-! ## The Lucas specialisation: discriminant `μ = −5` -/

/-- The Lucas numbers `L n = F(n−1) + F(n+1)`, realised as the Gibonacci sequence
with seeds `(a, b) = (1, 2)` (`L 0 = 2`, `L 1 = 1`). -/
def lucas (n : ℤ) : ℤ := gib 1 2 n

@[simp] theorem lucas_one : lucas 1 = 1 := by simp [lucas]

theorem lucas_zero : lucas 0 = 2 := by rw [lucas, gib_zero]

theorem lucas_recurrence (n : ℤ) : lucas (n + 2) = lucas (n + 1) + lucas n :=
  gib_recurrence 1 2 n

/-- Lucas numbers via Fibonacci: `L n = F(n−1) + F(n+1)`. -/
theorem lucas_eq_fib (n : ℤ) : lucas n = Int.fib (n - 1) + Int.fib (n + 1) := by
  have hj : Int.fib (n + 1) = Int.fib (n - 1) + Int.fib n := by
    rw [show (n : ℤ) + 1 = (n - 1) + 2 by ring, Int.fib_add_two, show (n : ℤ) - 1 + 1 = n by ring]
  simp only [lucas, gib]; rw [hj]; ring

/-- **Lucas Vajda identity**: the discriminant constant is `μ = −5`. -/
theorem lucas_vajda (x i j : ℤ) :
    lucas (x + i) * lucas (x + j) - lucas x * lucas (x + i + j)
      = (-1) ^ x.natAbs * (-5) * (Int.fib i * Int.fib j) := by
  have h := gib_vajda 1 2 x i j
  norm_num at h
  simpa [lucas] using h

/-! ## Gelin–Cesàro identity (open question 3 of oq-04) -/

/-- **Gelin–Cesàro identity**:
`F(n−2)·F(n−1)·F(n+1)·F(n+2) − F n⁴ = −1`.

Obtained by multiplying Cassini (`F(n−1)·F(n+1) = F n² + (−1)^|n|`) and the
Catalan `r = 2` instance (`F(n−2)·F(n+2) = F n² − (−1)^|n|`), whose product is a
difference of squares `(F n²)² − ((−1)^|n|)² = F n⁴ − 1`. -/
theorem fib_gelin_cesaro (n : ℤ) :
    Int.fib (n - 2) * Int.fib (n - 1) * Int.fib (n + 1) * Int.fib (n + 2)
      - Int.fib n ^ 4 = -1 := by
  -- Cassini: F(n+1)·F(n−1) − F n² = (−1)^|n|
  have hA := Int.fib_succ_mul_fib_pred_sub_fib_sq n
  -- Catalan r = 2, via Vajda at base n−2 with i = j = 2
  have hB := fib_vajda (n - 2) 2 2
  rw [show n - 2 + 2 = n by ring] at hB
  have hf2 : Int.fib 2 = 1 := by decide
  have hs : (-1 : ℤ) ^ (n - 2).natAbs = (-1) ^ n.natAbs := by
    rw [show (n : ℤ) - 2 = (n - 1) - 1 by ring, sign_flip (n - 1), sign_flip n]; ring
  rw [hf2, hs] at hB
  -- explicit product values
  have hP : Int.fib (n - 1) * Int.fib (n + 1) = Int.fib n ^ 2 + (-1) ^ n.natAbs := by
    linear_combination hA
  have hQ : Int.fib (n - 2) * Int.fib (n + 2) = Int.fib n ^ 2 - (-1) ^ n.natAbs := by
    linear_combination -hB
  have he2 : ((-1 : ℤ) ^ n.natAbs) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  calc
    Int.fib (n - 2) * Int.fib (n - 1) * Int.fib (n + 1) * Int.fib (n + 2) - Int.fib n ^ 4
        = (Int.fib (n - 2) * Int.fib (n + 2)) * (Int.fib (n - 1) * Int.fib (n + 1))
            - Int.fib n ^ 4 := by ring
      _ = (Int.fib n ^ 2 - (-1) ^ n.natAbs) * (Int.fib n ^ 2 + (-1) ^ n.natAbs)
            - Int.fib n ^ 4 := by rw [hP, hQ]
      _ = -1 := by linear_combination -he2

end FibonacciIdentitiesOQ04OQ01
