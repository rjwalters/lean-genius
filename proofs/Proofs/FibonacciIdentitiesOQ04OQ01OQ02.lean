import Mathlib

/-
# Cassini, d'Ocagne and Catalan for the full Horadam recurrence

`fibonacci-identities-oq-04-oq-01` (*Vajda's identity for Gibonacci sequences*)
proved the product identities for every solution of the **Fibonacci** recurrence
`G(n+2) = G(n+1) + G n`, replacing the Cassini sign `(−1)ⁿ` by the discriminant
`μ = a² − ab − b²`.  Its second open question asks to push the constant all the
way to the **full Horadam recurrence**

  `H(n+2) = p · H(n+1) + q · H n`,    `p, q ∈ ℤ` arbitrary,

where the controlling constant is no longer a fixed sign but the geometric factor
`(−q)ⁿ`.  This entry supplies that generalisation.

## The master identity

Fix two parameters `p q : ℤ` and two seeds `a b : ℤ`, and let `H` be the unique
integer sequence with `H 0 = a`, `H 1 = b`, `H(n+2) = p·H(n+1) + q·H n`.  The
headline result is the **two–index d'Ocagne identity for Horadam sequences**

  `H(n+k+1)·H n − H(n+k)·H(n+1) = (−q)ⁿ · (H(k+1)·a − H(k)·b)`.

A single induction on `n` (using the recurrence twice in the step) proves it.
The whole product hierarchy of the classical Fibonacci numbers falls out as
specialisations:

* **Cassini / Simson** is the case `k = 1`:
  `H(n+2)·H n − H(n+1)² = (−q)ⁿ · (H 2·a − b²)`,
  and the constant `H 2·a − b² = (p·b + q·a)·a − b²` is the Horadam discriminant.
* For the **Fibonacci numbers** `(p,q,a,b) = (1,1,0,1)` the discriminant is `−1`
  and `(−q)ⁿ = (−1)ⁿ`, recovering the textbook Cassini identity in the shifted
  form `F(n+2)·F n − F(n+1)² = (−1)ⁿ⁺¹`.
* The geometric factor `(−q)ⁿ` is exactly `det(M)ⁿ` for the companion matrix
  `M = !![p, q; 1, 0]` (`det M = −q`), the Horadam analogue of the
  `Q = !![1,1;1,0]` matrix viewpoint of the parent entry.

Everything is over `ℤ`, with **no axioms, no `sorry`, no `native_decide`**.
-/

namespace FibonacciHoradamCassini

variable (p q a b : ℤ)

/-- The Horadam sequence with parameters `p, q` and seeds `H 0 = a`, `H 1 = b`,
satisfying `H (n+2) = p · H (n+1) + q · H n`. -/
def H (p q a b : ℤ) : ℕ → ℤ
  | 0 => a
  | 1 => b
  | (n + 2) => p * H p q a b (n + 1) + q * H p q a b n

@[simp] lemma H_zero : H p q a b 0 = a := rfl
@[simp] lemma H_one : H p q a b 1 = b := rfl

/-- The defining recurrence of the Horadam sequence. -/
lemma H_rec (n : ℕ) : H p q a b (n + 2) = p * H p q a b (n + 1) + q * H p q a b n :=
  rfl

/-- **Two–index d'Ocagne identity for Horadam sequences.**

For every `k, n`,
`H(n+k+1)·H n − H(n+k)·H(n+1) = (−q)ⁿ · (H(k+1)·a − H(k)·b)`.

The right-hand constant `H(k+1)·a − H(k)·b` is the value of the left-hand
expression at `n = 0`. -/
theorem horadam_dOcagne (k n : ℕ) :
    H p q a b (n + k + 1) * H p q a b n - H p q a b (n + k) * H p q a b (n + 1)
      = (-q) ^ n * (H p q a b (k + 1) * a - H p q a b k * b) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 : n + 1 + k + 1 = (n + k) + 2 := by omega
      have h2 : n + 1 + k = (n + k) + 1 := by omega
      have h3 : n + 1 + 1 = n + 2 := by omega
      rw [h1, h2, h3, H_rec p q a b (n + k), H_rec p q a b n]
      linear_combination (-q) * ih

/-- **Generalised Cassini / Simson identity for Horadam sequences** — the `k = 1`
case of `horadam_dOcagne`:
`H(n+2)·H n − H(n+1)² = (−q)ⁿ · (H 2·a − b²)`. -/
theorem horadam_cassini (n : ℕ) :
    H p q a b (n + 2) * H p q a b n - H p q a b (n + 1) ^ 2
      = (-q) ^ n * (H p q a b 2 * a - b ^ 2) := by
  have := horadam_dOcagne p q a b 1 n
  simpa [sq, H_one] using this

/-- The Cassini constant written out from the seeds:
`H 2·a − b² = (p·b + q·a)·a − b²`. -/
lemma horadam_cassini_const :
    H p q a b 2 * a - b ^ 2 = (p * b + q * a) * a - b ^ 2 := by
  have : H p q a b 2 = p * b + q * a := by
    rw [H_rec p q a b 0]; simp
  rw [this]

/-! ### Specialisation: the classical Fibonacci numbers `(p,q,a,b) = (1,1,0,1)`. -/

/-- `H 1 1 0 1` is the Fibonacci sequence (`Nat.fib`, cast to `ℤ`). -/
lemma H_fib (n : ℕ) : H 1 1 0 1 n = (Nat.fib n : ℤ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp
    | 1 => simp
    | (m + 2) =>
        rw [H_rec, ih (m + 1) (by omega), ih m (by omega), Nat.fib_add_two]
        push_cast; ring

/-- Cassini's identity recovered for the Fibonacci numbers, in shifted form:
`F(n+2)·F n − F(n+1)² = (−1)ⁿ⁺¹`. -/
theorem fib_cassini_shifted (n : ℕ) :
    (Nat.fib (n + 2) : ℤ) * Nat.fib n - (Nat.fib (n + 1)) ^ 2 = (-1) ^ (n + 1) := by
  have h := horadam_cassini 1 1 0 1 n
  simp only [H_fib] at h
  rw [h]
  -- the Fibonacci discriminant: fib 2 · 0 − 1² = −1
  have hc : (Nat.fib 2 : ℤ) * 0 - (1 : ℤ) ^ 2 = -1 := by norm_num
  rw [hc, pow_succ]

end FibonacciHoradamCassini
