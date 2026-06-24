import Mathlib

/-
# Sum of squares of Fibonacci numbers: ∑ F_i² = F_n · F_{n+1}

A cornerstone Fibonacci identity: the sum of the squares of the first `n` Fibonacci
numbers equals the product of the `n`-th and `(n+1)`-th Fibonacci numbers,

  `F_1² + F_2² + ⋯ + F_n² = F_n · F_{n+1}`.

Geometrically this is the statement that squares of side `F_1, …, F_n` tile an
`F_n × F_{n+1}` rectangle — the picture behind the "Fibonacci spiral".

Mathlib records the *linear* sum of Fibonacci numbers,
`Nat.fib_succ_eq_succ_sum : fib (n + 1) = (∑ k ∈ range n, fib k) + 1`,
but **not** the sum of *squares*; this entry supplies it.

We work in Mathlib's `0`-indexed convention `fib 0 = 0`, `fib 1 = fib 2 = 1`.  Because
`fib 0 = 0`, the `i = 0` term contributes nothing, so the classical `1`-indexed sum
`∑_{i=1}^n F_i²` equals the `0`-indexed `∑_{i ∈ range (n+1)} fib i²`; both forms are
proved below and shown to agree.

The proof is the textbook one-line induction.  The inductive step is the telescoping
observation
  `F_{n+1} · F_{n+2} − F_n · F_{n+1} = F_{n+1} · (F_{n+2} − F_n) = F_{n+1} · F_{n+1} = F_{n+1}²`,
i.e. adding the next square `F_{n+1}²` to `F_n · F_{n+1}` advances the product to
`F_{n+1} · F_{n+2}` using only the recurrence `F_{n+2} = F_n + F_{n+1}` and `ring`.
-/

namespace FibonacciIdentitiesOQ03OQ02

/-- **Sum of squares of Fibonacci numbers** (`0`-indexed form).
`∑_{i ∈ range (n+1)} fib i² = fib n · fib (n+1)`.

Proof by induction on `n`: the step `Finset.sum_range_succ` peels off the top square
`fib (k+1)²`, the induction hypothesis rewrites the remaining sum to `fib k · fib (k+1)`,
and the recurrence `fib (k+2) = fib k + fib (k+1)` together with `ring` closes
`fib k · fib (k+1) + fib (k+1)² = fib (k+1) · fib (k+2)`. -/
theorem fib_sum_sq (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), Nat.fib i ^ 2 = Nat.fib n * Nat.fib (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have hrec : Nat.fib (k + 1 + 1) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
    rw [hrec]
    ring

/-- **Sum of squares of Fibonacci numbers** (`1`-indexed form, matching the classical
statement `∑_{i=1}^n F_i² = F_n · F_{n+1}`).

Derived from `fib_sum_sq` by discarding the `i = 0` term, which vanishes since
`fib 0 = 0`: `range (n+1) = insert 0 (Icc 1 n)`. -/
theorem fib_sum_sq_Icc (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, Nat.fib i ^ 2 = Nat.fib n * Nat.fib (n + 1) := by
  rw [← fib_sum_sq n]
  have h : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [h, Finset.sum_insert (by simp)]
  simp

/-- **Integer form.** The same identity over `ℤ`, convenient when the square-sum is
combined with subtractive Fibonacci identities downstream. -/
theorem fib_sum_sq_int (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (Nat.fib i : ℤ) ^ 2
      = (Nat.fib n : ℤ) * (Nat.fib (n + 1) : ℤ) := by
  exact_mod_cast fib_sum_sq n

/-- **Telescoping reading.** Adding the next square advances the running product by one
index: `(∑_{i ∈ range (n+1)} fib i²) + fib (n+1)² = fib (n+1) · fib (n+2)`.  This is the
inductive step in standalone form and exhibits the partial sums as the consecutive
products `fib n · fib (n+1)`. -/
theorem fib_sum_sq_succ (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), Nat.fib i ^ 2) + Nat.fib (n + 1) ^ 2
      = Nat.fib (n + 1) * Nat.fib (n + 2) := by
  rw [fib_sum_sq, Nat.fib_add_two]
  ring

/-- **Oblong / consecutive-product corollary.** Every partial sum of Fibonacci squares is
a product of two consecutive Fibonacci numbers (a "Fibonacci oblong number"). -/
theorem fib_sum_sq_isConsecutiveProduct (n : ℕ) :
    ∃ m : ℕ, ∑ i ∈ Finset.range (n + 1), Nat.fib i ^ 2 = Nat.fib m * Nat.fib (m + 1) :=
  ⟨n, fib_sum_sq n⟩

/-- Numerical check at `n = 6` (`1`-indexed `n = 6`): the sum
`0 + 1 + 1 + 4 + 9 + 25 + 64 = 104` equals `fib 6 · fib 7 = 8 · 13 = 104`.
The sum side is the theorem instance `fib_sum_sq 6`; the product value is checked by
`decide` (kernel reduction — no `native_decide`, so the entry stays `Lean.ofReduceBool`-free). -/
example : ∑ i ∈ Finset.range 7, Nat.fib i ^ 2 = Nat.fib 6 * Nat.fib 7 := fib_sum_sq 6

example : Nat.fib 6 * Nat.fib 7 = 104 := by decide

example : ∑ i ∈ Finset.Icc 1 6, Nat.fib i ^ 2 = Nat.fib 6 * Nat.fib 7 := fib_sum_sq_Icc 6

end FibonacciIdentitiesOQ03OQ02
