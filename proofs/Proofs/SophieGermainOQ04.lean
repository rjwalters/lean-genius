import Mathlib

/-!
# Sophie Germain OQ-04: the Sophie Germain identity and its compositeness corollary

Sophie Germain's *algebraic* identity (distinct from her work on Sophie Germain primes
in the base entry) factors a sum that looks stubbornly irreducible:

`a⁴ + 4·b⁴ = (a² - 2ab + 2b²) · (a² + 2ab + 2b²)`.

This entry proves that identity (`sophie_germain_identity`) and reads off its classic
consequence: numbers of the form `a⁴ + 4b⁴` are composite once both factors exceed `1`.
The headline specialization is the famous fact that

`n⁴ + 4` is prime **only** for `n = 1` (where it is `5`);

for every `n ≥ 2` it factors as `(n² - 2n + 2)(n² + 2n + 2)`, both factors `> 1`
(`not_prime_n_pow_four_add_four`). For example `5⁴ + 4 = 629 = 17 · 37`.

The identity is stated and proved over `ℤ` so that the subtraction `a² - 2ab + 2b²` is
genuine; the compositeness corollary is transported to `ℕ` by writing the smaller factor
as `(n-1)² + 1` (substituting `n = m + 2`), which avoids `ℕ`'s truncated subtraction
entirely.

No axioms, no sorries.
-/

namespace SophieGermainOQ04

/-- **The Sophie Germain identity** over `ℤ`:
`a⁴ + 4b⁴ = (a² - 2ab + 2b²)(a² + 2ab + 2b²)`. The two quadratic factors come from
completing `a⁴ + 4b⁴ = (a² + 2b²)² - (2ab)²` as a difference of squares. -/
theorem sophie_germain_identity (a b : ℤ) :
    a ^ 4 + 4 * b ^ 4
      = (a ^ 2 - 2 * a * b + 2 * b ^ 2) * (a ^ 2 + 2 * a * b + 2 * b ^ 2) := by
  ring

/-- The `b = 1` specialization: `n⁴ + 4 = (n² - 2n + 2)(n² + 2n + 2)` over `ℤ`. -/
theorem n_pow_four_add_four_factor (n : ℤ) :
    n ^ 4 + 4 = (n ^ 2 - 2 * n + 2) * (n ^ 2 + 2 * n + 2) := by
  have := sophie_germain_identity n 1
  simpa using this

/-- Each factor of the difference-of-squares form is at least `1` (over `ℤ`):
`a² - 2ab + 2b² = (a - b)² + b² ≥ 0`, and it is `> 0` unless `a = b = 0`. -/
theorem factor_nonneg (a b : ℤ) : 0 ≤ a ^ 2 - 2 * a * b + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg b]

/-- **Compositeness corollary.** For `n ≥ 2`, `n⁴ + 4` is not prime: it equals
`((n-1)² + 1)·(n² + 2n + 2)` with both factors `> 1`. Equivalently, `n⁴ + 4` is prime
only at `n = 1` (giving `5`). Worked out via `n = m + 2` so the smaller factor is the
non-truncated `(m+1)² + 1`. -/
theorem not_prime_n_pow_four_add_four {n : ℕ} (hn : 2 ≤ n) :
    ¬ Nat.Prime (n ^ 4 + 4) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hfac : (m + 2) ^ 4 + 4
      = ((m + 1) ^ 2 + 1) * ((m + 2) ^ 2 + 2 * (m + 2) + 2) := by ring
  rw [hfac]
  have h1 : (m + 1) ^ 2 + 1 ≠ 1 := by nlinarith [Nat.zero_le m]
  have h2 : (m + 2) ^ 2 + 2 * (m + 2) + 2 ≠ 1 := by nlinarith [Nat.zero_le m]
  exact Nat.not_prime_mul h1 h2

/-- The lone prime case: `1⁴ + 4 = 5` really is prime, so the bound `n ≥ 2` in
`not_prime_n_pow_four_add_four` is sharp. -/
theorem one_pow_four_add_four_prime : Nat.Prime (1 ^ 4 + 4) := by
  norm_num

/-- A concrete composite witness: `5⁴ + 4 = 629 = 17 · 37`. -/
theorem five_pow_four_add_four_eq : 5 ^ 4 + 4 = 17 * 37 := by norm_num

end SophieGermainOQ04
