/-
# Erdős Problem #823 — σ values computed from Mathlib, axiom-free

**Parent.** `Erdos823Problem.lean` (registered) formalizes Pollack's theorem that
for every α ≥ 1 there are sequences nₖ/mₖ → α with σ(nₖ) = σ(mₖ), where σ is the
sum-of-divisors function. Its motivating example is the smallest nontrivial
σ-pair, σ(14) = σ(15) = 24.

**Why this file exists.** The parent computes its concrete σ-values
(`sigma_14_value`, `sigma_15_value`, `sigma_14_15`, …) with `native_decide`.
Under the project's axiom-integrity policy `native_decide` trusts the compiler
and depends on `Lean.ofReduceBool`, so those statements are **not axiom-free**:
they should be counted as axiomatized. This file reproves the genuine σ-values
**symbolically from Mathlib's arithmetic-function API** — multiplicativity of σ
plus the value on primes and prime powers — so every result is checked by the
kernel with no `native_decide` and no `axiom`. `#print axioms` shows only the
ordinary foundational axioms.

**A latent bug spotted in passing.** The parent also asserts
`sigma_206_210 : σ 206 = σ 210` via `native_decide`, but this is **false**:
σ(206) = σ(2·103) = 3·104 = 312 while σ(210) = σ(2·3·5·7) = 3·4·6·8 = 576. We do
not reproduce it. (206 and 210 are not a σ-pair; the genuine small σ-pairs
include (14,15) and (957,958).)

**What is proved here (all 0-axiom):**
- σ(6) = 12, σ(14) = 24, σ(15) = 24, σ(28) = 56, σ(957) = 1440, σ(958) = 1440;
- the σ-pairs σ(14) = σ(15) and σ(957) = σ(958) — fibers of σ over 24 and 1440
  each containing two consecutive integers, the phenomenon Pollack's theorem
  amplifies to arbitrary ratios;
- 6 and 28 are perfect (σ(n) = 2n), tying into the perfect-number circle.

The method scales to any explicit n via its prime factorization.
-/

import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.NormNum.Prime

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Erdos823SigmaValues

/-!
## The value of σ on a prime

For a prime `p`, `divisors p = {1, p}` so `σ 1 p = 1 + p`. This is the only
building block we need beyond multiplicativity.
-/

/-- `σ 1 p = p + 1` for any prime `p`, proved from `Nat.Prime.divisors`. -/
theorem sigma_one_prime {p : ℕ} (hp : p.Prime) : σ 1 p = p + 1 := by
  rw [sigma_one_apply, hp.divisors, Finset.sum_pair (Ne.symm hp.ne_one)]
  omega

/-!
## σ values via multiplicativity

`ArithmeticFunction.isMultiplicative_sigma` gives `σ (m*n) = σ m · σ n` for
coprime `m, n`. Combined with `sigma_one_prime` (and `sigma_one_apply_prime_pow`
for prime powers) this evaluates σ at any explicit integer.
-/

/-- σ(6) = 12.  6 = 2·3, so σ(6) = σ(2)·σ(3) = 3·4. -/
theorem sigma_6 : σ 1 6 = 12 := by
  rw [show (6 : ℕ) = 2 * 3 from by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (show (2 : ℕ).gcd 3 = 1 from by decide),
      sigma_one_prime (by norm_num), sigma_one_prime (by norm_num)]
  norm_num

/-- σ(14) = 24.  14 = 2·7, so σ(14) = σ(2)·σ(7) = 3·8. -/
theorem sigma_14 : σ 1 14 = 24 := by
  rw [show (14 : ℕ) = 2 * 7 from by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (show (2 : ℕ).gcd 7 = 1 from by decide),
      sigma_one_prime (by norm_num), sigma_one_prime (by norm_num)]
  norm_num

/-- σ(15) = 24.  15 = 3·5, so σ(15) = σ(3)·σ(5) = 4·6. -/
theorem sigma_15 : σ 1 15 = 24 := by
  rw [show (15 : ℕ) = 3 * 5 from by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (show (3 : ℕ).gcd 5 = 1 from by decide),
      sigma_one_prime (by norm_num), sigma_one_prime (by norm_num)]
  norm_num

/-- σ(28) = 56.  28 = 2²·7, so σ(28) = σ(2²)·σ(7) = (1+2+4)·8 = 7·8. -/
theorem sigma_28 : σ 1 28 = 56 := by
  rw [show (28 : ℕ) = 2 ^ 2 * 7 from by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (show (2 ^ 2 : ℕ).gcd 7 = 1 from by decide),
      sigma_one_apply_prime_pow (show Nat.Prime 2 from by norm_num),
      sigma_one_prime (show Nat.Prime 7 from by norm_num)]
  simp [Finset.sum_range_succ]

/-- σ(957) = 1440.  957 = 3·11·29, so σ(957) = 4·12·30. -/
theorem sigma_957 : σ 1 957 = 1440 := by
  rw [show (957 : ℕ) = 3 * (11 * 29) from by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (show (3 : ℕ).gcd (11 * 29) = 1 from by decide),
      isMultiplicative_sigma.map_mul_of_coprime (show (11 : ℕ).gcd 29 = 1 from by decide),
      sigma_one_prime (show Nat.Prime 3 from by norm_num),
      sigma_one_prime (show Nat.Prime 11 from by norm_num),
      sigma_one_prime (show Nat.Prime 29 from by norm_num)]
  norm_num

/-- σ(958) = 1440.  958 = 2·479, so σ(958) = 3·480. -/
theorem sigma_958 : σ 1 958 = 1440 := by
  rw [show (958 : ℕ) = 2 * 479 from by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (show (2 : ℕ).gcd 479 = 1 from by decide),
      sigma_one_prime (show Nat.Prime 2 from by norm_num),
      sigma_one_prime (show Nat.Prime 479 from by norm_num)]
  norm_num

/-!
## σ-pairs and perfect numbers
-/

/-- The smallest nontrivial σ-pair: σ(14) = σ(15) = 24 (consecutive integers). -/
theorem sigma_pair_14_15 : σ 1 14 = σ 1 15 := by rw [sigma_14, sigma_15]

/-- A larger σ-pair of consecutive integers: σ(957) = σ(958) = 1440. -/
theorem sigma_pair_957_958 : σ 1 957 = σ 1 958 := by rw [sigma_957, sigma_958]

/-- 6 is perfect: σ(6) = 2·6. -/
theorem six_perfect : σ 1 6 = 2 * 6 := by rw [sigma_6]

/-- 28 is perfect: σ(28) = 2·28. -/
theorem twentyeight_perfect : σ 1 28 = 2 * 28 := by rw [sigma_28]

/-- Both 14 and 15 lie in the fiber σ⁻¹(24): the concrete witness behind the
parent's `IsSigmaPair 14 15` and the α = 1 case of Pollack's theorem. -/
theorem fiber_24 : σ 1 14 = 24 ∧ σ 1 15 = 24 := ⟨sigma_14, sigma_15⟩

end Erdos823SigmaValues
