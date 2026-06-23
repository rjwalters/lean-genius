/-
  There are infinitely many ODD abundant numbers.

  A positive integer `n` is *abundant* when `σ(n) > 2n` (Mathlib's
  `Nat.Abundant`). The smallest odd abundant number is `945 = 3³·5·7`
  (see `AbundantNumberOQ02.lean`); the abundant numbers are closed under
  taking positive multiples (`abundant_mul_right` in
  `AbundantMultiplesOQ01.lean`). Combining the two facts gives an infinite
  family of *odd* abundant numbers for free:

      945·1, 945·3, 945·5, 945·7, …  =  945·(2k+1)

  Each `945·(2k+1)` is a product of two odd numbers, hence odd, and is a
  positive multiple of the abundant number `945`, hence abundant. The map
  `k ↦ 945·(2k+1)` is injective, so the set `{n | Odd n ∧ n.Abundant}` is
  infinite.

  This is the odd-case complement to `infinitely_many_abundant`
  (`AbundantMultiplesOQ01.lean`), which uses the even family `12·(k+1)`. The
  even argument trivially produces even witnesses; the odd case genuinely
  needs the closure result together with an *odd* abundant seed, and `945`
  (the least such seed) is the natural choice. Restricting the multiplier to
  the odd numbers `2k+1` is exactly what keeps every witness odd.

  The proof is axiom-free (no `sorry`, no `axiom`, no `native_decide`): it
  reuses the kernel-reducible `abundant_945` and the purely arithmetic
  `abundant_mul_right`.
-/
import Mathlib
import Proofs.AbundantNumberOQ02
import Proofs.AbundantMultiplesOQ01

namespace AbundantOddInfiniteOQ03

open AbundantNumberOQ02 AbundantMultiplesOQ01

/-- The odd witnesses `945·(2k+1)`: `945, 2835, 4725, …`. Each is odd (a
product of the odd number `945` with the odd number `2k+1`) and abundant (a
positive multiple of the abundant number `945`). -/
theorem odd_abundant_945_mul (k : ℕ) :
    Odd (945 * (2 * k + 1)) ∧ (945 * (2 * k + 1)).Abundant := by
  refine ⟨Odd.mul (⟨472, by norm_num⟩ : Odd 945) (odd_two_mul_add_one k), ?_⟩
  exact abundant_mul_right abundant_945 (by positivity)

/-- The map `k ↦ 945·(2k+1)` is injective: multiplication by the nonzero
constant `945` is cancellative, and `2k+1` determines `k`. -/
theorem odd_mul_succ_injective :
    Function.Injective (fun k : ℕ => 945 * (2 * k + 1)) := by
  intro a b hab
  have : 2 * a + 1 = 2 * b + 1 := Nat.eq_of_mul_eq_mul_left (by norm_num) hab
  omega

/-- **There are infinitely many odd abundant numbers.** The infinite family
`{945·(2k+1) : k ∈ ℕ} = {945, 2835, 4725, …}` consists entirely of odd
abundant numbers, and its members are pairwise distinct, so the set of odd
abundant numbers is infinite.

This complements `infinitely_many_abundant` (which uses the even family
`12·(k+1)`): there the witnesses are automatically even, whereas here oddness
is preserved precisely because every multiplier `2k+1` is odd and the seed
`945` — the smallest odd abundant number — is odd. The proof is elementary
and axiom-free, resting on closure under multiples (`abundant_mul_right`) and
the odd abundant seed (`abundant_945`). -/
theorem infinitely_many_odd_abundant :
    {n : ℕ | Odd n ∧ n.Abundant}.Infinite :=
  Set.infinite_of_injective_forall_mem
    odd_mul_succ_injective
    (fun k => odd_abundant_945_mul k)

-- Confirms the result depends only on the standard foundational axioms
-- (propext, Classical.choice, Quot.sound) and NOT on `Lean.ofReduceBool`
-- (which `native_decide` would introduce) or `sorryAx`: the proof is axiom-free.
#print axioms infinitely_many_odd_abundant

end AbundantOddInfiniteOQ03
