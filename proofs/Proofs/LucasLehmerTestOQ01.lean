import Mathlib

/-
# The Lucas–Lehmer primality test for Mersenne numbers

For an odd prime `p`, the Mersenne number `M_p = 2^p - 1` is prime **iff** the
Lucas–Lehmer residue vanishes:

    s₀ = 4,   s_{i+1} = s_i² − 2,   M_p prime ⟺ s_{p-2} ≡ 0  (mod M_p).

Mathlib supplies the two directions *separately*
(`lucas_lehmer_sufficiency` : `LucasLehmerTest p → (mersenne p).Prime`, for `1 < p`,
and `lucas_lehmer_necessity` : `(mersenne p).Prime → LucasLehmerTest p`, for `3 ≤ p`)
together with a `norm_num` extension that evaluates `LucasLehmerTest p` by kernel
reduction.  It does **not** package the full biconditional, nor does it record
worked instances of the test deciding concrete Mersenne numbers.

This file assembles the genuine content the gallery was missing:

* the recurrence `s` spelled out (`s_zero`, `s_succ`) with its first values;
* the **iff** characterization `mersenne_prime_iff_lucasLehmerTest` (`3 ≤ p`),
  combining the sufficiency and necessity halves;
* four prime witnesses decided *through the test* — `M₅ = 31`, `M₇ = 127`,
  `M₁₃ = 8191`, `M₁₇ = 131071`;
* a composite witness — the test *fails* for `p = 11`, so `M₁₁ = 2047 = 23·89`
  is not prime, demonstrating both directions of the criterion.

Everything is decided by kernel reduction (`norm_num`'s `evalLucasLehmerTest`
uses `rfl` on the tail-recursive residue), so the file is axiom-free in the
foundational sense — no `native_decide`, hence no `Lean.ofReduceBool`.
-/

namespace LucasLehmerTestOQ01

open LucasLehmer

/-! ## The Lucas–Lehmer recurrence `sᵢ` -/

/-- The recurrence starts at `s₀ = 4`. -/
theorem s_zero : LucasLehmer.s 0 = 4 := rfl

/-- The defining recurrence `s_{i+1} = s_i² − 2` (over `ℤ`). -/
theorem s_succ (i : ℕ) : LucasLehmer.s (i + 1) = LucasLehmer.s i ^ 2 - 2 := rfl

/-- `s₁ = 4² − 2 = 14`. -/
theorem s_one : LucasLehmer.s 1 = 14 := by norm_num [LucasLehmer.s]

/-- `s₂ = 14² − 2 = 194`. -/
theorem s_two : LucasLehmer.s 2 = 194 := by norm_num [LucasLehmer.s]

/-- `s₃ = 194² − 2 = 37634`. -/
theorem s_three : LucasLehmer.s 3 = 37634 := by norm_num [LucasLehmer.s]

/-- By definition the test is the vanishing of the Lucas–Lehmer residue
`s_{p-2}` taken in `ZMod (2^p − 1)`. -/
theorem lucasLehmerTest_iff_residue (p : ℕ) :
    LucasLehmerTest p ↔ lucasLehmerResidue p = 0 := Iff.rfl

/-! ## The biconditional criterion

Mathlib proves the two implications under slightly different hypotheses
(`1 < p` for sufficiency, `3 ≤ p` for necessity). Bundling them under the
single hypothesis `3 ≤ p` gives the textbook statement. -/

/-- **Lucas–Lehmer test.** For `3 ≤ p`, the Mersenne number `2^p − 1` is prime
**iff** the Lucas–Lehmer test passes. -/
theorem mersenne_prime_iff_lucasLehmerTest (p : ℕ) (hp : 3 ≤ p) :
    (mersenne p).Prime ↔ LucasLehmerTest p :=
  ⟨lucas_lehmer_necessity p hp, lucas_lehmer_sufficiency p (by omega)⟩

/-! ## Prime witnesses, decided through the test -/

/-- `M₅ = 2⁵ − 1 = 31` is prime. -/
theorem mersenne_five_prime : (mersenne 5).Prime := by
  rw [mersenne_prime_iff_lucasLehmerTest 5 (by norm_num)]
  norm_num

/-- `M₇ = 2⁷ − 1 = 127` is prime. -/
theorem mersenne_seven_prime : (mersenne 7).Prime := by
  rw [mersenne_prime_iff_lucasLehmerTest 7 (by norm_num)]
  norm_num

/-- `M₁₃ = 2¹³ − 1 = 8191` is prime. -/
theorem mersenne_thirteen_prime : (mersenne 13).Prime := by
  rw [mersenne_prime_iff_lucasLehmerTest 13 (by norm_num)]
  norm_num

/-- `M₁₇ = 2¹⁷ − 1 = 131071` is prime. -/
theorem mersenne_seventeen_prime : (mersenne 17).Prime := by
  rw [mersenne_prime_iff_lucasLehmerTest 17 (by norm_num)]
  norm_num

/-! ## A composite witness: `p = 11`

`p = 11` is prime but `M₁₁ = 2047 = 23 · 89` is not — the Lucas–Lehmer test
correctly fails, exercising the necessity direction. -/

/-- The test fails at `p = 11`. -/
theorem lucasLehmerTest_eleven_false : ¬ LucasLehmerTest 11 := by norm_num

/-- Hence `M₁₁ = 2¹¹ − 1` is **not** prime (contrapositive of necessity). -/
theorem mersenne_eleven_not_prime : ¬ (mersenne 11).Prime := by
  rw [mersenne_prime_iff_lucasLehmerTest 11 (by norm_num)]
  exact lucasLehmerTest_eleven_false

/-- The explicit factorization confirming compositeness: `M₁₁ = 2047 = 23 · 89`. -/
theorem mersenne_eleven_factorization : mersenne 11 = 23 * 89 := by
  norm_num [mersenne]

end LucasLehmerTestOQ01
