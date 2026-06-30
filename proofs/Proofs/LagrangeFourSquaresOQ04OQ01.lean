/-
  Sums of three squares are NOT closed under multiplication.

  For sums of **two** squares (Brahmagupta–Fibonacci) and sums of **four**
  squares (Euler's identity) the representable set is multiplicatively closed:
  a product of two representable numbers is again representable. That closure is
  exactly what makes the two- and four-square theorems "multiplicative" — one
  reduces to primes. Three squares is the exception:

      3 = 1² + 1² + 1²,   5 = 0² + 1² + 2²,   yet   3·5 = 15  is NOT a sum of
      three squares.

  The obstruction is the classical mod-8 fact: a square is `≡ 0, 1, 4 (mod 8)`,
  so a sum of three squares is never `≡ 7 (mod 8)`. Since `15 ≡ 7` and
  `63 ≡ 7`, neither `3·5 = 15` nor `3·21 = 63` is a sum of three squares, even
  though `3, 5, 21` each are. Hence there is no ternary composition law: one
  cannot assemble a three-square representation of a product from
  representations of its factors — the concrete arithmetic shadow of the
  abstract fact (Hurwitz) that no bilinear 3-square identity exists.

  As a genuine contrast we also prove that the **four**-square set IS
  multiplicatively closed, via Euler's four-square identity over `ℤ` and
  `Int.natAbs`: representability is recovered exactly one dimension up
  (`15 = 1² + 1² + 2² + 3²`).

  This file is self-contained and axiom-free: the non-representability is proved
  here from the mod-8 obstruction rather than invoking the parent three-square
  theorem (whose *backward* direction is axiomatized). The parent's proved
  *forward* direction (`LagrangeFourSquaresOQ04.obstructed_not_three_squares`)
  is the same mod-8 argument.

  Fully verified: 0 sorries, 0 axioms, no `native_decide`.
-/
import Mathlib

namespace LagrangeFourSquaresOQ04OQ01

/-- A natural number is a sum of three squares. -/
def IsSumOfThreeSquares (n : ℕ) : Prop := ∃ a b c : ℕ, a ^ 2 + b ^ 2 + c ^ 2 = n

/-- A natural number is a sum of four squares. -/
def IsSumOfFourSquares (n : ℕ) : Prop :=
  ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n

/-! ### The mod-8 obstruction -/

/-- Every square is `≡ 0, 1, or 4 (mod 8)`. -/
theorem sq_mod_eight (k : ℕ) : k ^ 2 % 8 = 0 ∨ k ^ 2 % 8 = 1 ∨ k ^ 2 % 8 = 4 := by
  have hlt : k % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hk : k ^ 2 % 8 = (k % 8) ^ 2 % 8 := by rw [Nat.pow_mod]
  interval_cases h : k % 8 <;> rw [hk] <;> decide

/-- A sum of three squares is never `≡ 7 (mod 8)`. -/
theorem three_sq_not_seven_mod_eight (a b c : ℕ) :
    (a ^ 2 + b ^ 2 + c ^ 2) % 8 ≠ 7 := by
  rcases sq_mod_eight a with ha | ha | ha <;>
    rcases sq_mod_eight b with hb | hb | hb <;>
      rcases sq_mod_eight c with hc | hc | hc <;> omega

/-- If `n ≡ 7 (mod 8)` then `n` is not a sum of three squares. -/
theorem not_isSumOfThreeSquares_of_seven_mod_eight {n : ℕ} (hn : n % 8 = 7) :
    ¬ IsSumOfThreeSquares n := by
  rintro ⟨a, b, c, rfl⟩
  exact three_sq_not_seven_mod_eight a b c hn

/-! ### The three small three-square representations -/

/-- `3 = 1² + 1² + 1²`. -/
theorem three_isSumOfThreeSquares : IsSumOfThreeSquares 3 := ⟨1, 1, 1, by norm_num⟩

/-- `5 = 0² + 1² + 2²`. -/
theorem five_isSumOfThreeSquares : IsSumOfThreeSquares 5 := ⟨0, 1, 2, by norm_num⟩

/-- `21 = 4² + 2² + 1²`. -/
theorem twentyone_isSumOfThreeSquares : IsSumOfThreeSquares 21 := ⟨4, 2, 1, by norm_num⟩

/-! ### The obstructed products -/

/-- `15 ≡ 7 (mod 8)` is not a sum of three squares. -/
theorem not_isSumOfThreeSquares_15 : ¬ IsSumOfThreeSquares 15 :=
  not_isSumOfThreeSquares_of_seven_mod_eight (by norm_num)

/-- `63 ≡ 7 (mod 8)` is not a sum of three squares. -/
theorem not_isSumOfThreeSquares_63 : ¬ IsSumOfThreeSquares 63 :=
  not_isSumOfThreeSquares_of_seven_mod_eight (by norm_num)

/-! ### Non-closure of the three-square set -/

/-- **Main theorem.** The set of sums of three squares is *not* closed under
multiplication: there are `m, n` each a sum of three squares whose product
is not. Concrete witness `(m, n) = (3, 5)`, product `15`. -/
theorem not_isSumOfThreeSquares_mul_closed :
    ∃ m n : ℕ, IsSumOfThreeSquares m ∧ IsSumOfThreeSquares n
      ∧ ¬ IsSumOfThreeSquares (m * n) := by
  refine ⟨3, 5, three_isSumOfThreeSquares, five_isSumOfThreeSquares, ?_⟩
  intro h
  exact not_isSumOfThreeSquares_15 (by simpa using h)

/-- A **second, independent** witness `(m, n) = (3, 21)`, product `63`,
showing the failure is not a one-off. -/
theorem not_isSumOfThreeSquares_mul_closed' :
    ∃ m n : ℕ, IsSumOfThreeSquares m ∧ IsSumOfThreeSquares n
      ∧ ¬ IsSumOfThreeSquares (m * n) := by
  refine ⟨3, 21, three_isSumOfThreeSquares, twentyone_isSumOfThreeSquares, ?_⟩
  intro h
  exact not_isSumOfThreeSquares_63 (by simpa using h)

/-- Multiplicative closure of a predicate on `ℕ`. -/
def MulClosed (P : ℕ → Prop) : Prop := ∀ ⦃m n : ℕ⦄, P m → P n → P (m * n)

/-- Packaged as a failure of `MulClosed`: the three-square predicate is not
multiplicatively closed. -/
theorem not_mulClosed_isSumOfThreeSquares : ¬ MulClosed IsSumOfThreeSquares := by
  intro h
  have h15 : IsSumOfThreeSquares (3 * 5) :=
    h three_isSumOfThreeSquares five_isSumOfThreeSquares
  exact not_isSumOfThreeSquares_15 (by simpa using h15)

/-! ### Contrast: the four-square set IS multiplicatively closed -/

/-- Euler's four-square identity (over any commutative ring). -/
theorem euler_four_squares {R : Type*} [CommRing R] (a b c d x y z w : R) :
    (a * x - b * y - c * z - d * w) ^ 2 +
    (a * y + b * x + c * w - d * z) ^ 2 +
    (a * z - b * w + c * x + d * y) ^ 2 +
    (a * w + b * z - c * y + d * x) ^ 2 =
    (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := by
  ring

/-- Casting the square of an integer's absolute value back: `(↑|a|)² = a²`. -/
private theorem natAbs_sq_cast (a : ℤ) : ((a.natAbs : ℤ)) ^ 2 = a ^ 2 := by
  rw [← Int.abs_eq_natAbs, sq_abs]

/-- **Euler's four-square identity gives closure.** The product of two sums of
four squares is again a sum of four squares — the composition law the ternary
form lacks. The four component values are integers (Euler's identity has
subtractions), realized as `ℕ` squares via `Int.natAbs`. -/
theorem isSumOfFourSquares_mul {m n : ℕ}
    (hm : IsSumOfFourSquares m) (hn : IsSumOfFourSquares n) :
    IsSumOfFourSquares (m * n) := by
  obtain ⟨a, b, c, d, hm⟩ := hm
  obtain ⟨x, y, z, w, hn⟩ := hn
  refine ⟨(a * x - b * y - c * z - d * w : ℤ).natAbs,
          (a * y + b * x + c * w - d * z : ℤ).natAbs,
          (a * z - b * w + c * x + d * y : ℤ).natAbs,
          (a * w + b * z - c * y + d * x : ℤ).natAbs, ?_⟩
  have hm' : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 + (d : ℤ) ^ 2 = m := by
    exact_mod_cast hm
  have hn' : (x : ℤ) ^ 2 + (y : ℤ) ^ 2 + (z : ℤ) ^ 2 + (w : ℤ) ^ 2 = n := by
    exact_mod_cast hn
  have key :
      (((a * x - b * y - c * z - d * w : ℤ).natAbs : ℤ)) ^ 2
        + (((a * y + b * x + c * w - d * z : ℤ).natAbs : ℤ)) ^ 2
        + (((a * z - b * w + c * x + d * y : ℤ).natAbs : ℤ)) ^ 2
        + (((a * w + b * z - c * y + d * x : ℤ).natAbs : ℤ)) ^ 2
      = (m : ℤ) * n := by
    rw [natAbs_sq_cast, natAbs_sq_cast, natAbs_sq_cast, natAbs_sq_cast,
        euler_four_squares (a : ℤ) b c d x y z w, hm', hn']
  exact_mod_cast key

/-- The four-square set is multiplicatively closed. -/
theorem mulClosed_isSumOfFourSquares : MulClosed IsSumOfFourSquares :=
  fun _ _ hm hn => isSumOfFourSquares_mul hm hn

/-- **Recovery one dimension up.** The very product `15` that fails for three
squares *is* a sum of four squares: `15 = 1² + 1² + 2² + 3²`. -/
theorem fifteen_isSumOfFourSquares : IsSumOfFourSquares 15 := ⟨1, 1, 2, 3, by norm_num⟩

/-- And `63 = 1² + 1² + 5² + 6²` likewise. -/
theorem sixtythree_isSumOfFourSquares : IsSumOfFourSquares 63 := ⟨1, 1, 5, 6, by norm_num⟩

end LagrangeFourSquaresOQ04OQ01
