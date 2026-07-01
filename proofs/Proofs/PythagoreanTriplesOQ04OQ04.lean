import Mathlib.NumberTheory.SumFourSquares
import Mathlib.Tactic

/-
# Sums of Three and Four Squares: Lagrange's Theorem and Legendre's Obstruction
  (pythagorean-triples-oq-04-oq-04)

The two-square theorem (parent `pythagorean-triples-oq-04`) tells us *exactly*
which numbers are sums of two squares, and the answer is governed by a
congruence obstruction mod 4. This file extends the story to **three** and
**four** squares and contrasts their obstruction patterns.

The picture sharpens dramatically as the number of squares grows:

  * **Four squares — no obstruction at all.** Lagrange's four-square theorem
    (1770) says *every* natural number is a sum of four squares. We package
    Mathlib's `Nat.sum_four_squares` as `sum_four_squares`. There is no
    congruence class that four squares cannot reach.

  * **Three squares — a genuine obstruction.** Legendre's three-square theorem
    says `n` is a sum of three squares **iff** `n` is *not* of the form
    `4^a (8b + 7)`. The hard *sufficiency* direction (every other number *is*
    a sum of three squares) needs the deep theory of ternary quadratic forms
    and is left open here. But the **necessity** direction — that no number of
    the form `4^a (8b + 7)` is a sum of three squares — is completely
    elementary, and we prove it here from scratch:
      - squares are `0, 1, 4` mod `8`, so a sum of three squares is never
        `7` mod `8` (this kills the base case `a = 0`);
      - a `4`-power descent: if `4n` is a sum of three squares then so is `n`
        (all three squares must be even), which strips the powers of `4`.

So the contrast is: **two squares** ↦ obstruction mod 4 (`n ≡ 3`),
**three squares** ↦ obstruction `4^a(8b+7)`, **four squares** ↦ no obstruction.

Status: 0 axioms, 0 sorries (necessity direction of Legendre; Lagrange in full).
-/

namespace PythagoreanTriplesOQ04OQ04

/-- `n` is a sum of three squares. -/
def IsSumThreeSquares (n : ℕ) : Prop := ∃ a b c : ℕ, a ^ 2 + b ^ 2 + c ^ 2 = n

-- ============================================================================
-- Part I: Lagrange's four-square theorem — no obstruction
-- ============================================================================

/-- **Lagrange's four-square theorem.** Every natural number is a sum of four
squares. Packaged from Mathlib's `Nat.sum_four_squares`, whose proof runs through
the arithmetic of the quaternions / the descent of Euler's four-square identity.
The point of stating it here is the *contrast*: unlike two or three squares,
four squares have **no** congruence obstruction whatsoever. -/
theorem sum_four_squares (n : ℕ) :
    ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n :=
  Nat.sum_four_squares n

-- ============================================================================
-- Part II: The mod-8 obstruction (base case of Legendre necessity)
-- ============================================================================

/-- A perfect square is `0`, `1`, or `4` modulo `8`. -/
theorem sq_mod_eight (n : ℕ) : n ^ 2 % 8 = 0 ∨ n ^ 2 % 8 = 1 ∨ n ^ 2 % 8 = 4 := by
  have e : n ^ 2 % 8 = (n % 8) ^ 2 % 8 := by rw [Nat.pow_mod]
  have h : n % 8 < 8 := Nat.mod_lt _ (by norm_num)
  interval_cases (n % 8) <;> simp_all

/-- **The mod-8 obstruction.** A sum of three squares is never congruent to `7`
modulo `8`: each square contributes `0`, `1`, or `4`, and no three of those sum
to `7` mod `8`. This is the base-case heart of Legendre's necessity direction. -/
theorem sum_three_squares_mod_eight_ne_seven (a b c : ℕ) :
    (a ^ 2 + b ^ 2 + c ^ 2) % 8 ≠ 7 := by
  have ha := sq_mod_eight a
  have hb := sq_mod_eight b
  have hc := sq_mod_eight c
  omega

-- ============================================================================
-- Part III: The 4-power descent
-- ============================================================================

/-- A perfect square is `0` or `1` modulo `4`. -/
theorem sq_mod_four (n : ℕ) : n ^ 2 % 4 = 0 ∨ n ^ 2 % 4 = 1 := by
  have e : n ^ 2 % 4 = (n % 4) ^ 2 % 4 := by rw [Nat.pow_mod]
  have h : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases (n % 4) <;> simp_all

/-- If a square is `0` mod `4`, its root is even. (An odd number squared is
`1` mod `4`.) -/
theorem two_dvd_of_sq_mod_four_eq_zero {n : ℕ} (h : n ^ 2 % 4 = 0) : 2 ∣ n := by
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨r, rfl⟩ := he
    exact ⟨r, by ring⟩
  · exfalso
    obtain ⟨k, rfl⟩ := ho
    have hsq : (2 * k + 1) ^ 2 = 4 * (k ^ 2 + k) + 1 := by ring
    rw [hsq] at h
    omega

/-- **The 4-power descent.** If `4 * n` is a sum of three squares, then so is `n`.
Because `4n ≡ 0 (mod 4)` forces each of the three squares to be `0 (mod 4)`, so
all three roots are even; halving each root divides the total by `4`. -/
theorem three_squares_descent {n : ℕ} (h : IsSumThreeSquares (4 * n)) :
    IsSumThreeSquares n := by
  obtain ⟨a, b, c, habc⟩ := h
  -- Each square is 0 mod 4 because their sum is 4n ≡ 0 mod 4.
  have ha4 : a ^ 2 % 4 = 0 := by
    have := sq_mod_four a; have := sq_mod_four b; have := sq_mod_four c; omega
  have hb4 : b ^ 2 % 4 = 0 := by
    have := sq_mod_four a; have := sq_mod_four b; have := sq_mod_four c; omega
  have hc4 : c ^ 2 % 4 = 0 := by
    have := sq_mod_four a; have := sq_mod_four b; have := sq_mod_four c; omega
  -- Hence each root is even.
  obtain ⟨a', rfl⟩ := two_dvd_of_sq_mod_four_eq_zero ha4
  obtain ⟨b', rfl⟩ := two_dvd_of_sq_mod_four_eq_zero hb4
  obtain ⟨c', rfl⟩ := two_dvd_of_sq_mod_four_eq_zero hc4
  refine ⟨a', b', c', ?_⟩
  -- 4 * (a'² + b'² + c'²) = 4 * n, cancel the 4.
  have key : 4 * (a' ^ 2 + b' ^ 2 + c' ^ 2) = 4 * n := by rw [← habc]; ring
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) key

-- ============================================================================
-- Part IV: Legendre's obstruction (necessity direction)
-- ============================================================================

/-- **Legendre's obstruction (necessity direction).** No number of the form
`4^a (8b + 7)` is a sum of three squares.

Proof by induction on `a`. The base case `a = 0` is the mod-8 obstruction:
`8b + 7 ≡ 7 (mod 8)`. The inductive step strips one factor of `4` via the descent
lemma: `4^(a+1)(8b+7) = 4 · 4^a(8b+7)`, and if the left side were a sum of three
squares the descent would make `4^a(8b+7)` one too, contradicting the hypothesis. -/
theorem not_sum_three_squares_legendre (a b : ℕ) :
    ¬ IsSumThreeSquares (4 ^ a * (8 * b + 7)) := by
  induction a with
  | zero =>
    rw [pow_zero, one_mul]
    rintro ⟨x, y, z, hxyz⟩
    have h7 : (x ^ 2 + y ^ 2 + z ^ 2) % 8 = 7 := by rw [hxyz]; omega
    exact sum_three_squares_mod_eight_ne_seven x y z h7
  | succ k ih =>
    intro h
    apply ih
    apply three_squares_descent
    rwa [show 4 ^ (k + 1) * (8 * b + 7) = 4 * (4 ^ k * (8 * b + 7)) by ring] at h

-- ============================================================================
-- Part V: Contrast in a single number — 7
-- ============================================================================

/-- `7` is **not** a sum of three squares (the smallest such number): it is the
`a = 0, b = 0` case of Legendre's obstruction. -/
theorem seven_not_sum_three_squares : ¬ IsSumThreeSquares 7 := by
  have := not_sum_three_squares_legendre 0 0
  simpa using this

/-- Yet `7` **is** a sum of four squares: `7 = 2² + 1² + 1² + 1²`. This exhibits
the exact gap between the three-square obstruction and Lagrange's four squares. -/
theorem seven_sum_four_squares : ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 7 :=
  ⟨2, 1, 1, 1, by norm_num⟩

/-- The three-square obstruction is nonempty at every scale: for each `a`, the
number `4^a · 7` is not a sum of three squares, but (by Lagrange) is a sum of
four squares. -/
theorem obstruction_persists (a : ℕ) :
    ¬ IsSumThreeSquares (4 ^ a * 7) ∧
      (∃ w x y z : ℕ, w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = 4 ^ a * 7) := by
  refine ⟨?_, sum_four_squares _⟩
  have := not_sum_three_squares_legendre a 0
  simpa using this

end PythagoreanTriplesOQ04OQ04
