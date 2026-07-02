/-
  Open Question (derived): Segner's Multiplicative Recurrence for Catalan Numbers

  Parent (combinations-formula-oq-02, "Catalan Numbers and Central Binomial Coefficients")
  proves the *additive* identity Cₙ·(n+1) = C(2n,n), the 4ⁿ bounds, monotonicity, and the
  convolution recurrence C_{n+1} = ∑ₖ Cₖ·C_{n-k}. Its header advertises a third recurrence —
  the *multiplicative* (Segner / Euler) ratio recurrence

        C_{n+1} = (2·(2n+1) / (n+2)) · Cₙ,

  i.e. in integer form

        C_{n+1}·(n+2) = 2·(2n+1)·Cₙ,

  but the parent file never proves it. This file supplies that proof, plus the sharp ratio
  bounds it yields, VERIFIED and AXIOM-FREE.

  The multiplicative recurrence is the practical way to *compute* Catalan numbers (no
  factorials, no subtraction, no convolution sum) and it pins the growth rate exactly:

        2·Cₙ ≤ C_{n+1} < 4·Cₙ        (for n ≥ 1),

  the discrete shadow of the asymptotic Cₙ ~ 4ⁿ / (n^{3/2}√π). We work with Mathlib's
  `catalan` and `Nat.centralBinom` (which agree with the parent's definitions) so the whole
  development is a few lines built on `Nat.succ_mul_centralBinom_succ`.

  References:
  - Segner (1758): the multiplicative recurrence for triangulation counts
  - Euler–Segner correspondence; Stanley, "Catalan Numbers" (2015)
  - Parent: CombinationsFormulaOQ02.lean

  Tags: combinatorics, catalan-numbers, central-binomial, recurrence, growth-bounds
-/

import Mathlib

namespace CatalanSegner

/-- Bridge to the central binomial coefficient: `Cₙ · (n+1) = C(2n,n)`.
    This is Mathlib's `catalan_eq_centralBinom_div` cleared of the division, using that
    `n+1` divides the central binomial coefficient. It matches the parent entry's
    `catalan_mul_succ`. -/
theorem catalan_mul_succ (n : ℕ) : catalan n * (n + 1) = Nat.centralBinom n := by
  rw [catalan_eq_centralBinom_div]
  exact Nat.div_mul_cancel (Nat.succ_dvd_centralBinom n)

/-- Catalan numbers are positive. (From the bridge: `Cₙ·(n+1) = C(2n,n) > 0`.) -/
theorem catalan_pos (n : ℕ) : 0 < catalan n := by
  rcases Nat.eq_zero_or_pos (catalan n) with h | h
  · have hb := catalan_mul_succ n
    rw [h, Nat.zero_mul] at hb
    exact absurd hb.symm (Nat.centralBinom_pos n).ne'
  · exact h

/-!
## Segner's multiplicative recurrence
-/

/-- **Segner's recurrence** (integer form): `C_{n+1}·(n+2) = 2·(2n+1)·Cₙ`.

    Proof: from the bridge, `C_{n+1}·(n+2) = C(2(n+1), n+1)` and `Cₙ·(n+1) = C(2n,n)`;
    Mathlib's `Nat.succ_mul_centralBinom_succ` gives `(n+1)·C(2(n+1),n+1) = 2(2n+1)·C(2n,n)`.
    Substituting and cancelling the common factor `n+1` yields the claim. -/
theorem catalan_ratio_recurrence (n : ℕ) :
    catalan (n + 1) * (n + 2) = 2 * (2 * n + 1) * catalan n := by
  have h1 : catalan (n + 1) * (n + 2) = Nat.centralBinom (n + 1) := by
    have h := catalan_mul_succ (n + 1)
    simpa [Nat.add_assoc] using h
  have h2 : catalan n * (n + 1) = Nat.centralBinom n := catalan_mul_succ n
  have h3 : (n + 1) * Nat.centralBinom (n + 1) = 2 * (2 * n + 1) * Nat.centralBinom n :=
    Nat.succ_mul_centralBinom_succ n
  have h4 : (n + 1) * (catalan (n + 1) * (n + 2))
      = (n + 1) * (2 * (2 * n + 1) * catalan n) := by
    rw [h1, h3, ← h2]; ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos n) h4

/-!
## Sharp ratio bounds

The recurrence multiplies `Cₙ` by `2(2n+1)/(n+2)`, a factor strictly between `2` and `4`
for `n ≥ 1`. This bounds the growth rate on both sides.
-/

/-- Upper ratio bound: `C_{n+1} < 4·Cₙ`. (Because `2(2n+1) < 4(n+2)`.) -/
theorem catalan_succ_lt_four_mul (n : ℕ) : catalan (n + 1) < 4 * catalan n := by
  have hpos := catalan_pos n
  have key : catalan (n + 1) * (n + 2) < (4 * catalan n) * (n + 2) := by
    rw [catalan_ratio_recurrence n]; nlinarith [hpos]
  exact lt_of_mul_lt_mul_right key (Nat.zero_le _)

/-- Lower ratio bound: `2·Cₙ ≤ C_{n+1}` for `n ≥ 1`. (Because `2(n+2) ≤ 2(2n+1)`.) -/
theorem two_mul_catalan_le_succ (n : ℕ) (hn : 1 ≤ n) :
    2 * catalan n ≤ catalan (n + 1) := by
  have hpos := catalan_pos n
  have key : (2 * catalan n) * (n + 2) ≤ catalan (n + 1) * (n + 2) := by
    rw [catalan_ratio_recurrence n]; nlinarith [hpos, hn]
  exact Nat.le_of_mul_le_mul_right key (by omega)

/-- Divisibility consequence: `n+2` divides `2·(2n+1)·Cₙ`, with quotient `C_{n+1}`.
    (Immediate from the recurrence.) -/
theorem succ_succ_dvd_two_mul (n : ℕ) : (n + 2) ∣ 2 * (2 * n + 1) * catalan n := by
  refine ⟨catalan (n + 1), ?_⟩
  rw [← catalan_ratio_recurrence n]; ring

/-- The multiplicative recurrence reproduces the value table without factorials:
    `C₅ = 42` from `C₄ = 14` via `C₅·6 = 2·9·14 = 252`. -/
example : catalan 5 * 6 = 2 * 9 * catalan 4 := catalan_ratio_recurrence 4

#check @catalan_ratio_recurrence
#check @catalan_succ_lt_four_mul
#check @two_mul_catalan_le_succ
#check @succ_succ_dvd_two_mul

end CatalanSegner
