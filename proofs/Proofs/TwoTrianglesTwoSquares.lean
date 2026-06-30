/-
  Sums of two triangular numbers and the `4n+1` two-square slice.

  CONTEXT.  This is the *two*-summand analogue of `Proofs.ThreeSquaresGaussEureka`
  (Gauss's Eureka theorem: every natural is a sum of three triangular numbers,
  the `8n+3` slice of Legendre's three-square sufficiency).  Whereas Eureka is
  conditional on the still-open three-square *sufficiency* axiom, the *two*-square
  theorem is fully available in Mathlib, so the result here is **unconditional and
  axiom-free**.

  MAIN RESULT (`isSumTwoTriangular_iff`):

      For every natural number `n`,
          `n` is a sum of two triangular numbers `T(k) = k(k+1)/2`
      **iff**
          `4n + 1` is a sum of two integer squares.

  The bridge is the classical change of variables
      `4·(T(a) + T(b)) + 1 = (a+b+1)² + (a−b)²`,
  a *rotation* of the lattice `(a,b) ↦ (a+b+1, a−b)`.  The forward direction
  reads it left-to-right.  The backward direction observes that `4n+1 ≡ 1 (mod 4)`
  forces one of the two squares even and the other odd, say `X = 2t`, `Y = 2s+1`;
  then the *inverse* rotation `p = s+t`, `q = s−t` (no division needed) gives
  `2n = p(p+1) + q(q+1)`, and each integer triangular value `k(k+1)/2` coincides
  with a natural triangular number (since `T(k) = T(−1−k)`).

  Composing with Mathlib's sum-of-two-squares characterization
  (`Nat.eq_sq_add_sq_iff`) turns this into a complete arithmetic test
  (`isSumTwoTriangular_iff_factorization`): `n` is a sum of two triangular numbers
  iff every prime `≡ 3 (mod 4)` divides `4n+1` to an even power.  (Note the naive
  "no prime factor `≡ 3 (mod 4)`" form is *false*: `n = 2 = T₁+T₁` while
  `4·2+1 = 9 = 3²`.)

  No `sorry`, no `axiom`, no `native_decide`.
-/

import Mathlib

namespace TwoTrianglesTwoSquares

/-- The `k`-th triangular number `T(k) = k(k+1)/2`. -/
def tri (k : ℕ) : ℕ := k * (k + 1) / 2

/-- `n` is a sum of two triangular numbers. -/
def IsSumTwoTriangular (n : ℕ) : Prop := ∃ a b : ℕ, tri a + tri b = n

@[simp] lemma tri_zero : tri 0 = 0 := rfl
@[simp] lemma tri_one : tri 1 = 1 := rfl
@[simp] lemma tri_two : tri 2 = 3 := rfl

/-- Twice a triangular number is `k(k+1)` — the division is exact. -/
lemma two_mul_tri (k : ℕ) : 2 * tri k = k * (k + 1) := by
  unfold tri
  exact Nat.mul_div_cancel' (Nat.even_mul_succ_self k).two_dvd

/-- Integer form of `two_mul_tri`. -/
lemma two_mul_tri_int (k : ℕ) : 2 * (tri k : ℤ) = (k : ℤ) * ((k : ℤ) + 1) := by
  exact_mod_cast two_mul_tri k

/-- For any integer index `k`, the integer `k(k+1)` equals `j(j+1)` for some
*natural* `j` — because `T(k) = T(−1−k)`, so negative indices give nothing new. -/
lemma exists_nat_tri_index (k : ℤ) : ∃ j : ℕ, (j : ℤ) * ((j : ℤ) + 1) = k * (k + 1) := by
  rcases le_or_gt 0 k with hk | hk
  · exact ⟨k.toNat, by rw [Int.toNat_of_nonneg hk]⟩
  · refine ⟨(-1 - k).toNat, ?_⟩
    have h : (0 : ℤ) ≤ -1 - k := by omega
    rw [Int.toNat_of_nonneg h]; ring

/-- For any integer `p`, `p(p+1)` is twice a natural triangular number. -/
lemma exists_nat_two_mul_tri (p : ℤ) : ∃ j : ℕ, 2 * (tri j : ℤ) = p * (p + 1) := by
  obtain ⟨j, hj⟩ := exists_nat_tri_index p
  exact ⟨j, by rw [two_mul_tri_int]; exact hj⟩

/-- The defining rotation identity:
`4·(T(a) + T(b)) + 1 = (a+b+1)² + (a−b)²`. -/
lemma sum_tri_identity (a b : ℕ) :
    4 * ((tri a : ℤ) + (tri b : ℤ)) + 1 = ((a : ℤ) + b + 1) ^ 2 + ((a : ℤ) - b) ^ 2 := by
  have hA := two_mul_tri_int a
  have hB := two_mul_tri_int b
  linear_combination 2 * hA + 2 * hB

/-- **Forward direction.** A sum of two triangular numbers makes `4n+1` a sum of
two integer squares. -/
theorem isSumTwoTriangular_to_sq (n : ℕ) (h : IsSumTwoTriangular n) :
    ∃ X Y : ℤ, X ^ 2 + Y ^ 2 = 4 * (n : ℤ) + 1 := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨(a : ℤ) + b + 1, (a : ℤ) - b, ?_⟩
  have hn : (tri a : ℤ) + (tri b : ℤ) = (n : ℤ) := by exact_mod_cast hab
  have hid := sum_tri_identity a b
  linarith [hid, hn]

/-- The arithmetic core of the backward direction: from
`(2s+1)² + (2t)² = 4n+1` produce `p, q` with `2n = p(p+1) + q(q+1)`. -/
lemma core_pq (n : ℕ) (s t : ℤ) (h : (2 * s + 1) ^ 2 + (2 * t) ^ 2 = 4 * (n : ℤ) + 1) :
    ∃ p q : ℤ, 2 * (n : ℤ) = p * (p + 1) + q * (q + 1) := by
  refine ⟨s + t, s - t, ?_⟩
  have hexp : (s + t) * ((s + t) + 1) + (s - t) * ((s - t) + 1)
      = 2 * s ^ 2 + 2 * t ^ 2 + 2 * s := by ring
  have h' : 4 * s ^ 2 + 4 * s + 1 + 4 * t ^ 2 = 4 * (n : ℤ) + 1 := by linear_combination h
  rw [hexp]; linarith [h']

/-- **Backward direction.** If `4n+1` is a sum of two integer squares then `n` is
a sum of two triangular numbers. -/
theorem sq_to_isSumTwoTriangular (n : ℕ)
    (h : ∃ X Y : ℤ, X ^ 2 + Y ^ 2 = 4 * (n : ℤ) + 1) : IsSumTwoTriangular n := by
  obtain ⟨X, Y, hXY⟩ := h
  -- Parity analysis: `4n+1 ≡ 1 (mod 4)` ⟹ exactly one of `X, Y` is odd.
  obtain ⟨p, q, hpq⟩ : ∃ p q : ℤ, 2 * (n : ℤ) = p * (p + 1) + q * (q + 1) := by
    rcases Int.even_or_odd X with hX | hX <;> rcases Int.even_or_odd Y with hY | hY
    · -- both even: contradiction (sum ≡ 0, not 1, mod 4)
      exfalso
      obtain ⟨a, ha⟩ := hX; obtain ⟨b, hb⟩ := hY
      have hcon : (4 : ℤ) * (a ^ 2 + b ^ 2) = 4 * (n : ℤ) + 1 := by
        rw [ha, hb] at hXY; linear_combination hXY
      have hdvd : (4 : ℤ) ∣ 1 := ⟨a ^ 2 + b ^ 2 - (n : ℤ), by linear_combination -hcon⟩
      exact absurd hdvd (by norm_num)
    · -- X even, Y odd
      obtain ⟨t, ht⟩ := hX; obtain ⟨s, hs⟩ := hY
      apply core_pq n s t
      rw [hs, ht] at hXY; linear_combination hXY
    · -- X odd, Y even
      obtain ⟨s, hs⟩ := hX; obtain ⟨t, ht⟩ := hY
      apply core_pq n s t
      rw [hs, ht] at hXY; linear_combination hXY
    · -- both odd: contradiction (sum ≡ 2, not 1, mod 4)
      exfalso
      obtain ⟨a, ha⟩ := hX; obtain ⟨b, hb⟩ := hY
      have hcon : (4 : ℤ) * (a ^ 2 + a + b ^ 2 + b) + 2 = 4 * (n : ℤ) + 1 := by
        rw [ha, hb] at hXY; linear_combination hXY
      have hdvd : (4 : ℤ) ∣ 1 := ⟨(n : ℤ) - (a ^ 2 + a + b ^ 2 + b), by linear_combination hcon⟩
      exact absurd hdvd (by norm_num)
  -- Convert the integer indices `p, q` to natural triangular numbers.
  obtain ⟨jp, hjp⟩ := exists_nat_two_mul_tri p
  obtain ⟨jq, hjq⟩ := exists_nat_two_mul_tri q
  refine ⟨jp, jq, ?_⟩
  have hsum : 2 * ((tri jp : ℤ) + (tri jq : ℤ)) = 2 * (n : ℤ) := by
    rw [hpq]; linear_combination hjp + hjq
  have : (tri jp : ℤ) + (tri jq : ℤ) = (n : ℤ) := by linarith [hsum]
  exact_mod_cast this

/-- **Main equivalence.** `n` is a sum of two triangular numbers **iff** `4n+1`
is a sum of two integer squares. -/
theorem isSumTwoTriangular_iff (n : ℕ) :
    IsSumTwoTriangular n ↔ ∃ X Y : ℤ, X ^ 2 + Y ^ 2 = 4 * (n : ℤ) + 1 :=
  ⟨isSumTwoTriangular_to_sq n, sq_to_isSumTwoTriangular n⟩

/-- Sum of two integer squares ↔ sum of two natural squares (the squared
quantities only depend on absolute values). -/
lemma int_sq_iff_nat_sq (m : ℕ) :
    (∃ X Y : ℤ, X ^ 2 + Y ^ 2 = (m : ℤ)) ↔ ∃ x y : ℕ, x ^ 2 + y ^ 2 = m := by
  constructor
  · rintro ⟨X, Y, h⟩
    refine ⟨X.natAbs, Y.natAbs, ?_⟩
    have hx : ((X.natAbs : ℤ)) ^ 2 = X ^ 2 := by rw [← Int.abs_eq_natAbs, sq_abs]
    have hy : ((Y.natAbs : ℤ)) ^ 2 = Y ^ 2 := by rw [← Int.abs_eq_natAbs, sq_abs]
    have : ((X.natAbs : ℤ)) ^ 2 + ((Y.natAbs : ℤ)) ^ 2 = (m : ℤ) := by rw [hx, hy]; exact h
    exact_mod_cast this
  · rintro ⟨x, y, h⟩; exact ⟨x, y, by exact_mod_cast h⟩

/-- Natural-number restatement of the main equivalence. -/
theorem isSumTwoTriangular_iff_nat (n : ℕ) :
    IsSumTwoTriangular n ↔ ∃ x y : ℕ, x ^ 2 + y ^ 2 = 4 * n + 1 := by
  rw [isSumTwoTriangular_iff]
  have hcast : (4 * (n : ℤ) + 1) = ((4 * n + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [hcast, int_sq_iff_nat_sq]

/-- **Complete arithmetic characterization** via Mathlib's two-square theorem.
`n` is a sum of two triangular numbers iff every prime `≡ 3 (mod 4)` divides
`4n+1` to an even power (`padicValNat q (4n+1)`, equivalently `(4n+1).factorization q`). -/
theorem isSumTwoTriangular_iff_factorization (n : ℕ) :
    IsSumTwoTriangular n ↔
      ∀ q ∈ (4 * n + 1).primeFactors, q % 4 = 3 → Even (padicValNat q (4 * n + 1)) := by
  rw [isSumTwoTriangular_iff_nat]
  have hflip : (∃ x y : ℕ, x ^ 2 + y ^ 2 = 4 * n + 1) ↔ (∃ a b : ℕ, 4 * n + 1 = a ^ 2 + b ^ 2) := by
    constructor <;> rintro ⟨a, b, h⟩ <;> exact ⟨a, b, h.symm⟩
  rw [hflip, Nat.eq_sq_add_sq_iff]

end TwoTrianglesTwoSquares
