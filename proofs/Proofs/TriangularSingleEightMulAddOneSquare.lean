/-
  Triangular numbers and the `8n+1` perfect-square test.

  CONTEXT.  This is the *one*-summand base case of the triangular-rank hierarchy
  whose higher tiers already live in the gallery:

    * rank 3 (`Proofs.ThreeSquaresGaussEureka`): *every* natural is a sum of three
      triangular numbers (Gauss's Eureka theorem, the `8n+3` slice of Legendre's
      three-square sufficiency);
    * rank 2 (`Proofs.TwoTrianglesTwoSquares`): `n` is a sum of two triangular
      numbers iff `4n+1` is a sum of two squares;
    * rank 1 (THIS FILE): `n` is *itself* a triangular number iff `8n+1` is a
      perfect square.

  MAIN RESULT (`isTriangular_iff_isSquare`):

      For every natural number `n`,
          `n = T(k) = k(k+1)/2` for some `k`
      **iff**
          `8n + 1` is a perfect square.

  The bridge is the single defining identity `(2k+1)² = 8·T(k) + 1`.  The forward
  direction reads it left-to-right.  The backward direction notes that `8n+1` is
  odd, so any `r` with `r² = 8n+1` is odd, `r = 2k+1`, and the same identity run
  in reverse pins `n = T(k)`.  Since the index `k` is recovered exactly
  (`eq_tri_of_eight_mul_add_one`) and `T` is strictly monotone
  (`tri_strictMono`), the representation is unique when it exists.

  As `8n+1` being a perfect square is decidable, the characterization upgrades
  `IsTriangular` to a `DecidablePred` (`instance` below), giving a constant-cost
  triangular-number test.

  No `sorry`, no `axiom`, no `native_decide`.
-/

import Mathlib

namespace TriangularSingle

/-- The `k`-th triangular number `T(k) = k(k+1)/2`. -/
def tri (k : ℕ) : ℕ := k * (k + 1) / 2

/-- `n` is a triangular number: `n = T(k)` for some `k`. -/
def IsTriangular (n : ℕ) : Prop := ∃ k : ℕ, tri k = n

@[simp] lemma tri_zero : tri 0 = 0 := rfl
@[simp] lemma tri_one : tri 1 = 1 := rfl
@[simp] lemma tri_two : tri 2 = 3 := rfl

/-- Twice a triangular number is `k(k+1)` — the halving is exact. -/
lemma two_mul_tri (k : ℕ) : 2 * tri k = k * (k + 1) := by
  unfold tri
  exact Nat.mul_div_cancel' (Nat.even_mul_succ_self k).two_dvd

/-- **Defining identity.** The odd square `(2k+1)²` equals `8·T(k) + 1`. -/
lemma sq_two_mul_add_one (k : ℕ) : (2 * k + 1) ^ 2 = 8 * tri k + 1 := by
  have h : 2 * tri k = k * (k + 1) := two_mul_tri k
  have h8 : 8 * tri k = 4 * (k * (k + 1)) := by omega
  rw [h8]; ring

/-- `T` is strictly monotone, so a triangular index is unique when it exists. -/
lemma tri_strictMono : StrictMono tri := by
  intro a b hab
  have h2a : 2 * tri a = a * (a + 1) := two_mul_tri a
  have h2b : 2 * tri b = b * (b + 1) := two_mul_tri b
  have hlt : a * (a + 1) < b * (b + 1) := by nlinarith [hab]
  omega

/-- **Characterization of triangular numbers.** `n` is a triangular number iff
`8n + 1` is a perfect square. -/
theorem isTriangular_iff_isSquare (n : ℕ) :
    IsTriangular n ↔ IsSquare (8 * n + 1) := by
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨2 * k + 1, by rw [← pow_two]; exact (sq_two_mul_add_one k).symm⟩
  · rintro ⟨r, hr⟩
    -- `8n+1` is odd, hence `r·r` is odd, hence `r` is odd: `r = 2k+1`.
    have hodd : Odd (r * r) := by rw [← hr]; exact ⟨4 * n, by ring⟩
    obtain ⟨k, hk⟩ := (Nat.odd_mul.mp hodd).1
    refine ⟨k, ?_⟩
    have hval : 8 * tri k + 1 = 8 * n + 1 := by
      rw [← sq_two_mul_add_one k, hr, hk]; ring
    omega

/-- The triangular index is recovered exactly: if `8n+1 = (2k+1)²` then `n = T(k)`. -/
theorem eq_tri_of_eight_mul_add_one (n k : ℕ) (h : 8 * n + 1 = (2 * k + 1) ^ 2) :
    n = tri k := by
  have hkey := sq_two_mul_add_one k
  omega

/-- Being a perfect square is decidable, so the characterization makes
`IsTriangular` a decidable predicate: a constant-cost triangular-number test. -/
instance : DecidablePred IsTriangular := fun n =>
  decidable_of_iff _ (isTriangular_iff_isSquare n).symm

-- Sanity checks: `T₄ = 10`, `T₆ = 21`, while `5` and `8` are not triangular.
-- (`Nat.sqrt` does not reduce under kernel `decide`, so the negative cases are
-- closed through the characterization and a finite square-search instead.)
example : IsTriangular 10 := ⟨4, by norm_num [tri]⟩
example : IsTriangular 21 := ⟨6, by norm_num [tri]⟩

example : ¬ IsTriangular 5 := by
  rw [isTriangular_iff_isSquare]
  rintro ⟨r, hr⟩
  have hb : r ≤ 6 := by nlinarith [hr]
  interval_cases r <;> omega

example : ¬ IsTriangular 8 := by
  rw [isTriangular_iff_isSquare]
  rintro ⟨r, hr⟩
  have hb : r ≤ 8 := by nlinarith [hr]
  interval_cases r <;> omega

-- The square witness for `10`: `8·10 + 1 = 81 = 9²`.
example : IsSquare (8 * 10 + 1) := ⟨9, by norm_num⟩

end TriangularSingle
