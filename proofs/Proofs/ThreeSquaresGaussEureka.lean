/-
  Gauss's Eureka theorem from the three-square sufficiency axiom.

  CONTEXT.  `Proofs.ThreeSquares` formalizes Legendre's three-square theorem,
  proving the **necessity** direction axiom-free
  (`excluded_form_not_sum_three_sq`: a number of the form `4^a(8b+7)` is never a
  sum of three integer squares) and isolating the **sufficiency** direction as a
  single axiom
      not_excluded_form_is_sum_three_sq {n : ℕ} (h : ¬IsExcludedForm n) :
          ∃ a b c : ℤ, a^2 + b^2 + c^2 = n          (ThreeSquares.lean:1838)

  THIS FILE supplies a famous classical *consequence* of that sufficiency:

      **Gauss's Eureka theorem (1796):** every natural number is a sum of three
      triangular numbers `T(k) = k(k+1)/2`.  ("ΕΥΡΗΚΑ! num = Δ + Δ + Δ".)

  The reduction is entirely elementary and is proved here **axiom-free**.  Its
  two unconditional ingredients are:

    1. `eight_mul_add_three_iff` — for every `n`, the integer `8n+3` is a sum of
       three squares *iff* `n` is a sum of three triangular numbers.  The forward
       direction uses that `8n+3 ≡ 3 (mod 4)` forces all three squares odd, and
       an odd square is exactly `8·T(k)+1`; the backward direction is the same
       identity run in reverse.

    2. `not_excluded_eight_mul_add_three` — `8n+3` is never of the excluded form
       `4^a(8b+7)` (it is odd and `≡ 3 (mod 8) ≠ 7`).

  Combining (1) and (2): the three-square sufficiency, *applied only at the
  arithmetic progression `8n+3`*, yields Eureka.  We package this as the
  hypothesis-parametrised theorem `gauss_eureka_of_sufficiency`, which is
  therefore axiom-free; discharging its hypothesis with
  `ThreeSquares.not_excluded_form_is_sum_three_sq` (or the proved
  `ThreeSquares.legendre_three_squares`) gives the unconditional statement.

  In fact `eight_mul_add_three_iff` shows the two are *logically equivalent*:
  Eureka for `n` ⇔ three-square representability of `8n+3`.  Gauss's theorem is
  thus exactly the `8n+3`-slice of Legendre's sufficiency, no more and no less.

  No `sorry`, no `axiom`, no `native_decide`.
-/

import Mathlib
import Proofs.ThreeSquares

namespace ThreeSquaresGaussEureka

open ThreeSquares

/-- The `k`-th triangular number `T(k) = k(k+1)/2`. -/
def tri (k : ℕ) : ℕ := k * (k + 1) / 2

/-- `n` is a sum of three triangular numbers (the content of Gauss's Eureka
theorem: this predicate holds for every `n`). -/
def IsSumThreeTriangular (n : ℕ) : Prop :=
  ∃ a b c : ℕ, tri a + tri b + tri c = n

@[simp] lemma tri_zero : tri 0 = 0 := rfl
@[simp] lemma tri_one : tri 1 = 1 := rfl
@[simp] lemma tri_two : tri 2 = 3 := rfl

/-- Twice a triangular number is `k(k+1)` — the division is exact. -/
lemma two_mul_tri (k : ℕ) : 2 * tri k = k * (k + 1) := by
  unfold tri
  exact Nat.mul_div_cancel' (Nat.even_mul_succ_self k).two_dvd

/-- The defining identity: an odd square `(2a+1)²` equals `8·T(a) + 1`. -/
lemma sq_two_mul_add_one (a : ℕ) : (2 * a + 1) ^ 2 = 8 * tri a + 1 := by
  have h2 : 2 * tri a = a * (a + 1) := two_mul_tri a
  have hexp : (2 * a + 1) ^ 2 = 4 * (a * (a + 1)) + 1 := by ring
  rw [hexp, show (8 : ℕ) * tri a = 4 * (2 * tri a) by ring, h2]

/-- Every odd integer's square has the shape `8·T(j) + 1` for some natural `j`. -/
lemma odd_sq_eq_eight_tri_add_one {x : ℤ} (hx : Odd x) :
    ∃ j : ℕ, x ^ 2 = 8 * (tri j : ℤ) + 1 := by
  -- Reduce to the natural-number identity on `|x| = 2j+1`.
  obtain ⟨j, hj⟩ := Int.natAbs_odd.mpr hx
  refine ⟨j, ?_⟩
  have hnat : x.natAbs ^ 2 = 8 * tri j + 1 := by
    rw [hj]; exact sq_two_mul_add_one j
  have hcast : (x.natAbs : ℤ) ^ 2 = x ^ 2 := by
    rw [← Int.abs_eq_natAbs, sq_abs]
  calc x ^ 2 = (x.natAbs : ℤ) ^ 2 := hcast.symm
    _ = ((x.natAbs ^ 2 : ℕ) : ℤ) := by push_cast; ring
    _ = ((8 * tri j + 1 : ℕ) : ℤ) := by rw [hnat]
    _ = 8 * (tri j : ℤ) + 1 := by push_cast; ring

/-- An integer whose square is `≡ 1 (mod 4)` is odd. -/
lemma odd_of_sq_mod_four_one {x : ℤ} (h : x ^ 2 % 4 = 1) : Odd x := by
  rcases Int.even_or_odd x with he | ho
  · exfalso
    obtain ⟨m, hm⟩ := he
    have hx2 : x ^ 2 = 4 * m ^ 2 := by rw [hm]; ring
    omega
  · exact ho

/-- **Key equivalence.** `8n+3` is a sum of three integer squares **iff** `n` is
a sum of three triangular numbers. -/
theorem eight_mul_add_three_iff (n : ℕ) :
    (∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = 8 * (n : ℤ) + 3) ↔
      IsSumThreeTriangular n := by
  constructor
  · -- Forward: a representation of `8n+3` is built from three odd squares.
    rintro ⟨x, y, z, h⟩
    -- Each square is `≡ 1 (mod 4)`, hence each of `x, y, z` is odd.
    have hx4 := int_sq_mod_four x
    have hy4 := int_sq_mod_four y
    have hz4 := int_sq_mod_four z
    have hsum : (x ^ 2 + y ^ 2 + z ^ 2) % 4 = 3 := by rw [h]; omega
    have hall : x ^ 2 % 4 = 1 ∧ y ^ 2 % 4 = 1 ∧ z ^ 2 % 4 = 1 := by omega
    have hxo : Odd x := odd_of_sq_mod_four_one hall.1
    have hyo : Odd y := odd_of_sq_mod_four_one hall.2.1
    have hzo : Odd z := odd_of_sq_mod_four_one hall.2.2
    obtain ⟨jx, hjx⟩ := odd_sq_eq_eight_tri_add_one hxo
    obtain ⟨jy, hjy⟩ := odd_sq_eq_eight_tri_add_one hyo
    obtain ⟨jz, hjz⟩ := odd_sq_eq_eight_tri_add_one hzo
    refine ⟨jx, jy, jz, ?_⟩
    have hZ : ((tri jx + tri jy + tri jz : ℕ) : ℤ) = (n : ℤ) := by
      push_cast
      rw [hjx, hjy, hjz] at h
      linarith
    exact_mod_cast hZ
  · -- Backward: `(2a+1)² + (2b+1)² + (2c+1)² = 8(T a + T b + T c) + 3`.
    rintro ⟨a, b, c, habc⟩
    refine ⟨2 * (a : ℤ) + 1, 2 * (b : ℤ) + 1, 2 * (c : ℤ) + 1, ?_⟩
    have keya : (2 * (a : ℤ) + 1) ^ 2 = 8 * (tri a : ℤ) + 1 := by
      exact_mod_cast sq_two_mul_add_one a
    have keyb : (2 * (b : ℤ) + 1) ^ 2 = 8 * (tri b : ℤ) + 1 := by
      exact_mod_cast sq_two_mul_add_one b
    have keyc : (2 * (c : ℤ) + 1) ^ 2 = 8 * (tri c : ℤ) + 1 := by
      exact_mod_cast sq_two_mul_add_one c
    have hsum : (tri a : ℤ) + (tri b : ℤ) + (tri c : ℤ) = (n : ℤ) := by
      exact_mod_cast habc
    rw [keya, keyb, keyc]; linarith

/-- `8n+3` is never of the excluded form `4^a(8b+7)`: it is odd and `≡ 3 (mod 8)`. -/
theorem not_excluded_eight_mul_add_three (n : ℕ) :
    ¬ ThreeSquares.IsExcludedForm (8 * n + 3) := by
  have hodd : Odd (8 * n + 3) := ⟨4 * n + 1, by ring⟩
  rw [ThreeSquares.odd_excluded_iff hodd]
  omega

/-- **Gauss's Eureka theorem, reduced to three-square sufficiency.**

Given the sufficiency direction of Legendre's three-square theorem (as a
hypothesis `suff`), every natural number is a sum of three triangular numbers.
This theorem is *axiom-free*; instantiating `suff` with
`ThreeSquares.not_excluded_form_is_sum_three_sq` (or the proved
`ThreeSquares.legendre_three_squares`) yields the unconditional Eureka theorem.

The reduction invokes sufficiency only at the arithmetic progression `8n+3`. -/
theorem gauss_eureka_of_sufficiency
    (suff : ∀ m : ℕ, ¬ ThreeSquares.IsExcludedForm m →
      ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = m)
    (n : ℕ) : IsSumThreeTriangular n := by
  obtain ⟨x, y, z, hxyz⟩ := suff (8 * n + 3) (not_excluded_eight_mul_add_three n)
  apply (eight_mul_add_three_iff n).mp
  exact ⟨x, y, z, by push_cast at hxyz ⊢; linarith⟩

/-- The logical equivalence made explicit: Eureka for `n` holds **iff** `8n+3`
is a sum of three squares.  Gauss's theorem is precisely the `8n+3`-slice of
Legendre's sufficiency. -/
theorem eureka_iff_three_square_repr (n : ℕ) :
    IsSumThreeTriangular n ↔
      ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = 8 * (n : ℤ) + 3 :=
  (eight_mul_add_three_iff n).symm

end ThreeSquaresGaussEureka
