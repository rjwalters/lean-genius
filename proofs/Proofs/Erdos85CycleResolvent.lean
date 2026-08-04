import Proofs.Erdos85SecondOrderEvenDefect
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Data.Rat.Lemmas

/-!
# Cycle resolvent square factors

Polynomial identities underlying the determinant of `xI-A(C_n)`.
-/

namespace Erdos85

open Polynomial Polynomial.Chebyshev

/-- The standard discriminant identity for the rescaled Chebyshev
polynomials: `C_m^2-4=(X^2-4)S_{m-1}^2`. -/
theorem chebyshev_C_sq_sub_four (m : ℤ) :
    C ℤ m ^ 2 - 4 = (X ^ 2 - 4) * S ℤ (m - 1) ^ 2 := by
  have hs := S_sq_add_S_sq (R := ℤ) (m - 1)
  have hc := C_eq_S_sub_X_mul_S (R := ℤ) m
  rw [show m - 1 + 1 = m by ring] at hs
  rw [hc]
  linear_combination (norm := ring_nf) 4 * hs

/-- Even cycle factors have square class `(X-2)(X+2)`. -/
theorem chebyshev_C_even_sub_two (m : ℤ) :
    C ℤ (2 * m) - 2 =
      (X - 2) * (X + 2) * S ℤ (m - 1) ^ 2 := by
  have hmul := C_mul_C (R := ℤ) m m
  rw [sub_self, C_zero] at hmul
  rw [show m + m = 2 * m by ring] at hmul
  have hdisc := chebyshev_C_sq_sub_four m
  linear_combination (norm := ring_nf) hdisc - hmul

/-- Odd cycle factors have square class `X-2`. -/
theorem chebyshev_C_odd_sub_two (m : ℤ) :
    C ℤ (2 * m + 1) - 2 =
      (X - 2) * (S ℤ m + S ℤ (m - 1)) ^ 2 := by
  have hmul := C_mul_C (R := ℤ) m (m + 1)
  have hs := S_sq_add_S_sq (R := ℤ) (m - 1)
  have hrec := S_add_one (R := ℤ) m
  rw [show m + (m + 1) = 2 * m + 1 by ring,
    show m - (m + 1) = -1 by ring, C_neg_one] at hmul
  rw [show m - 1 + 1 = m by ring] at hs
  have hC : C ℤ (2 * m + 1) = C ℤ m * C ℤ (m + 1) - X := by
    rw [hmul]
    ring
  rw [hC, C_eq_S_sub_X_mul_S (R := ℤ) m,
    C_eq_S_sub_X_mul_S (R := ℤ) (m + 1),
    show m + 1 - 1 = m by ring, hrec]
  linear_combination (norm := ring_nf) (X + 2) * hs

/-- Evaluation of the even-cycle factor at the second-order spectral
parameter `d-1`. -/
theorem chebyshev_C_even_eval_secondOrder (d : ℤ) (m : ℤ) :
    (C ℤ (2 * m) - 2).eval (d - 1) =
      (d - 3) * (d + 1) * (S ℤ (m - 1)).eval (d - 1) ^ 2 := by
  rw [chebyshev_C_even_sub_two]
  simp only [eval_mul, eval_sub, eval_add, eval_pow, eval_X, eval_ofNat]
  ring

/-- Evaluation of the odd-cycle factor at the second-order spectral
parameter `d-1`. -/
theorem chebyshev_C_odd_eval_secondOrder (d : ℤ) (m : ℤ) :
    (C ℤ (2 * m + 1) - 2).eval (d - 1) =
      (d - 3) *
        ((S ℤ m + S ℤ (m - 1)).eval (d - 1)) ^ 2 := by
  rw [chebyshev_C_odd_sub_two]
  simp only [eval_mul, eval_sub, eval_add, eval_pow, eval_X, eval_ofNat]
  ring

/-- The extra even-cycle square class `(d-3)(d+1)` is not a rational
square for `d≥4`; it lies strictly between the consecutive integer squares
`(d-2)^2` and `(d-1)^2`. -/
theorem secondOrder_evenCycle_factor_not_isSquare (d : ℕ) (hd : 4 ≤ d) :
    ¬ IsSquare (((d - 3) * (d + 1) : ℕ) : ℚ) := by
  rw [Rat.isSquare_natCast_iff]
  rintro ⟨a, ha⟩
  obtain ⟨e, rfl⟩ : ∃ e : ℕ, d = e + 4 := ⟨d - 4, by omega⟩
  norm_num at ha ⊢
  have ha' : (e + 1) * (e + 5) = a * a := by
    simpa [show e + 4 - 3 = e + 1 by omega] using ha
  have hlower : (e + 2) ^ 2 < (e + 1) * (e + 5) := by nlinarith
  have hupper : (e + 1) * (e + 5) < (e + 3) ^ 2 := by nlinarith
  have ha_nonneg : 0 ≤ a := Nat.zero_le a
  have hleft : e + 2 < a := by nlinarith [ha']
  have hright : a < e + 3 := by nlinarith [ha']
  omega

/-- A nonsquare square class can occur an even number of times in a square
product.  This is the arithmetic step used after multiplying the individual
cycle factors. -/
theorem even_of_nonsquare_pow_mul_sq_isSquare
    {b s : ℚ} {e : ℕ} (hb : ¬ IsSquare b) (hb0 : b ≠ 0) (hs0 : s ≠ 0)
    (h : IsSquare (b ^ e * s ^ 2)) : Even e := by
  by_contra hnot
  have hodd : Odd e := Nat.not_even_iff_odd.mp hnot
  obtain ⟨k, hk⟩ := hodd
  obtain ⟨q, hq⟩ := h
  apply hb
  refine ⟨q / (b ^ k * s), ?_⟩
  have hbk : b ^ k ≠ 0 := pow_ne_zero _ hb0
  have hden : b ^ k * s ≠ 0 := mul_ne_zero hbk hs0
  rw [hk] at hq
  field_simp [hden]
  calc
    b * (b ^ k) ^ 2 * s ^ 2 = b ^ (2 * k + 1) * s ^ 2 := by
      rw [pow_add, pow_mul]
      ring
    _ = q ^ 2 := by rw [hq]; ring

/-- The integer resolvent factor associated with a cycle length. -/
noncomputable def cycleResolventAt (d r : ℕ) : ℤ :=
  (C ℤ (r : ℤ) - 2).eval ((d : ℤ) - 1)

/-- An even cycle contributes `(d-3)(d+1)` times an integer square. -/
theorem cycleResolventAt_of_even {d r : ℕ} (hr : Even r) :
    ∃ s : ℤ, cycleResolventAt d r =
      ((d : ℤ) - 3) * ((d : ℤ) + 1) * s ^ 2 := by
  obtain ⟨m, rfl⟩ := hr
  refine ⟨(S ℤ ((m : ℤ) - 1)).eval ((d : ℤ) - 1), ?_⟩
  simpa [cycleResolventAt, Nat.cast_add, two_mul] using
    chebyshev_C_even_eval_secondOrder (d : ℤ) (m : ℤ)

/-- An odd cycle contributes `d-3` times an integer square. -/
theorem cycleResolventAt_of_odd {d r : ℕ} (hr : Odd r) :
    ∃ s : ℤ, cycleResolventAt d r = ((d : ℤ) - 3) * s ^ 2 := by
  obtain ⟨m, rfl⟩ := hr
  refine ⟨(S ℤ (m : ℤ) + S ℤ ((m : ℤ) - 1)).eval ((d : ℤ) - 1), ?_⟩
  simpa [cycleResolventAt, Nat.cast_add, Nat.cast_one, two_mul] using
    chebyshev_C_odd_eval_secondOrder (d : ℤ) (m : ℤ)

/-- Number of even lengths in a cycle-length list. -/
def evenCycleCount : List ℕ → ℕ
  | [] => 0
  | r :: rs => if Even r then evenCycleCount rs + 1 else evenCycleCount rs

def oddCycleCount : List ℕ → ℕ
  | [] => 0
  | r :: rs => if Odd r then oddCycleCount rs + 1 else oddCycleCount rs

theorem evenCycleCount_add_oddCycleCount (rs : List ℕ) :
    evenCycleCount rs + oddCycleCount rs = rs.length := by
  induction rs with
  | nil => simp [evenCycleCount, oddCycleCount]
  | cons r rs ih =>
      by_cases he : Even r
      · have ho : ¬Odd r := Nat.not_odd_iff_even.mpr he
        simp [evenCycleCount, oddCycleCount, he, ho]
        omega
      · have ho : Odd r := Nat.not_even_iff_odd.mp he
        simp [evenCycleCount, oddCycleCount, he, ho]
        omega

theorem odd_oddCycleCount_iff_odd_sum (rs : List ℕ) :
    Odd (oddCycleCount rs) ↔ Odd rs.sum := by
  induction rs with
  | nil => simp [oddCycleCount]
  | cons r rs ih =>
      by_cases he : Even r
      · have ho : ¬Odd r := Nat.not_odd_iff_even.mpr he
        simp [oddCycleCount, he, ho, ih, Nat.odd_add]
      · have ho : Odd r := Nat.not_even_iff_odd.mp he
        simp [oddCycleCount, he, ho, ih, Nat.odd_add]

/-- Product square class for an arbitrary list of cycle lengths. -/
theorem cycleResolventAt_list_product (d : ℕ) (rs : List ℕ) :
    ∃ s : ℤ, (rs.map (cycleResolventAt d)).prod =
      ((d : ℤ) - 3) ^ rs.length *
        ((d : ℤ) + 1) ^ evenCycleCount rs * s ^ 2 := by
  induction rs with
  | nil =>
      exact ⟨1, by simp [evenCycleCount]⟩
  | cons r rs ih =>
      obtain ⟨t, ht⟩ := ih
      by_cases hr : Even r
      · obtain ⟨u, hu⟩ := cycleResolventAt_of_even (d := d) hr
        refine ⟨u * t, ?_⟩
        simp only [List.map_cons, List.prod_cons, List.length_cons,
          evenCycleCount, if_pos hr, hu, ht]
        rw [pow_succ, pow_succ]
        ring
      · have hodd : Odd r := Nat.not_even_iff_odd.mp hr
        obtain ⟨u, hu⟩ := cycleResolventAt_of_odd (d := d) hodd
        refine ⟨u * t, ?_⟩
        simp only [List.map_cons, List.prod_cons, List.length_cons,
          evenCycleCount, if_neg hr, hu, ht]
        rw [pow_succ]
        ring

theorem evenCycleCount_le_length (rs : List ℕ) :
    evenCycleCount rs ≤ rs.length := by
  induction rs with
  | nil => simp [evenCycleCount]
  | cons r rs ih =>
      simp only [evenCycleCount, List.length_cons]
      split <;> omega

theorem odd_length_sub_evenCycleCount_of_odd_sum
    (rs : List ℕ) (h : Odd rs.sum) :
    Odd (rs.length - evenCycleCount rs) := by
  have hcount := evenCycleCount_add_oddCycleCount rs
  have hsub : rs.length - evenCycleCount rs = oddCycleCount rs := by omega
  rw [hsub, odd_oddCycleCount_iff_odd_sum]
  exact h

/-- Once the standard component determinant factorization is supplied, the
global square identity forces an even number of even defect cycles. -/
theorem evenCycleCount_even_of_square_factorization
    (d : ℕ) (hd : 4 ≤ d) (rs : List ℕ)
    (hodd : Odd (rs.length - evenCycleCount rs))
    (q : ℚ)
    (hfactor : ((rs.map (cycleResolventAt d)).prod : ℚ) =
      (d - 3 : ℚ) * q ^ 2)
    (hprod0 : (rs.map (cycleResolventAt d)).prod ≠ 0) :
    Even (evenCycleCount rs) := by
  obtain ⟨s, hs⟩ := cycleResolventAt_list_product d rs
  let e := evenCycleCount rs
  obtain ⟨k, hk⟩ := hodd
  have helen : e ≤ rs.length := evenCycleCount_le_length rs
  have hlen : rs.length = e + (2 * k + 1) := by omega
  have ha0 : (d - 3 : ℚ) ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast (show d ≠ 3 by omega)
  have hc0 : (d + 1 : ℚ) ≠ 0 := by positivity
  have hs0 : (s : ℚ) ≠ 0 := by
    intro hz
    have hsZ : s = 0 := by exact_mod_cast hz
    apply hprod0
    rw [hs, hsZ]
    simp
  have hsQ : ((rs.map (cycleResolventAt d)).prod : ℚ) =
      (d - 3 : ℚ) ^ rs.length *
        (d + 1 : ℚ) ^ e * (s : ℚ) ^ 2 := by
    exact_mod_cast hs
  have hsq : IsSquare
      ((((d - 3) * (d + 1) : ℕ) : ℚ) ^ e *
        (((d - 3 : ℚ) ^ k * (s : ℚ)) ^ 2)) := by
    refine ⟨q, ?_⟩
    rw [hlen] at hsQ
    have hcast : (((d - 3) * (d + 1) : ℕ) : ℚ) =
        (d - 3 : ℚ) * (d + 1 : ℚ) := by
      push_cast
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [hcast]
    have hmain := hsQ.symm.trans hfactor
    apply (mul_left_cancel₀ ha0)
    calc
      (d - 3 : ℚ) *
          (((d - 3 : ℚ) * (d + 1 : ℚ)) ^ e *
            (((d - 3 : ℚ) ^ k * (s : ℚ)) ^ 2)) =
          (d - 3 : ℚ) ^ (e + (2 * k + 1)) *
            (d + 1 : ℚ) ^ e * (s : ℚ) ^ 2 := by
        simp only [mul_pow, ← pow_mul, pow_add]
        rw [show k * 2 = 2 * k by omega]
        ring
      _ = (d - 3 : ℚ) * (q * q) := by simpa [pow_two] using hmain
  change Even e
  refine even_of_nonsquare_pow_mul_sq_isSquare
    (b := ((((d - 3) * (d + 1) : ℕ) : ℚ)))
    (s := (d - 3 : ℚ) ^ k * (s : ℚ))
    (e := e) (secondOrder_evenCycle_factor_not_isSquare d hd) ?_ ?_ hsq
  · exact_mod_cast (mul_ne_zero (show d - 3 ≠ 0 by omega)
      (show d + 1 ≠ 0 by omega))
  · exact mul_ne_zero (pow_ne_zero _ ha0) hs0

/-- User-facing form: an odd total cycle order and the determinant square
factorization force an even number of even cycles. -/
theorem evenCycleCount_even_of_odd_sum_and_square_factorization
    (d : ℕ) (hd : 4 ≤ d) (rs : List ℕ) (hsum : Odd rs.sum)
    (q : ℚ)
    (hfactor : ((rs.map (cycleResolventAt d)).prod : ℚ) =
      (d - 3 : ℚ) * q ^ 2)
    (hprod0 : (rs.map (cycleResolventAt d)).prod ≠ 0) :
    Even (evenCycleCount rs) :=
  evenCycleCount_even_of_square_factorization d hd rs
    (odd_length_sub_evenCycleCount_of_odd_sum rs hsum) q hfactor hprod0

end Erdos85
