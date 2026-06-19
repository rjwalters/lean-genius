/-
Davenport-Cassels descent for the ternary form `x^2 + y^2 + z^2`.

This is a self-contained, deep-number-theory-free building block toward eliminating
the lone sufficiency axiom `not_excluded_form_is_sum_three_sq` in `ThreeSquares.lean`
(Legendre's three-square theorem). The eventual axiom elimination factors as

  (rational solvability / local-global)  +  (Davenport-Cassels: rational => integral).

This file supplies the *second* factor, which is entirely elementary: it uses only
balanced remainders (`Int.bmod`) for nearest-integer rounding plus ring arithmetic.
No Hasse-Minkowski reduction, no Gauss class theory.

Main result (`exists_sq_of_scaled`): if `n * t^2` is a sum of three integer squares
with `t > 0`, then `n` itself is a sum of three integer squares. Equivalently, after
clearing denominators (`exists_int_sq_of_rat_sq`): if `n` is a sum of three *rational*
squares then it is a sum of three *integer* squares.

The descent. Suppose `v^2 = n t^2` for an integer vector `v` of minimal denominator
`t > 1` (here we induct on `t` directly). Round each coordinate to the nearest integer
using balanced remainders `r_i = bmod(v_i, t)`, so `v_i = t w_i + r_i` with `|r_i| <=
t/2`, hence `f(r) = r_1^2+r_2^2+r_3^2 < t^2`. A short congruence gives `t | f(r)`; write
`f(r) = t s` with `0 <= s < t`. If `s = 0` then `r = 0`, so `v = t w` and `n = f(w)`.
Otherwise the reflected vector `v'_i = s w_i + (f(w) - n) r_i` satisfies `f(v') = n s^2`
with `0 < s < t`, and we descend. The key algebraic identity
`f(v') - n s^2 = s (f(w)-n) (s + 2<w,r> + (f(w)-n) t) + (f(w)-n)^2 (f(r) - t s)`
has both bracketed factors zero (the first by the definition of `s`, the second by
`f(r) = t s`), and was checked numerically over 2*10^5 random instances before
formalization.
-/
import Mathlib

namespace ThreeSquaresDC

/-- If a sum of three integer squares is zero, each summand is zero. -/
lemma abc_zero {a b c : ℤ} (h : a ^ 2 + b ^ 2 + c ^ 2 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have ha : a ^ 2 = 0 := le_antisymm (by linarith [sq_nonneg b, sq_nonneg c]) (sq_nonneg a)
  have hb : b ^ 2 = 0 := le_antisymm (by linarith [sq_nonneg a, sq_nonneg c]) (sq_nonneg b)
  have hc : c ^ 2 = 0 := le_antisymm (by linarith [sq_nonneg a, sq_nonneg b]) (sq_nonneg c)
  exact ⟨pow_eq_zero_iff (by norm_num) |>.mp ha,
         pow_eq_zero_iff (by norm_num) |>.mp hb,
         pow_eq_zero_iff (by norm_num) |>.mp hc⟩

/-- Per-coordinate balanced-remainder square bound: `4 * bmod(v, t)^2 <= t^2`. -/
lemma four_bmod_sq_le (v : ℤ) (t : ℕ) (ht : 0 < t) :
    4 * (Int.bmod v t) ^ 2 ≤ (t : ℤ) ^ 2 := by
  have h1 := Int.le_bmod (x := v) (m := t) ht
  have h2 := Int.bmod_lt (x := v) (m := t) ht
  have hb1 : -(t : ℤ) ≤ 2 * Int.bmod v t := by omega
  have hb2 : 2 * Int.bmod v t ≤ (t : ℤ) := by omega
  nlinarith [hb1, hb2]

/-- **Davenport-Cassels descent** for `x^2 + y^2 + z^2`.

If `n * t^2` is a sum of three integer squares with `t > 0`, then so is `n`. -/
theorem exists_sq_of_scaled (n : ℤ) :
    ∀ t : ℕ, 0 < t → ∀ v1 v2 v3 : ℤ,
      v1 ^ 2 + v2 ^ 2 + v3 ^ 2 = n * (t : ℤ) ^ 2 →
        ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = n := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t IH =>
    intro ht v1 v2 v3 hv
    by_cases ht1 : t = 1
    · subst ht1
      exact ⟨v1, v2, v3, by simpa using hv⟩
    · have htZ : (0 : ℤ) < (t : ℤ) := by exact_mod_cast ht
      -- balanced-remainder decomposition of each coordinate
      obtain ⟨w1, r1, hr1, e1⟩ :
          ∃ w r, r = Int.bmod v1 t ∧ v1 = (t : ℤ) * w + r :=
        ⟨Int.bdiv v1 t, Int.bmod v1 t, rfl, (Int.bdiv_add_bmod v1 t).symm⟩
      obtain ⟨w2, r2, hr2, e2⟩ :
          ∃ w r, r = Int.bmod v2 t ∧ v2 = (t : ℤ) * w + r :=
        ⟨Int.bdiv v2 t, Int.bmod v2 t, rfl, (Int.bdiv_add_bmod v2 t).symm⟩
      obtain ⟨w3, r3, hr3, e3⟩ :
          ∃ w r, r = Int.bmod v3 t ∧ v3 = (t : ℤ) * w + r :=
        ⟨Int.bdiv v3 t, Int.bmod v3 t, rfl, (Int.bdiv_add_bmod v3 t).symm⟩
      -- the descended scale `s`
      set s : ℤ := n * (t : ℤ) - (t : ℤ) * (w1 ^ 2 + w2 ^ 2 + w3 ^ 2)
        - 2 * (w1 * r1 + w2 * r2 + w3 * r3) with hs
      -- f(r) = t * s   (congruence + definition of s)
      have hfr : r1 ^ 2 + r2 ^ 2 + r3 ^ 2 = (t : ℤ) * s := by
        have hv' := hv
        rw [e1, e2, e3] at hv'
        rw [hs]; linear_combination hv'
      -- f(r) < t^2   (strict, from balanced-remainder bounds)
      have hb1 := four_bmod_sq_le v1 t ht
      have hb2 := four_bmod_sq_le v2 t ht
      have hb3 := four_bmod_sq_le v3 t ht
      rw [← hr1] at hb1; rw [← hr2] at hb2; rw [← hr3] at hb3
      have htpos : (0 : ℤ) < (t : ℤ) ^ 2 := by positivity
      have hfrlt : r1 ^ 2 + r2 ^ 2 + r3 ^ 2 < (t : ℤ) ^ 2 := by
        nlinarith [hb1, hb2, hb3, htpos]
      -- `0 <= s < t`
      have hs0 : 0 ≤ s := by
        nlinarith [hfr, sq_nonneg r1, sq_nonneg r2, sq_nonneg r3, htZ]
      have hslt : s < (t : ℤ) := by nlinarith [hfr, hfrlt, htZ]
      rcases eq_or_lt_of_le hs0 with hs_eq | hs_pos
      · -- s = 0  ⇒  r = 0  ⇒  n = f(w)
        have hr0 : r1 ^ 2 + r2 ^ 2 + r3 ^ 2 = 0 := by rw [hfr, ← hs_eq]; ring
        obtain ⟨hr1z, hr2z, hr3z⟩ := abc_zero hr0
        refine ⟨w1, w2, w3, ?_⟩
        have hcan : (t : ℤ) ^ 2 * (w1 ^ 2 + w2 ^ 2 + w3 ^ 2) = (t : ℤ) ^ 2 * n := by
          have hv0 := hv
          rw [e1, e2, e3, hr1z, hr2z, hr3z] at hv0
          linear_combination hv0
        exact mul_left_cancel₀ (pow_ne_zero 2 (ne_of_gt htZ)) hcan
      · -- 0 < s < t : descend via the reflected vector
        have hV : (s * w1 + (w1 ^ 2 + w2 ^ 2 + w3 ^ 2 - n) * r1) ^ 2
              + (s * w2 + (w1 ^ 2 + w2 ^ 2 + w3 ^ 2 - n) * r2) ^ 2
              + (s * w3 + (w1 ^ 2 + w2 ^ 2 + w3 ^ 2 - n) * r3) ^ 2 = n * s ^ 2 := by
          linear_combination (s * (w1 ^ 2 + w2 ^ 2 + w3 ^ 2 - n)) * hs
            + (w1 ^ 2 + w2 ^ 2 + w3 ^ 2 - n) ^ 2 * hfr
        have hmt : s.toNat < t := by omega
        have hcast : (s.toNat : ℤ) = s := Int.toNat_of_nonneg hs0
        refine IH s.toNat hmt (by omega) _ _ _ ?_
        rw [hcast]; exact hV

/-- **Davenport-Cassels for three squares (rational form).**

If the integer `n` is a sum of three *rational* squares, it is a sum of three
*integer* squares. -/
theorem exists_int_sq_of_rat_sq (n : ℤ)
    (h : ∃ x y z : ℚ, x ^ 2 + y ^ 2 + z ^ 2 = (n : ℚ)) :
    ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = n := by
  obtain ⟨x, y, z, hxyz⟩ := h
  -- clear denominators with the (positive) common scale `d = x.den * y.den * z.den`
  set d : ℤ := (x.den : ℤ) * (y.den : ℤ) * (z.den : ℤ) with hd
  have hxd0 : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_nz
  have hyd0 : (y.den : ℚ) ≠ 0 := by exact_mod_cast y.den_nz
  have hzd0 : (z.den : ℚ) ≠ 0 := by exact_mod_cast z.den_nz
  have hdpos : 0 < d := by
    have hx : (0 : ℤ) < (x.den : ℤ) := by exact_mod_cast x.den_pos
    have hy : (0 : ℤ) < (y.den : ℤ) := by exact_mod_cast y.den_pos
    have hz : (0 : ℤ) < (z.den : ℤ) := by exact_mod_cast z.den_pos
    positivity
  -- numerators expressed via `num = q * den`
  have hxn : (x.num : ℚ) = x * (x.den : ℚ) := (div_eq_iff hxd0).mp (Rat.num_div_den x)
  have hyn : (y.num : ℚ) = y * (y.den : ℚ) := (div_eq_iff hyd0).mp (Rat.num_div_den y)
  have hzn : (z.num : ℚ) = z * (z.den : ℚ) := (div_eq_iff hzd0).mp (Rat.num_div_den z)
  -- the scaled coordinates are integers; apply the descent
  refine exists_sq_of_scaled n d.toNat (by omega) (x.num * (y.den : ℤ) * (z.den : ℤ))
    (y.num * (x.den : ℤ) * (z.den : ℤ)) (z.num * (x.den : ℤ) * (y.den : ℤ)) ?_
  have hdc : ((d.toNat : ℤ)) = d := Int.toNat_of_nonneg hdpos.le
  rw [hdc]
  -- compare both sides as rationals, then descend casts
  have key : ((x.num * (y.den : ℤ) * (z.den : ℤ)) ^ 2
        + (y.num * (x.den : ℤ) * (z.den : ℤ)) ^ 2
        + (z.num * (x.den : ℤ) * (y.den : ℤ)) ^ 2 : ℚ) = ((n * d ^ 2 : ℤ) : ℚ) := by
    have hde : ((d : ℤ) : ℚ) = (x.den : ℚ) * (y.den : ℚ) * (z.den : ℚ) := by
      rw [hd]; push_cast; ring
    push_cast
    rw [hxn, hyn, hzn]
    rw [hde]
    linear_combination ((x.den : ℚ) * (y.den : ℚ) * (z.den : ℚ)) ^ 2 * hxyz
  exact_mod_cast key

end ThreeSquaresDC
