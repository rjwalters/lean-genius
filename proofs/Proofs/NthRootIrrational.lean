/-
Proof: Irrationality of nth Roots of Non-Perfect Powers
Date: 2026-02-06
Research: sqrt2-irrational-oq-03
Method: General theorem via irrational_nrt_of_notint_nrt
-/

import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-
# Irrationality of nth Roots of Non-Perfect Powers

## What This Proves

We prove a general theorem: for any integers n ≥ 2 and m ≥ 1, if m is not
a perfect nth power (i.e., no integer k satisfies k^n = m), then the nth
root m^(1/n) is irrational.

This single result subsumes all of our existing specific irrationality proofs:
- √2, √3, √5, √6, √7 (square roots of non-perfect-squares)
- ∛2, ∛3, ∛5, ∛6, ∛7, ∛9, ∛10 (cube roots of non-perfect-cubes)
- ⁴√2, ⁴√3, etc. (fourth roots of non-fourth-powers)
- And infinitely many more

## Strategy

The proof follows a clean three-step pattern using Mathlib's
`irrational_nrt_of_notint_nrt`:

1. **Power identity**: Show that (m^(1/n))^n = m
2. **Not an integer**: Show that if m is not a perfect nth power,
   then m^(1/n) is not an integer (contrapositive: if it were integer k,
   then k^n = m, contradicting our hypothesis)
3. **Conclude irrationality**: Apply `irrational_nrt_of_notint_nrt`

## Significance

This is the natural generalization of the √2 irrationality proof.
The classical parity argument for √2 is specific to square roots,
but the algebraic argument via `irrational_nrt_of_notint_nrt`
works uniformly for all roots.
-/

namespace NthRootIrrational

/- ## The nth Root Function -/

/-- The real nth root of m: m^(1/n) -/
noncomputable def nthRoot (n : ℕ) (m : ℕ) : ℝ := (m : ℝ) ^ (1/(n : ℝ))

/- ## Power Identity -/

/-- Key property: (m^(1/n))^n = m, for n ≥ 1 and m ≥ 0.
    This is the fundamental identity that connects the nth root back
    to the original value. -/
theorem nthRoot_pow (n m : ℕ) (hn : 0 < n) :
    nthRoot n m ^ n = m := by
  unfold nthRoot
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ m)]
  simp [Nat.pos_iff_ne_zero.mp hn]

/- ## Not-an-Integer Lemma -/

/-- If m is not a perfect nth power, then m^(1/n) is not an integer.
    Contrapositive: if m^(1/n) = k for some integer k, then k^n = m,
    so m IS a perfect nth power. -/
theorem nthRoot_not_int (n m : ℕ) (hn : 0 < n)
    (hm : ¬ ∃ (k : ℤ), k ^ n = (m : ℤ)) :
    ¬ ∃ (k : ℤ), nthRoot n m = k := by
  intro ⟨k, hk⟩
  apply hm
  use k
  have h1 : nthRoot n m ^ n = m := nthRoot_pow n m hn
  rw [hk] at h1
  exact_mod_cast h1

/- ## The General Theorem -/

/-- **General Irrationality of nth Roots**

    For any n ≥ 2 and m ≥ 1, if m is not a perfect nth power
    (no integer k satisfies k^n = m), then m^(1/n) is irrational.

    This subsumes:
    - √2, √3, √5, √6, √7 (n=2, m not a perfect square)
    - ∛2, ∛3, ∛5, ∛7 (n=3, m not a perfect cube)
    - ⁴√2, ⁴√3 (n=4, m not a perfect 4th power)
    - And all higher roots -/
theorem irrational_nthRoot (n m : ℕ) (hn : 1 < n)
    (hm : ¬ ∃ (k : ℤ), k ^ n = (m : ℤ)) :
    Irrational (nthRoot n m) := by
  apply irrational_nrt_of_notint_nrt n m
  · exact_mod_cast nthRoot_pow n m (by omega)
  · exact nthRoot_not_int n m (by omega) hm
  · omega

/- ## Not-a-Perfect-Power Lemmas

   We prove specific instances using bounds and case analysis.
   For odd powers: k ≤ 0 ⟹ k^n ≤ 0, contradicting k^n = m > 0.
   For even powers: k^n = |k|^n, reducing to natural number case.
   In both cases: find upper bound, then use interval_cases.
-/

/-- 2 is not a perfect cube -/
theorem two_not_perfect_cube : ¬ ∃ (k : ℤ), k ^ 3 = 2 := by
  intro ⟨k, hk⟩
  have h1 : 0 < k := by
    by_contra h
    push_neg at h
    have hcube : k ^ 3 ≤ 0 := by
      have : k ^ 3 = k * k * k := by ring
      rw [this]; nlinarith
    omega
  have h2 : k < 2 := by
    by_contra h
    push_neg at h
    have hcube : k ^ 3 ≥ 8 := by
      have : k ^ 3 = k * k * k := by ring
      rw [this]; nlinarith
    omega
  have : k = 1 := by omega
  rw [this] at hk; norm_num at hk

/-- 3 is not a perfect cube -/
theorem three_not_perfect_cube : ¬ ∃ (k : ℤ), k ^ 3 = 3 := by
  intro ⟨k, hk⟩
  have h1 : 0 < k := by
    by_contra h; push_neg at h
    have : k ^ 3 ≤ 0 := by
      have : k ^ 3 = k * k * k := by ring
      rw [this]; nlinarith
    omega
  have h2 : k < 2 := by
    by_contra h; push_neg at h
    have : k ^ 3 ≥ 8 := by
      have : k ^ 3 = k * k * k := by ring
      rw [this]; nlinarith
    omega
  have : k = 1 := by omega
  rw [this] at hk; norm_num at hk

/-- 5 is not a perfect cube -/
theorem five_not_perfect_cube : ¬ ∃ (k : ℤ), k ^ 3 = 5 := by
  intro ⟨k, hk⟩
  have h1 : 0 < k := by
    by_contra h; push_neg at h
    have : k ^ 3 ≤ 0 := by
      have : k ^ 3 = k * k * k := by ring
      rw [this]; nlinarith
    omega
  have h2 : k < 2 := by
    by_contra h; push_neg at h
    have : k ^ 3 ≥ 8 := by
      have : k ^ 3 = k * k * k := by ring
      rw [this]; nlinarith
    omega
  have : k = 1 := by omega
  rw [this] at hk; norm_num at hk

/-- 2 is not a perfect square -/
theorem two_not_perfect_sq : ¬ ∃ (k : ℤ), k ^ 2 = 2 := by
  intro ⟨k, hk⟩
  have habs : (k.natAbs : ℤ) ^ 2 = 2 := by rw [Int.natAbs_sq]; exact hk
  have hle : k.natAbs ≤ 1 := by
    by_contra h; push_neg at h
    have : (k.natAbs : ℤ) ≥ 2 := by omega
    have : (k.natAbs : ℤ) ^ 2 ≥ 4 := by nlinarith
    omega
  interval_cases k.natAbs <;> omega

/-- 3 is not a perfect square -/
theorem three_not_perfect_sq : ¬ ∃ (k : ℤ), k ^ 2 = 3 := by
  intro ⟨k, hk⟩
  have habs : (k.natAbs : ℤ) ^ 2 = 3 := by rw [Int.natAbs_sq]; exact hk
  have hle : k.natAbs ≤ 1 := by
    by_contra h; push_neg at h
    have : (k.natAbs : ℤ) ≥ 2 := by omega
    have : (k.natAbs : ℤ) ^ 2 ≥ 4 := by nlinarith
    omega
  interval_cases k.natAbs <;> omega

/-- 5 is not a perfect square -/
theorem five_not_perfect_sq : ¬ ∃ (k : ℤ), k ^ 2 = 5 := by
  intro ⟨k, hk⟩
  have habs : (k.natAbs : ℤ) ^ 2 = 5 := by rw [Int.natAbs_sq]; exact hk
  have hle : k.natAbs ≤ 2 := by
    by_contra h; push_neg at h
    have : (k.natAbs : ℤ) ≥ 3 := by omega
    have : (k.natAbs : ℤ) ^ 2 ≥ 9 := by nlinarith
    omega
  interval_cases k.natAbs <;> omega

/-- 2 is not a perfect 4th power -/
theorem two_not_perfect_fourth : ¬ ∃ (k : ℤ), k ^ 4 = 2 := by
  intro ⟨k, hk⟩
  have habs : (k.natAbs : ℤ) ^ 2 = k ^ 2 := Int.natAbs_sq k
  have hnat : (k.natAbs : ℤ) ^ 4 = 2 := by
    have : (k.natAbs : ℤ) ^ 4 = ((k.natAbs : ℤ) ^ 2) ^ 2 := by ring
    rw [this, habs]; linarith [show k ^ 4 = (k ^ 2) ^ 2 from by ring]
  have hle : k.natAbs ≤ 1 := by
    by_contra h; push_neg at h
    have hge : (k.natAbs : ℤ) ≥ 2 := by omega
    have hge2 : (k.natAbs : ℤ) ^ 2 ≥ 4 := by nlinarith
    have : (k.natAbs : ℤ) ^ 4 ≥ 16 := by nlinarith
    omega
  interval_cases k.natAbs <;> omega

/-- 3 is not a perfect 4th power -/
theorem three_not_perfect_fourth : ¬ ∃ (k : ℤ), k ^ 4 = 3 := by
  intro ⟨k, hk⟩
  have habs : (k.natAbs : ℤ) ^ 2 = k ^ 2 := Int.natAbs_sq k
  have hnat : (k.natAbs : ℤ) ^ 4 = 3 := by
    have : (k.natAbs : ℤ) ^ 4 = ((k.natAbs : ℤ) ^ 2) ^ 2 := by ring
    rw [this, habs]; linarith [show k ^ 4 = (k ^ 2) ^ 2 from by ring]
  have hle : k.natAbs ≤ 1 := by
    by_contra h; push_neg at h
    have hge : (k.natAbs : ℤ) ≥ 2 := by omega
    have hge2 : (k.natAbs : ℤ) ^ 2 ≥ 4 := by nlinarith
    have : (k.natAbs : ℤ) ^ 4 ≥ 16 := by nlinarith
    omega
  interval_cases k.natAbs <;> omega

/-- 2 is not a perfect 5th power -/
theorem two_not_perfect_fifth : ¬ ∃ (k : ℤ), k ^ 5 = 2 := by
  intro ⟨k, hk⟩
  have h1 : 0 < k := by
    by_contra h; push_neg at h
    have hexp : k ^ 5 = k * (k * k) * (k * k) := by ring
    have hkk : 0 ≤ k * k := mul_self_nonneg k
    have : k * (k * k) ≤ 0 := by nlinarith
    have : k * (k * k) * (k * k) ≤ 0 := by nlinarith
    omega
  have h2 : k < 2 := by
    by_contra h; push_neg at h
    -- k ≥ 2: k^5 ≥ 2^5 = 32
    have : 2 ≤ k := h
    have hk2 : 4 ≤ k * k := by nlinarith
    have hk3 : 8 ≤ k * k * k := by nlinarith
    have hk4 : 16 ≤ k * k * k * k := by nlinarith
    have hk5 : 32 ≤ k * k * k * k * k := by nlinarith
    have hexp : k ^ 5 = k * k * k * k * k := by ring
    omega
  have : k = 1 := by omega
  rw [this] at hk; norm_num at hk

/- ## Concrete Corollaries: Square Roots -/

/-- √2 is irrational (2 is not a perfect square) -/
theorem irrational_sqrt2 : Irrational (nthRoot 2 2) :=
  irrational_nthRoot 2 2 (by norm_num) two_not_perfect_sq

/-- √3 is irrational -/
theorem irrational_sqrt3 : Irrational (nthRoot 2 3) :=
  irrational_nthRoot 2 3 (by norm_num) three_not_perfect_sq

/-- √5 is irrational -/
theorem irrational_sqrt5 : Irrational (nthRoot 2 5) :=
  irrational_nthRoot 2 5 (by norm_num) five_not_perfect_sq

/- ## Concrete Corollaries: Cube Roots -/

/-- ∛2 is irrational -/
theorem irrational_cbrt2 : Irrational (nthRoot 3 2) :=
  irrational_nthRoot 3 2 (by norm_num) two_not_perfect_cube

/-- ∛3 is irrational -/
theorem irrational_cbrt3 : Irrational (nthRoot 3 3) :=
  irrational_nthRoot 3 3 (by norm_num) three_not_perfect_cube

/-- ∛5 is irrational -/
theorem irrational_cbrt5 : Irrational (nthRoot 3 5) :=
  irrational_nthRoot 3 5 (by norm_num) five_not_perfect_cube

/- ## Concrete Corollaries: Fourth Roots -/

/-- ⁴√2 is irrational -/
theorem irrational_fourthrt2 : Irrational (nthRoot 4 2) :=
  irrational_nthRoot 4 2 (by norm_num) two_not_perfect_fourth

/-- ⁴√3 is irrational -/
theorem irrational_fourthrt3 : Irrational (nthRoot 4 3) :=
  irrational_nthRoot 4 3 (by norm_num) three_not_perfect_fourth

/- ## Fifth Roots -/

/-- ⁵√2 is irrational -/
theorem irrational_fifthrt2 : Irrational (nthRoot 5 2) :=
  irrational_nthRoot 5 2 (by norm_num) two_not_perfect_fifth

/- ## The Characterization -/

/-- For n ≥ 1, if m = k^n for some natural k, then m^(1/n) = k (rational).
    This is the converse direction, showing the characterization is tight. -/
theorem nthRoot_of_perfect_power (n : ℕ) (k : ℕ) (hn : 0 < n) :
    nthRoot n (k ^ n) = k := by
  unfold nthRoot
  rw [Nat.cast_pow]
  rw [← Real.rpow_natCast (k : ℝ) n]
  rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ k)]
  simp [Nat.pos_iff_ne_zero.mp hn]

/-- Examples of perfect powers giving integer roots -/
example : nthRoot 2 4 = 2 := nthRoot_of_perfect_power 2 2 (by norm_num)
example : nthRoot 3 8 = 2 := nthRoot_of_perfect_power 3 2 (by norm_num)
example : nthRoot 3 27 = 3 := nthRoot_of_perfect_power 3 3 (by norm_num)
example : nthRoot 4 16 = 2 := nthRoot_of_perfect_power 4 2 (by norm_num)

end NthRootIrrational
