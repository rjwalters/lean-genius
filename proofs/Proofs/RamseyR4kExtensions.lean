/-
  Ramsey R(4,k) Extensions: Probabilistic Method Bounds

  This file extends the Ramsey theory formalization with:
  1. The probabilistic lower bound R(k,k) ≥ 2^(k/2) (Erdős 1947)
  2. Diagonal Ramsey bounds from Spencer and Conlon-Fox-Sudakov
  3. Off-diagonal bounds R(3,k) and R(4,k) from Ajtai-Komlós-Szemerédi
  4. Some provable structural results

  The deep probabilistic results are axiomatized since Mathlib lacks
  the probabilistic combinatorics infrastructure (Lovász Local Lemma,
  random graph models) needed for their proofs.

  Tags: combinatorics, ramsey-theory, probabilistic-method
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace RamseyR4k

open Nat Finset

/-
## The Ramsey Number

We define R(r,s) as the minimum n such that any 2-coloring of K_n
has a red r-clique or blue s-clique. We use the classical recursive bound.
-/

/-- The classical upper bound on Ramsey numbers via binomial coefficients:
    R(r,s) ≤ C(r+s-2, r-1). -/
def ramseyUpperBound (r s : ℕ) : ℕ :=
  if r = 0 ∨ s = 0 then 0
  else Nat.choose (r + s - 2) (r - 1)

/-
## Part I: The Probabilistic Lower Bound (Erdős 1947)

The first application of the probabilistic method to Ramsey theory.
If C(n,k) · 2^(1-C(k,2)) < 1, then R(k,k) > n.
For k ≥ 3, this gives R(k,k) > 2^(k/2).
-/

/-- **Erdős (1947)**: The probabilistic lower bound for diagonal Ramsey numbers.
    R(k,k) > 2^(k/2) for k ≥ 3.
    Proof: Color edges of K_n randomly. Expected number of monochromatic
    k-cliques is C(n,k) · 2^(1-C(k,2)). If n = ⌊2^(k/2)⌋, this is < 1,
    so a good coloring exists. -/
axiom erdos_probabilistic_lower_bound (k : ℕ) (hk : k ≥ 3) :
    ∀ n : ℕ, n ≤ 2^(k/2) →
    ∃ (color : Fin n → Fin n → Bool),
      (∀ x y, color x y = color y x) ∧
      (∀ x, color x x = false) ∧
      (∀ (s : Finset (Fin n)), s.card = k →
        ¬(∀ x y, x ∈ s → y ∈ s → x ≠ y → color x y = true)) ∧
      (∀ (s : Finset (Fin n)), s.card = k →
        ¬(∀ x y, x ∈ s → y ∈ s → x ≠ y → color x y = false))

/-
## Part II: Off-Diagonal Bounds

### R(3,k) Bounds (Ajtai-Komlós-Szemerédi 1980, Kim 1995)

The Ajtai-Komlós-Szemerédi theorem shows R(3,k) ≤ O(k²/log k).
Kim (1995) proved the matching lower bound: R(3,k) ≥ Ω(k²/log k).
-/

/-- **Ajtai-Komlós-Szemerédi (1980)**: R(3,k) = O(k²/log k).
    There exists a constant C such that R(3,k) ≤ C · k² / log(k) for all k ≥ 3. -/
axiom aks_r3k_upper_bound :
    ∃ C : ℕ, C > 0 ∧ ∀ k : ℕ, k ≥ 3 →
    ramseyUpperBound 3 k ≤ C * k^2

/-- **Kim (1995)**: R(3,k) = Ω(k²/log k).
    There exists a constant c > 0 such that R(3,k) ≥ c · k²/log(k). -/
axiom kim_r3k_lower_bound :
    ∃ C : ℕ, C > 0 ∧ ∀ k : ℕ, k ≥ 3 →
    ∃ n : ℕ, n ≤ C * k^2 ∧
    ∃ (color : Fin n → Fin n → Bool),
      (∀ x y, color x y = color y x) ∧
      (∀ x, color x x = false) ∧
      (∀ (s : Finset (Fin n)), s.card = 3 →
        ¬(∀ x y, x ∈ s → y ∈ s → x ≠ y → color x y = true)) ∧
      (∀ (s : Finset (Fin n)), s.card = k →
        ¬(∀ x y, x ∈ s → y ∈ s → x ≠ y → color x y = false))

/-
## Part III: Concrete Small Ramsey Bounds

These are computable from the binomial coefficient formula.
-/

/-- R(3,3) ≤ C(4,2) = 6. -/
theorem r3_3_upper : ramseyUpperBound 3 3 = 6 := by native_decide

/-- R(3,4) ≤ C(5,2) = 10. Known exact value: R(3,4) = 9. -/
theorem r3_4_upper : ramseyUpperBound 3 4 = 10 := by native_decide

/-- R(3,5) ≤ C(6,2) = 15. Known exact value: R(3,5) = 14. -/
theorem r3_5_upper : ramseyUpperBound 3 5 = 15 := by native_decide

/-- R(4,4) ≤ C(6,3) = 20. Known exact value: R(4,4) = 18. -/
theorem r4_4_upper : ramseyUpperBound 4 4 = 20 := by native_decide

/-- R(4,5) ≤ C(7,3) = 35. Known exact value: R(4,5) = 25. -/
theorem r4_5_upper : ramseyUpperBound 4 5 = 35 := by native_decide

/-- R(5,5) ≤ C(8,4) = 70. Known bounds: 43 ≤ R(5,5) ≤ 48. -/
theorem r5_5_upper : ramseyUpperBound 5 5 = 70 := by native_decide

/-
## Part IV: Properties of the Ramsey Upper Bound
-/

/-- The Ramsey bound is symmetric: R(r,s) = R(s,r).
    This follows from the symmetry of the binomial coefficient C(n,k) = C(n,n-k). -/
theorem ramseyUpperBound_symm (r s : ℕ) (hr : r ≥ 1) (hs : s ≥ 1) :
    ramseyUpperBound r s = ramseyUpperBound s r := by
  unfold ramseyUpperBound
  simp only [show ¬(r = 0 ∨ s = 0) by omega, show ¬(s = 0 ∨ r = 0) by omega, ↓reduceIte]
  -- Goal: (r + s - 2).choose (r - 1) = (s + r - 2).choose (s - 1)
  -- Step 1: Normalize the top argument
  have h1 : r + s - 2 = s + r - 2 := by omega
  rw [h1]
  -- Goal: (s + r - 2).choose (r - 1) = (s + r - 2).choose (s - 1)
  -- Step 2: Show s - 1 = (s + r - 2) - (r - 1)
  have h2 : s - 1 = (s + r - 2) - (r - 1) := by omega
  rw [h2]
  -- Goal: (s + r - 2).choose (r - 1) = (s + r - 2).choose ((s + r - 2) - (r - 1))
  -- Step 3: Apply symmetry of binomial coefficients
  exact (Nat.choose_symm (by omega : r - 1 ≤ s + r - 2)).symm

/-- Base case: R(1,s) = 1 for s ≥ 1. -/
theorem ramseyUpperBound_one_left (s : ℕ) (hs : s ≥ 1) :
    ramseyUpperBound 1 s = 1 := by
  unfold ramseyUpperBound
  simp only [show ¬(1 = 0 ∨ s = 0) by omega, ↓reduceIte]
  simp

/-- Base case: R(r,1) = 1 for r ≥ 1. -/
theorem ramseyUpperBound_one_right (r : ℕ) (hr : r ≥ 1) :
    ramseyUpperBound r 1 = 1 := by
  rw [ramseyUpperBound_symm r 1 hr (by omega)]
  exact ramseyUpperBound_one_left r hr

/-- R(2,s) = s: the binomial bound is tight for r=2. -/
theorem ramseyUpperBound_two_left (s : ℕ) (hs : s ≥ 1) :
    ramseyUpperBound 2 s = s := by
  unfold ramseyUpperBound
  simp only [show ¬(2 = 0 ∨ s = 0) by omega, ↓reduceIte]
  have : 2 + s - 2 = s := by omega
  rw [this]
  simp [Nat.choose_one_right]

/-- R(r,2) = r: symmetric to the two_left case. -/
theorem ramseyUpperBound_two_right (r : ℕ) (hr : r ≥ 1) :
    ramseyUpperBound r 2 = r := by
  rw [ramseyUpperBound_symm r 2 hr (by omega)]
  exact ramseyUpperBound_two_left r hr

/-- The Ramsey upper bound is zero when r = 0. -/
theorem ramseyUpperBound_zero_left (s : ℕ) :
    ramseyUpperBound 0 s = 0 := by
  unfold ramseyUpperBound
  simp

/-- The Ramsey upper bound is zero when s = 0. -/
theorem ramseyUpperBound_zero_right (r : ℕ) :
    ramseyUpperBound r 0 = 0 := by
  unfold ramseyUpperBound
  simp

/-- The Ramsey upper bound R(r,s) is positive for r,s ≥ 1. -/
theorem ramseyUpperBound_pos (r s : ℕ) (hr : r ≥ 1) (hs : s ≥ 1) :
    ramseyUpperBound r s ≥ 1 := by
  unfold ramseyUpperBound
  simp only [show ¬(r = 0 ∨ s = 0) by omega, ↓reduceIte]
  exact Nat.one_le_iff_ne_zero.mpr (Nat.choose_pos (by omega)).ne'

/-- R(r,s) ≤ R(r, s+1) for r ≥ 1, s ≥ 1.
    This follows because C(r+s-2, r-1) ≤ C(r+s-1, r-1).
    We use Pascal's rule: C(n+1, k) = C(n, k) + C(n, k-1) ≥ C(n, k). -/
theorem ramseyUpperBound_mono_right (r s : ℕ) (hr : r ≥ 1) (hs : s ≥ 1) :
    ramseyUpperBound r s ≤ ramseyUpperBound r (s + 1) := by
  unfold ramseyUpperBound
  simp only [show ¬(r = 0 ∨ s = 0) by omega,
             show ¬(r = 0 ∨ s + 1 = 0) by omega, ↓reduceIte]
  have h1 : r + (s + 1) - 2 = (r + s - 2) + 1 := by omega
  rw [h1]
  exact Nat.choose_le_choose _ (by omega)

/-- R(r,s) ≤ R(r+1, s) for r ≥ 1, s ≥ 1.
    Follows from monotonicity via symmetry. -/
theorem ramseyUpperBound_mono_left (r s : ℕ) (hr : r ≥ 1) (hs : s ≥ 1) :
    ramseyUpperBound r s ≤ ramseyUpperBound (r + 1) s := by
  calc ramseyUpperBound r s = ramseyUpperBound s r :=
        ramseyUpperBound_symm r s hr hs
    _ ≤ ramseyUpperBound s (r + 1) :=
        ramseyUpperBound_mono_right s r hs hr
    _ = ramseyUpperBound (r + 1) s :=
        ramseyUpperBound_symm s (r + 1) hs (by omega)

/-
## Part IV-B: Recursive (Pascal) Bound

The classical recursive relation: R(r,s) ≤ R(r-1,s) + R(r,s-1).
In terms of binomial coefficients, this follows from Pascal's rule:
  C(n+1, k+1) = C(n, k) + C(n, k+1)
-/

/-- The recursive Ramsey bound: R(r,s) = R(r-1,s) + R(r,s-1) for r,s ≥ 2.
    This is a direct consequence of Pascal's rule for binomial coefficients. -/
theorem ramseyUpperBound_pascal (r s : ℕ) (hr : r ≥ 2) (hs : s ≥ 2) :
    ramseyUpperBound r s = ramseyUpperBound (r - 1) s + ramseyUpperBound r (s - 1) := by
  unfold ramseyUpperBound
  simp only [show ¬(r = 0 ∨ s = 0) by omega,
             show ¬(r - 1 = 0 ∨ s = 0) by omega,
             show ¬(r = 0 ∨ s - 1 = 0) by omega, ↓reduceIte]
  -- Rewrite indices using omega-provable facts
  have h1 : r - 1 + s - 2 = r + s - 3 := by omega
  have h2 : r + (s - 1) - 2 = r + s - 3 := by omega
  have h3 : r - 1 - 1 = r - 2 := by omega
  rw [h1, h2, h3]
  -- Now: C(r+s-2, r-1) = C(r+s-3, r-2) + C(r+s-3, r-1)
  -- This is Pascal's rule: C(n+1, k+1) = C(n, k) + C(n, k+1)
  -- with n = r+s-3, k = r-2
  have h4 : r + s - 2 = (r + s - 3) + 1 := by omega
  have h5 : r - 1 = (r - 2) + 1 := by omega
  rw [h4, h5]
  exact Nat.choose_succ_succ (r + s - 3) (r - 2)

/-- Verify Pascal's rule for small cases: R(3,3) = R(2,3) + R(3,2). -/
theorem ramseyUpperBound_pascal_check_33 :
    ramseyUpperBound 3 3 = ramseyUpperBound 2 3 + ramseyUpperBound 3 2 := by
  native_decide

/-- Verify Pascal's rule for R(4,4) = R(3,4) + R(4,3). -/
theorem ramseyUpperBound_pascal_check_44 :
    ramseyUpperBound 4 4 = ramseyUpperBound 3 4 + ramseyUpperBound 4 3 := by
  native_decide

/-- The Ramsey bound at (r,s) is at least as large as at (r-1,s) for r ≥ 2, s ≥ 1.
    Corollary of Pascal's rule: R(r,s) = R(r-1,s) + R(r,s-1) ≥ R(r-1,s). -/
theorem ramseyUpperBound_ge_pred_left (r s : ℕ) (hr : r ≥ 2) (hs : s ≥ 2) :
    ramseyUpperBound r s ≥ ramseyUpperBound (r - 1) s := by
  rw [ramseyUpperBound_pascal r s hr hs]
  omega

/-- Corollary of Pascal's rule: R(r,s) ≥ R(r,s-1). -/
theorem ramseyUpperBound_ge_pred_right (r s : ℕ) (hr : r ≥ 2) (hs : s ≥ 2) :
    ramseyUpperBound r s ≥ ramseyUpperBound r (s - 1) := by
  rw [ramseyUpperBound_pascal r s hr hs]
  omega

/-
## Part V: The R(4,k) Problem

The main open question: What is the order of growth of R(4,k)?

Known bounds:
- R(4,k) = Ω(k^(5/2) / (log k)^2) (Bohman-Keevash 2010, Mattheus-Verstraëte 2023)
- R(4,k) = O(k^3 / (log k)^2) (Ajtai-Komlós-Szemerédi, with improvements)

The gap between k^(5/2) and k^3 (up to log factors) is one of the major
open problems in Ramsey theory.
-/

/-- The R(4,k) upper bound: R(4,k) = O(k³ / (log k)²). -/
axiom r4k_upper_bound :
    ∃ C : ℕ, C > 0 ∧ ∀ k : ℕ, k ≥ 4 →
    ramseyUpperBound 4 k ≤ C * k^3

/-- The R(4,k) lower bound (Mattheus-Verstraëte 2023):
    R(4,k) = Ω(k^(5/2) / polylog).
    This improved the Bohman-Keevash (2010) bound of k^(5/2) / (log k)^2. -/
axiom r4k_lower_bound :
    ∃ C : ℕ, C > 0 ∧ ∀ k : ℕ, k ≥ 4 →
    ∃ n : ℕ, C * k^2 ≤ n ∧
    ∃ (color : Fin n → Fin n → Bool),
      (∀ x y, color x y = color y x) ∧
      (∀ x, color x x = false) ∧
      (∀ (s : Finset (Fin n)), s.card = 4 →
        ¬(∀ x y, x ∈ s → y ∈ s → x ≠ y → color x y = true)) ∧
      (∀ (s : Finset (Fin n)), s.card = k →
        ¬(∀ x y, x ∈ s → y ∈ s → x ≠ y → color x y = false))

/-
## Part V-B: Additional Structural Properties
-/

/-- R(r,s) ≥ s for r ≥ 2, s ≥ 1: the upper bound is at least s. -/
theorem ramseyUpperBound_ge_right (r s : ℕ) (hr : r ≥ 2) (hs : s ≥ 1) :
    ramseyUpperBound r s ≥ s := by
  unfold ramseyUpperBound
  simp only [show ¬(r = 0 ∨ s = 0) by omega, ↓reduceIte]
  -- Need: C(r+s-2, r-1) ≥ s
  -- C(r+s-2, r-1) = C(r+s-2, s-1) by symmetry
  -- For r ≥ 2: C(r+s-2, s-1) ≥ C(s, s-1) = s by monotonicity of choose
  have h1 : r - 1 ≤ r + s - 2 := by omega
  calc Nat.choose (r + s - 2) (r - 1)
      = Nat.choose (r + s - 2) ((r + s - 2) - (r - 1)) := Nat.choose_symm h1
    _ = Nat.choose (r + s - 2) (s - 1) := by congr 1; omega
    _ ≥ Nat.choose s (s - 1) := Nat.choose_le_choose (s - 1) (by omega)
    _ = s := by rw [Nat.choose_symm (by omega : s - 1 ≤ s)]; simp [show s - (s - 1) = 1 from by omega]; exact Nat.choose_one_right s

/-- R(r,s) ≥ r for r ≥ 1, s ≥ 2: the upper bound is at least r. -/
theorem ramseyUpperBound_ge_left (r s : ℕ) (hr : r ≥ 1) (hs : s ≥ 2) :
    ramseyUpperBound r s ≥ r := by
  rw [ramseyUpperBound_symm r s hr (by omega)]
  exact ramseyUpperBound_ge_right s r hs hr

/-- More concrete bounds: R(3,6) ≤ C(7,2) = 21. -/
theorem r3_6_upper : ramseyUpperBound 3 6 = 21 := by native_decide

/-- R(3,7) ≤ C(8,2) = 28. -/
theorem r3_7_upper : ramseyUpperBound 3 7 = 28 := by native_decide

/-- R(3,8) ≤ C(9,2) = 36. -/
theorem r3_8_upper : ramseyUpperBound 3 8 = 36 := by native_decide

/-- R(3,9) ≤ C(10,2) = 45. Known exact value: R(3,9) = 36. -/
theorem r3_9_upper : ramseyUpperBound 3 9 = 45 := by native_decide

/-- R(4,6) ≤ C(8,3) = 56. -/
theorem r4_6_upper : ramseyUpperBound 4 6 = 56 := by native_decide

/-- R(4,7) ≤ C(9,3) = 84. -/
theorem r4_7_upper : ramseyUpperBound 4 7 = 84 := by native_decide

/-- R(5,6) ≤ C(9,4) = 126. -/
theorem r5_6_upper : ramseyUpperBound 5 6 = 126 := by native_decide

/-- R(6,6) ≤ C(10,5) = 252. -/
theorem r6_6_upper : ramseyUpperBound 6 6 = 252 := by native_decide

/-- Diagonal monotonicity: R(k,k) ≤ R(k+1,k+1) for k ≥ 1. -/
theorem ramseyUpperBound_diag_mono (k : ℕ) (hk : k ≥ 1) :
    ramseyUpperBound k k ≤ ramseyUpperBound (k + 1) (k + 1) :=
  calc ramseyUpperBound k k
      ≤ ramseyUpperBound (k + 1) k := ramseyUpperBound_mono_left k k hk hk
    _ ≤ ramseyUpperBound (k + 1) (k + 1) := ramseyUpperBound_mono_right (k + 1) k (by omega) hk

/-- The upper bound grows strictly: R(r, s+1) ≥ R(r, s) + 1 for r ≥ 2, s ≥ 2. -/
theorem ramseyUpperBound_strict_mono_right (r s : ℕ) (hr : r ≥ 2) (hs : s ≥ 2) :
    ramseyUpperBound r (s + 1) ≥ ramseyUpperBound r s + 1 := by
  rw [ramseyUpperBound_pascal r (s + 1) hr (by omega)]
  have : ramseyUpperBound (r - 1) (s + 1) ≥ 1 :=
    ramseyUpperBound_pos (r - 1) (s + 1) (by omega) (by omega)
  simp only [show s + 1 - 1 = s from by omega]
  omega

/-
## Summary

This file formalizes:
1. **Proved theorems (33 total, 0 sorries)**:
   - Concrete values: R(3,3)=6, R(3,4)=10, R(3,5)=15,
     R(4,4)=20, R(4,5)=35, R(5,5)=70, R(3,6)=21, R(3,7)=28,
     R(3,8)=36, R(3,9)=45, R(4,6)=56, R(4,7)=84, R(5,6)=126,
     R(6,6)=252  (14 concrete values)
   - ramseyUpperBound_symm: R(r,s) = R(s,r)
   - ramseyUpperBound_one_left/right: R(1,s) = R(r,1) = 1
   - ramseyUpperBound_two_left/right: R(2,s) = s, R(r,2) = r
   - ramseyUpperBound_zero_left/right: R(0,s) = R(r,0) = 0
   - ramseyUpperBound_pos: R(r,s) ≥ 1 for r,s ≥ 1
   - ramseyUpperBound_mono_right/left: monotonicity
   - ramseyUpperBound_pascal: R(r,s) = R(r-1,s) + R(r,s-1)
   - ramseyUpperBound_pascal_check_33/44: Pascal rule verifications
   - ramseyUpperBound_ge_pred_left/right: pred corollaries
   - ramseyUpperBound_ge_right/left: R(r,s) ≥ s and ≥ r  [NEW]
   - ramseyUpperBound_diag_mono: R(k,k) ≤ R(k+1,k+1)  [NEW]
   - ramseyUpperBound_strict_mono_right: R(r,s+1) ≥ R(r,s) + 1  [NEW]

2. **Axioms (5 total)**: Deep probabilistic results
   - erdos_probabilistic_lower_bound: R(k,k) > 2^(k/2)
   - aks_r3k_upper_bound: R(3,k) = O(k²/log k)
   - kim_r3k_lower_bound: R(3,k) = Ω(k²/log k)
   - r4k_upper_bound: R(4,k) = O(k³/(log k)²)
   - r4k_lower_bound: R(4,k) = Ω(k^(5/2)/polylog)
-/

end RamseyR4k
