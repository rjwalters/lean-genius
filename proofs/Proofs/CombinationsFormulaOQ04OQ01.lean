import Mathlib

/-
# Combinations Formula — OQ-04-OQ-01: Ultra-Log-Concavity of a Pascal Row

## Research Problem: combinations-formula-oq-04-oq-01

The parent (`combinations-formula-oq-04`) proves the *bare* log-concavity inequality for a
Pascal row,

      C(n,k) · C(n,k+2)  ≤  C(n,k+1)² ,

by cancelling the common positive factor in the product of the two adjacent-ratio relations
(Mathlib's `Nat.choose_succ_right_eq`).  This open question asks to **strengthen the inequality
to an exact quantitative statement**: how large is the log-concavity gap
`C(n,k+1)² − C(n,k)·C(n,k+2)`?

Substituting `n = k + 2 + t` and writing `a = C(n,k)`, `b = C(n,k+1)`, `c = C(n,k+2)`, the
parent's mechanism gives the exact product identity

      a · c · (t+2)(k+2)  =  b² · (k+1)(t+1).                              (★)

The parent throws away all information except the *sign* of the difference
`(t+2)(k+2) − (k+1)(t+1)`.  But that difference is not merely positive — it is **exactly**

      (t+2)(k+2) − (k+1)(t+1)  =  t + k + 3  =  n + 1 .

Feeding this back into (★) turns the inequality into the sharp identity

      ( b² − a·c ) · (k+1)(n−k−1)  =  (n+1) · a·c ,

i.e. the log-concavity defect is governed *exactly* by `n + 1`.  Equivalently, over `ℚ`,

      b² / (a·c)  =  1  +  (n+1) / ((k+1)(n−k−1))  >  1 ,

which is precisely the ultra-log-concavity excess factor: the Pascal row is not just
log-concave, its consecutive-ratio deviation from a geometric sequence is the explicit rational
`1 + (n+1)/((k+1)(n−k−1))`.  This strictly strengthens the parent (the parent's `≤`, and the
strict interior `<`, both drop out of the identity immediately).

## What is proved

* `choose_adjacent_ratio_prod` — the subtraction-free product identity (★) in `n, k`.
* `choose_logConcavity_defect` — the **exact defect identity** (additive, subtraction-free):
  `C(n,k+1)² · (k+1)(n−k−1) = C(n,k)·C(n,k+2) · ((k+1)(n−k−1) + (n+1))`.
* `choose_logConcavity_gap` — the same in gap form:
  `(C(n,k+1)² − C(n,k)·C(n,k+2)) · (k+1)(n−k−1) = (n+1) · C(n,k)·C(n,k+2)`.
* `choose_logConcave_le` / `choose_logConcave_lt` — the parent inequality and its strict
  interior form, both recovered from the identity.
* `choose_ratio_rat` — the rational ultra-log-concavity excess:
  `(C(n,k+1):ℚ)² / (C(n,k)·C(n,k+2)) = 1 + (n+1)/((k+1)(n−k−1))`.

Tags: combinatorics, binomial-coefficients, pascals-triangle, log-concavity, ultra-log-concave,
newton-inequality
-/

namespace CombinationsFormulaOQ04OQ01

open Nat

/-- **Adjacent-ratio product identity (★).**  Writing `n = k + 2 + t`, the two relations from
    `Nat.choose_succ_right_eq` combine into the subtraction-free identity
    `C(n,k)·C(n,k+2)·(t+2)(k+2) = C(n,k+1)²·(k+1)(t+1)`.  This is the exact form behind the
    parent's log-concavity inequality. -/
theorem choose_adjacent_ratio_prod (k t : ℕ) :
    (k + 2 + t).choose k * (k + 2 + t).choose (k + 2) * ((t + 2) * (k + 2))
      = ((k + 2 + t).choose (k + 1)) ^ 2 * ((k + 1) * (t + 1)) := by
  have R1 : (k + 2 + t).choose (k + 1) * (k + 1) = (k + 2 + t).choose k * (t + 2) := by
    have := Nat.choose_succ_right_eq (k + 2 + t) k
    simpa [show (k + 2 + t) - k = t + 2 by omega] using this
  have R2 : (k + 2 + t).choose (k + 2) * (k + 2) = (k + 2 + t).choose (k + 1) * (t + 1) := by
    have := Nat.choose_succ_right_eq (k + 2 + t) (k + 1)
    simpa [show (k + 2 + t) - (k + 1) = t + 1 by omega] using this
  set a := (k + 2 + t).choose k
  set b := (k + 2 + t).choose (k + 1)
  set c := (k + 2 + t).choose (k + 2)
  have e1 : a * (t + 2) = b * (k + 1) := R1.symm
  have e2 : c * (k + 2) = b * (t + 1) := R2
  have step : a * c * ((t + 2) * (k + 2)) = (a * (t + 2)) * (c * (k + 2)) := by ring
  rw [step, e1, e2]; ring

/-- **Exact log-concavity defect identity (additive, subtraction-free).**  For `k + 2 ≤ n`,

      C(n,k+1)² · (k+1)(n−k−1)  =  C(n,k)·C(n,k+2) · ( (k+1)(n−k−1) + (n+1) ).

The multiplier `(k+1)(n−k−1) + (n+1)` on the right *exceeds* the multiplier `(k+1)(n−k−1)` on the
left by exactly `n+1`; that surplus is the quantitative content the parent's inequality
discards. -/
theorem choose_logConcavity_defect (n k : ℕ) (h : k + 2 ≤ n) :
    (n.choose (k + 1)) ^ 2 * ((k + 1) * (n - k - 1))
      = n.choose k * n.choose (k + 2) * ((k + 1) * (n - k - 1) + (n + 1)) := by
  obtain ⟨t, rfl⟩ : ∃ t, n = k + 2 + t := ⟨n - (k + 2), by omega⟩
  have key := choose_adjacent_ratio_prod k t
  -- `n - k - 1 = t + 1` and `(t+2)(k+2) = (k+1)(t+1) + (n+1)` (subtraction-free after rewrite)
  have hnk : (k + 2 + t) - k - 1 = t + 1 := by omega
  rw [hnk]
  have expand : (t + 2) * (k + 2) = (k + 1) * (t + 1) + ((k + 2 + t) + 1) := by ring
  -- rewrite (★) using the split of (t+2)(k+2)
  calc (k + 2 + t).choose (k + 1) ^ 2 * ((k + 1) * (t + 1))
        = (k + 2 + t).choose k * (k + 2 + t).choose (k + 2) * ((t + 2) * (k + 2)) := key.symm
    _ = (k + 2 + t).choose k * (k + 2 + t).choose (k + 2)
          * ((k + 1) * (t + 1) + ((k + 2 + t) + 1)) := by rw [expand]

/-- **Log-concavity gap identity.**  The gap form of the defect identity: for `k + 2 ≤ n`,

      ( C(n,k+1)² − C(n,k)·C(n,k+2) ) · (k+1)(n−k−1)  =  (n+1) · C(n,k)·C(n,k+2).

Here the truncated subtraction `C(n,k+1)² − C(n,k)·C(n,k+2)` is exact (the subtrahend is the
smaller by log-concavity), and the identity shows the defect is a fixed `(n+1)`-multiple of the
outer product, scaled down by `(k+1)(n−k−1)`. -/
theorem choose_logConcavity_gap (n k : ℕ) (h : k + 2 ≤ n) :
    ((n.choose (k + 1)) ^ 2 - n.choose k * n.choose (k + 2)) * ((k + 1) * (n - k - 1))
      = (n + 1) * (n.choose k * n.choose (k + 2)) := by
  have hd := choose_logConcavity_defect n k h
  -- from  b²·M = ac·(M + (n+1))  with M = (k+1)(n-k-1), derive (b² - ac)·M = (n+1)·ac
  set M := (k + 1) * (n - k - 1)
  set A := n.choose k * n.choose (k + 2)
  set B := (n.choose (k + 1)) ^ 2
  -- hd : B * M = A * (M + (n + 1))
  have hBM : B * M = A * M + A * (n + 1) := by rw [hd]; ring
  rw [Nat.sub_mul, hBM, Nat.add_sub_cancel_left]
  ring

/-- **Parent inequality, recovered.**  `C(n,k)·C(n,k+2) ≤ C(n,k+1)²` for all `n, k`
    (the log-concavity of a Pascal row), obtained from the exact defect identity in the
    interior and trivially outside it. -/
theorem choose_logConcave_le (n k : ℕ) :
    n.choose k * n.choose (k + 2) ≤ (n.choose (k + 1)) ^ 2 := by
  rcases lt_or_ge n (k + 2) with h | h
  · rw [Nat.choose_eq_zero_of_lt h]; simp
  · have hd := choose_logConcavity_defect n k h
    have hMpos : 0 < (k + 1) * (n - k - 1) := by
      have : 0 < n - k - 1 := by omega
      positivity
    nlinarith [Nat.zero_le (n.choose k * n.choose (k + 2)), Nat.zero_le (n + 1)]

/-- **Strict log-concavity in the interior.**  For `k + 2 ≤ n` the inequality is strict:
    `C(n,k)·C(n,k+2) < C(n,k+1)²`.  The exact defect identity makes this immediate — the surplus
    `(n+1)·C(n,k)·C(n,k+2)` is strictly positive since `C(n,k), C(n,k+2) > 0` in the interior. -/
theorem choose_logConcave_lt (n k : ℕ) (h : k + 2 ≤ n) :
    n.choose k * n.choose (k + 2) < (n.choose (k + 1)) ^ 2 := by
  have hd := choose_logConcavity_defect n k h
  have hMpos : 0 < (k + 1) * (n - k - 1) := by
    have : 0 < n - k - 1 := by omega
    positivity
  have hApos : 0 < n.choose k * n.choose (k + 2) :=
    Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))
  nlinarith [hApos, hMpos]

/-- **Centered restatement.**  Rewriting `k = j − 1`, the exact defect identity holds at the
    interior index `j` (`1 ≤ j`, `j + 1 ≤ n`):

      C(n,j)² · j(n−j)  =  C(n,j−1)·C(n,j+1) · ( j(n−j) + (n+1) ). -/
theorem choose_logConcavity_defect' (n j : ℕ) (hj : 1 ≤ j) (h : j + 1 ≤ n) :
    (n.choose j) ^ 2 * (j * (n - j))
      = n.choose (j - 1) * n.choose (j + 1) * (j * (n - j) + (n + 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hd := choose_logConcavity_defect n k (by omega)
  have h1 : k + 1 - 1 = k := by omega
  have h2 : n - (k + 1) = n - k - 1 := by omega
  rw [h1, h2]
  exact hd

/-- **Rational ultra-log-concavity excess.**  For `k + 2 ≤ n`, the exact consecutive-square
    ratio is

      C(n,k+1)² / ( C(n,k)·C(n,k+2) )  =  1  +  (n+1) / ( (k+1)(n−k−1) )  >  1 .

The explicit excess `(n+1)/((k+1)(n−k−1))` over the geometric value `1` is what makes the row
*ultra*-log-concave, not merely log-concave. -/
theorem choose_ratio_rat (n k : ℕ) (h : k + 2 ≤ n) :
    ((n.choose (k + 1) : ℚ)) ^ 2 / (n.choose k * n.choose (k + 2))
      = 1 + (n + 1) / ((k + 1) * (n - k - 1) : ℕ) := by
  obtain ⟨t, rfl⟩ : ∃ t, n = k + 2 + t := ⟨n - (k + 2), by omega⟩
  have hnk : (k + 2 + t) - k - 1 = t + 1 := by omega
  rw [hnk]
  have key := choose_adjacent_ratio_prod k t
  have hac : 0 < (k + 2 + t).choose k * (k + 2 + t).choose (k + 2) :=
    Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))
  have hkt : 0 < (k + 1) * (t + 1) := by positivity
  have hacQ : ((k + 2 + t).choose k : ℚ) * (k + 2 + t).choose (k + 2) ≠ 0 := by
    exact_mod_cast hac.ne'
  have hktQ : (((k + 1) * (t + 1) : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hkt.ne'
  have keyQ : ((k + 2 + t).choose k : ℚ) * (k + 2 + t).choose (k + 2) * ((t + 2) * (k + 2))
      = ((k + 2 + t).choose (k + 1) : ℚ) ^ 2 * ((k + 1) * (t + 1)) := by exact_mod_cast key
  have hRHS : (1 : ℚ) + ((k + 2 + t : ℕ) + 1) / ((k + 1) * (t + 1) : ℕ)
      = (((k + 1) * (t + 1) : ℕ) + ((k + 2 + t : ℕ) + 1)) / ((k + 1) * (t + 1) : ℕ) := by
    rw [eq_div_iff hktQ, add_mul, one_mul, div_mul_cancel₀ _ hktQ]
  rw [hRHS, div_eq_div_iff hacQ hktQ]
  push_cast
  push_cast at keyQ
  linear_combination -keyQ

#check @choose_adjacent_ratio_prod
#check @choose_logConcavity_defect
#check @choose_logConcavity_gap
#check @choose_logConcave_le
#check @choose_logConcave_lt
#check @choose_logConcavity_defect'
#check @choose_ratio_rat

/-
## Summary

The parent proves the Pascal row is log-concave.  This entry upgrades that qualitative
inequality to the **exact** defect identity

      ( C(n,k+1)² − C(n,k)·C(n,k+2) ) · (k+1)(n−k−1)  =  (n+1) · C(n,k)·C(n,k+2),

equivalently the rational ratio `C(n,k+1)²/(C(n,k)·C(n,k+2)) = 1 + (n+1)/((k+1)(n−k−1))`.  Both
the parent's `≤` and its strict interior `<` fall out as one-line corollaries.  The whole file
rests only on Mathlib's `Nat.choose_succ_right_eq`; no new axioms.
-/

end CombinationsFormulaOQ04OQ01
