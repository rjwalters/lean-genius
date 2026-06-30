/-
Stirling Numbers of the Second Kind — OQ-01-OQ-02:
the general finite-difference (inclusion–exclusion) closed form

  k! · S(n,k) = ∑_{j=0}^{k} (-1)^j · C(k,j) · (k-j)^n.

Source: Open question OQ-02 of the gallery entry `stirling-second-kind-oq-01`
(itself OQ-01 of the parent `stirling-second-kind`).

## The open question

The parent entry (`StirlingSecondKindOQ01.lean`) proved only the single two-block
column `S(n,2) = 2^(n-1) − 1`. Mathlib
(`Mathlib/Combinatorics/Enumerative/Stirling.lean`) defines
`Nat.stirlingSecond n k` by the Pascal-style recurrence

  S(n+1,k+1) = (k+1)·S(n,k+1) + S(n,k),     S(0,0)=1,  S(0,k+1)=0,  S(n+1,0)=0,

together with the boundary columns, but it does **not** record the canonical
closed form.  This file fills that gap.

## Strategy — the surjection recurrence, factorial-cleared in ℤ

Write the factorial-cleared finite-difference sum

  T(n,k) := ∑_{j=0}^{k} (-1)^j · C(k,j) · (k-j)^n      (an integer; subtraction lives in ℤ).

`T(n,k)` is exactly the number of surjections `[n] ↠ [k]` (inclusion–exclusion over
the `k` "missed value" events), so the target is `k!·S(n,k) = T(n,k)`.  We prove it
by induction on `n`, the heart being the **surjection recurrence**

  T(n+1,k+1) = (k+1)·(T(n,k+1) + T(n,k)),

which mirrors `S(n+1,k+1) = (k+1)·S(n,k+1) + S(n,k)` once each side is multiplied by
the appropriate factorial.  The recurrence itself rests on two elementary binomial
facts:

* an **absorption** identity  (k+1−j)·C(k+1,j) = (k+1)·C(k,j), which turns one factor
  of the base `(k+1−j)` into the multiplier `(k+1)` while lowering the upper index, and
* **Pascal's rule** C(k+1,j+1) = C(k,j) + C(k,j+1),

after which everything is bookkeeping with `Finset.sum_range_succ'`.

As a sanity check we recover the parent's column `S(n,2) = 2^(n-1) − 1`.
-/
import Mathlib

namespace StirlingSecondKindOQ01OQ02

open Finset

/-- The factorial-cleared finite-difference sum
`T n k = ∑_{j=0}^{k} (-1)^j · C(k,j) · (k-j)^n`, an integer (the alternating signs and
the base `k-j` both live in `ℤ`).  Combinatorially `T n k` is the number of surjections
from an `n`-element set onto a `k`-element set. -/
def T (n k : ℕ) : ℤ :=
  ∑ j ∈ range (k + 1), (-1 : ℤ) ^ j * (k.choose j : ℤ) * ((k : ℤ) - (j : ℤ)) ^ n

/-- **Absorption identity** (over `ℕ`): `(k+1)·C(k,j) = (k+1−j)·C(k+1,j)`.
Both sides are `0` once `j > k+1`, so the statement is unconditional. -/
theorem nat_absorb (k j : ℕ) :
    (k + 1) * k.choose j = (k + 1 - j) * (k + 1).choose j := by
  have h1 : (k + 1) * k.choose j = (k + 1).choose (j + 1) * (j + 1) :=
    Nat.add_one_mul_choose_eq k j
  have h2 : (k + 1).choose (j + 1) * (j + 1) = (k + 1).choose j * (k + 1 - j) :=
    Nat.choose_succ_right_eq (k + 1) j
  rw [h1, h2, Nat.mul_comm]

/-- The absorption identity cast into `ℤ`, in the exact shape used inside the sum:
for `j ≤ k+1`,  `((k:ℤ)+1 − j)·C(k+1,j) = ((k:ℤ)+1)·C(k,j)`. -/
theorem absorbZ (k j : ℕ) (hj : j ≤ k + 1) :
    ((k : ℤ) + 1 - (j : ℤ)) * ((k + 1).choose j : ℤ)
      = ((k : ℤ) + 1) * (k.choose j : ℤ) := by
  have hnat := nat_absorb k j
  have hcast : (((k + 1 - j : ℕ)) : ℤ) = (k : ℤ) + 1 - (j : ℤ) := by
    have : (j : ℤ) ≤ (k : ℤ) + 1 := by exact_mod_cast hj
    push_cast [Nat.cast_sub hj]
    ring
  have : ((k : ℤ) + 1) * (k.choose j : ℤ)
      = ((k + 1 - j : ℕ) : ℤ) * ((k + 1).choose j : ℤ) := by
    exact_mod_cast hnat
  rw [this, hcast]

/-- **The surjection recurrence.**
`T (n+1) (k+1) = (k+1) · (T n (k+1) + T n k)`. -/
theorem rec_lemma (n k : ℕ) :
    T (n + 1) (k + 1) = ((k : ℤ) + 1) * (T n (k + 1) + T n k) := by
  -- Abbreviation for the "shifted" sum W that both sides funnel through.
  set W : ℤ := ∑ j ∈ range (k + 2),
      (-1 : ℤ) ^ j * (k.choose j : ℤ) * ((k : ℤ) + 1 - (j : ℤ)) ^ n with hW
  -- STEP A:  T (n+1) (k+1) = ((k:ℤ)+1) * W   (via absorption).
  have hA : T (n + 1) (k + 1) = ((k : ℤ) + 1) * W := by
    rw [hW, T, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjle : j ≤ k + 1 := by
      have := Finset.mem_range.mp hj; omega
    have habs := absorbZ k j hjle
    have hbase : (((k + 1 : ℕ)) : ℤ) - (j : ℤ) = (k : ℤ) + 1 - (j : ℤ) := by push_cast; ring
    rw [hbase, pow_succ]
    -- goal: (-1)^j * C(k+1,j) * (b^n * b) = (k+1) * ((-1)^j * C(k,j) * b^n)
    linear_combination ((-1 : ℤ) ^ j * ((k : ℤ) + 1 - (j : ℤ)) ^ n) * habs
  -- STEP B:  T n (k+1) + T n k = W   (via Pascal, peeling the bottom index).
  have hB : T n (k + 1) + T n k = W := by
    -- Peel the j = 0 term of T n (k+1) and of W with `sum_range_succ'`.
    have hTk1 : T n (k + 1)
        = (∑ i ∈ range (k + 1),
            (-1 : ℤ) ^ (i + 1) * ((k + 1).choose (i + 1) : ℤ) * ((k : ℤ) - (i : ℤ)) ^ n)
          + ((k : ℤ) + 1) ^ n := by
      rw [T, Finset.sum_range_succ']
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        have : (((k + 1 : ℕ)) : ℤ) - ((i + 1 : ℕ) : ℤ) = (k : ℤ) - (i : ℤ) := by push_cast; ring
        rw [this]
      · simp
    have hWval : W
        = (∑ i ∈ range (k + 1),
            (-1 : ℤ) ^ (i + 1) * (k.choose (i + 1) : ℤ) * ((k : ℤ) - (i : ℤ)) ^ n)
          + ((k : ℤ) + 1) ^ n := by
      rw [hW, Finset.sum_range_succ']
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        have : (k : ℤ) + 1 - ((i + 1 : ℕ) : ℤ) = (k : ℤ) - (i : ℤ) := by push_cast; ring
        rw [this]
      · simp
    rw [hTk1, hWval, T]
    -- Now: (Σ_T + (k+1)^n) + Σ_{Tnk} = (Σ_W + (k+1)^n)
    -- Cancel the boundary term and merge sums via `sum_range_succ'`-free Pascal per index.
    have hmerge :
        (∑ i ∈ range (k + 1),
            (-1 : ℤ) ^ (i + 1) * ((k + 1).choose (i + 1) : ℤ) * ((k : ℤ) - (i : ℤ)) ^ n)
          + (∑ i ∈ range (k + 1),
              (-1 : ℤ) ^ i * (k.choose i : ℤ) * ((k : ℤ) - (i : ℤ)) ^ n)
        = ∑ i ∈ range (k + 1),
            (-1 : ℤ) ^ (i + 1) * (k.choose (i + 1) : ℤ) * ((k : ℤ) - (i : ℤ)) ^ n := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      have hp : (((k + 1).choose (i + 1) : ℕ) : ℤ)
          = (k.choose i : ℤ) + (k.choose (i + 1) : ℤ) := by
        have := Nat.choose_succ_succ' k i
        exact_mod_cast this
      rw [hp]; ring
    linear_combination hmerge
  rw [hA, hB]

/-- **Main theorem — the finite-difference closed form (factorial-cleared, in ℤ).**

For all `n k : ℕ`,

  `k! · S(n,k) = ∑_{j=0}^{k} (-1)^j · C(k,j) · (k-j)^n`. -/
theorem factorial_mul_stirlingSecond (n k : ℕ) :
    (k.factorial : ℤ) * (Nat.stirlingSecond n k : ℤ) = T n k := by
  induction n generalizing k with
  | zero =>
    -- T 0 k = ∑ (-1)^j C(k,j) = if k = 0 then 1 else 0 = S(0,k)
    simp only [T, pow_zero, mul_one]
    rw [Int.alternating_sum_range_choose]
    cases k with
    | zero => simp
    | succ k => simp
  | succ n ih =>
    cases k with
    | zero =>
      -- S(n+1,0) = 0 and T (n+1) 0 = 0^(n+1) = 0
      simp [T, Nat.stirlingSecond_succ_zero, zero_pow (Nat.succ_ne_zero n)]
    | succ k =>
      rw [rec_lemma, ← ih (k + 1), ← ih k, Nat.stirlingSecond_succ_succ]
      push_cast [Nat.factorial_succ]
      ring

/-- The number of surjections `[n] ↠ [k]` is non-negative integer `T n k` and equals
`k!·S(n,k)`; recorded here as the cleared form rearranged to expose `S`. -/
theorem stirlingSecond_eq_finiteDifference (n k : ℕ) :
    (Nat.stirlingSecond n k : ℤ) * (k.factorial : ℤ) = T n k := by
  rw [mul_comm]; exact factorial_mul_stirlingSecond n k

/-- Evaluation of the closed form at the two-block column: for `n ≥ 1`,
`T n 2 = 2^n − 2`. -/
theorem T_two {n : ℕ} (hn : n ≠ 0) : T n 2 = 2 ^ n - 2 := by
  rw [T]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  norm_num
  rw [zero_pow hn]
  ring

/-- **Specialization recovering the parent column.**
For `n ≥ 1`,  `2 · S(n,2) = 2^n − 2`. -/
theorem two_mul_stirlingSecond_two {n : ℕ} (hn : n ≠ 0) :
    (2 : ℤ) * (Nat.stirlingSecond n 2 : ℤ) = 2 ^ n - 2 := by
  have h := factorial_mul_stirlingSecond n 2
  rw [T_two hn] at h
  norm_num at h
  linarith [h]

/-- **Parent's closed form, recovered.**  For `n ≥ 1`,
`S(n,2) = 2^(n-1) − 1` (stated over `ℤ`). -/
theorem stirlingSecond_two {n : ℕ} (hn : 1 ≤ n) :
    (Nat.stirlingSecond n 2 : ℤ) = 2 ^ (n - 1) - 1 := by
  have h := two_mul_stirlingSecond_two (by omega : n ≠ 0)
  have hpow : (2 : ℤ) ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hpow] at h
  linarith [h]

end StirlingSecondKindOQ01OQ02
