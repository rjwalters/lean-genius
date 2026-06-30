import Mathlib
import Proofs.GeometricSeriesOQ07OQ01OQ01OQ01

/-
# The explicit (inclusion–exclusion) closed form for the Eulerian numbers

The parent entry **geometric-series-oq-07-oq-01-oq-01-oq-01** builds the combinatorial
Eulerian numbers `⟨n,k⟩` (`eulerian n k`) from the triangle recurrence and identifies them
with the coefficients of the Eulerian polynomial.  Its child
**geometric-series-oq-07-oq-01-oq-01-oq-01-oq-01** computed the row sum `∑ⱼ ⟨n,j⟩ = n!` and
the explicit closed forms of the *low columns* `k = 0,1,2`, and recorded the **general
closed form** as its declared open question:

  `⟨n,k⟩ = ∑_{i=0}^{k} (-1)ⁱ · C(n+1,i) · (k+1-i)ⁿ`.

This entry settles it.  We define the alternating binomial sum `eulerianExplicit n k`
(the right-hand side, as an integer) and prove it equals `⟨n,k⟩` for **all** `n,k`.

## Method

`eulerianExplicit` satisfies the very recurrence that *defines* `eulerian`:

  `eulerianExplicit (n+1) (k+1)
      = (k+2)·eulerianExplicit n (k+1) + (n-k)·eulerianExplicit n k`     (`eulerianExplicit_succ_succ`)

The proof of this recurrence is a finite-difference computation: split `C(n+2,i)` by
Pascal's rule, reindex, and collapse the result using the two binomial *absorption*
identities

  `C(n+1,i)·(n+1-i) = (n+1)·C(n,i)`        (`absorb_down`)
  `C(n+1,j+1)·(j+1) = (n+1)·C(n,j)`        (`absorb_up`).

The two stray sums cancel exactly.  With the recurrence and the base row `n = 0` in hand,
a single induction on `n` matches `eulerianExplicit` to `eulerian`; the truncated natural
subtraction `(n-k : ℕ)` is reconciled with the integer `(n-k : ℤ)` using the parent's
diagonal vanishing `⟨n,k⟩ = 0` for `n < k`.
-/

namespace GeometricSeriesOQ07OQ01OQ01OQ01OQ02

open Finset GeometricSeriesOQ07OQ01OQ01OQ01

/-- The **explicit (inclusion–exclusion) form** of the Eulerian number `⟨n,k⟩`, as an
integer: `∑_{i=0}^{k} (-1)ⁱ · C(n+1,i) · (k+1-i)ⁿ`.  We prove below
(`eulerian_eq_explicit`) that this equals the combinatorial `eulerian n k`. -/
def eulerianExplicit (n k : ℕ) : ℤ :=
  ∑ i ∈ range (k + 1), (-1 : ℤ) ^ i * ((n + 1).choose i : ℤ) * ((k : ℤ) + 1 - i) ^ n

/-! ## Binomial absorption identities -/

/-- **Upward absorption.** `C(n+1,j+1)·(j+1) = (n+1)·C(n,j)` (over `ℤ`). -/
theorem absorb_up (n j : ℕ) :
    ((n + 1).choose (j + 1) : ℤ) * ((j : ℤ) + 1) = ((n : ℤ) + 1) * (n.choose j : ℤ) := by
  have h := Nat.add_one_mul_choose_eq n j
  have h' : ((n + 1) * n.choose j : ℤ) = ((n + 1).choose (j + 1) * (j + 1) : ℤ) := by
    exact_mod_cast h
  push_cast at h'
  linarith [h']

/-- **Downward absorption.** `C(n+1,i)·(n+1-i) = (n+1)·C(n,i)` (over `ℤ`, valid for all `i`
including `i > n`, where both sides vanish). -/
theorem absorb_down (n i : ℕ) :
    ((n + 1).choose i : ℤ) * ((n : ℤ) + 1 - i) = ((n : ℤ) + 1) * (n.choose i : ℤ) := by
  rcases le_or_gt i n with hi | hi
  · -- `i ≤ n`: a genuine binomial identity, obtained from `absorb_up` via symmetry.
    have key : (n + 1).choose i * (n + 1 - i) = (n + 1) * n.choose i := by
      have hs : (n + 1).choose i = (n + 1).choose ((n - i) + 1) := by
        rw [show (n - i) + 1 = (n + 1) - i from by omega, Nat.choose_symm (by omega : i ≤ n + 1)]
      calc (n + 1).choose i * (n + 1 - i)
          = (n + 1).choose ((n - i) + 1) * ((n - i) + 1) := by
            rw [hs, show n + 1 - i = (n - i) + 1 from by omega]
        _ = (n + 1) * n.choose (n - i) := by rw [← Nat.add_one_mul_choose_eq n (n - i)]
        _ = (n + 1) * n.choose i := by rw [Nat.choose_symm hi]
    have hcast : (((n + 1).choose i * (n + 1 - i) : ℕ) : ℤ) = (((n + 1) * n.choose i : ℕ) : ℤ) := by
      exact_mod_cast key
    push_cast [Nat.cast_sub (show i ≤ n + 1 from by omega)] at hcast
    linarith [hcast]
  · -- `i > n`: the RHS vanishes (`C(n,i) = 0`); so must the LHS.
    rw [Nat.choose_eq_zero_of_lt hi, Nat.cast_zero, mul_zero]
    rcases eq_or_lt_of_le (show n + 1 ≤ i from hi) with he | hlt
    · -- `i = n+1`: the factor `(n+1-i)` vanishes.
      rw [← he]; push_cast; ring
    · -- `i > n+1`: the binomial `C(n+1,i)` vanishes.
      rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero, zero_mul]

/-! ## `eulerianExplicit` satisfies the Eulerian recurrence -/

/-- **Upward collapse.** The "`i·C(n+1,i)`" sum (the defect between `S1` and `(k+2)·A`)
collapses, via `absorb_up`, to `-(n+1)` times the row-`n` alternating sum `Σ`. -/
private theorem x_collapse (n k : ℕ) :
    (∑ i ∈ range (k + 1 + 1),
        (-1 : ℤ) ^ i * ((n + 1).choose i : ℤ) * ((i : ℤ) * ((k : ℤ) + 1 + 1 - i) ^ n))
      + ((n : ℤ) + 1) *
        (∑ i ∈ range (k + 1), (-1 : ℤ) ^ i * (n.choose i : ℤ) * ((k : ℤ) + 1 - i) ^ n) = 0 := by
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j _
  have hcast : ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 := by push_cast; ring
  rw [hcast, show ((k : ℤ) + 1 + 1 - ((j : ℤ) + 1)) = ((k : ℤ) + 1 - j) from by ring]
  linear_combination (-(-1 : ℤ) ^ j * ((k : ℤ) + 1 - (j : ℤ)) ^ n) * absorb_up n j

/-- **Downward collapse.** The "`(n+1-i)·C(n+1,i)`" sum (the defect packaging `S2` and
`(n-k)·B`) collapses, via `absorb_down`, to `(n+1)` times the same `Σ`. -/
private theorem y_collapse (n k : ℕ) :
    (∑ i ∈ range (k + 1),
        (-1 : ℤ) ^ i * ((n + 1).choose i : ℤ) * (((n : ℤ) + 1 - i) * ((k : ℤ) + 1 - i) ^ n))
      = ((n : ℤ) + 1) *
        (∑ i ∈ range (k + 1), (-1 : ℤ) ^ i * (n.choose i : ℤ) * ((k : ℤ) + 1 - i) ^ n) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  linear_combination ((-1 : ℤ) ^ i * ((k : ℤ) + 1 - (i : ℤ)) ^ n) * absorb_down n i

/-- **The key recurrence.**  `eulerianExplicit` obeys the same triangle recurrence as the
combinatorial Eulerian numbers:
`eulerianExplicit (n+1) (k+1) = (k+2)·eulerianExplicit n (k+1) + (n-k)·eulerianExplicit n k`
(with integer subtraction `n-k`). -/
theorem eulerianExplicit_succ_succ (n k : ℕ) :
    eulerianExplicit (n + 1) (k + 1)
      = ((k : ℤ) + 2) * eulerianExplicit n (k + 1)
        + ((n : ℤ) - k) * eulerianExplicit n k := by
  -- Normalised forms of the three `eulerianExplicit` sums (bases `↑k+1+1` and `↑k+1`).
  have hLHSe : eulerianExplicit (n + 1) (k + 1)
      = ∑ i ∈ range (k + 1 + 1), (-1 : ℤ) ^ i * ((n + 1 + 1).choose i : ℤ)
          * ((k : ℤ) + 1 + 1 - i) ^ (n + 1) := by
    simp only [eulerianExplicit]; apply Finset.sum_congr rfl; intro i _; push_cast; ring
  have hAe : eulerianExplicit n (k + 1)
      = ∑ i ∈ range (k + 1 + 1), (-1 : ℤ) ^ i * ((n + 1).choose i : ℤ)
          * ((k : ℤ) + 1 + 1 - i) ^ n := by
    simp only [eulerianExplicit]; apply Finset.sum_congr rfl; intro i _; push_cast; ring
  have hBe : eulerianExplicit n k
      = ∑ i ∈ range (k + 1), (-1 : ℤ) ^ i * ((n + 1).choose i : ℤ)
          * ((k : ℤ) + 1 - i) ^ n := rfl
  rw [hLHSe, hAe, hBe]
  -- Abbreviations: `S1`, `S2`, `Sig` are auxiliary sums.
  -- `S1 = (k+2)·A + (n+1)·Σ`  via the upward collapse.
  have hS1 : (∑ i ∈ range (k + 1 + 1), (-1 : ℤ) ^ i * ((n + 1).choose i : ℤ)
          * ((k : ℤ) + 1 + 1 - i) ^ (n + 1))
      = ((k : ℤ) + 2) * (∑ i ∈ range (k + 1 + 1), (-1 : ℤ) ^ i * ((n + 1).choose i : ℤ)
            * ((k : ℤ) + 1 + 1 - i) ^ n)
        + ((n : ℤ) + 1) * (∑ i ∈ range (k + 1), (-1 : ℤ) ^ i * (n.choose i : ℤ)
            * ((k : ℤ) + 1 - i) ^ n) := by
    have e1 : (∑ i ∈ range (k + 1 + 1), (-1 : ℤ) ^ i * ((n + 1).choose i : ℤ)
              * ((k : ℤ) + 1 + 1 - i) ^ (n + 1))
        - ((k : ℤ) + 2) * (∑ i ∈ range (k + 1 + 1), (-1 : ℤ) ^ i * ((n + 1).choose i : ℤ)
              * ((k : ℤ) + 1 + 1 - i) ^ n)
        + (∑ i ∈ range (k + 1 + 1), (-1 : ℤ) ^ i * ((n + 1).choose i : ℤ)
              * ((i : ℤ) * ((k : ℤ) + 1 + 1 - i) ^ n)) = 0 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero
      intro i _
      rw [pow_succ]; ring
    linear_combination e1 - x_collapse n k
  -- `S2 = (n+1)·Σ - (n-k)·B`  via the downward collapse.
  have hS2 : (∑ i ∈ range (k + 1), (-1 : ℤ) ^ i * ((n + 1).choose i : ℤ)
          * ((k : ℤ) + 1 - i) ^ (n + 1))
      = ((n : ℤ) + 1) * (∑ i ∈ range (k + 1), (-1 : ℤ) ^ i * (n.choose i : ℤ)
            * ((k : ℤ) + 1 - i) ^ n)
        - ((n : ℤ) - k) * (∑ i ∈ range (k + 1), (-1 : ℤ) ^ i * ((n + 1).choose i : ℤ)
            * ((k : ℤ) + 1 - i) ^ n) := by
    have e2 : ((n : ℤ) - k) * (∑ i ∈ range (k + 1), (-1 : ℤ) ^ i * ((n + 1).choose i : ℤ)
              * ((k : ℤ) + 1 - i) ^ n)
        + (∑ i ∈ range (k + 1), (-1 : ℤ) ^ i * ((n + 1).choose i : ℤ)
              * ((k : ℤ) + 1 - i) ^ (n + 1))
        - (∑ i ∈ range (k + 1), (-1 : ℤ) ^ i * ((n + 1).choose i : ℤ)
              * (((n : ℤ) + 1 - i) * ((k : ℤ) + 1 - i) ^ n)) = 0 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_eq_zero
      intro i _
      rw [pow_succ]; ring
    linear_combination e2 + y_collapse n k
  -- Pascal step: `LHS = S1 - S2`.
  have hLHS : (∑ i ∈ range (k + 1 + 1), (-1 : ℤ) ^ i * ((n + 1 + 1).choose i : ℤ)
          * ((k : ℤ) + 1 + 1 - i) ^ (n + 1))
      = (∑ i ∈ range (k + 1 + 1), (-1 : ℤ) ^ i * ((n + 1).choose i : ℤ)
            * ((k : ℤ) + 1 + 1 - i) ^ (n + 1))
        - (∑ i ∈ range (k + 1), (-1 : ℤ) ^ i * ((n + 1).choose i : ℤ)
            * ((k : ℤ) + 1 - i) ^ (n + 1)) := by
    have e3 : (∑ i ∈ range (k + 1 + 1), (-1 : ℤ) ^ i * ((n + 1 + 1).choose i : ℤ)
              * ((k : ℤ) + 1 + 1 - i) ^ (n + 1))
        - (∑ i ∈ range (k + 1 + 1), (-1 : ℤ) ^ i * ((n + 1).choose i : ℤ)
              * ((k : ℤ) + 1 + 1 - i) ^ (n + 1))
        + (∑ i ∈ range (k + 1), (-1 : ℤ) ^ i * ((n + 1).choose i : ℤ)
              * ((k : ℤ) + 1 - i) ^ (n + 1)) = 0 := by
      rw [← Finset.sum_sub_distrib, Finset.sum_range_succ']
      simp only [Nat.choose_zero_right, Nat.cast_one, sub_self, add_zero]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero
      intro j _
      have hp : ((n + 1 + 1).choose (j + 1) : ℤ)
          = ((n + 1).choose j : ℤ) + ((n + 1).choose (j + 1) : ℤ) := by
        have h := Nat.choose_succ_succ (n + 1) j
        exact_mod_cast h
      have hcast : ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 := by push_cast; ring
      rw [hcast, show ((k : ℤ) + 1 + 1 - ((j : ℤ) + 1)) = ((k : ℤ) + 1 - j) from by ring, hp]
      ring
    linear_combination e3
  linear_combination hLHS + hS1 - hS2

/-- The `n = 0` row of the explicit form: `∑_{i=0}^{k+1} (-1)ⁱ·C(1,i) = 0`
(the alternating sum of the binomials in row `1` past the first cancels). -/
private theorem base_row_sum (k : ℕ) :
    ∑ i ∈ range (k + 2), (-1 : ℤ) ^ i * (Nat.choose 1 i : ℤ) = 0 := by
  induction k with
  | zero => norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  | succ k ih =>
    rw [show k + 1 + 2 = k + 2 + 1 from rfl, Finset.sum_range_succ, ih,
      Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero, add_zero]

/-! ## Matching to the combinatorial definition -/

/-- **The explicit closed form for the Eulerian numbers.**
`⟨n,k⟩ = ∑_{i=0}^{k} (-1)ⁱ · C(n+1,i) · (k+1-i)ⁿ`. -/
theorem eulerian_eq_explicit (n k : ℕ) :
    (eulerian n k : ℤ) = eulerianExplicit n k := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp [eulerianExplicit, eulerian]
    | succ k =>
      rw [eulerian_zero_succ, Nat.cast_zero]
      symm
      unfold eulerianExplicit
      simp only [pow_zero, mul_one, Nat.zero_add]
      exact base_row_sum k
  | succ n ih =>
    cases k with
    | zero =>
      rw [eulerian_succ_zero, Nat.cast_one]
      simp [eulerianExplicit]
    | succ k =>
      rw [eulerian_succ_succ]
      push_cast
      rw [ih (k + 1), ih k]
      have hbridge : ((n - k : ℕ) : ℤ) * eulerianExplicit n k
          = ((n : ℤ) - k) * eulerianExplicit n k := by
        rcases le_or_gt k n with hkn | hkn
        · rw [Nat.cast_sub hkn]
        · have hz : eulerianExplicit n k = 0 := by
            rw [← ih k, eulerian_eq_zero_of_lt hkn, Nat.cast_zero]
          rw [hz, mul_zero, mul_zero]
      rw [hbridge, eulerianExplicit_succ_succ]

end GeometricSeriesOQ07OQ01OQ01OQ01OQ02
