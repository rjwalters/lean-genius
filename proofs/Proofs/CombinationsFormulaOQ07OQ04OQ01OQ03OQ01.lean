import Mathlib
import Proofs.CombinationsFormulaOQ07
import Proofs.CombinationsFormulaOQ07OQ04OQ01
import Proofs.CombinationsFormulaOQ07OQ04OQ01OQ03

/-
# The Rectangular (Off-Diagonal) Two-Sided Falling-Factorial Moment

## Open Question OQ-07-OQ-04-OQ-01-OQ-03-OQ-01

The parent file (OQ-07-OQ-04-OQ-01-OQ-03) computes the **two-sided** falling-factorial moment of
the *square* of one Pascal row,

  ∑_{k=0}^{n} (k)_r · (n − k)_s · C(n, k)²  =  (n)_r · (n)_s · C(2n − r − s, n − r − s),   (✦)

weighting the diagonal product `C(n, k)·C(n, k)` from both ends.  The square is special: both
factors come from the *same* row `n`.  The genuinely more general object replaces it by the
product of **two different rows** `C(m, k)·C(n, k)` — the "rectangular" or off-diagonal Vandermonde
product whose unweighted sum is the classical convolution `∑ C(m,k)·C(n,k) = C(m + n, n)`.  Its
two-sided falling moment is

  ∑_{k=0}^{n} (k)_r · (n − k)_s · C(m, k) · C(n, k) = (m)_r · (n)_s · C(m + n − r − s, n − r − s)  (✧)

valid for `r + s ≤ n ≤ m`.  This is absent from Mathlib.  The two row sizes `m` and `n` enter the
answer **independently**: the left falling weight of order `r` attaches to the left row `m` and
pushes it down to `m − r`, while the right falling weight of order `s` attaches to the right row
`n` and pushes it down to `n − s`; the single surviving Vandermonde entry sits at
`C((m−r) + (n−s), (n−s) − r) = C(m + n − r − s, n − r − s)`.  The diagonal `m = n` collapses (✧)
to the parent's (✦); the orderless case `r = s = 0` collapses it to Vandermonde's identity itself.

Special cases:

  r, s = 0       :  ∑ C(m,k)·C(n,k)            = C(m + n, n)               (Vandermonde — OQ-07)
  s = 0          :  ∑ (k)_r · C(m,k)·C(n,k)    = (m)_r·C(m + n − r, n − r)  (the one-sided moment)
  m = n          :  ∑ (k)_r·(n−k)_s·C(n,k)²    = (n)_r·(n)_s·C(2n−r−s,n−r−s)  (the parent's (✦))

## The proof of (✧): the parent's two ladders, with the rows decoupled

The left weight is removed by the grandparent's iterated **falling absorption**, now read on the
*left* row `m`,

  (k)_r · C(m, k) = (m)_r · C(m − r, k − r)                    (r ≤ k ≤ m).   (descFactorial_mul_choose)

The right weight is removed by the parent's **mirror co-absorption** on the *right* row `n`,

  (n − k)_s · C(n, k) = (n)_s · C(n − s, k)                    (k + s ≤ n).   (descFactorial_sub_mul_choose)

Applying both to `C(m, k)·C(n, k)`, the order-`< r` terms (left) and order-`> n − s` terms (right)
vanish, and reindexing `k ↦ r + j` turns the survivors into a Vandermonde convolution between the
two *independently shortened* rows `m − r` and `n − s`,

  ∑_{j} C(m − r, j) · C(n − s, j + r) = C(m + n − r − s, n − r − s),   (vandermonde_diag_two)

the same two-parameter diagonal that closed the parent — but here both of its rows are shortened,
which is exactly what lets a left weight on `m` and a right weight on `n` act at once.  Pulling out
the constant `(m)_r · (n)_s` gives (✧).  The hypothesis `n ≤ m` keeps every surviving index
`k ≤ n − s ≤ n ≤ m` inside the absorption domain `k ≤ m` of the left row.

## Results

1. `sum_rectangular_twoSided_descFactorial` — the rectangular two-sided closed form (✧).
2. `sum_rectangular_oneSided`         — the `s = 0` one-sided rectangular moment.
3. `sum_rectangular_vandermonde`      — the `r = s = 0` Vandermonde convolution `C(m + n, n)`.
4. `sum_recovers_twoSided_squared`    — the `m = n` diagonal recovers the parent's (✦).

## Axioms: 0 | Sorries: 0
-/

namespace CombinationsFormulaOQ07OQ04OQ01OQ03OQ01

open Finset

/-- **The rectangular two-sided falling-factorial moment.** `(✧)`  For all `r + s ≤ n ≤ m`,

      ∑_{k=0}^{n} (k)_r · (n − k)_s · C(m, k) · C(n, k)
        = (m)_r · (n)_s · C(m + n − r − s, n − r − s).

    The order-`< r` terms vanish on the left, the order-`> n − s` terms vanish on the right, the
    grandparent's left absorption (on row `m`) and the parent's right co-absorption (on row `n`)
    rewrite each survivor, and the doubly-shortened Vandermonde diagonal closes the inner sum. -/
theorem sum_rectangular_twoSided_descFactorial (r s m n : ℕ) (hrs : r + s ≤ n) (hnm : n ≤ m) :
    ∑ k ∈ range (n + 1),
        k.descFactorial r * (n - k).descFactorial s * (m.choose k * n.choose k)
      = m.descFactorial r * n.descFactorial s * (m + n - r - s).choose (n - r - s) := by
  -- Discard the low-order (left) and high-order (right) vanishing terms, keep `k ∈ [r, n − s]`.
  have split : ∑ k ∈ range (n + 1),
        k.descFactorial r * (n - k).descFactorial s * (m.choose k * n.choose k)
      = ∑ k ∈ Finset.Ico r (n - s + 1),
        k.descFactorial r * (n - k).descFactorial s * (m.choose k * n.choose k) := by
    have e1 := (Finset.sum_Ico_consecutive
        (fun k => k.descFactorial r * (n - k).descFactorial s * (m.choose k * n.choose k))
        (Nat.zero_le r) (show r ≤ n + 1 by omega)).symm
    have e2 := (Finset.sum_Ico_consecutive
        (fun k => k.descFactorial r * (n - k).descFactorial s * (m.choose k * n.choose k))
        (show r ≤ n - s + 1 by omega) (show n - s + 1 ≤ n + 1 by omega)).symm
    have z1 : ∑ k ∈ Finset.Ico 0 r,
        k.descFactorial r * (n - k).descFactorial s * (m.choose k * n.choose k) = 0 :=
      Finset.sum_eq_zero (fun k hk => by
        rw [Finset.mem_Ico] at hk
        rw [Nat.descFactorial_eq_zero_iff_lt.mpr hk.2]; ring)
    have z2 : ∑ k ∈ Finset.Ico (n - s + 1) (n + 1),
        k.descFactorial r * (n - k).descFactorial s * (m.choose k * n.choose k) = 0 :=
      Finset.sum_eq_zero (fun k hk => by
        rw [Finset.mem_Ico] at hk
        rw [Nat.descFactorial_eq_zero_iff_lt.mpr (show n - k < s by omega)]; ring)
    rw [Finset.range_eq_Ico, e1, z1, zero_add, e2, z2, add_zero]
  rw [split, Finset.sum_Ico_eq_sum_range, show n - s + 1 - r = (n - r - s) + 1 by omega]
  -- Absorb from both ends term by term, decoupling the two rows.
  have hterm : ∀ i ∈ range ((n - r - s) + 1),
      (r + i).descFactorial r * (n - (r + i)).descFactorial s
          * (m.choose (r + i) * n.choose (r + i))
        = m.descFactorial r * n.descFactorial s
            * ((m - r).choose i * (n - s).choose (i + r)) := by
    intro i hi
    rw [Finset.mem_range, Nat.lt_succ_iff] at hi
    have hA := CombinationsFormulaOQ07OQ04OQ01.descFactorial_mul_choose r m (r + i)
      (by omega) (by omega)
    rw [show r + i - r = i by omega] at hA
    -- hA : (r+i).descFactorial r * m.choose (r+i) = m.descFactorial r * (m-r).choose i
    have hB := CombinationsFormulaOQ07OQ04OQ01OQ03.descFactorial_sub_mul_choose s n (r + i)
      (by omega) (by omega)
    -- hB : (n-(r+i)).descFactorial s * n.choose (r+i) = n.descFactorial s * (n-s).choose (r+i)
    calc (r + i).descFactorial r * (n - (r + i)).descFactorial s
            * (m.choose (r + i) * n.choose (r + i))
        = ((r + i).descFactorial r * m.choose (r + i))
            * ((n - (r + i)).descFactorial s * n.choose (r + i)) := by ring
      _ = (m.descFactorial r * (m - r).choose i)
            * (n.descFactorial s * (n - s).choose (r + i)) := by rw [hA, hB]
      _ = m.descFactorial r * n.descFactorial s
            * ((m - r).choose i * (n - s).choose (i + r)) := by
            rw [show i + r = r + i by omega]; ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  -- Close with the doubly-shortened Vandermonde diagonal.
  have hvd := CombinationsFormulaOQ07OQ04OQ01OQ03.vandermonde_diag_two (m - r) (n - s) r
    (by omega)
  rw [show (n - s) - r + 1 = (n - r - s) + 1 by omega] at hvd
  rw [hvd, show (m - r) + (n - s) = m + n - r - s by omega,
      show (n - s) - r = n - r - s by omega]

/-- **One-sided rectangular moment** (`s = 0` case of `(✧)`):
    `∑ (k)_r · C(m,k)·C(n,k) = (m)_r · C(m + n − r, n − r)`, for `r ≤ n ≤ m`.
    The left falling weight attaches to the left row `m`; the right row `n` is untouched. -/
theorem sum_rectangular_oneSided (r m n : ℕ) (hr : r ≤ n) (hnm : n ≤ m) :
    ∑ k ∈ range (n + 1), k.descFactorial r * (m.choose k * n.choose k)
      = m.descFactorial r * (m + n - r).choose (n - r) := by
  have h := sum_rectangular_twoSided_descFactorial r 0 m n (by omega) hnm
  simp only [Nat.descFactorial_zero, Nat.sub_zero, mul_one] at h
  exact h

/-- **Vandermonde convolution** recovered as the orderless `r = s = 0` case of `(✧)`:
    `∑ C(m,k)·C(n,k) = C(m + n, n)`, for `n ≤ m`.  (Off-diagonal counterpart of `∑ C(n,k)²`.) -/
theorem sum_rectangular_vandermonde (m n : ℕ) (hnm : n ≤ m) :
    ∑ k ∈ range (n + 1), m.choose k * n.choose k = (m + n).choose n := by
  have h := sum_rectangular_twoSided_descFactorial 0 0 m n (by omega) hnm
  simp only [Nat.descFactorial_zero, Nat.sub_zero, one_mul, mul_one] at h
  exact h

/-- **Diagonal `m = n` recovers the parent's two-sided squared moment `(✦)`:**
    `∑ (k)_r·(n−k)_s·C(n,k)² = (n)_r·(n)_s·C(2n−r−s, n−r−s)`.  Agrees with
    `CombinationsFormulaOQ07OQ04OQ01OQ03.sum_twoSided_descFactorial_weighted_sq`. -/
theorem sum_recovers_twoSided_squared (r s n : ℕ) (hrs : r + s ≤ n) :
    ∑ k ∈ range (n + 1),
        k.descFactorial r * (n - k).descFactorial s * (n.choose k) ^ 2
      = n.descFactorial r * n.descFactorial s * (2 * n - r - s).choose (n - r - s) := by
  have h := sum_rectangular_twoSided_descFactorial r s n n hrs (le_refl n)
  rw [show n + n - r - s = 2 * n - r - s by omega] at h
  rw [← h]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [pow_two]

/-- Sanity check of `(✧)` at `r = 1, s = 1, m = 4, n = 3`:
    `∑ k(3−k)·C(4,k)·C(3,k) = (4)_1·(3)_1·C(5,1) = 4·3·5 = 60`. -/
example : ∑ k ∈ range 4,
      k.descFactorial 1 * (3 - k).descFactorial 1 * ((4 : ℕ).choose k * (3 : ℕ).choose k)
    = (4 : ℕ).descFactorial 1 * (3 : ℕ).descFactorial 1 * (4 + 3 - 1 - 1).choose (3 - 1 - 1) := by
  decide

/-- Sanity check of the Vandermonde case at `m = 5, n = 3`:
    `∑ C(5,k)·C(3,k) = C(8, 3) = 56`. -/
example : ∑ k ∈ range 4, (5 : ℕ).choose k * (3 : ℕ).choose k = (5 + 3).choose 3 := by
  decide

end CombinationsFormulaOQ07OQ04OQ01OQ03OQ01
