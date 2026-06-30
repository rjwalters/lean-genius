import Mathlib
import Proofs.CombinationsFormulaOQ07
import Proofs.CombinationsFormulaOQ07OQ04OQ01

/-
# The Two-Sided Falling-Factorial Moment of the Squares of Binomial Coefficients

## Open Question OQ-07-OQ-04-OQ-01-OQ-03

The parent file (OQ-07-OQ-04-OQ-01) computes the *one-sided* falling-factorial moment of the
squared Pascal row in one uniform closed form,

  ∑_{k=0}^{n} (k)_r · C(n, k)²  =  (n)_r · C(2n − r, n − r),                          (★)

weighting each term by the falling factorial `(k)_r = Nat.descFactorial k r` anchored at the
*left* end `k = 0`.  By the row symmetry `C(n, k) = C(n, n − k)` the squared row is a
palindrome, so it is just as natural to weight from the *right* end `k = n` by `(n − k)_s`.
The genuinely new object is the **two-sided** moment that weights from *both* ends at once,

  ∑_{k=0}^{n} (k)_r · (n − k)_s · C(n, k)²  =  (n)_r · (n)_s · C(2n − r − s, n − r − s),  (✦)

valid for all `r + s ≤ n`.  This is absent from Mathlib.  It is a strict generalisation of the
parent's one-sided ladder — and reveals that left- and right-falling weights combine
**additively in the off-centre shift**: a left order `r` and a right order `s` together push the
single Vandermonde entry from the centre `C(2n, n)` out to `C(2n − r − s, n − r − s)`, exactly as
if their orders were added.  Special cases:

  r, s = 0       :  ∑ C(n,k)²              = C(2n, n)           (central binomial — OQ-07)
  s = 0          :  ∑ (k)_r · C(n,k)²      = (n)_r·C(2n−r, n−r) (the one-sided moment ★)
  r = 0          :  ∑ (n−k)_s · C(n,k)²    = (n)_s·C(2n−s, n−s) (its mirror image)
  r = s = 1      :  ∑ k(n−k) · C(n,k)²     = n²·C(2n−2, n−2)    (the symmetric first moment)

## The proof of (✦): absorption from both ends + a two-parameter Vandermonde diagonal

The left weight is removed by the parent's iterated **falling absorption** (the conceptual core
of OQ-07-OQ-04-OQ-01),

  (k)_r · C(n, k) = (n)_r · C(n − r, k − r)                    (r ≤ k ≤ n).        (descFactorial_mul_choose)

The right weight is removed by its **mirror co-absorption**, obtained by reflecting the row
`C(n, k) = C(n, n − k)`, applying the same absorption at the reflected index, and reflecting back:

  (n − k)_s · C(n, k) = (n)_s · C(n − s, k)                    (k + s ≤ n).         (descFactorial_sub_mul_choose)

Applying both to `C(n, k)² = C(n, k) · C(n, k)`, the order-`< r` terms (left) and order-`> n − s`
terms (right) vanish, and reindexing `k ↦ r + j` turns the survivors into a Vandermonde
convolution along a **doubly-shifted diagonal**

  ∑_{j} C(n − r, j) · C(n − s, j + r) = C(2n − r − s, n − r − s),                   (vandermonde_diag_two)

a genuine two-parameter generalisation of the parent's `vandermonde_diag` (which is the case
`s = 0`).  Pulling out the constant `(n)_r · (n)_s` gives (✦).

## Results

1. `descFactorial_sub_mul_choose` — the right-end (mirror) co-absorption.
2. `vandermonde_diag_two` — the two-parameter (doubly-shifted) Vandermonde diagonal.
3. `sum_twoSided_descFactorial_weighted_sq` — the two-sided closed form (✦), for all `r + s ≤ n`.
4. `sum_oneSided_of_twoSided`, `sum_twoSided_first` — the `s = 0` (recovers ★) and `r = s = 1`
   specialisations.

## Axioms: 0 | Sorries: 0
-/

namespace CombinationsFormulaOQ07OQ04OQ01OQ03

open Finset

/-- **Right-end (mirror) co-absorption.** Reflecting the row `C(n, k) = C(n, n − k)`, applying
    the parent's falling absorption at the reflected index `n − k`, and reflecting back gives

      (n − k)_s · C(n, k) = (n)_s · C(n − s, k)                 (k ≤ n, s ≤ n − k).

    This is the right-anchored counterpart of `descFactorial_mul_choose`. -/
theorem descFactorial_sub_mul_choose (s n k : ℕ) (hk : k ≤ n) (hs : s ≤ n - k) :
    (n - k).descFactorial s * n.choose k = n.descFactorial s * (n - s).choose k := by
  have hsymm1 : n.choose k = n.choose (n - k) := (Nat.choose_symm hk).symm
  have habs := CombinationsFormulaOQ07OQ04OQ01.descFactorial_mul_choose s n (n - k)
    (by omega) (by omega)
  -- habs : (n-k).descFactorial s * n.choose (n-k) = n.descFactorial s * (n-s).choose ((n-k)-s)
  rw [hsymm1, habs]
  congr 1
  rw [show (n - k) - s = (n - s) - k by omega]
  exact Nat.choose_symm (by omega)

/-- **Two-parameter Vandermonde diagonal.** Reading Vandermonde's convolution
    `add_choose_eq_sum_range` (OQ-07) along the diagonal shifted `t` off-centre against a
    *second* row `b`:

      ∑_{j=0}^{b−t} C(a, j) · C(b, j + t) = C(a + b, b − t)              (t ≤ b).

    The reflection `C(b, j + t) = C(b, (b−t) − j)` (`Nat.choose_symm`) aligns the shifted
    summand with the convolution.  The parent's `vandermonde_diag` is the case `a = n − r`,
    `b = n`, `t = r`; here the second row `b` is itself shortened, which is what lets a *right*
    falling weight enter the shift. -/
theorem vandermonde_diag_two (a b t : ℕ) (ht : t ≤ b) :
    ∑ j ∈ range ((b - t) + 1), a.choose j * b.choose (j + t) = (a + b).choose (b - t) := by
  rw [CombinationsFormulaOQ07.add_choose_eq_sum_range a b (b - t)]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Finset.mem_range, Nat.lt_succ_iff] at hj
  have hle : j + t ≤ b := by omega
  rw [show (b - t) - j = b - (j + t) by omega, Nat.choose_symm hle]

/-- **The two-sided falling-factorial moment.** `(✦)`  For all `r + s ≤ n`,

      ∑_{k=0}^{n} (k)_r · (n − k)_s · C(n, k)²  =  (n)_r · (n)_s · C(2n − r − s, n − r − s).

    The order-`< r` terms vanish on the left, the order-`> n − s` terms vanish on the right, the
    two absorptions rewrite each survivor, and the doubly-shifted Vandermonde diagonal closes the
    inner sum. -/
theorem sum_twoSided_descFactorial_weighted_sq (r s n : ℕ) (hrs : r + s ≤ n) :
    ∑ k ∈ range (n + 1),
        k.descFactorial r * (n - k).descFactorial s * (n.choose k) ^ 2
      = n.descFactorial r * n.descFactorial s * (2 * n - r - s).choose (n - r - s) := by
  -- Discard the low-order (left) and high-order (right) vanishing terms, keep `k ∈ [r, n − s]`.
  have split : ∑ k ∈ range (n + 1),
        k.descFactorial r * (n - k).descFactorial s * (n.choose k) ^ 2
      = ∑ k ∈ Finset.Ico r (n - s + 1),
        k.descFactorial r * (n - k).descFactorial s * (n.choose k) ^ 2 := by
    have e1 := (Finset.sum_Ico_consecutive
        (fun k => k.descFactorial r * (n - k).descFactorial s * (n.choose k) ^ 2)
        (Nat.zero_le r) (show r ≤ n + 1 by omega)).symm
    have e2 := (Finset.sum_Ico_consecutive
        (fun k => k.descFactorial r * (n - k).descFactorial s * (n.choose k) ^ 2)
        (show r ≤ n - s + 1 by omega) (show n - s + 1 ≤ n + 1 by omega)).symm
    have z1 : ∑ k ∈ Finset.Ico 0 r,
        k.descFactorial r * (n - k).descFactorial s * (n.choose k) ^ 2 = 0 :=
      Finset.sum_eq_zero (fun k hk => by
        rw [Finset.mem_Ico] at hk
        rw [Nat.descFactorial_eq_zero_iff_lt.mpr hk.2]; ring)
    have z2 : ∑ k ∈ Finset.Ico (n - s + 1) (n + 1),
        k.descFactorial r * (n - k).descFactorial s * (n.choose k) ^ 2 = 0 :=
      Finset.sum_eq_zero (fun k hk => by
        rw [Finset.mem_Ico] at hk
        rw [Nat.descFactorial_eq_zero_iff_lt.mpr (show n - k < s by omega)]; ring)
    rw [Finset.range_eq_Ico, e1, z1, zero_add, e2, z2, add_zero]
  rw [split, Finset.sum_Ico_eq_sum_range, show n - s + 1 - r = (n - r - s) + 1 by omega]
  -- Absorb from both ends term by term.
  have hterm : ∀ i ∈ range ((n - r - s) + 1),
      (r + i).descFactorial r * (n - (r + i)).descFactorial s * (n.choose (r + i)) ^ 2
        = n.descFactorial r * n.descFactorial s
            * ((n - r).choose i * (n - s).choose (i + r)) := by
    intro i hi
    rw [Finset.mem_range, Nat.lt_succ_iff] at hi
    have hA := CombinationsFormulaOQ07OQ04OQ01.descFactorial_mul_choose r n (r + i)
      (by omega) (by omega)
    rw [show r + i - r = i by omega] at hA
    -- hA : (r+i).descFactorial r * n.choose (r+i) = n.descFactorial r * (n-r).choose i
    have hB := descFactorial_sub_mul_choose s n (r + i) (by omega) (by omega)
    -- hB : (n-(r+i)).descFactorial s * n.choose (r+i) = n.descFactorial s * (n-s).choose (r+i)
    calc (r + i).descFactorial r * (n - (r + i)).descFactorial s * (n.choose (r + i)) ^ 2
        = ((r + i).descFactorial r * n.choose (r + i))
            * ((n - (r + i)).descFactorial s * n.choose (r + i)) := by ring
      _ = (n.descFactorial r * (n - r).choose i)
            * (n.descFactorial s * (n - s).choose (r + i)) := by rw [hA, hB]
      _ = n.descFactorial r * n.descFactorial s
            * ((n - r).choose i * (n - s).choose (i + r)) := by
            rw [show i + r = r + i by omega]; ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  -- Close with the doubly-shifted Vandermonde diagonal.
  have hvd := vandermonde_diag_two (n - r) (n - s) r (by omega)
  rw [show (n - s) - r + 1 = (n - r - s) + 1 by omega] at hvd
  rw [hvd, show (n - r) + (n - s) = 2 * n - r - s by omega,
      show (n - s) - r = n - r - s by omega]

/-- **Recovering the one-sided moment `(★)`** as the `s = 0` case of `(✦)`:
    `∑ (k)_r · C(n,k)² = (n)_r · C(2n − r, n − r)`.  Agrees with the parent's
    `sum_descFactorial_weighted_sq`. -/
theorem sum_oneSided_of_twoSided (r n : ℕ) (hr : r ≤ n) :
    ∑ k ∈ range (n + 1), k.descFactorial r * (n.choose k) ^ 2
      = n.descFactorial r * (2 * n - r).choose (n - r) := by
  have h := sum_twoSided_descFactorial_weighted_sq r 0 n (by omega)
  simp only [Nat.descFactorial_zero, Nat.sub_zero, mul_one] at h
  exact h

/-- **Symmetric first moment** (`r = s = 1`): `∑ k(n−k) · C(n,k)² = n² · C(2n−2, n−2)`. -/
theorem sum_twoSided_first (n : ℕ) (hn : 2 ≤ n) :
    ∑ k ∈ range (n + 1), k * (n - k) * (n.choose k) ^ 2
      = n ^ 2 * (2 * n - 2).choose (n - 2) := by
  have h := sum_twoSided_descFactorial_weighted_sq 1 1 n (by omega)
  simp only [Nat.descFactorial_one] at h
  rw [show 2 * n - 1 - 1 = 2 * n - 2 by omega, show n - 1 - 1 = n - 2 by omega] at h
  rw [h]; ring

/-- Sanity check of (✦) at `r = 1, s = 1, n = 3`:
    `∑ k(3−k)·C(3,k)² = 0 + 18 + 18 + 0 = 36 = 3²·C(4,1)`. -/
example : ∑ k ∈ range 4,
      k.descFactorial 1 * (3 - k).descFactorial 1 * ((3 : ℕ).choose k) ^ 2
    = (3 : ℕ).descFactorial 1 * (3 : ℕ).descFactorial 1 * (2 * 3 - 1 - 1).choose (3 - 1 - 1) := by
  decide

/-- Sanity check of (✦) at `r = 2, s = 1, n = 4`:
    `∑ (k)_2·(4−k)·C(4,k)² = (4)_2·(4)_1·C(5,1) = 12·4·5 = 240`. -/
example : ∑ k ∈ range 5,
      k.descFactorial 2 * (4 - k).descFactorial 1 * ((4 : ℕ).choose k) ^ 2
    = (4 : ℕ).descFactorial 2 * (4 : ℕ).descFactorial 1 * (2 * 4 - 2 - 1).choose (4 - 2 - 1) := by
  decide

end CombinationsFormulaOQ07OQ04OQ01OQ03
