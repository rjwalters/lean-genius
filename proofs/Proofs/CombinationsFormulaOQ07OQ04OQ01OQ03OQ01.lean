import Mathlib
import Proofs.CombinationsFormulaOQ07
import Proofs.CombinationsFormulaOQ07OQ04OQ01
import Proofs.CombinationsFormulaOQ07OQ04OQ01OQ03

/-
# The Two-Sided Cross Moment of a Product of Two Pascal Rows

## Open Question OQ-07-OQ-04-OQ-01-OQ-03-OQ-01

Two falling-factorial moment generalisations of the central binomial identity
`∑_k C(n,k)² = C(2n, n)` (OQ-07) have already been computed in this family:

* **Two rows, left weight only** (OQ-07-OQ-04-OQ-01-OQ-01): replacing the squared row
  `C(n,k)²` by a product of *two different* rows `C(m,k)·C(n,k)` and weighting from the
  left end by `(k)_r`,

    ∑_{k} (k)_r · C(m,k)·C(n,k)  =  (m)_r · C(m + n − r, n − r),                  (♦)

* **One row squared, both ends weighted** (OQ-07-OQ-04-OQ-01-OQ-03): keeping the square
  `C(n,k)²` but weighting from *both* ends by `(k)_r · (n − k)_s`,

    ∑_{k} (k)_r · (n − k)_s · C(n,k)²  =  (n)_r · (n)_s · C(2n − r − s, n − r − s).  (✦)

OQ-07-OQ-04-OQ-01-OQ-03 ends by asking for their **common generalisation**: does the same
reflect-and-absorb scheme give the *two-sided cross moment*, weighting the product of two
different rows from both ends at once?  The answer is yes, in one closed form:

  ∑_{k=0}^{n} (k)_r · (n − k)_s · C(m,k)·C(n,k)
        =  (m)_r · (n)_s · C(m + n − r − s, n − r − s),     (r ≤ m, r + s ≤ n).      (✦✦)

This is absent from Mathlib.  It sits at the join of the two generalisations above and
recovers each as a face:

  s = 0 :  (✦✦) ⇒  ∑ (k)_r·C(m,k)·C(n,k)      = (m)_r·C(m+n−r, n−r)        (the two-row moment ♦)
  m = n :  (✦✦) ⇒  ∑ (k)_r·(n−k)_s·C(n,k)²    = (n)_r·(n)_s·C(2n−r−s, n−r−s) (the two-sided moment ✦)
  r,s = 0: (✦✦) ⇒  ∑ C(m,k)·C(n,k)            = C(m+n, n)                   (asymmetric Vandermonde)

## The proof of (✦✦): one absorption per end, on its own row

The weights peel off independently because each is anchored to its **own** row.  The left
weight `(k)_r` absorbs into row `m` by the parent's iterated falling absorption,

  (k)_r · C(m, k) = (m)_r · C(m − r, k − r)                    (r ≤ k ≤ m),

and the right weight `(n − k)_s` co-absorbs into row `n` by the mirror co-absorption of
OQ-07-OQ-04-OQ-01-OQ-03,

  (n − k)_s · C(n, k) = (n)_s · C(n − s, k)                    (k + s ≤ n).

Splitting `C(m,k)·C(n,k)` into its two factors, the order-`< r` terms (left) and
order-`> n − s` terms (right) vanish; on the survivors `k ∈ [r, n − s]` the two absorptions
fire on disjoint factors, and reindexing `k ↦ r + j` lands the residual on the **doubly-shifted
two-parameter Vandermonde diagonal** already proved for (✦),

  ∑_{j} C(m − r, j) · C(n − s, j + r) = C(m + n − r − s, n − r − s),   (vandermonde_diag_two).

Pulling out the constant `(m)_r · (n)_s` gives (✦✦).  The single new wrinkle versus (✦) is
that the two rows now differ, so the survivor window `[r, n − s]` can stick out past `m`; on
those terms `C(m, k) = 0` and the matching `C(m − r, ·) = 0`, so they vanish on both sides and
the per-term identity still holds (handled by the `r + i ≤ m` case split below).

## Results

1. `sum_twoSided_descFactorial_mixed` — the two-sided cross moment (✦✦), for `r ≤ m`, `r + s ≤ n`.
2. `sum_oneSided_mixed_of_twoSided` — the `s = 0` face: recovers the two-row moment (♦).
3. `sum_twoSided_sq_of_mixed` — the `m = n` face: recovers the two-sided square moment (✦).
4. `sum_mixed_vandermonde` — the `r = s = 0` face: the asymmetric Vandermonde `C(m+n, n)`.
5. `sum_twoSided_mixed_first` — the `r = s = 1` symmetric first cross moment
   `∑ k(n−k)·C(m,k)·C(n,k) = m·n·C(m+n−2, n−2)`.

## Axioms: 0 | Sorries: 0
-/

namespace CombinationsFormulaOQ07OQ04OQ01OQ03OQ01

open Finset

/-- **The two-sided cross moment.** `(✦✦)`  For `r ≤ m` and `r + s ≤ n`,

      ∑_{k=0}^{n} (k)_r · (n − k)_s · C(m,k)·C(n,k)
            =  (m)_r · (n)_s · C(m + n − r − s, n − r − s).

    Each weight is anchored to its own row: the left weight `(k)_r` absorbs into row `m` and the
    right weight `(n − k)_s` co-absorbs into row `n`.  The order-`< r` and order-`> n − s` terms
    vanish, the survivors `k ∈ [r, n − s]` are rewritten by the two absorptions on disjoint
    factors (terms with `k > m` vanish on both sides), and the doubly-shifted two-parameter
    Vandermonde diagonal closes the inner sum. -/
theorem sum_twoSided_descFactorial_mixed (r s m n : ℕ) (hr : r ≤ m) (hrs : r + s ≤ n) :
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
  -- Absorb from both ends term by term, with a case split on whether `k = r + i` exceeds `m`.
  have hterm : ∀ i ∈ range ((n - r - s) + 1),
      (r + i).descFactorial r * (n - (r + i)).descFactorial s
          * (m.choose (r + i) * n.choose (r + i))
        = m.descFactorial r * n.descFactorial s
            * ((m - r).choose i * (n - s).choose (i + r)) := by
    intro i hi
    rw [Finset.mem_range, Nat.lt_succ_iff] at hi
    -- Right co-absorption on row `n` always applies: `r + i ≤ n − s ≤ n` and `s ≤ n − (r + i)`.
    have hB := CombinationsFormulaOQ07OQ04OQ01OQ03.descFactorial_sub_mul_choose s n (r + i)
      (by omega) (by omega)
    -- hB : (n-(r+i)).descFactorial s * n.choose (r+i) = n.descFactorial s * (n-s).choose (r+i)
    by_cases hk : r + i ≤ m
    · -- Left absorption on row `m` applies.
      have hA := CombinationsFormulaOQ07OQ04OQ01.descFactorial_mul_choose r m (r + i)
        (by omega) hk
      rw [show r + i - r = i by omega] at hA
      -- hA : (r+i).descFactorial r * m.choose (r+i) = m.descFactorial r * (m-r).choose i
      calc (r + i).descFactorial r * (n - (r + i)).descFactorial s
              * (m.choose (r + i) * n.choose (r + i))
          = ((r + i).descFactorial r * m.choose (r + i))
              * ((n - (r + i)).descFactorial s * n.choose (r + i)) := by ring
        _ = (m.descFactorial r * (m - r).choose i)
              * (n.descFactorial s * (n - s).choose (r + i)) := by rw [hA, hB]
        _ = m.descFactorial r * n.descFactorial s
              * ((m - r).choose i * (n - s).choose (i + r)) := by
              rw [show i + r = r + i by omega]; ring
    · -- `k = r + i > m`: both sides vanish since `C(m, r+i) = 0` and `C(m−r, i) = 0`.
      have hcm : m.choose (r + i) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      have hcmr : (m - r).choose i = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [hcm, hcmr]; ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  -- Close with the doubly-shifted two-parameter Vandermonde diagonal (from OQ-…-OQ-03).
  have hvd := CombinationsFormulaOQ07OQ04OQ01OQ03.vandermonde_diag_two (m - r) (n - s) r (by omega)
  rw [show (n - s) - r + 1 = (n - r - s) + 1 by omega] at hvd
  rw [hvd, show (m - r) + (n - s) = m + n - r - s by omega,
      show (n - s) - r = n - r - s by omega]

/-- **The `s = 0` face: the two-row (one-sided) moment `(♦)`.**
    `∑ (k)_r · C(m,k)·C(n,k) = (m)_r · C(m+n−r, n−r)` (`r ≤ m`, `r ≤ n`).  This is the headline
    of OQ-07-OQ-04-OQ-01-OQ-01, here over the symmetric range `[0, n]`; the `r ≤ n` hypothesis
    is the `s = 0` shadow of `r + s ≤ n` and is needed because that range only reaches `k = n`
    (for `r > n` every term carries the vanishing weight `(k)_r = 0`). -/
theorem sum_oneSided_mixed_of_twoSided (r m n : ℕ) (hr : r ≤ m) (hrn : r ≤ n) :
    ∑ k ∈ range (n + 1), k.descFactorial r * (m.choose k * n.choose k)
      = m.descFactorial r * (m + n - r).choose (n - r) := by
  have h := sum_twoSided_descFactorial_mixed r 0 m n hr (by omega)
  simp only [Nat.descFactorial_zero, Nat.sub_zero, mul_one] at h
  exact h

/-- **The `m = n` face: the two-sided square moment `(✦)`.**
    `∑ (k)_r · (n−k)_s · C(n,k)² = (n)_r · (n)_s · C(2n−r−s, n−r−s)` (`r + s ≤ n`).  This is the
    headline of OQ-07-OQ-04-OQ-01-OQ-03. -/
theorem sum_twoSided_sq_of_mixed (r s n : ℕ) (hrs : r + s ≤ n) :
    ∑ k ∈ range (n + 1), k.descFactorial r * (n - k).descFactorial s * (n.choose k) ^ 2
      = n.descFactorial r * n.descFactorial s * (2 * n - r - s).choose (n - r - s) := by
  have h := sum_twoSided_descFactorial_mixed r s n n (by omega) hrs
  rw [show n + n - r - s = 2 * n - r - s by omega] at h
  rw [← h]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [pow_two]

/-- **The `r = s = 0` face: the asymmetric Vandermonde** `∑ C(m,k)·C(n,k) = C(m+n, n)`. -/
theorem sum_mixed_vandermonde (m n : ℕ) :
    ∑ k ∈ range (n + 1), m.choose k * n.choose k = (m + n).choose n := by
  have h := sum_twoSided_descFactorial_mixed 0 0 m n (Nat.zero_le m) (by omega)
  simp only [Nat.descFactorial_zero, one_mul, Nat.sub_zero] at h
  exact h

/-- **Symmetric first cross moment** (`r = s = 1`):
    `∑ k(n−k) · C(m,k)·C(n,k) = m·n · C(m+n−2, n−2)` (`1 ≤ m`, `2 ≤ n`). -/
theorem sum_twoSided_mixed_first (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n) :
    ∑ k ∈ range (n + 1), k * (n - k) * (m.choose k * n.choose k)
      = m * n * (m + n - 2).choose (n - 2) := by
  have h := sum_twoSided_descFactorial_mixed 1 1 m n hm (by omega)
  simp only [Nat.descFactorial_one] at h
  rw [show m + n - 1 - 1 = m + n - 2 by omega, show n - 1 - 1 = n - 2 by omega] at h
  rw [h]

/-- Sanity check of `(✦✦)` at `r = 1, s = 1, m = 2, n = 3`:
    `∑ k(3−k)·C(2,k)·C(3,k) = 0 + 12 + 6 + 0 = 18 = 2·3·C(3,1)`. -/
example : ∑ k ∈ range 4,
      k.descFactorial 1 * (3 - k).descFactorial 1 * ((2 : ℕ).choose k * (3 : ℕ).choose k)
    = (2 : ℕ).descFactorial 1 * (3 : ℕ).descFactorial 1 * (2 + 3 - 1 - 1).choose (3 - 1 - 1) := by
  decide

/-- Sanity check of `(✦✦)` at `r = 2, s = 1, m = 3, n = 4`:
    `∑ (k)_2·(4−k)·C(3,k)·C(4,k) = (3)_2·(4)_1·C(4,1) = 6·4·4 = 96`. -/
example : ∑ k ∈ range 5,
      k.descFactorial 2 * (4 - k).descFactorial 1 * ((3 : ℕ).choose k * (4 : ℕ).choose k)
    = (3 : ℕ).descFactorial 2 * (4 : ℕ).descFactorial 1 * (3 + 4 - 2 - 1).choose (4 - 2 - 1) := by
  decide

end CombinationsFormulaOQ07OQ04OQ01OQ03OQ01
