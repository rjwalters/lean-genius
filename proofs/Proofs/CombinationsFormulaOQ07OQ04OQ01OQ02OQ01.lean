import Mathlib
import Proofs.CombinationsFormulaOQ07OQ04OQ01
import Proofs.CombinationsFormulaOQ07OQ04OQ01OQ02
import Proofs.CombinationsFormulaOQ07OQ04OQ01OQ03

/-
# The General Power Moment of the Asymmetric Two-Row Vandermonde Diagonal

## Open Question OQ-07-OQ-04-OQ-01-OQ-02-OQ-01

The sibling file OQ-07-OQ-04-OQ-01-OQ-02 computes the **general raw power moment of the
*squared* Pascal row** in one Stirling-weighted closed form,

  ∑_{k=0}^{n} k^p · C(n, k)²  =  ∑_{r=0}^{p} S(p, r) · (n)_r · C(2n − r, n − r),         (▲)

where `S(p, r) = Nat.stirlingSecond p r` and `(x)_r = Nat.descFactorial x r`.  Its explicit
follow-up asks whether the *same* Stirling bridge applies verbatim to the **asymmetric
two-row** moment — replacing the square `C(n,k)²` by a product of two *different* Pascal rows
`C(m,k)·C(n,k)`:

  ∑_{k=0}^{n} k^p · C(m, k)·C(n, k)  =  ∑_{r=0}^{p} S(p, r) · (m)_r · C(m + n − r, n − r).  (▲▲)

The answer is yes — but with one genuinely new side condition, `p ≤ n`, that the symmetric
case hides.  This is the raw-power companion of the falling-factorial cross moment
`∑ (k)_r·C(m,k)·C(n,k) = (m)_r·C(m+n−r, n−r)`; (▲▲) is absent from Mathlib.

## The two ingredients

1. **The one-sided cross moment** `(♦)` (proved here from the merged ancestors, since it was
   never separately formalized):

     ∑_{k=0}^{n} (k)_r · C(m, k)·C(n, k)  =  (m)_r · C(m + n − r, n − r),     (r ≤ n).

   The left weight `(k)_r` absorbs into row `m` by the parent's iterated falling absorption
   `(k)_r·C(m,k) = (m)_r·C(m−r, k−r)` (`descFactorial_mul_choose`); reindexing `k ↦ r + j`
   lands the residual `∑_j C(m−r, j)·C(n, j+r)` on the asymmetric Vandermonde diagonal
   `C(m+n−r, n−r)` (`vandermonde_diag_two`).  The single hypothesis is `r ≤ n`: terms with
   `k > m` simply vanish (`C(m, k) = 0` matched by `C(m−r, k−r) = 0`), so unlike the
   absorption step itself the *statement* needs no `r ≤ m`.  Indeed for `m < r ≤ n` both sides
   are `0` — the left because every survivor `k ≥ r > m` kills `C(m, k)`, the right because
   `(m)_r = 0`.

2. **The Stirling bridge** `(♦♦)` `m^p = ∑_{r} S(p, r)·(m)_r` from OQ-07-OQ-04-OQ-01-OQ-02.

Expanding `k^p` by `(♦♦)`, swapping the order of summation, and closing each inner `k`-sum
with `(♦)` gives `(▲▲)`.

## Why `p ≤ n` — the asymmetric obstruction

In the symmetric moment `(▲)` the leading coefficient is `(n)_r`, which **self-annihilates**
for `r > n`; so the orders `r > n` drop out of `∑_{r=0}^{p}` for free and `(▲)` needs no bound
on `p`.  In the asymmetric `(▲▲)` the leading coefficient is `(m)_r`, which does **not** vanish
on the window `n < r ≤ m`.  There the inner moment `(♦)` is `0` (left side) but the closed
form `(m)_r·C(m+n−r, n−r)` is *not* `0`, so the two part company: `(▲▲)` as written would
acquire spurious terms.  Requiring `p ≤ n` keeps every Stirling order `r ≤ p ≤ n` inside the
range where `(♦)` holds, and is exactly the condition under which the asymmetric closed form is
faithful.  (By the `m ↔ n` symmetry of the left side, the mirror form with `(n)_r·C(m+n−r,
m−r)` holds under `p ≤ m`; together they cover `p ≤ max(m, n)`.)

## Results

1. `sum_descFactorial_cross` — the one-sided cross moment `(♦)`, `r ≤ n`, no `r ≤ m` needed.
2. `sum_pow_cross` — the general asymmetric power moment `(▲▲)`, for `p ≤ n`.
3. `sum_cross_vandermonde` — the `p = 0` face: the asymmetric Vandermonde `C(m+n, n)`.
4. `sum_first_cross` — the `p = 1` face: `∑ k·C(m,k)·C(n,k) = m·C(m+n−1, n−1)`.
5. `sum_pow_weighted_sq_of_cross` — the `m = n` face: recovers the sibling's symmetric `(▲)`.

## Axioms: 0 | Sorries: 0
-/

namespace CombinationsFormulaOQ07OQ04OQ01OQ02OQ01

open Finset

/-- **The one-sided cross moment** `(♦)`.  For `r ≤ n`,

      ∑_{k=0}^{n} (k)_r · C(m, k)·C(n, k)  =  (m)_r · C(m + n − r, n − r).

    The left weight absorbs into row `m`; reindexing lands the residual on the asymmetric
    Vandermonde diagonal.  Only `r ≤ n` is required: for `m < r ≤ n` both sides vanish (the
    left because the survivors `k ≥ r > m` kill `C(m, k)`, the right because `(m)_r = 0`). -/
theorem sum_descFactorial_cross (r m n : ℕ) (hr : r ≤ n) :
    ∑ k ∈ range (n + 1), k.descFactorial r * (m.choose k * n.choose k)
      = m.descFactorial r * (m + n - r).choose (n - r) := by
  rcases le_or_lt r m with hm | hm
  · -- Genuine case `r ≤ m` (and `r ≤ n`): absorb on row `m`, close with Vandermonde.
    have split : ∑ k ∈ range (n + 1), k.descFactorial r * (m.choose k * n.choose k)
        = ∑ k ∈ Finset.Ico r (n + 1), k.descFactorial r * (m.choose k * n.choose k) := by
      have e := Finset.sum_Ico_consecutive
        (fun k => k.descFactorial r * (m.choose k * n.choose k))
        (Nat.zero_le r) (show r ≤ n + 1 by omega)
      have z : ∑ k ∈ Finset.Ico 0 r,
          k.descFactorial r * (m.choose k * n.choose k) = 0 :=
        Finset.sum_eq_zero (fun k hk => by
          rw [Finset.mem_Ico] at hk
          rw [Nat.descFactorial_eq_zero_iff_lt.mpr hk.2]; ring)
      rw [Finset.range_eq_Ico, ← e, z, zero_add]
    rw [split, Finset.sum_Ico_eq_sum_range, show n + 1 - r = (n - r) + 1 by omega]
    have hterm : ∀ i ∈ range ((n - r) + 1),
        (r + i).descFactorial r * (m.choose (r + i) * n.choose (r + i))
          = m.descFactorial r * ((m - r).choose i * n.choose (i + r)) := by
      intro i hi
      rw [Finset.mem_range, Nat.lt_succ_iff] at hi
      by_cases hk : r + i ≤ m
      · have hA := CombinationsFormulaOQ07OQ04OQ01.descFactorial_mul_choose r m (r + i)
          (by omega) hk
        rw [show r + i - r = i by omega] at hA
        calc (r + i).descFactorial r * (m.choose (r + i) * n.choose (r + i))
            = ((r + i).descFactorial r * m.choose (r + i)) * n.choose (r + i) := by ring
          _ = (m.descFactorial r * (m - r).choose i) * n.choose (r + i) := by rw [hA]
          _ = m.descFactorial r * ((m - r).choose i * n.choose (i + r)) := by
                rw [show i + r = r + i by omega]; ring
      · -- `k = r + i > m`: `C(m, r+i) = 0` and `C(m−r, i) = 0`, both sides vanish.
        have hcm : m.choose (r + i) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        have hcmr : (m - r).choose i = 0 := Nat.choose_eq_zero_of_lt (by omega)
        rw [hcm, hcmr]; ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hvd := CombinationsFormulaOQ07OQ04OQ01OQ03.vandermonde_diag_two (m - r) n r hr
    rw [hvd, show (m - r) + n = m + n - r by omega]
  · -- `m < r ≤ n`: both sides are `0`.
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr hm, Nat.zero_mul]
    refine Finset.sum_eq_zero (fun k hk => ?_)
    rw [Finset.mem_range, Nat.lt_succ_iff] at hk
    rcases lt_or_le k r with hk2 | hk2
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hk2]; ring
    · rw [Nat.choose_eq_zero_of_lt (show m < k by omega)]; ring

/-- **The general asymmetric power moment** `(▲▲)`.  For `p ≤ n`,

      ∑_{k=0}^{n} k^p · C(m, k)·C(n, k)  =  ∑_{r=0}^{p} S(p, r) · (m)_r · C(m + n − r, n − r).

    Expand each `k^p` by the Stirling bridge, swap the order of summation, and close the inner
    `k`-sum with the one-sided cross moment `(♦)`.  The hypothesis `p ≤ n` keeps every Stirling
    order `r ≤ p` inside the range `r ≤ n` where `(♦)` is faithful. -/
theorem sum_pow_cross (p m n : ℕ) (hp : p ≤ n) :
    ∑ k ∈ range (n + 1), k ^ p * (m.choose k * n.choose k)
      = ∑ r ∈ range (p + 1),
          Nat.stirlingSecond p r * (m.descFactorial r * (m + n - r).choose (n - r)) := by
  have step1 : ∑ k ∈ range (n + 1), k ^ p * (m.choose k * n.choose k)
      = ∑ k ∈ range (n + 1), ∑ r ∈ range (p + 1),
          Nat.stirlingSecond p r * (k.descFactorial r * (m.choose k * n.choose k)) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [CombinationsFormulaOQ07OQ04OQ01OQ02.pow_eq_sum_stirlingSecond_descFactorial k p,
        Finset.sum_mul]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    ring
  rw [step1, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun r hr => ?_)
  rw [Finset.mem_range, Nat.lt_succ_iff] at hr
  rw [← Finset.mul_sum, sum_descFactorial_cross r m n (by omega)]

/-- **The `p = 0` face: the asymmetric Vandermonde** `∑ C(m,k)·C(n,k) = C(m+n, n)`. -/
theorem sum_cross_vandermonde (m n : ℕ) :
    ∑ k ∈ range (n + 1), m.choose k * n.choose k = (m + n).choose n := by
  have h := sum_descFactorial_cross 0 m n (Nat.zero_le n)
  simpa using h

/-- **The `p = 1` face: the first cross moment** `∑ k·C(m,k)·C(n,k) = m·C(m+n−1, n−1)`
    (`1 ≤ n`). -/
theorem sum_first_cross (m n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ range (n + 1), k * (m.choose k * n.choose k)
      = m * (m + n - 1).choose (n - 1) := by
  have h := sum_descFactorial_cross 1 m n hn
  simpa [Nat.descFactorial_one] using h

/-- **The `m = n` face: recovers the sibling's symmetric power moment** `(▲)`.
    `∑ k^p·C(n,k)² = ∑_r S(p,r)·(n)_r·C(2n−r, n−r)` (`p ≤ n`).  The sibling proves this
    *unconditionally* in `p` because `(n)_r` self-annihilates for `r > n`; here it appears as
    the `m = n` shadow of `(▲▲)`, valid on the common range `p ≤ n`. -/
theorem sum_pow_weighted_sq_of_cross (p n : ℕ) (hp : p ≤ n) :
    ∑ k ∈ range (n + 1), k ^ p * (n.choose k) ^ 2
      = ∑ r ∈ range (p + 1),
          Nat.stirlingSecond p r * (n.descFactorial r * (2 * n - r).choose (n - r)) := by
  have h := sum_pow_cross p n n hp
  rw [show n + n = 2 * n by ring] at h
  rw [← h]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [pow_two]

/-- Sanity check of `(▲▲)` at `p = 2, m = 3, n = 4`:
    `∑ k²·C(3,k)·C(4,k) = ∑_r S(2,r)·(3)_r·C(7−r, 4−r)`. -/
example : ∑ k ∈ range 5, k ^ 2 * ((3 : ℕ).choose k * (4 : ℕ).choose k)
    = ∑ r ∈ range 3, Nat.stirlingSecond 2 r
        * ((3 : ℕ).descFactorial r * (3 + 4 - r).choose (4 - r)) := by
  decide

/-- Sanity check of the one-sided cross moment `(♦)` at `r = 2, m = 3, n = 5`:
    `∑ (k)_2·C(3,k)·C(5,k) = (3)_2·C(6, 3) = 6·20 = 120`. -/
example : ∑ k ∈ range 6, k.descFactorial 2 * ((3 : ℕ).choose k * (5 : ℕ).choose k)
    = (3 : ℕ).descFactorial 2 * (3 + 5 - 2).choose (5 - 2) := by
  decide

/-- Sanity check that `(♦)` vanishes correctly in the asymmetric window `m < r ≤ n`
    (`r = 4, m = 2, n = 5`): the left side is `0` and `(2)_4 = 0`. -/
example : ∑ k ∈ range 6, k.descFactorial 4 * ((2 : ℕ).choose k * (5 : ℕ).choose k)
    = (2 : ℕ).descFactorial 4 * (2 + 5 - 4).choose (5 - 4) := by
  decide

end CombinationsFormulaOQ07OQ04OQ01OQ02OQ01
