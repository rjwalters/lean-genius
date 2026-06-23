import Mathlib
import Proofs.CombinationsFormulaOQ07
import Proofs.CombinationsFormulaOQ07OQ04OQ01

/-
# The Mixed (Two-Row) Falling-Factorial Moment

## Open Question OQ-07-OQ-04-OQ-01-OQ-01

The parent file (OQ-07-OQ-04-OQ-01) computes, for the *square* of a single Pascal row,
the general falling-factorial moment

  ∑_{k=0}^{n} (k)_r · C(n, k)²  =  (n)_r · C(2n − r, n − r),                       (★)

where `(k)_r = Nat.descFactorial k r` is the falling factorial.  Its proof has two
ingredients: a single-row *iterated absorption* `(k)_r · C(n,k) = (n)_r · C(n−r, k−r)`
and a Vandermonde diagonal that closes the resulting convolution.

The square `C(n,k)²` is symmetric, but the absorption only ever touches **one** of the two
factors.  This suggests the natural generalisation: take the falling-factorial moment of
the product of **two different** Pascal rows, `C(m, k)·C(n, k)` with `m ≠ n`.  The single
plain row `C(n, k)` is untouched by absorption on row `m`, and the answer is a single,
asymmetric off-centre Vandermonde entry:

  ∑_{k=0}^{m} (k)_r · C(m, k)·C(n, k)  =  (m)_r · C(m + n − r, n − r),   (r ≤ m).  (♦)

This is the **mixed moment** and it is absent from Mathlib.  It unifies several identities
of the OQ-07 family as specialisations:

  m = n :  (♦) ⇒  ∑ (k)_r·C(n,k)²        = (n)_r·C(2n−r, n−r)   (the parent (★))
  r = 0 :  (♦) ⇒  ∑ C(m,k)·C(n,k)        = C(m+n, n)            (asymmetric Vandermonde)
  r = 1 :  (♦) ⇒  ∑ k·C(m,k)·C(n,k)      = m·C(m+n−1, n−1)      (mixed first moment)

## The proof of (♦)

The iterated absorption from the parent applies to **row `m`** verbatim:

  (k)_r · C(m, k) = (m)_r · C(m − r, k − r)              (r ≤ k ≤ m).

Summing over `k`, the orders `k < r` vanish and reindexing `k ↦ k − r` leaves the constant
`(m)_r` times a genuine two-row Vandermonde convolution on the **shifted diagonal**

  ∑_{i=0}^{m−r} C(m − r, i) · C(n, i + r) = C(m + n − r, n − r).    (vandermonde_mixed_diag)

Unlike the square case, the two factors no longer reflect into each other directly.  The
clean route is to reflect the *first* factor, `i ↦ (m−r) − i`, which turns `C(n, i+r)` into
`C(n, m − i)`; the sum is then literally Vandermonde's convolution
`∑_i C(m−r, i)·C(n, m−i) = C(m+n−r, m)` (after harmlessly extending the range, the extra
terms carrying `C(m−r, i) = 0`), and `C(m+n−r, m) = C(m+n−r, n−r)` by symmetry.

## Results

1. `vandermonde_mixed_diag` — the two-row off-centre Vandermonde diagonal.
2. `sum_descFactorial_mixed` — the mixed closed form (♦), for all `r ≤ m`.
3. `sum_descFactorial_sq_recovered` — the parent square moment (★) recovered at `m = n`.
4. `sum_mixed_vandermonde`, `sum_first_mixed` — the `r = 0` (Vandermonde) and `r = 1`
   (mixed first moment) specialisations.

## Axioms: 0 | Sorries: 0
-/

namespace CombinationsFormulaOQ07OQ04OQ01OQ01

open Finset

/-- **Mixed (two-row) Vandermonde diagonal.** For `r ≤ m`,

      ∑_{i=0}^{m−r} C(m − r, i) · C(n, i + r) = C(m + n − r, n − r).

    Reflecting the first factor `i ↦ (m−r) − i` rewrites `C(n, i+r)` as `C(n, m − i)`,
    turning the sum into Vandermonde's convolution `∑_i C(m−r, i)·C(n, m−i) = C(m+n−r, m)`
    (the range harmlessly extended, the new terms carrying `C(m−r, i) = 0`); the answer
    `C(m+n−r, m) = C(m+n−r, n−r)` follows by symmetry of the binomial coefficient. -/
theorem vandermonde_mixed_diag (r m n : ℕ) (hr : r ≤ m) :
    ∑ i ∈ range ((m - r) + 1), (m - r).choose i * n.choose (i + r)
      = (m + n - r).choose (n - r) := by
  -- Reflect i ↦ (m-r) - i to turn `C(n, i+r)` into `C(n, m - i)`.
  have hreflect : ∑ i ∈ range ((m - r) + 1), (m - r).choose i * n.choose (i + r)
      = ∑ i ∈ range ((m - r) + 1), (m - r).choose i * n.choose (m - i) := by
    rw [← Finset.sum_range_reflect
          (fun i => (m - r).choose i * n.choose (i + r)) ((m - r) + 1)]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range, Nat.lt_succ_iff] at hi
    dsimp only
    rw [show (m - r) + 1 - 1 - i = (m - r) - i by omega,
        Nat.choose_symm (show i ≤ m - r by omega),
        show (m - r) - i + r = m - i by omega]
  -- Extend the range to `m + 1`; the new terms vanish since `C(m-r, i) = 0` for `i > m-r`.
  have hextend : ∑ i ∈ range ((m - r) + 1), (m - r).choose i * n.choose (m - i)
      = ∑ i ∈ range (m + 1), (m - r).choose i * n.choose (m - i) := by
    refine Finset.sum_subset (Finset.range_subset.mpr (by omega)) (fun i _ hi => ?_)
    simp only [Finset.mem_range, not_lt] at hi
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.zero_mul]
  rw [hreflect, hextend, ← CombinationsFormulaOQ07.add_choose_eq_sum_range (m - r) n m,
      show (m - r) + n = m + n - r by omega,
      show n - r = (m + n - r) - m by omega, Nat.choose_symm (by omega)]

/-- **The mixed falling-factorial moment.** `(♦)`  For all `r ≤ m`,

      ∑_{k=0}^{m} (k)_r · C(m, k)·C(n, k)  =  (m)_r · C(m + n − r, n − r).

    Orders `k < r` vanish; the iterated absorption on row `m` rewrites each remaining term;
    the mixed Vandermonde diagonal closes the inner sum. -/
theorem sum_descFactorial_mixed (r m n : ℕ) (hr : r ≤ m) :
    ∑ k ∈ range (m + 1), k.descFactorial r * (m.choose k * n.choose k)
      = m.descFactorial r * (m + n - r).choose (n - r) := by
  -- Discard the vanishing low-order terms `k < r`, reindex `k ↦ k − r`.
  have key : ∑ k ∈ range (m + 1), k.descFactorial r * (m.choose k * n.choose k)
           = ∑ k ∈ Finset.Ico r (m + 1), k.descFactorial r * (m.choose k * n.choose k) := by
    rw [Finset.range_eq_Ico,
        ← Finset.sum_Ico_consecutive _ (Nat.zero_le r) (show r ≤ m + 1 by omega)]
    have hlow : ∑ k ∈ Finset.Ico 0 r, k.descFactorial r * (m.choose k * n.choose k) = 0 :=
      Finset.sum_eq_zero (fun k hk => by
        rw [Finset.mem_Ico] at hk
        rw [Nat.descFactorial_eq_zero_iff_lt.mpr hk.2, Nat.zero_mul])
    rw [hlow, zero_add]
  rw [key, Finset.sum_Ico_eq_sum_range, show m + 1 - r = (m - r) + 1 by omega]
  -- Falling absorption (on row `m`) term by term.
  have hterm : ∀ i ∈ range ((m - r) + 1),
      (r + i).descFactorial r * (m.choose (r + i) * n.choose (r + i))
        = m.descFactorial r * ((m - r).choose i * n.choose (i + r)) := by
    intro i hi
    rw [Finset.mem_range, Nat.lt_succ_iff] at hi
    have habs := CombinationsFormulaOQ07OQ04OQ01.descFactorial_mul_choose r m (r + i)
      (by omega) (by omega)
    rw [show r + i - r = i by omega] at habs
    calc (r + i).descFactorial r * (m.choose (r + i) * n.choose (r + i))
        = ((r + i).descFactorial r * m.choose (r + i)) * n.choose (r + i) := by ring
      _ = (m.descFactorial r * (m - r).choose i) * n.choose (r + i) := by rw [habs]
      _ = m.descFactorial r * ((m - r).choose i * n.choose (i + r)) := by
            rw [show i + r = r + i by omega]; ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, vandermonde_mixed_diag r m n hr]

/-- **Recovers the parent square moment `(★)`** at `m = n`:
    `∑ (k)_r·C(n,k)² = (n)_r·C(2n−r, n−r)`. -/
theorem sum_descFactorial_sq_recovered (r n : ℕ) (hr : r ≤ n) :
    ∑ k ∈ range (n + 1), k.descFactorial r * (n.choose k) ^ 2
      = n.descFactorial r * (2 * n - r).choose (n - r) := by
  have h := sum_descFactorial_mixed r n n hr
  rw [show n + n - r = 2 * n - r by omega] at h
  rw [← h]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [pow_two]

/-- **Asymmetric Vandermonde** (`r = 0`): `∑_{k=0}^{m} C(m,k)·C(n,k) = C(m+n, n)`. -/
theorem sum_mixed_vandermonde (m n : ℕ) :
    ∑ k ∈ range (m + 1), m.choose k * n.choose k = (m + n).choose n := by
  have h := sum_descFactorial_mixed 0 m n (Nat.zero_le m)
  simp only [Nat.descFactorial_zero, one_mul, Nat.sub_zero] at h
  exact h

/-- **Mixed first moment** (`r = 1`): `∑ k·C(m,k)·C(n,k) = m·C(m+n−1, n−1)`. -/
theorem sum_first_mixed (m n : ℕ) (hm : 1 ≤ m) :
    ∑ k ∈ range (m + 1), k * (m.choose k * n.choose k)
      = m * (m + n - 1).choose (n - 1) := by
  have h := sum_descFactorial_mixed 1 m n hm
  simp only [Nat.descFactorial_one] at h
  exact h

/-- Sanity check of `(♦)` at `r = 2, m = 3, n = 4`:
    `∑_k (k)_2·C(3,k)·C(4,k) = (3)_2·C(5, 2) = 6·10 = 60`. -/
example : ∑ k ∈ range 4, k.descFactorial 2 * ((3 : ℕ).choose k * (4 : ℕ).choose k)
    = (3 : ℕ).descFactorial 2 * (3 + 4 - 2).choose (4 - 2) := by decide

/-- Sanity check of the asymmetric Vandermonde at `m = 3, n = 4`:
    `∑_k C(3,k)·C(4,k) = 1·1+3·4+3·6+1·4 = 35 = C(7, 4)`. -/
example : ∑ k ∈ range 4, (3 : ℕ).choose k * (4 : ℕ).choose k = (3 + 4 : ℕ).choose 4 := by decide

end CombinationsFormulaOQ07OQ04OQ01OQ01
