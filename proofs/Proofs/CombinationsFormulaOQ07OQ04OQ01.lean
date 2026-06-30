import Mathlib
import Proofs.CombinationsFormulaOQ07
import Proofs.CombinationsFormulaOQ07OQ01
import Proofs.CombinationsFormulaOQ07OQ03
import Proofs.CombinationsFormulaOQ07OQ04

/-
# The r-th Falling-Factorial Moment of the Squares of Binomial Coefficients

## Open Question OQ-07-OQ-04-OQ-01

The parent file (OQ-07-OQ-04) computes the falling-factorial **second** moment of the
squared Pascal row,

  ∑_{k=0}^{n} k(k − 1) · C(n, k)² = n(n − 1) · C(2n − 2, n − 2),

and its open question asks for the **third — and general r-th — moment**.  The clean
object is the *falling-factorial* (descending-factorial) moment, and it has a single,
uniform closed form for **every** order `r`:

  ∑_{k=0}^{n} (k)_r · C(n, k)²  =  (n)_r · C(2n − r, n − r),                       (★)

where `(x)_r = x(x−1)⋯(x−r+1) = Nat.descFactorial x r` is the falling factorial.  This is
absent from Mathlib.  Special cases recover the entire moment ladder of this OQ family:

  r = 0 :  ∑ C(n,k)²            = C(2n, n)            (central binomial — OQ-07)
  r = 1 :  ∑ k · C(n,k)²        = n · C(2n−1, n−1)    (first moment — OQ-03)
  r = 2 :  ∑ k(k−1) · C(n,k)²   = n(n−1) · C(2n−2, n−2)   (parent OQ-04)
  r = 3 :  ∑ k(k−1)(k−2)·C(n,k)² = n(n−1)(n−2) · C(2n−3, n−3)   (the **third** moment)

The raw power moment is then read off by Stirling expansion `k³ = (k)_3 + 3(k)_2 + (k)_1`:

  ∑ k³ · C(n,k)² = n(n−1)(n−2)·C(2n−3,n−3) + 3n(n−1)·C(2n−2,n−2) + n·C(2n−1,n−1).   (▲)

## The proof of (★): iterated absorption + a shifted Vandermonde diagonal

The single committee-chair absorption `k · C(n, k) = n · C(n−1, k−1)` (OQ-01) iterates,
by induction on `r`, to the **falling absorption**

  (k)_r · C(n, k) = (n)_r · C(n − r, k − r)              (r ≤ k ≤ n).            (descFactorial_mul_choose)

Unlike the *square* form `k²·C(n,k)² = n²·C(n−1,k−1)²`, the falling product keeps one
plain factor `C(n, k)`.  Summing over `k`, the orders `k < r` vanish (a falling factorial
of length `r` kills any base `< r`), and reindexing `k ↦ k − r` leaves a genuine
**Vandermonde convolution along the diagonal shifted `r` off-centre**

  ∑_{j=0}^{n−r} C(n − r, j) · C(n, j + r) = C(2n − r, n − r),                     (vandermonde_diag)

the parent Vandermonde anchor (`add_choose_eq_sum_range`) read with `C(n, j+r)` realigned
to `C(n, n−r−j)` by symmetry.  Pulling out the constant `(n)_r` gives (★).

This is why the falling moment is "clean" for *every* `r`: it lands on a single
off-diagonal Vandermonde entry `C(2n−r, n−r)` directly, with no order-dependent
recombination.

## Results

1. `descFactorial_mul_choose` — the iterated (falling) absorption, the conceptual core.
2. `vandermonde_diag` — the `r`-shifted Vandermonde diagonal.
3. `sum_descFactorial_weighted_sq` — the general closed form (★), for all `r ≤ n`.
4. `sum_first_weighted_sq`, `sum_falling_second`, `sum_falling_third` — the
   `r = 1, 2, 3` specialisations (the third moment is the headline of this OQ).
5. `sum_cube_weighted_sq` — the raw power moment (▲) via the Stirling expansion of `k³`.

## Axioms: 0 | Sorries: 0
-/

namespace CombinationsFormulaOQ07OQ04OQ01

open Finset

/-- **Iterated (falling) absorption.** Applying the committee-chair identity
    `k · C(n, k) = n · C(n − 1, k − 1)` (OQ-01) `r` times converts a falling-factorial
    weight `(k)_r` on `C(n, k)` into a coefficient `(n)_r` on the `r`-fold–shifted
    `C(n − r, k − r)`:

      (k)_r · C(n, k) = (n)_r · C(n − r, k − r)        (r ≤ k ≤ n).

    Proved by induction on `r`, peeling one falling factor per step. -/
theorem descFactorial_mul_choose :
    ∀ (r n k : ℕ), r ≤ k → k ≤ n →
      k.descFactorial r * n.choose k = n.descFactorial r * (n - r).choose (k - r) := by
  intro r
  induction r with
  | zero => intro n k _ _; simp
  | succ r ih =>
      intro n k hr hkn
      have hrk : r ≤ k := by omega
      have ihr := ih n k hrk hkn
      have habs := CombinationsFormulaOQ07OQ01.mul_choose_eq
        (n := n - r) (k := k - r) (by omega) (by omega)
      -- habs : (k - r) * (n - r).choose (k - r) = (n - r) * (n - r - 1).choose (k - r - 1)
      rw [Nat.descFactorial_succ, Nat.descFactorial_succ]
      calc (k - r) * k.descFactorial r * n.choose k
          = (k - r) * (k.descFactorial r * n.choose k) := by ring
        _ = (k - r) * (n.descFactorial r * (n - r).choose (k - r)) := by rw [ihr]
        _ = n.descFactorial r * ((k - r) * (n - r).choose (k - r)) := by ring
        _ = n.descFactorial r * ((n - r) * (n - r - 1).choose (k - r - 1)) := by rw [habs]
        _ = (n - r) * n.descFactorial r * (n - r - 1).choose (k - r - 1) := by ring
        _ = (n - r) * n.descFactorial r * (n - (r + 1)).choose (k - (r + 1)) := by
              rw [show n - r - 1 = n - (r + 1) by omega, show k - r - 1 = k - (r + 1) by omega]

/-- **Shifted Vandermonde diagonal.** Reading Vandermonde's convolution
    `add_choose_eq_sum_range` (OQ-07) along the diagonal `r` steps off-centre:

      ∑_{j=0}^{n−r} C(n − r, j) · C(n, j + r) = C(2n − r, n − r).

    The reflection `C(n, (n−r)−j) = C(n, j + r)` (`Nat.choose_symm`) aligns the
    convolution term with the shifted summand. -/
theorem vandermonde_diag (r n : ℕ) (hr : r ≤ n) :
    ∑ j ∈ range ((n - r) + 1), (n - r).choose j * n.choose (j + r)
      = (2 * n - r).choose (n - r) := by
  have hv := CombinationsFormulaOQ07.add_choose_eq_sum_range (n - r) n (n - r)
  rw [show (n - r) + n = 2 * n - r by omega] at hv
  rw [hv]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Finset.mem_range, Nat.lt_succ_iff] at hj
  have hsymm := Nat.choose_symm (n := n) (k := j + r) (by omega)
  rw [show n - (j + r) = (n - r) - j by omega] at hsymm
  rw [hsymm]

/-- **The r-th falling-factorial moment.** `(★)`  For all `r ≤ n`,

      ∑_{k=0}^{n} (k)_r · C(n, k)²  =  (n)_r · C(2n − r, n − r).

    Orders `k < r` vanish, the iterated absorption rewrites each remaining term, and the
    shifted Vandermonde diagonal closes the inner sum. -/
theorem sum_descFactorial_weighted_sq (r n : ℕ) (hr : r ≤ n) :
    ∑ k ∈ range (n + 1), k.descFactorial r * (n.choose k) ^ 2
      = n.descFactorial r * (2 * n - r).choose (n - r) := by
  -- Discard the vanishing low-order terms `k < r`, reindex `k ↦ k − r`.
  have key : ∑ k ∈ range (n + 1), k.descFactorial r * (n.choose k) ^ 2
           = ∑ k ∈ Finset.Ico r (n + 1), k.descFactorial r * (n.choose k) ^ 2 := by
    rw [Finset.range_eq_Ico,
        ← Finset.sum_Ico_consecutive _ (Nat.zero_le r) (show r ≤ n + 1 by omega)]
    have hlow : ∑ k ∈ Finset.Ico 0 r, k.descFactorial r * (n.choose k) ^ 2 = 0 :=
      Finset.sum_eq_zero (fun k hk => by
        rw [Finset.mem_Ico] at hk
        rw [Nat.descFactorial_eq_zero_iff_lt.mpr hk.2, zero_mul])
    rw [hlow, zero_add]
  rw [key, Finset.sum_Ico_eq_sum_range, show n + 1 - r = (n - r) + 1 by omega]
  -- Falling absorption term by term.
  have hterm : ∀ i ∈ range ((n - r) + 1),
      (r + i).descFactorial r * (n.choose (r + i)) ^ 2
        = n.descFactorial r * ((n - r).choose i * n.choose (i + r)) := by
    intro i hi
    rw [Finset.mem_range, Nat.lt_succ_iff] at hi
    have habs := descFactorial_mul_choose r n (r + i) (by omega) (by omega)
    rw [show r + i - r = i by omega] at habs
    calc (r + i).descFactorial r * (n.choose (r + i)) ^ 2
        = ((r + i).descFactorial r * n.choose (r + i)) * n.choose (r + i) := by ring
      _ = (n.descFactorial r * (n - r).choose i) * n.choose (r + i) := by rw [habs]
      _ = n.descFactorial r * ((n - r).choose i * n.choose (i + r)) := by
            rw [show i + r = r + i by omega]; ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, vandermonde_diag r n hr]

/-- `(k)_2 = k(k − 1)`. -/
private theorem descFactorial_two (k : ℕ) : k.descFactorial 2 = k * (k - 1) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Nat.descFactorial_succ, Nat.descFactorial_one, Nat.mul_comm]

/-- `(k)_3 = k(k − 1)(k − 2)`. -/
private theorem descFactorial_three (k : ℕ) : k.descFactorial 3 = k * (k - 1) * (k - 2) := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, Nat.descFactorial_succ, descFactorial_two]; ring

/-- **First moment** (`r = 1`, recovers OQ-03): `∑ k · C(n,k)² = n · C(2n−1, n−1)`. -/
theorem sum_first_weighted_sq (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ range (n + 1), k * (n.choose k) ^ 2 = n * (2 * n - 1).choose (n - 1) := by
  have h := sum_descFactorial_weighted_sq 1 n hn
  simp only [Nat.descFactorial_one] at h
  exact h

/-- **Falling second moment** (`r = 2`, the parent closed form):
    `∑ k(k−1) · C(n,k)² = n(n−1) · C(2n−2, n−2)`. -/
theorem sum_falling_second (n : ℕ) (hn : 2 ≤ n) :
    ∑ k ∈ range (n + 1), k * (k - 1) * (n.choose k) ^ 2
      = n * (n - 1) * (2 * n - 2).choose (n - 2) := by
  have h := sum_descFactorial_weighted_sq 2 n hn
  simp only [descFactorial_two] at h
  exact h

/-- **Falling third moment** (`r = 3`, the headline of this open question):
    `∑ k(k−1)(k−2) · C(n,k)² = n(n−1)(n−2) · C(2n−3, n−3)`. -/
theorem sum_falling_third (n : ℕ) (hn : 3 ≤ n) :
    ∑ k ∈ range (n + 1), k * (k - 1) * (k - 2) * (n.choose k) ^ 2
      = n * (n - 1) * (n - 2) * (2 * n - 3).choose (n - 3) := by
  have h := sum_descFactorial_weighted_sq 3 n hn
  simp only [descFactorial_three] at h
  exact h

/-- **Raw cubic (third power) moment** `(▲)`, via the Stirling expansion
    `k³ = (k)_3 + 3(k)_2 + (k)_1`:

      ∑ k³ · C(n,k)² = n(n−1)(n−2)·C(2n−3,n−3) + 3n(n−1)·C(2n−2,n−2) + n·C(2n−1,n−1). -/
theorem sum_cube_weighted_sq (n : ℕ) (hn : 3 ≤ n) :
    ∑ k ∈ range (n + 1), k ^ 3 * (n.choose k) ^ 2
      = n * (n - 1) * (n - 2) * (2 * n - 3).choose (n - 3)
        + 3 * (n * (n - 1) * (2 * n - 2).choose (n - 2))
        + n * (2 * n - 1).choose (n - 1) := by
  have hsplit : ∑ k ∈ range (n + 1), k ^ 3 * (n.choose k) ^ 2
      = (∑ k ∈ range (n + 1), k * (k - 1) * (k - 2) * (n.choose k) ^ 2)
        + 3 * (∑ k ∈ range (n + 1), k * (k - 1) * (n.choose k) ^ 2)
        + (∑ k ∈ range (n + 1), k * (n.choose k) ^ 2) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have hstir : k ^ 3 = k * (k - 1) * (k - 2) + 3 * (k * (k - 1)) + k := by
      rcases k with _ | _ | j
      · rfl
      · rfl
      · rw [show j + 1 + 1 - 1 = j + 1 by omega, show j + 1 + 1 - 2 = j by omega]; ring
    rw [hstir]; ring
  rw [hsplit, sum_falling_third n hn, sum_falling_second n (by omega),
      sum_first_weighted_sq n (by omega)]

/-- Sanity check of (★) at `r = 3, n = 4`:
    `∑_{k} (k)_3·C(4,k)² = (4)_3·C(5, 1) = 24·5 = 120`. -/
example : ∑ k ∈ range 5, k.descFactorial 3 * ((4 : ℕ).choose k) ^ 2
    = (4 : ℕ).descFactorial 3 * (2 * 4 - 3).choose (4 - 3) := by decide

/-- Sanity check of the falling third moment at `n = 4`:
    `∑ k(k−1)(k−2)·C(4,k)² = 0+0+0+96+24 = 120 = 4·3·2·C(5,1)`. -/
example : ∑ k ∈ range 5, k * (k - 1) * (k - 2) * ((4 : ℕ).choose k) ^ 2
    = 4 * (4 - 1) * (4 - 2) * (2 * 4 - 3).choose (4 - 3) := by decide

/-- Sanity check of the raw cubic moment `(▲)` at `n = 4`. -/
example : ∑ k ∈ range 5, k ^ 3 * ((4 : ℕ).choose k) ^ 2
    = 4 * (4 - 1) * (4 - 2) * (2 * 4 - 3).choose (4 - 3)
      + 3 * (4 * (4 - 1) * (2 * 4 - 2).choose (4 - 2))
      + 4 * (2 * 4 - 1).choose (4 - 1) := by decide

end CombinationsFormulaOQ07OQ04OQ01
