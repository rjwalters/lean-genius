import Mathlib
import Proofs.CombinationsFormulaOQ07OQ04OQ01OQ02
import Proofs.CombinationsFormulaOQ07OQ04OQ01OQ03OQ01

/-
# The General Power Moment of a Product of Two Pascal Rows, via Stirling Numbers

## Open Question OQ-07-OQ-04-OQ-01-OQ-02-OQ-01

Two ingredients sit in this branch of the family, each computed in one closed form:

* **The Stirling bridge** (OQ-07-OQ-04-OQ-01-OQ-02): the monomial-to-falling-factorial change
  of basis, with Stirling numbers of the second kind as coefficients,

    m^p  =  ∑_{r=0}^{p} S(p, r) · (m)_r,                                               (♦)

  where `S(p, r) = Nat.stirlingSecond p r` and `(x)_r = Nat.descFactorial x r`.

* **The one-sided (two-row) falling moment** (OQ-07-OQ-04-OQ-01-OQ-03-OQ-01, the `s = 0` face
  of the two-sided cross moment): weighting a product of *two different* Pascal rows from the
  left end,

    ∑_{k=0}^{n} (k)_r · C(m,k)·C(n,k)  =  (m)_r · C(m + n − r, n − r),    (r ≤ m, r ≤ n).  (♠)

The sibling OQ-07-OQ-04-OQ-01-OQ-02 used (♦) to upgrade the *symmetric* falling moment
`∑ (k)_r·C(n,k)²` into the raw power moment `∑ k^p·C(n,k)²`.  Its explicit follow-up asks
whether the *identical* expand-swap-close argument upgrades the asymmetric one-sided moment
(♠) into the raw power moment of the asymmetric Vandermonde diagonal.  It does:

  ∑_{k=0}^{n} k^p · C(m,k)·C(n,k)  =  ∑_{r=0}^{p} S(p, r) · (m)_r · C(m + n − r, n − r).  (▲)

Expand each `k^p` by the bridge (♦), swap the order of summation, and close the inner
`k`-sum with (♠).  The argument is uniform in `p`: it subsumes the linear moment
`∑ k·C(m,k)·C(n,k) = m·C(m+n−1, n−1)` and every higher moment at once, and recovers the
sibling's symmetric power moment exactly at `m = n`.

## The side condition, and where it can be dropped

Unlike the symmetric case, the per-order inner moment (♠) is **not** unconditionally equal to
the closed form `(m)_r·C(m+n−r, n−r)`: the offending regime is `m ≥ r > n`, where the left
sum vanishes (every `k ≤ n < r` kills `(k)_r`) yet the closed form `(m)_r·C(m+n−r, 0) = (m)_r`
need not.  Two clean hypotheses each rule it out, giving two headline forms of (▲):

* `sum_pow_mixed`     — assume `p ≤ n`: then every order `r ≤ p ≤ n` lands in the good range.
* `sum_pow_mixed_of_le` — assume `m ≤ n`: then `r > n ⇒ r > m ⇒ (m)_r = 0`, so the bad terms
  vanish on *both* sides and the moment holds for **all** `p`.

The second specialises at `m = n` to the sibling's unconditional `sum_pow_weighted_sq`,
confirming this result genuinely subsumes it.

## What is new here (relative to Mathlib and the gallery)

The closed form (▲) is absent from Mathlib.  Both inputs are gallery results: the Stirling
bridge (♦) is itself a Mathlib gap-filler from the sibling file, and (♠) is the `s = 0` face
of the two-sided cross moment.  The contribution of this file is the join — the asymmetric raw
power moment in one closed form — plus the `m`-relaxed inner moment lemmas it needs.

## Results

1. `sum_oneSided_mixed_all`    — (♠) with the `r ≤ m` hypothesis relaxed (valid for all `r ≤ n`).
2. `sum_oneSided_mixed_le`     — (♠) for **all** orders `r`, under `m ≤ n`.
3. `sum_pow_mixed`             — the power moment (▲) under `p ≤ n`.
4. `sum_pow_mixed_of_le`       — the power moment (▲) for **all** `p`, under `m ≤ n`.
5. `sum_pow_weighted_sq_of_mixed` — the `m = n` face: recovers the sibling's `sum_pow_weighted_sq`.
6. `sum_linear_mixed`          — the `p = 1` face: `∑ k·C(m,k)·C(n,k) = m·C(m+n−1, n−1)`.

## Axioms: 0 | Sorries: 0
-/

namespace CombinationsFormulaOQ07OQ04OQ01OQ02OQ01

open Finset

/-- **One-sided two-row moment, `m`-hypothesis relaxed.**  For `r ≤ n` (and *any* `m`),

      ∑_{k=0}^{n} (k)_r · C(m,k)·C(n,k)  =  (m)_r · C(m + n − r, n − r).

    The headline `(♠)` of OQ-07-OQ-04-OQ-01-OQ-03-OQ-01 (its `s = 0` face) carries the extra
    hypothesis `r ≤ m`.  When `r > m` both sides vanish: the right side because `(m)_r = 0`,
    and the left because each term carries either `(k)_r = 0` (when `k < r`) or `C(m, k) = 0`
    (when `k ≥ r > m`). -/
theorem sum_oneSided_mixed_all (r m n : ℕ) (hrn : r ≤ n) :
    ∑ k ∈ range (n + 1), k.descFactorial r * (m.choose k * n.choose k)
      = m.descFactorial r * (m + n - r).choose (n - r) := by
  rcases le_or_lt r m with hrm | hrm
  · exact CombinationsFormulaOQ07OQ04OQ01OQ03OQ01.sum_oneSided_mixed_of_twoSided r m n hrm hrn
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hrm, Nat.zero_mul]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rcases lt_or_le k r with hk | hk
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.zero_mul]
    · rw [Nat.choose_eq_zero_of_lt (show m < k by omega), Nat.zero_mul, Nat.mul_zero]

/-- **One-sided two-row moment for all orders, under `m ≤ n`.**  When `m ≤ n` the closed form
    `(♠)` holds for *every* order `r` with no further hypothesis: for `r ≤ n` it is
    `sum_oneSided_mixed_all`, and for `r > n ≥ m` both sides vanish (`(m)_r = 0`, and every
    `k ≤ n < r` kills `(k)_r`). -/
theorem sum_oneSided_mixed_le (r m n : ℕ) (hmn : m ≤ n) :
    ∑ k ∈ range (n + 1), k.descFactorial r * (m.choose k * n.choose k)
      = m.descFactorial r * (m + n - r).choose (n - r) := by
  rcases le_or_lt r n with hrn | hrn
  · exact sum_oneSided_mixed_all r m n hrn
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (show m < r by omega), Nat.zero_mul]
    refine Finset.sum_eq_zero (fun k hk => ?_)
    rw [Finset.mem_range, Nat.lt_succ_iff] at hk
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr (show k < r by omega), Nat.zero_mul]

/-- **The general power moment** `(▲)`, under `p ≤ n`.  For all `m n : ℕ` and `p ≤ n`,

      ∑_{k=0}^{n} k^p · C(m,k)·C(n,k)  =  ∑_{r=0}^{p} S(p, r) · (m)_r · C(m + n − r, n − r).

    Expand each `k^p` by the Stirling bridge `(♦)`, swap the order of summation, and close the
    inner `k`-sum with the one-sided two-row moment `(♠)`.  The hypothesis `p ≤ n` guarantees
    every order `r ≤ p` satisfies `r ≤ n`, so `sum_oneSided_mixed_all` applies term by term. -/
theorem sum_pow_mixed (p m n : ℕ) (hp : p ≤ n) :
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
  rw [← Finset.mul_sum, sum_oneSided_mixed_all r m n (by omega)]

/-- **The general power moment** `(▲)`, under `m ≤ n`, for **all** `p`.  Same closed form, with
    the side condition moved from `p ≤ n` to `m ≤ n`; now every order `r` is admissible because
    `sum_oneSided_mixed_le` needs no constraint on `r`.  At `m = n` this is unconditional in `p`. -/
theorem sum_pow_mixed_of_le (p m n : ℕ) (hmn : m ≤ n) :
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
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [← Finset.mul_sum, sum_oneSided_mixed_le r m n hmn]

/-- **The `m = n` face: the sibling's symmetric power moment.**  Specialising `sum_pow_mixed_of_le`
    to `m = n` (admissible since `n ≤ n`) and folding `C(n,k)·C(n,k)` back into `C(n,k)²` recovers
    `CombinationsFormulaOQ07OQ04OQ01OQ02.sum_pow_weighted_sq` verbatim — unconditional in `p`. -/
theorem sum_pow_weighted_sq_of_mixed (p n : ℕ) :
    ∑ k ∈ range (n + 1), k ^ p * (n.choose k) ^ 2
      = ∑ r ∈ range (p + 1),
          Nat.stirlingSecond p r * (n.descFactorial r * (2 * n - r).choose (n - r)) := by
  have h := sum_pow_mixed_of_le p n n (le_refl n)
  rw [show (2 * n) = n + n from two_mul n, ← h]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [pow_two]

/-- **The `p = 1` face: the linear two-row moment.**  `∑ k·C(m,k)·C(n,k) = m·C(m+n−1, n−1)`
    (for `1 ≤ n`).  The Stirling row `S(1, ·) = 0, 1` collapses `(▲)` to its single `r = 1`
    term, where `(m)_1 = m`. -/
theorem sum_linear_mixed (m n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ range (n + 1), k * (m.choose k * n.choose k)
      = m * (m + n - 1).choose (n - 1) := by
  have h := sum_pow_mixed 1 m n hn
  rw [Finset.sum_range_succ, Finset.sum_range_one,
      show Nat.stirlingSecond 1 0 = 0 from rfl,
      show Nat.stirlingSecond 1 1 = 1 from rfl,
      Nat.descFactorial_one] at h
  simpa using h

/-- Sanity check of `(▲)` at `p = 2, m = 3, n = 4`:
    `∑_{k} k²·C(3,k)·C(4,k) = ∑_{r} S(2,r)·(3)_r·C(7−r, 4−r)`. -/
example : ∑ k ∈ range 5, k ^ 2 * ((3 : ℕ).choose k * (4 : ℕ).choose k)
    = ∑ r ∈ range 3, Nat.stirlingSecond 2 r
        * ((3 : ℕ).descFactorial r * (3 + 4 - r).choose (4 - r)) := by
  decide

/-- Sanity check of the linear face at `m = 3, n = 4`:
    `∑_k k·C(3,k)·C(4,k) = 0 + 12 + 18 + 4·... ` evaluates to `3·C(6,3) = 3·20 = 60`. -/
example : ∑ k ∈ range 5, k * ((3 : ℕ).choose k * (4 : ℕ).choose k)
    = 3 * (3 + 4 - 1).choose (4 - 1) := by
  decide

end CombinationsFormulaOQ07OQ04OQ01OQ02OQ01
