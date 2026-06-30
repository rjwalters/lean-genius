import Mathlib
import Proofs.CombinationsFormulaOQ07OQ04OQ01

/-
# The General Power Moment of the Squared Pascal Row, via Stirling Numbers

## Open Question OQ-07-OQ-04-OQ-01-OQ-02

The parent file (OQ-07-OQ-04-OQ-01) computes the *falling-factorial* moment of the squared
Pascal row in one uniform closed form,

  ∑_{k=0}^{n} (k)_r · C(n, k)²  =  (n)_r · C(2n − r, n − r),                          (★)

where `(x)_r = Nat.descFactorial x r`.  Its explicit follow-up asks for the **raw power
moments** `∑ k^p · C(n,k)²` for general `p`.  The parent file handles `p = 3` by hand,
case-bashing the single expansion `k³ = (k)_3 + 3(k)_2 + (k)_1`.  The honest, *general*
answer is not another ad-hoc expansion but the change of basis from monomials to falling
factorials, whose coefficients are the **Stirling numbers of the second kind**:

  m^p  =  ∑_{r=0}^{p} S(p, r) · (m)_r,                                                 (♦)

where `S(p, r) = Nat.stirlingSecond p r`.  Mathlib's `Nat.stirlingSecond` ships only the
defining recurrence and a few edge values — the fundamental bridge (♦) connecting Stirling
numbers to the monomial/falling-factorial change of basis is **absent**.  We prove it here,
then read off the general power moment in a single line:

  ∑_{k=0}^{n} k^p · C(n,k)²  =  ∑_{r=0}^{p} S(p, r) · (n)_r · C(2n − r, n − r).         (▲)

Both (♦) and (▲) hold for **all** `p, n` with no side condition: in (▲) the orders `r > n`
contribute nothing because `(n)_r = 0`, which is exactly why the parent's `r ≤ n` hypothesis
on (★) can be dropped here (`sum_descFactorial_weighted_sq_all`).

## Proof of the bridge (♦)

Induction on `p`.  The one arithmetic fact needed is the falling-factorial shift

  m · (m)_r = (m)_{r+1} + r · (m)_r,                                          (m_mul_descFactorial)

a restatement of `(m)_{r+1} = (m − r) · (m)_r` valid over ℕ for every `r` (when `r > m`
both sides vanish).  Multiplying the inductive hypothesis by `m` and substituting this shift
produces two sums; reindexing one of them by `r ↦ r + 1` and folding in Stirling's recurrence
`S(p+1, r+1) = (r+1)·S(p, r+1) + S(p, r)` reassembles `∑_r S(p+1, r) (m)_r`.  The two
"reindexing" sums match because the boundary terms vanish: `S(p, p+1) = 0` (`p < p+1`) and the
`r = 0` falling-factorial term carries a literal factor `0`.

## Results

1. `pow_eq_sum_stirlingSecond_descFactorial` — the Stirling bridge (♦), a Mathlib gap-filler.
2. `sum_descFactorial_weighted_sq_all` — the parent moment (★) with the `r ≤ n` hypothesis
   removed (both sides vanish for `r > n`).
3. `sum_pow_weighted_sq` — the general raw power moment (▲), for **all** `p` and `n`.

## Axioms: 0 | Sorries: 0
-/

namespace CombinationsFormulaOQ07OQ04OQ01OQ02

open Finset

/-- **Falling-factorial shift.** For all `m r : ℕ`,

      m · (m)_r = (m)_{r+1} + r · (m)_r.

    This is `(m)_{r+1} = (m − r)·(m)_r` rearranged: when `r ≤ m`, `(m − r) + r = m`; when
    `r > m`, both `(m)_r` and `(m)_{r+1}` are `0`. -/
private theorem m_mul_descFactorial (m r : ℕ) :
    m * m.descFactorial r = m.descFactorial (r + 1) + r * m.descFactorial r := by
  rcases le_or_lt r m with h | h
  · rw [Nat.descFactorial_succ, ← Nat.add_mul, Nat.sub_add_cancel h]
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr h,
        Nat.descFactorial_eq_zero_iff_lt.mpr (show m < r + 1 by omega)]
    ring

/-- **The Stirling bridge** `(♦)`.  For all `m p : ℕ`,

      m^p  =  ∑_{r=0}^{p} S(p, r) · (m)_r,

    expressing the monomial `m^p` in the falling-factorial basis with the Stirling numbers of
    the second kind as coefficients.  This fundamental change of basis is not in Mathlib
    (which provides only `Nat.stirlingSecond`'s recurrence).  Proved by induction on `p`,
    using the falling-factorial shift and Stirling's recurrence. -/
theorem pow_eq_sum_stirlingSecond_descFactorial (m p : ℕ) :
    m ^ p = ∑ r ∈ range (p + 1), Nat.stirlingSecond p r * m.descFactorial r := by
  induction p with
  | zero => simp
  | succ p ih =>
      -- Multiply the IH by `m` and split via the falling-factorial shift.
      have hL : m ^ (p + 1)
          = (∑ r ∈ range (p + 1), Nat.stirlingSecond p r * m.descFactorial (r + 1))
            + ∑ r ∈ range (p + 1), Nat.stirlingSecond p r * (r * m.descFactorial r) := by
        rw [pow_succ, ih, Finset.sum_mul, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun r _ => ?_)
        calc Nat.stirlingSecond p r * m.descFactorial r * m
            = Nat.stirlingSecond p r * (m * m.descFactorial r) := by ring
          _ = Nat.stirlingSecond p r * (m.descFactorial (r + 1) + r * m.descFactorial r) := by
                rw [m_mul_descFactorial]
          _ = Nat.stirlingSecond p r * m.descFactorial (r + 1)
              + Nat.stirlingSecond p r * (r * m.descFactorial r) := by ring
      -- Expand the target sum using Stirling's recurrence.
      have hR : (∑ r ∈ range (p + 1 + 1), Nat.stirlingSecond (p + 1) r * m.descFactorial r)
          = (∑ r ∈ range (p + 1),
              (r + 1) * Nat.stirlingSecond p (r + 1) * m.descFactorial (r + 1))
            + ∑ r ∈ range (p + 1), Nat.stirlingSecond p r * m.descFactorial (r + 1) := by
        rw [Finset.sum_range_succ' (fun r => Nat.stirlingSecond (p + 1) r * m.descFactorial r) (p + 1),
            Nat.stirlingSecond_succ_zero, Nat.zero_mul, Nat.add_zero, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun r _ => ?_)
        rw [Nat.stirlingSecond_succ_succ]
        ring
      -- The two `r`-weighted sums coincide: reindex `r ↦ r+1`, boundary terms vanish.
      have hB : (∑ r ∈ range (p + 1), Nat.stirlingSecond p r * (r * m.descFactorial r))
          = ∑ r ∈ range (p + 1),
              (r + 1) * Nat.stirlingSecond p (r + 1) * m.descFactorial (r + 1) := by
        rw [Finset.sum_range_succ'
              (fun r => Nat.stirlingSecond p r * (r * m.descFactorial r)) p,
            Finset.sum_range_succ
              (fun r => (r + 1) * Nat.stirlingSecond p (r + 1) * m.descFactorial (r + 1)) p,
            Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self p)]
        simp only [Nat.mul_zero, Nat.zero_mul, Nat.add_zero]
        refine Finset.sum_congr rfl (fun r _ => ?_)
        ring
      rw [hL, hR, hB]
      ring

/-- **Parent moment, hypothesis-free.**  The parent's closed form `(★)` holds for *every*
    `r` (not just `r ≤ n`): when `r > n` the left side vanishes term by term (each `k ≤ n < r`
    gives `(k)_r = 0`) and the right side vanishes because `(n)_r = 0`. -/
theorem sum_descFactorial_weighted_sq_all (r n : ℕ) :
    ∑ k ∈ range (n + 1), k.descFactorial r * (n.choose k) ^ 2
      = n.descFactorial r * (2 * n - r).choose (n - r) := by
  rcases le_or_lt r n with h | h
  · exact CombinationsFormulaOQ07OQ04OQ01.sum_descFactorial_weighted_sq r n h
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr h, Nat.zero_mul]
    refine Finset.sum_eq_zero (fun k hk => ?_)
    rw [Finset.mem_range, Nat.lt_succ_iff] at hk
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr (show k < r by omega), Nat.zero_mul]

/-- **The general power moment** `(▲)`.  For all `p n : ℕ`,

      ∑_{k=0}^{n} k^p · C(n, k)²  =  ∑_{r=0}^{p} S(p, r) · (n)_r · C(2n − r, n − r).

    Expand each `k^p` by the Stirling bridge `(♦)`, swap the order of summation, and close
    the inner `k`-sum with the hypothesis-free parent moment.  This subsumes the parent's
    hand-rolled cubic moment and the entire `r = 0, 1, 2, 3, …` ladder uniformly. -/
theorem sum_pow_weighted_sq (p n : ℕ) :
    ∑ k ∈ range (n + 1), k ^ p * (n.choose k) ^ 2
      = ∑ r ∈ range (p + 1),
          Nat.stirlingSecond p r * (n.descFactorial r * (2 * n - r).choose (n - r)) := by
  have step1 : ∑ k ∈ range (n + 1), k ^ p * (n.choose k) ^ 2
      = ∑ k ∈ range (n + 1), ∑ r ∈ range (p + 1),
          Nat.stirlingSecond p r * (k.descFactorial r * (n.choose k) ^ 2) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [pow_eq_sum_stirlingSecond_descFactorial k p, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    ring
  rw [step1, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [← Finset.mul_sum, sum_descFactorial_weighted_sq_all r n]

/-- **Consistency with the parent's cubic moment.**  Specialising `(▲)` to `p = 3` and
    evaluating the Stirling row `S(3, ·) = 0, 1, 3, 1` recovers exactly the hand-rolled
    expansion `∑ k³·C(n,k)² = (n)_1·C(2n−1,n−1) + 3·(n)_2·C(2n−2,n−2) + (n)_3·C(2n−3,n−3)`
    proved separately in the parent file. -/
example (n : ℕ) :
    ∑ k ∈ range (n + 1), k ^ 3 * (n.choose k) ^ 2
      = n.descFactorial 1 * (2 * n - 1).choose (n - 1)
        + 3 * (n.descFactorial 2 * (2 * n - 2).choose (n - 2))
        + n.descFactorial 3 * (2 * n - 3).choose (n - 3) := by
  rw [sum_pow_weighted_sq 3 n, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
      show Nat.stirlingSecond 3 0 = 0 from rfl, show Nat.stirlingSecond 3 1 = 1 from rfl,
      show Nat.stirlingSecond 3 2 = 3 from rfl, show Nat.stirlingSecond 3 3 = 1 from rfl]
  ring

/-- Sanity check of the Stirling bridge `(♦)` at `m = 5, p = 3`: `5³ = 125`,
    and `∑_{r} S(3,r)·(5)_r = 0 + 1·5 + 3·20 + 1·60 = 125`. -/
example : (5 : ℕ) ^ 3 = ∑ r ∈ range 4, Nat.stirlingSecond 3 r * (5 : ℕ).descFactorial r := by
  decide

/-- Sanity check of the general power moment `(▲)` at `p = 4, n = 4`:
    `∑_{k} k⁴·C(4,k)² = ∑_{r} S(4,r)·(4)_r·C(8−r, 4−r)`. -/
example : ∑ k ∈ range 5, k ^ 4 * ((4 : ℕ).choose k) ^ 2
    = ∑ r ∈ range 5, Nat.stirlingSecond 4 r
        * ((4 : ℕ).descFactorial r * (2 * 4 - r).choose (4 - r)) := by
  decide

end CombinationsFormulaOQ07OQ04OQ01OQ02
