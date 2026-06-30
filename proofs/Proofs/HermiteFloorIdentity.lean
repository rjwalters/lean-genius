/-
# Hermite's Identity for the Floor Function

For every real `x` and every integer `n ≥ 1`,
$$\sum_{k=0}^{n-1} \left\lfloor x + \frac{k}{n} \right\rfloor = \lfloor n x \rfloor.$$

This is the classical identity of Charles Hermite (1880s).  It is *not* the
Hermite–Lindemann transcendence theorem (an unrelated result that already lives
in the gallery as `HermiteLindemann.lean`), nor is it about Hermite polynomials
or Hermite normal form.

## Strategy

The proof factors through two elementary steps:

1. **Real → integer reduction.**  Using `Int.floor_div_natCast`
   (`⌊a / n⌋ = ⌊a⌋ / n`, where the right-hand division is Euclidean division on
   `ℤ`) together with `Int.floor_add_natCast`, each real floor collapses to an
   integer Euclidean quotient:
   `⌊x + k/n⌋ = (⌊n·x⌋ + k) / n`.

2. **Integer Hermite sum.**  The remaining statement
   `∑_{k=0}^{n-1} (a + k) / n = a` (for any `a : ℤ`, `n ≥ 1`) is proved by
   integer induction on `a`.  Shifting `a ↦ a + 1` reindexes the sum and changes
   it by exactly `1`, so the linear function `a ↦ a` is pinned down by its value
   `0` at `a = 0`.

Because Euclidean division `/` on `ℤ` has a nonnegative remainder, for a positive
divisor it coincides with floor division, which is precisely what makes step (1)
valid for negative arguments.

No axioms beyond Lean/Mathlib's foundations; `0` sorries.
-/
import Mathlib

open Finset

namespace HermiteFloorIdentity

/-- **Integer Hermite sum.**  For `n ≥ 1` and any integer `a`,
the Euclidean quotients `(a + k) / n` over `k = 0, …, n-1` sum to `a`. -/
theorem int_hermite_sum (n : ℕ) (hn : 0 < n) (a : ℤ) :
    ∑ k ∈ range n, (a + (k : ℤ)) / (n : ℤ) = a := by
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  -- The shift recurrence: replacing `b` by `b + 1` increases the sum by `1`.
  have step : ∀ b : ℤ,
      (∑ k ∈ range n, (b + 1 + (k : ℤ)) / (n : ℤ))
        = (∑ k ∈ range n, (b + (k : ℤ)) / (n : ℤ)) + 1 := by
    intro b
    -- Reindex `k ↦ k + 1`, matching the `g (k+1)` shape of `sum_range_succ'`.
    have key : (∑ k ∈ range n, (b + 1 + (k : ℤ)) / (n : ℤ))
        = (∑ k ∈ range n, (b + (((k + 1 : ℕ) : ℤ))) / (n : ℤ)) := by
      refine Finset.sum_congr rfl ?_
      intro k _; congr 1; push_cast; ring
    rw [key]
    -- `∑_{range(n+1)} g = (∑_{range n} g(·+1)) + g 0`  and  `= (∑_{range n} g) + g n`.
    have h1 := Finset.sum_range_succ' (fun j : ℕ => (b + (j : ℤ)) / (n : ℤ)) n
    have h2 := Finset.sum_range_succ (fun j : ℕ => (b + (j : ℤ)) / (n : ℤ)) n
    simp only at h1 h2
    -- Endpoint quotients: `g 0 = b/n` and `g n = b/n + 1`.
    have hg0 : (b + (((0 : ℕ) : ℤ))) / (n : ℤ) = b / (n : ℤ) := by norm_num
    have hgn : (b + ((n : ℤ))) / (n : ℤ) = b / (n : ℤ) + 1 := by
      rw [show b + (n : ℤ) = b + 1 * (n : ℤ) by ring, Int.add_mul_ediv_right b 1 hn']
    linarith [h1, h2, hg0, hgn]
  -- Integer induction on `a`, using the shift recurrence both ways.
  refine Int.induction_on a ?_ ?_ ?_
  · refine Finset.sum_eq_zero ?_
    intro x hx
    rw [Finset.mem_range] at hx
    rw [zero_add]
    have hnabs : |(n : ℤ)| = (n : ℤ) := abs_of_pos (by exact_mod_cast hn)
    refine Int.ediv_eq_zero_of_lt_abs (by positivity) ?_
    rw [hnabs]; exact_mod_cast hx
  · intro i ih
    rw [step (i : ℤ), ih]
  · intro i ih
    have hs := step (-(i : ℤ) - 1)
    have heq : (∑ k ∈ range n, (-(i : ℤ) - 1 + 1 + (k : ℤ)) / (n : ℤ))
        = (∑ k ∈ range n, (-(i : ℤ) + (k : ℤ)) / (n : ℤ)) := by
      refine Finset.sum_congr rfl ?_
      intro k _; congr 1; ring
    rw [heq, ih] at hs
    linarith [hs]

/-- **Hermite's identity.**  For every real `x` and every `n ≥ 1`,
`∑_{k=0}^{n-1} ⌊x + k/n⌋ = ⌊n·x⌋`. -/
theorem hermite_floor_identity (x : ℝ) (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ range n, ⌊x + (k : ℝ) / (n : ℝ)⌋ = ⌊(n : ℝ) * x⌋ := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  -- Step 1: collapse each real floor to an integer Euclidean quotient.
  have hterm : ∀ k ∈ range n,
      ⌊x + (k : ℝ) / (n : ℝ)⌋ = (⌊(n : ℝ) * x⌋ + (k : ℤ)) / (n : ℤ) := by
    intro k _
    have hx : x + (k : ℝ) / (n : ℝ) = ((n : ℝ) * x + (k : ℝ)) / (n : ℝ) := by
      field_simp
    rw [hx, Int.floor_div_natCast, Int.floor_add_natCast]
  -- Step 2: apply the integer Hermite sum.
  rw [Finset.sum_congr rfl hterm, int_hermite_sum n hn ⌊(n : ℝ) * x⌋]

end HermiteFloorIdentity
