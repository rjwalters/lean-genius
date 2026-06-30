import Mathlib

/-
# A Two-Sided (Jordan-Decomposition) Abel Trap for Alternating Series

The parent file `AlternatingSeriesTestOQ01OQ02` proves, via summation by parts, a
**symmetric** Abel/Dirichlet error bound for the alternating block sum
`∑_{i∈[N,M)} (-1)^i a i` of an *arbitrary* (non-monotone) real sequence:

`|∑_{i∈[N,M)} (-1)^i a i| ≤ |a (M-1)| + ∑_{i∈[N,M-1)} |a (i+1) - a i|`.

The right-hand side is a boundary term plus the **total variation** of `a`. The proof
discards sign information twice: it bounds the sign partial sums by `|∑_{i<k}(-1)^i| ≤ 1`,
and it bounds each increment by its absolute value `|a(i+1)-a i|`.

This file sharpens that estimate to a genuinely **two-sided, asymmetric trap**. The key
observation is that the sign partial sums are not merely bounded in absolute value — they
lie in the unit interval:

`0 ≤ ∑_{i<k} (-1)^i ≤ 1`     (they are exactly `0` or `1`, `neg_one_geom_sum`).

A multiplier `B ∈ [0,1]` maps a real number `x` into the *order interval*
`[min x 0, max x 0]` (not the symmetric `[-|x|, |x|]`). Feeding this into Abel's
transformation traps the canonical alternating sum `∑_{j<n} (-1)^j c j` between the
**positive and negative variations** of `c` separately (its Jordan decomposition):

* upper bound uses only the *downward* steps `(c j - c (j+1))⁺`;
* lower bound uses only the *upward*  steps `(c (j+1) - c j)⁺`;
* the boundary term `c (n-1)` enters two-sidedly as `max (c (n-1)) 0` / `min (c (n-1)) 0`,
  absorbing the parent's separate `|a (M-1)|` term.

The bound is strictly tighter than the parent's symmetric one whenever the increments have
mixed signs. As a sanity check it **recovers the classical Leibniz bracket**
`0 ≤ ∑_{j<n} (-1)^j c j ≤ c 0` for antitone `c ≥ 0` (`leibniz_bracket`): the upward
variation vanishes and the downward variation telescopes.

All results are over `ℝ` and build on `Finset.sum_range_by_parts`. The asymmetric
Jordan-decomposition trap is absent from Mathlib and from the parent file.
-/

namespace AlternatingSeriesTestOQ01OQ02OQ01

open Finset

/-! ### The sign partial sums lie in `[0,1]` -/

/-- The partial sums of the sign sequence `(-1)^i` are nonnegative: they are `0` or `1`. -/
theorem signSum_nonneg (k : ℕ) : 0 ≤ ∑ i ∈ range k, (-1 : ℝ) ^ i := by
  rw [neg_one_geom_sum]; split <;> norm_num

/-- The partial sums of the sign sequence `(-1)^i` are at most `1`: they are `0` or `1`.
This is the *positivity* refinement of the parent's `|∑ (-1)^i| ≤ 1`. -/
theorem signSum_le_one (k : ℕ) : ∑ i ∈ range k, (-1 : ℝ) ^ i ≤ 1 := by
  rw [neg_one_geom_sum]; split <;> norm_num

/-! ### Multiplying by a number in `[0,1]` lands in the order interval `[min x 0, max x 0]` -/

/-- For `B ∈ [0,1]`, the product `x * B` never exceeds `max x 0`. (If `x ≥ 0` then
`x * B ≤ x`; if `x < 0` then `x * B ≤ 0`.) -/
theorem mul_le_max (x : ℝ) {B : ℝ} (h0 : 0 ≤ B) (h1 : B ≤ 1) : x * B ≤ max x 0 := by
  rcases le_total 0 x with hx | hx
  · rw [max_eq_left hx]; nlinarith [mul_le_mul_of_nonneg_left h1 hx]
  · rw [max_eq_right hx]; nlinarith [mul_nonneg (neg_nonneg.2 hx) h0]

/-- For `B ∈ [0,1]`, the product `x * B` is never below `min x 0`. (If `x ≥ 0` then
`x * B ≥ 0`; if `x < 0` then `x * B ≥ x`.) -/
theorem min_le_mul (x : ℝ) {B : ℝ} (h0 : 0 ≤ B) (h1 : B ≤ 1) : min x 0 ≤ x * B := by
  rcases le_total 0 x with hx | hx
  · rw [min_eq_right hx]; exact mul_nonneg hx h0
  · rw [min_eq_left hx]; nlinarith [mul_nonneg (neg_nonneg.2 hx) (by linarith : (0 : ℝ) ≤ 1 - B)]

/-! ### Abel transformation of the canonical alternating sum -/

/-- **Summation by parts** for the canonical alternating sum, specialised to the sign
sequence `g j = (-1)^j` (whose partial sums are the `signSum`s). For any real `c` and `n`:

`∑_{i<n} (-1)^i c i = c (n-1) · (∑_{i<n} (-1)^i) − ∑_{j<n-1} (c (j+1) − c j) · (∑_{i<j+1} (-1)^i)`. -/
private theorem abel_sub_identity (c : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range n, (-1 : ℝ) ^ i * c i
      = c (n - 1) * (∑ i ∈ range n, (-1 : ℝ) ^ i)
        - ∑ j ∈ range (n - 1), (c (j + 1) - c j) * (∑ i ∈ range (j + 1), (-1 : ℝ) ^ i) := by
  have h := Finset.sum_range_by_parts (fun j => c j) (fun j => (-1 : ℝ) ^ j) n
  simp only [smul_eq_mul] at h
  rw [show (∑ i ∈ range n, c i * (-1 : ℝ) ^ i) = ∑ i ∈ range n, (-1 : ℝ) ^ i * c i from
      Finset.sum_congr rfl fun i _ => by ring] at h
  exact h

/-! ### The asymmetric two-sided trap -/

/-- **Upper half of the Abel trap.** The canonical alternating sum is bounded above by the
positive part of the boundary coefficient plus the **downward variation** of `c`:

`∑_{i<n} (-1)^i c i ≤ max (c (n-1)) 0 + ∑_{j<n-1} max (c j - c (j+1)) 0`.

Only the steps where `c` *decreases* contribute. No monotonicity is assumed. -/
theorem alternating_range_le (c : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range n, (-1 : ℝ) ^ i * c i
      ≤ max (c (n - 1)) 0 + ∑ j ∈ range (n - 1), max (c j - c (j + 1)) 0 := by
  rw [abel_sub_identity c n]
  have hbd : c (n - 1) * (∑ i ∈ range n, (-1 : ℝ) ^ i) ≤ max (c (n - 1)) 0 :=
    mul_le_max _ (signSum_nonneg n) (signSum_le_one n)
  -- The subtracted sum dominates `-(downward variation)`, proved termwise after pairing.
  have hSlow : (0 : ℝ) ≤ (∑ j ∈ range (n - 1), max (c j - c (j + 1)) 0)
      + ∑ j ∈ range (n - 1), (c (j + 1) - c j) * (∑ i ∈ range (j + 1), (-1 : ℝ) ^ i) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_nonneg fun j _ => ?_
    have hterm := mul_le_max (c j - c (j + 1)) (signSum_nonneg (j + 1)) (signSum_le_one (j + 1))
    have heq : (c (j + 1) - c j) * (∑ i ∈ range (j + 1), (-1 : ℝ) ^ i)
        = -((c j - c (j + 1)) * (∑ i ∈ range (j + 1), (-1 : ℝ) ^ i)) := by ring
    rw [heq]; linarith
  linarith

/-- **Lower half of the Abel trap.** The canonical alternating sum is bounded below by the
negative part of the boundary coefficient minus the **upward variation** of `c`:

`min (c (n-1)) 0 - ∑_{j<n-1} max (c (j+1) - c j) 0 ≤ ∑_{i<n} (-1)^i c i`.

Only the steps where `c` *increases* contribute. No monotonicity is assumed. -/
theorem alternating_range_ge (c : ℕ → ℝ) (n : ℕ) :
    min (c (n - 1)) 0 - ∑ j ∈ range (n - 1), max (c (j + 1) - c j) 0
      ≤ ∑ i ∈ range n, (-1 : ℝ) ^ i * c i := by
  rw [abel_sub_identity c n]
  have hbd : min (c (n - 1)) 0 ≤ c (n - 1) * (∑ i ∈ range n, (-1 : ℝ) ^ i) :=
    min_le_mul _ (signSum_nonneg n) (signSum_le_one n)
  have hSup : ∑ j ∈ range (n - 1), (c (j + 1) - c j) * (∑ i ∈ range (j + 1), (-1 : ℝ) ^ i)
      ≤ ∑ j ∈ range (n - 1), max (c (j + 1) - c j) 0 :=
    Finset.sum_le_sum fun j _ =>
      mul_le_max _ (signSum_nonneg (j + 1)) (signSum_le_one (j + 1))
  linarith

/-- **The two-sided trap, packaged.** The canonical alternating sum lies in the closed
interval cut out by the upper and lower variation bounds. -/
theorem alternating_range_mem_Icc (c : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ range n, (-1 : ℝ) ^ i * c i) ∈
      Set.Icc (min (c (n - 1)) 0 - ∑ j ∈ range (n - 1), max (c (j + 1) - c j) 0)
              (max (c (n - 1)) 0 + ∑ j ∈ range (n - 1), max (c j - c (j + 1)) 0) :=
  ⟨alternating_range_ge c n, alternating_range_le c n⟩

/-! ### Recovering the classical Leibniz bracket -/

/-- **Classical Leibniz trap as the monotone special case.** For an antitone, nonnegative
sequence `c` the upward variation vanishes and the downward variation telescopes, collapsing
the asymmetric trap to the textbook bracket

`0 ≤ ∑_{j<n} (-1)^j c j ≤ c 0`.

This shows the asymmetric bound *contains* the classical one. -/
theorem leibniz_bracket (c : ℕ → ℝ) (hanti : Antitone c) (hpos : ∀ i, 0 ≤ c i) (n : ℕ) :
    (∑ i ∈ range n, (-1 : ℝ) ^ i * c i) ∈ Set.Icc (0 : ℝ) (c 0) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [hpos 0]
  constructor
  · -- lower: `min (c (n-1)) 0 = 0` and the upward variation is `0`.
    refine le_trans ?_ (alternating_range_ge c n)
    have hmin : min (c (n - 1)) 0 = 0 := min_eq_right (hpos _)
    have hup : ∑ j ∈ range (n - 1), max (c (j + 1) - c j) 0 = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      exact max_eq_right (by linarith [hanti (Nat.le_succ j)])
    rw [hmin, hup]; norm_num
  · -- upper: `max (c (n-1)) 0 = c (n-1)` and the downward variation telescopes to `c 0 - c (n-1)`.
    refine le_trans (alternating_range_le c n) ?_
    have hmax : max (c (n - 1)) 0 = c (n - 1) := max_eq_left (hpos _)
    have hdown : ∑ j ∈ range (n - 1), max (c j - c (j + 1)) 0
        = c 0 - c (n - 1) := by
      have hpt : ∀ j ∈ range (n - 1), max (c j - c (j + 1)) 0 = c j - c (j + 1) := by
        intro j _; exact max_eq_left (by linarith [hanti (Nat.le_succ j)])
      rw [Finset.sum_congr rfl hpt, Finset.sum_range_sub' c (n - 1)]
    rw [hmax, hdown]; linarith

/-! ### Partial-sum (Cauchy-difference) form, even truncation point -/

/-- **Two-sided trap for partial-sum differences at an even truncation point.** Writing
`S_k = ∑_{i<k} (-1)^i a i`, for `N` even and `N < M` the difference `S_M - S_N` equals the
canonical block `∑_{j<M-N} (-1)^j a (N+j)`, so the asymmetric trap applies verbatim with
the boundary coefficient `a (M-1)` entering two-sidedly via `max`/`min`. This refines the
parent's symmetric `|S_M - S_N| ≤ |a (M-1)| + (total variation)`. -/
theorem partialSum_diff_mem_Icc (a : ℕ → ℝ) {N M : ℕ} (hN : Even N) (hNM : N < M) :
    ((∑ i ∈ range M, (-1 : ℝ) ^ i * a i) - ∑ i ∈ range N, (-1 : ℝ) ^ i * a i) ∈
      Set.Icc
        (min (a (M - 1)) 0
          - ∑ j ∈ range (M - N - 1), max (a (N + (j + 1)) - a (N + j)) 0)
        (max (a (M - 1)) 0
          + ∑ j ∈ range (M - N - 1), max (a (N + j) - a (N + (j + 1))) 0) := by
  -- Reindex the block `[N,M)` to `range (M-N)`; the constant sign `(-1)^N = 1` drops out.
  have hblock : (∑ i ∈ range M, (-1 : ℝ) ^ i * a i) - ∑ i ∈ range N, (-1 : ℝ) ^ i * a i
      = ∑ j ∈ range (M - N), (-1 : ℝ) ^ j * a (N + j) := by
    rw [← Finset.sum_Ico_eq_sub _ (le_of_lt hNM), Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_add, hN.neg_one_pow, one_mul]
  set c : ℕ → ℝ := fun j => a (N + j) with hc
  -- `c j = a (N+j)` definitionally; only the boundary index needs `c (M-N-1) = a (M-1)`.
  have hlast : c (M - N - 1) = a (M - 1) := by simp only [hc]; congr 1; omega
  rw [hblock, ← hlast]
  exact alternating_range_mem_Icc c (M - N)

end AlternatingSeriesTestOQ01OQ02OQ01
