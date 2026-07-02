/-
# Alternating-Series Boole Summation — OQ-01-OQ-02
## Sharp two-sided remainder estimates for the convergent tail

The parent entry (`AlternatingSeriesBooleSummationOQ01.lean`) passes the finite Boole
identity to the limit `m → ∞`, showing that for an antitone null sequence `a` the
alternating partial sums `altSum a 0 m = ∑_{j<m} (-1)^j a_j` converge to some `L`.
It leaves the *quantitative* question open: how far is the `m`-th partial sum from `L`?

This entry answers that with the classical **sharp alternating-series remainder bound**

  `|L − altSum a 0 m| ≤ a_m`   for every `m`,

together with the two-sided bracketing that makes it sharp: consecutive partial sums lie
on opposite sides of `L` (`partial_bracket`), so `L` is trapped between `altSum a 0 m`
and `altSum a 0 (m+1)`, and the gap between those is exactly `a_m`. Specializing to
`m = 0` gives the whole-series localization `L ∈ [0, a_0]` (`sum_mem_Icc`).

## The argument

Mathlib's alternating-series test supplies the *one-sided* bracketing for the series
from `0`: even partial sums are `≤ L` (`Antitone.alternating_series_le_tendsto`) and odd
partial sums are `≥ L` (`Antitone.tendsto_le_alternating_series`). Splitting `m` into even
and odd and using the successor identity `altSum a 0 (m+1) = altSum a 0 m + (-1)^m a_m`
(the parent's `altSum_succ`) turns each one-sided bound into a two-sided sandwich of width
`a_m`, from which `|L − altSum a 0 m| ≤ a_m` follows. Antitonicity together with `a → 0`
also forces `a_m ≥ 0`, which is what makes the bound an honest absolute-value estimate.

## What Mathlib has — and what this adds

Mathlib has the convergence test and the even/odd one-sided bracketing. This entry
combines them into the single sharp remainder bound `|L − Sₘ| ≤ aₘ`, the alternating
bracketing `(Sₘ − L)(Sₘ₊₁ − L) ≤ 0`, and the localization `L ∈ [0, a₀]` — the concrete
error control that the parent's qualitative convergence statement leaves open.

**Sorry count**: 0. **Axiom count**: 0 (only Lean/Mathlib foundational axioms).
-/
import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Normed
import Proofs.AlternatingSeriesBooleSummationOQ01

namespace AlternatingSeriesBooleSummationOQ01OQ02

open AlternatingSeriesBooleSummationOQ01 Finset Filter Topology

variable {a : ℕ → ℝ}

/-- For an antitone null sequence every term is nonnegative: each `a m` bounds the tail,
which tends to `0`. -/
theorem term_nonneg (ha : Antitone a) (ha0 : Tendsto a atTop (𝓝 0)) (m : ℕ) :
    0 ≤ a m := by
  refine le_of_tendsto ha0 ?_
  filter_upwards [eventually_ge_atTop m] with j hj
  exact ha hj

/-- `altSum a 0 m` is Mathlib's `range`-form alternating partial sum. -/
theorem altSum_eq_range (m : ℕ) :
    altSum a 0 m = ∑ i ∈ range m, (-1 : ℝ) ^ i * a i := by
  rw [altSum, Finset.range_eq_Ico]

/-- Even partial sums lie below the limit: `altSum a 0 (2k) ≤ L`. -/
theorem even_partial_le (ha : Antitone a) {L : ℝ}
    (hL : Tendsto (fun m => altSum a 0 m) atTop (𝓝 L)) (k : ℕ) :
    altSum a 0 (2 * k) ≤ L := by
  have hL' : Tendsto (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i * a i) atTop (𝓝 L) := by
    simpa [altSum_eq_range] using hL
  rw [altSum_eq_range]
  exact ha.alternating_series_le_tendsto hL' k

/-- Odd partial sums lie above the limit: `L ≤ altSum a 0 (2k+1)`. -/
theorem le_odd_partial (ha : Antitone a) {L : ℝ}
    (hL : Tendsto (fun m => altSum a 0 m) atTop (𝓝 L)) (k : ℕ) :
    L ≤ altSum a 0 (2 * k + 1) := by
  have hL' : Tendsto (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i * a i) atTop (𝓝 L) := by
    simpa [altSum_eq_range] using hL
  rw [altSum_eq_range]
  exact ha.tendsto_le_alternating_series hL' k

/-- **Sharp alternating-series remainder bound.**  For an antitone null sequence with
alternating sum `L`, the `m`-th partial sum approximates `L` to within the `m`-th term:
`|L − altSum a 0 m| ≤ a_m`.  This is the best possible bound: the error is squeezed
between `0` and `a_m` by the bracketing of consecutive partial sums. -/
theorem remainder_bound (ha : Antitone a) (ha0 : Tendsto a atTop (𝓝 0)) {L : ℝ}
    (hL : Tendsto (fun m => altSum a 0 m) atTop (𝓝 L)) (m : ℕ) :
    |L - altSum a 0 m| ≤ a m := by
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- m = 2k : altSum ≤ L ≤ altSum + a m
    have hkk : m = 2 * k := by omega
    subst hkk
    have h1 : altSum a 0 (2 * k) ≤ L := even_partial_le ha hL k
    have h2 : L ≤ altSum a 0 (2 * k + 1) := le_odd_partial ha hL k
    have hs : altSum a 0 (2 * k + 1) = altSum a 0 (2 * k) + a (2 * k) := by
      rw [altSum_succ a (Nat.zero_le _), pow_mul]; norm_num
    rw [hs] at h2
    have hnn : 0 ≤ a (2 * k) := term_nonneg ha ha0 (2 * k)
    rw [abs_le]; constructor <;> linarith
  · -- m = 2k+1 : altSum - a m ≤ L ≤ altSum
    have hkk : m = 2 * k + 1 := by omega
    subst hkk
    have h2 : L ≤ altSum a 0 (2 * k + 1) := le_odd_partial ha hL k
    have h1 : altSum a 0 (2 * k + 1 + 1) ≤ L := by
      have := even_partial_le ha hL (k + 1)
      rwa [(by ring : 2 * (k + 1) = 2 * k + 1 + 1)] at this
    have hs : altSum a 0 (2 * k + 1 + 1) = altSum a 0 (2 * k + 1) - a (2 * k + 1) := by
      have hp : ((-1 : ℝ) ^ (2 * k + 1)) = -1 := by rw [pow_succ, pow_mul]; norm_num
      rw [altSum_succ a (Nat.zero_le _), hp]; ring
    rw [hs] at h1
    have hnn : 0 ≤ a (2 * k + 1) := term_nonneg ha ha0 (2 * k + 1)
    rw [abs_le]; constructor <;> linarith

/-- **Two-sided bracketing.**  Consecutive partial sums straddle the limit: the products
`(altSum a 0 m − L)` and `(altSum a 0 (m+1) − L)` have opposite signs (their product is
`≤ 0`).  This is what makes the remainder bound sharp — `L` is trapped in the interval
whose endpoints are consecutive partial sums, of width `a_m`. -/
theorem partial_bracket (ha : Antitone a) {L : ℝ}
    (hL : Tendsto (fun m => altSum a 0 m) atTop (𝓝 L)) (m : ℕ) :
    (altSum a 0 m - L) * (altSum a 0 (m + 1) - L) ≤ 0 := by
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hkk : m = 2 * k := by omega
    subst hkk
    have h1 : altSum a 0 (2 * k) ≤ L := even_partial_le ha hL k
    have h2 : L ≤ altSum a 0 (2 * k + 1) := le_odd_partial ha hL k
    exact mul_nonpos_iff.mpr (Or.inr ⟨by linarith, by linarith⟩)
  · have hkk : m = 2 * k + 1 := by omega
    subst hkk
    have h2 : L ≤ altSum a 0 (2 * k + 1) := le_odd_partial ha hL k
    have h1 : altSum a 0 (2 * k + 1 + 1) ≤ L := by
      have := even_partial_le ha hL (k + 1)
      rwa [(by ring : 2 * (k + 1) = 2 * k + 1 + 1)] at this
    exact mul_nonpos_iff.mpr (Or.inl ⟨by linarith, by linarith⟩)

/-- **Localization of the full alternating sum.**  Taking `m = 0` in the remainder bound
(where `altSum a 0 0 = 0`) traps the whole alternating series in `[0, a_0]`. -/
theorem sum_mem_Icc (ha : Antitone a) {L : ℝ}
    (hL : Tendsto (fun m => altSum a 0 m) atTop (𝓝 L)) :
    L ∈ Set.Icc (0 : ℝ) (a 0) := by
  have h0 : altSum a 0 0 = 0 := by simp [altSum]
  have hlow : altSum a 0 (2 * 0) ≤ L := even_partial_le ha hL 0
  have hup : L ≤ altSum a 0 (2 * 0 + 1) := le_odd_partial ha hL 0
  have hup' : altSum a 0 (2 * 0 + 1) = a 0 := by
    rw [altSum_succ a (Nat.zero_le _), h0]; norm_num
  rw [show 2 * 0 = 0 from rfl, h0] at hlow
  rw [hup'] at hup
  exact ⟨hlow, hup⟩

end AlternatingSeriesBooleSummationOQ01OQ02
