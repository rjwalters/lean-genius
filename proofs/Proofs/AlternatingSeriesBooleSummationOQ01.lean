/-
# Alternating-Series Boole Summation — OQ-01
## Passing the finite Boole identity to the limit `m → ∞`

The parent entry `AlternatingSeriesBooleSummation.lean` proves the exact **finite** Boole
summation identity

  `altSum a n m = ½·((-1)^n a_n - (-1)^m a_m) - ½·altSum (Δa) n m`   (`boole_first`),

where `altSum a n m = ∑_{j=n}^{m-1} (-1)^j a_j` and `Δa_j = a_{j+1} - a_j`, valid on every
finite window `n ≤ m` with no convergence assumed.  Its first open question asks whether
letting `m → ∞` for a convergent alternating series gives a clean *limit-level* statement
tying the finite engine to Mathlib's notion of convergence.

This file answers that.  For a null sequence `a → 0`, the endpoint term `(-1)^m a_m → 0`
(`sign_mul_tendsto_zero`), so passing `boole_first` to the limit shows:

* if the alternating series converges, `altSum a n m → S`, then the **forward-difference
  alternating series converges too**, to `(-1)^n a_n - 2S` (`fdiff_altSum_tendsto`); and
* the two limits obey the limit form of Boole's identity,
  `S = ½·(-1)^n a_n - ½·T`   (`boole_tendsto`).

Combined with Mathlib's alternating-series test (`Antitone.tendsto_alternating_series_of_
tendsto_zero`) we get an unconditional statement for antitone null sequences: every tail
converges (`altSum_tendsto_of_antitone`) and its forward-difference series converges to the
Boole value (`boole_tendsto_of_antitone`).

**A deliberate subtlety.**  The correct limit object here is the limit of the *partial sums*
`altSum a n m` as `m → ∞`, i.e. `Filter.Tendsto`, **not** `HasSum`/`∑'`.  An alternating
series such as `∑ (-1)^j / (j+1)` converges conditionally but is not summable, so `HasSum`
(unconditional net convergence) genuinely fails; there is no honest `tsum`-level restatement.
That is why every result below is phrased with `Tendsto … atTop`.

All results are over `ℝ` and axiom-free.
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Normed

namespace AlternatingSeriesBooleSummationOQ01

open Finset Filter Topology

/-- The forward difference `Δa_j = a_{j+1} - a_j` (as in the parent file). -/
def fdiff (a : ℕ → ℝ) (j : ℕ) : ℝ := a (j + 1) - a j

/-- The alternating partial sum `∑_{j=n}^{m-1} (-1)^j a_j` (as in the parent file). -/
def altSum (a : ℕ → ℝ) (n m : ℕ) : ℝ := ∑ j ∈ Finset.Ico n m, (-1 : ℝ) ^ j * a j

/-! ## The finite engine (restated for self-containment) -/

theorem altSum_succ (a : ℕ → ℝ) {n m : ℕ} (h : n ≤ m) :
    altSum a n (m + 1) = altSum a n m + (-1 : ℝ) ^ m * a m := by
  simp only [altSum]
  rw [Finset.sum_Ico_succ_top h]

/-- **First-order Boole summation formula** (parent `boole_first`). -/
theorem boole_first (a : ℕ → ℝ) (n m : ℕ) (h : n ≤ m) :
    altSum a n m
      = (1 / 2) * ((-1 : ℝ) ^ n * a n - (-1 : ℝ) ^ m * a m)
        - (1 / 2) * altSum (fdiff a) n m := by
  induction m, h using Nat.le_induction with
  | base => simp only [altSum, Finset.Ico_self, Finset.sum_empty]; ring
  | succ k hk ih =>
    rw [altSum_succ a hk, altSum_succ (fdiff a) hk, ih, fdiff, pow_succ]
    ring

/-- Consecutive-window additivity: `altSum a 0 n + altSum a n m = altSum a 0 m` for `n ≤ m`. -/
theorem altSum_zero_add (a : ℕ → ℝ) {n m : ℕ} (h : n ≤ m) :
    altSum a 0 n + altSum a n m = altSum a 0 m := by
  simp only [altSum]
  rw [Finset.sum_Ico_consecutive _ (Nat.zero_le n) h]

/-! ## The endpoint term vanishes -/

/-- The absolute value of the signed term is just `|a m|`. -/
theorem abs_sign_mul (a : ℕ → ℝ) (m : ℕ) : |(-1 : ℝ) ^ m * a m| = |a m| := by
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

/-- For a null sequence, the alternating endpoint term `(-1)^m a_m` tends to `0`. -/
theorem sign_mul_tendsto_zero {a : ℕ → ℝ} (ha0 : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun m => (-1 : ℝ) ^ m * a m) atTop (𝓝 0) := by
  have hupper : Tendsto (fun m => |a m|) atTop (𝓝 0) := by
    simpa using ha0.abs
  have hlower : Tendsto (fun m => -|a m|) atTop (𝓝 0) := by
    simpa using hupper.neg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlower hupper (fun m => ?_) (fun m => ?_)
  · have := neg_abs_le ((-1 : ℝ) ^ m * a m)
    rwa [abs_sign_mul a m] at this
  · have := le_abs_self ((-1 : ℝ) ^ m * a m)
    rwa [abs_sign_mul a m] at this

/-! ## Passing Boole's identity to the limit -/

/-- **Limit of the forward-difference alternating series.**  If `a → 0` and the alternating
series converges (`altSum a n m → S` as `m → ∞`), then the *forward-difference* alternating
series converges as well, and its limit is `(-1)^n a_n - 2S`. -/
theorem fdiff_altSum_tendsto {a : ℕ → ℝ} {n : ℕ} {S : ℝ}
    (ha0 : Tendsto a atTop (𝓝 0))
    (hS : Tendsto (fun m => altSum a n m) atTop (𝓝 S)) :
    Tendsto (fun m => altSum (fdiff a) n m) atTop (𝓝 ((-1 : ℝ) ^ n * a n - 2 * S)) := by
  -- From `boole_first`, `altSum (Δa) n m = (-1)^n a_n - (-1)^m a_m - 2·altSum a n m` for `m ≥ n`.
  have heq : (fun m => altSum (fdiff a) n m)
      =ᶠ[atTop] (fun m => ((-1 : ℝ) ^ n * a n - (-1 : ℝ) ^ m * a m) - 2 * altSum a n m) := by
    filter_upwards [eventually_ge_atTop n] with m hm
    have := boole_first a n m hm
    -- solve the identity for `altSum (Δa) n m`
    linarith [this]
  rw [tendsto_congr' heq]
  have hend : Tendsto (fun m => (-1 : ℝ) ^ n * a n - (-1 : ℝ) ^ m * a m) atTop
      (𝓝 ((-1 : ℝ) ^ n * a n - 0)) :=
    tendsto_const_nhds.sub (sign_mul_tendsto_zero ha0)
  have := hend.sub (hS.const_mul 2)
  simpa using this

/-- **Limit form of Boole's identity.**  If `a → 0`, the alternating series converges to `S`
and the forward-difference alternating series converges to `T`, then `S = ½·(-1)^n a_n - ½·T`.
This is exactly the parent's `boole_first` after `m → ∞`. -/
theorem boole_tendsto {a : ℕ → ℝ} {n : ℕ} {S T : ℝ}
    (ha0 : Tendsto a atTop (𝓝 0))
    (hS : Tendsto (fun m => altSum a n m) atTop (𝓝 S))
    (hT : Tendsto (fun m => altSum (fdiff a) n m) atTop (𝓝 T)) :
    S = (1 / 2) * ((-1 : ℝ) ^ n * a n) - (1 / 2) * T := by
  have hT' := fdiff_altSum_tendsto ha0 hS
  have : T = (-1 : ℝ) ^ n * a n - 2 * S := tendsto_nhds_unique hT hT'
  rw [this]; ring

/-! ## Unconditional version for antitone null sequences (via the alternating-series test) -/

/-- Every tail of an antitone null sequence's alternating series converges.  From Mathlib's
alternating-series test applied to the full series, then the consecutive-window identity. -/
theorem altSum_tendsto_of_antitone {a : ℕ → ℝ} (ha : Antitone a)
    (ha0 : Tendsto a atTop (𝓝 0)) (n : ℕ) :
    ∃ S, Tendsto (fun m => altSum a n m) atTop (𝓝 S) := by
  obtain ⟨L, hL⟩ := ha.tendsto_alternating_series_of_tendsto_zero ha0
  -- `hL : Tendsto (fun m => ∑ i ∈ range m, (-1)^i * a i) atTop (𝓝 L)`, i.e. `altSum a 0 m → L`.
  have hL' : Tendsto (fun m => altSum a 0 m) atTop (𝓝 L) := by
    refine hL.congr (fun m => ?_)
    rw [altSum, Finset.range_eq_Ico]
  refine ⟨L - altSum a 0 n, ?_⟩
  have heq : (fun m => altSum a n m) =ᶠ[atTop]
      (fun m => altSum a 0 m - altSum a 0 n) := by
    filter_upwards [eventually_ge_atTop n] with m hm
    have := altSum_zero_add a hm
    linarith [this]
  rw [tendsto_congr' heq]
  exact hL'.sub_const _

/-- **Boole's identity at the limit, unconditionally, for antitone null sequences.**  The
forward-difference alternating series converges to the Boole value `(-1)^n a_n - 2S`, where
`S` is the sum of the alternating series from `n`. -/
theorem boole_tendsto_of_antitone {a : ℕ → ℝ} (ha : Antitone a)
    (ha0 : Tendsto a atTop (𝓝 0)) (n : ℕ) :
    ∃ S, Tendsto (fun m => altSum a n m) atTop (𝓝 S) ∧
      Tendsto (fun m => altSum (fdiff a) n m) atTop (𝓝 ((-1 : ℝ) ^ n * a n - 2 * S)) := by
  obtain ⟨S, hS⟩ := altSum_tendsto_of_antitone ha ha0 n
  exact ⟨S, hS, fdiff_altSum_tendsto ha0 hS⟩

#check @fdiff_altSum_tendsto
#check @boole_tendsto
#check @boole_tendsto_of_antitone

end AlternatingSeriesBooleSummationOQ01
