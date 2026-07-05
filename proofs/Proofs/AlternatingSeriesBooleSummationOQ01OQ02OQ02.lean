/-
# Alternating-Series Boole Summation — OQ-01-OQ-02-OQ-02
## A sharp remainder bound for the forward-difference (first-order Boole) series

Two threads meet in this entry.

* The grandparent `AlternatingSeriesBooleSummationOQ01.lean` passes the finite Boole
  identity to the limit: for a null sequence `a → 0` whose alternating series converges,
  `altSum a 0 m → S`, the **forward-difference alternating series** converges too, to the
  Boole value `T = a₀ − 2S` (`fdiff_altSum_tendsto` / `boole_tendsto`, at `n = 0`).
* The parent `AlternatingSeriesBooleSummationOQ01OQ02.lean` supplies the **sharp
  remainder bound** for the *original* series, `|S − altSum a 0 m| ≤ aₘ`, via the even/odd
  bracketing `altSum a 0 (2k) ≤ S ≤ altSum a 0 (2k+1)`.

The open question is quantitative: **how fast does the forward-difference (Boole) series
approach its limit `T`?**  This file answers it, and the answer is sharper than the naive
triangle-inequality estimate suggests.

## The result

The finite Boole identity, solved for the forward-difference partial sum, is *exact*:

  `altSum (Δa) 0 m = a₀ − (−1)ᵐ aₘ − 2·altSum a 0 m`   (`fdiff_altSum_eq`).

Subtracting from the limit `T = a₀ − 2S` gives the **exact remainder identity**

  `T − altSum (Δa) 0 m = (−1)ᵐ aₘ − 2·(S − altSum a 0 m)`   (`fdiff_remainder_eq`),

tying the Boole-series remainder to the original-series remainder `rₘ = S − altSum a 0 m`.
The triangle inequality alone only gives `|T − altSum (Δa) 0 m| ≤ 3 aₘ`.  But the sign of
`rₘ` is *correlated* with the sign of `(−1)ᵐ aₘ` — the bracketing forces `rₘ ∈ [0, aₘ]` for
even `m` and `rₘ ∈ [−aₘ, 0]` for odd `m` — so the two terms partially cancel and we get the
**sharp** bound

  `|T − altSum (Δa) 0 m| ≤ aₘ`   (`fdiff_remainder_bound`).

That is exactly the same sharp bound the original alternating series enjoys: the first-order
Boole transform **preserves** the sharp `aₘ` error control (it does not accelerate it — the
naive `3 aₘ` would have suggested it *degrades* it, and both readings are wrong).

This is not a corollary of the alternating-series test applied to the Boole series itself:
the forward-difference terms `Δaⱼ = aⱼ₊₁ − aⱼ` are one-signed for antitone `a` but their
magnitudes need not be monotone, so `Δa` need not satisfy the test's hypotheses.  The bound
has to be routed through the original series' bracketing, which is what this entry does.

`fdiff_remainder_tendsto_zero` records the resulting `O(aₘ)` convergence, and
`fdiff_remainder_bound_of_antitone` packages the unconditional statement for antitone null
sequences (existence of `S`, convergence of the Boole series to `a₀ − 2S`, and the sharp
bound at every `m`).

**Sorry count**: 0.  **Axiom count**: 0 (only Lean/Mathlib foundational axioms).
-/
import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Normed
import Proofs.AlternatingSeriesBooleSummationOQ01
import Proofs.AlternatingSeriesBooleSummationOQ01OQ02

namespace AlternatingSeriesBooleSummationOQ01OQ02OQ02

open AlternatingSeriesBooleSummationOQ01 AlternatingSeriesBooleSummationOQ01OQ02
open Finset Filter Topology

variable {a : ℕ → ℝ}

/-! ## The exact finite identity for the forward-difference partial sum -/

/-- **Forward-difference partial sum, solved exactly.**  Rearranging the first-order Boole
identity `boole_first` at `n = 0` isolates the forward-difference partial sum:

`altSum (Δa) 0 m = a₀ − (−1)ᵐ aₘ − 2·altSum a 0 m`.

No convergence is used — this holds for every `m`. -/
theorem fdiff_altSum_eq (a : ℕ → ℝ) (m : ℕ) :
    altSum (fdiff a) 0 m = a 0 - (-1 : ℝ) ^ m * a m - 2 * altSum a 0 m := by
  have h := boole_first a 0 m (Nat.zero_le m)
  linear_combination 2 * h

/-- **Exact remainder identity.**  With `S = lim altSum a 0 m` and Boole limit `T = a₀ − 2S`,
the Boole-series remainder is pinned to the original-series remainder `S − altSum a 0 m`:

`(a₀ − 2S) − altSum (Δa) 0 m = (−1)ᵐ aₘ − 2·(S − altSum a 0 m)`.

This is pure algebra from `fdiff_altSum_eq`; the analytic input enters only in identifying
`a₀ − 2S` as the limit `T` (`fdiff_tendsto`). -/
theorem fdiff_remainder_eq (a : ℕ → ℝ) (S : ℝ) (m : ℕ) :
    (a 0 - 2 * S) - altSum (fdiff a) 0 m
      = (-1 : ℝ) ^ m * a m - 2 * (S - altSum a 0 m) := by
  rw [fdiff_altSum_eq]; ring

/-! ## The Boole limit and the sharp remainder bound -/

/-- The forward-difference (Boole) series converges to `a₀ − 2S`, where `S` is the sum of the
original alternating series.  This is `fdiff_altSum_tendsto` at `n = 0`, so `a₀ − 2S` is the
genuine limit that the remainder bound below measures against. -/
theorem fdiff_tendsto (ha0 : Tendsto a atTop (𝓝 0)) {S : ℝ}
    (hS : Tendsto (fun m => altSum a 0 m) atTop (𝓝 S)) :
    Tendsto (fun m => altSum (fdiff a) 0 m) atTop (𝓝 (a 0 - 2 * S)) := by
  have h := fdiff_altSum_tendsto ha0 hS
  simpa using h

/-- **Sharp remainder bound for the forward-difference (Boole) series.**  For an antitone
null sequence with alternating sum `S`, the `m`-th partial sum of the forward-difference
series approximates its limit `a₀ − 2S` to within the `m`-th term of `a`:

`|(a₀ − 2S) − altSum (Δa) 0 m| ≤ aₘ`.

The naive triangle inequality on `fdiff_remainder_eq` only gives `3 aₘ`; the sharp `aₘ`
comes from the sign correlation supplied by the even/odd bracketing of the original series
(`even_partial_le` / `le_odd_partial`).  Note that `aₘ ≥ 0` is *not* assumed: it is forced by
the same bracketing (`altSum a 0 (2k) ≤ S ≤ altSum a 0 (2k+1) = altSum a 0 (2k) + aₘ`), so
antitonicity and convergence of the original series are all that is needed. -/
theorem fdiff_remainder_bound (ha : Antitone a)
    {S : ℝ} (hS : Tendsto (fun m => altSum a 0 m) atTop (𝓝 S)) (m : ℕ) :
    |(a 0 - 2 * S) - altSum (fdiff a) 0 m| ≤ a m := by
  rw [fdiff_remainder_eq a S m]
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- m = 2k : the original remainder rₘ = S − altSum lies in [0, aₘ]
    have hm : m = 2 * k := by omega
    subst hm
    have hp : ((-1 : ℝ) ^ (2 * k)) = 1 := by rw [pow_mul]; norm_num
    have hlo : altSum a 0 (2 * k) ≤ S := even_partial_le ha hS k
    have hhi : S ≤ altSum a 0 (2 * k + 1) := le_odd_partial ha hS k
    have hs : altSum a 0 (2 * k + 1) = altSum a 0 (2 * k) + a (2 * k) := by
      rw [altSum_succ a (Nat.zero_le (2 * k)), hp]; ring
    rw [hs] at hhi
    rw [hp, abs_le]
    constructor <;> linarith
  · -- m = 2k+1 : the original remainder rₘ lies in [−aₘ, 0]
    have hm : m = 2 * k + 1 := by omega
    subst hm
    have hp : ((-1 : ℝ) ^ (2 * k + 1)) = -1 := by rw [pow_succ, pow_mul]; norm_num
    have hhi : S ≤ altSum a 0 (2 * k + 1) := le_odd_partial ha hS k
    have hlo : altSum a 0 (2 * k + 1 + 1) ≤ S := by
      have := even_partial_le ha hS (k + 1)
      rwa [(by ring : 2 * (k + 1) = 2 * k + 1 + 1)] at this
    have hs : altSum a 0 (2 * k + 1 + 1) = altSum a 0 (2 * k + 1) - a (2 * k + 1) := by
      rw [altSum_succ a (Nat.zero_le (2 * k + 1)), hp]; ring
    rw [hs] at hlo
    rw [hp, abs_le]
    constructor <;> linarith

/-- **`O(aₘ)` convergence of the Boole series.**  The forward-difference remainder tends to
`0`; combined with `fdiff_remainder_bound` this says the Boole series converges to its limit
at the same `aₘ` rate as the original alternating series. -/
theorem fdiff_remainder_tendsto_zero (ha0 : Tendsto a atTop (𝓝 0)) {S : ℝ}
    (hS : Tendsto (fun m => altSum a 0 m) atTop (𝓝 S)) :
    Tendsto (fun m => (a 0 - 2 * S) - altSum (fdiff a) 0 m) atTop (𝓝 0) := by
  have h : Tendsto (fun m => altSum (fdiff a) 0 m) atTop (𝓝 (a 0 - 2 * S)) :=
    fdiff_tendsto ha0 hS
  have hc : Tendsto (fun _ : ℕ => a 0 - 2 * S) atTop (𝓝 (a 0 - 2 * S)) := tendsto_const_nhds
  have h2 := hc.sub h
  simpa using h2

/-- **Unconditional packaging for antitone null sequences.**  Every antitone null sequence
`a` has: a convergent alternating series `altSum a 0 m → S`, a convergent forward-difference
(Boole) series `altSum (Δa) 0 m → a₀ − 2S`, and the sharp remainder bound
`|(a₀ − 2S) − altSum (Δa) 0 m| ≤ aₘ` at every `m`. -/
theorem fdiff_remainder_bound_of_antitone (ha : Antitone a) (ha0 : Tendsto a atTop (𝓝 0)) :
    ∃ S, Tendsto (fun m => altSum a 0 m) atTop (𝓝 S) ∧
      Tendsto (fun m => altSum (fdiff a) 0 m) atTop (𝓝 (a 0 - 2 * S)) ∧
      ∀ m, |(a 0 - 2 * S) - altSum (fdiff a) 0 m| ≤ a m := by
  obtain ⟨S, hS⟩ := altSum_tendsto_of_antitone ha ha0 0
  exact ⟨S, hS, fdiff_tendsto ha0 hS, fun m => fdiff_remainder_bound ha hS m⟩

#check @fdiff_altSum_eq
#check @fdiff_remainder_eq
#check @fdiff_remainder_bound
#check @fdiff_remainder_bound_of_antitone

-- Axiom audit: only the foundational `propext` / `Classical.choice` / `Quot.sound`.
#print axioms fdiff_remainder_bound
#print axioms fdiff_remainder_bound_of_antitone

end AlternatingSeriesBooleSummationOQ01OQ02OQ02
