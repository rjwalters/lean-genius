/-
# Alternating-Series Boole Summation — OQ-01-OQ-02-OQ-01
## Strict localization for a strictly antitone null sequence

The parent entry (`AlternatingSeriesBooleSummationOQ01OQ02.lean`) established, for an
*antitone* null sequence `a`, the sharp alternating-series remainder bound
`|L − Sₘ| ≤ aₘ` (`remainder_bound`) and the closed-interval localization
`L ∈ [0, a₀]` (`sum_mem_Icc`), where `Sₘ = altSum a 0 m = ∑_{j<m} (-1)ʲ aⱼ` and `L`
is the alternating sum.

Those bounds are attained at the degenerate boundary. If `a` is only *antitone* it
may be eventually constant, in which case a partial sum can *equal* the limit and `L`
can sit on an endpoint of `[0, a₀]` (e.g. `a ≡ 0` gives `L = 0 = a₀`). This entry
shows that as soon as `a` is **strictly** antitone every one of those inequalities is
strict:

  * `even_partial_lt` / `lt_odd_partial` — even (resp. odd) partial sums lie
    *strictly* below (resp. above) the limit;
  * `remainder_bound_strict` — `|L − Sₘ| < aₘ` for every `m`;
  * `sum_mem_Ioo` — the whole alternating sum lands in the *open* interval,
    `L ∈ (0, a₀)`.

## The argument

Mathlib's alternating-series test still supplies only the *non-strict* even/odd
bracketing `S_{2k} ≤ L ≤ S_{2k+1}`, imported here through the parent's
`even_partial_le` / `le_odd_partial`. Strictness comes from one extra monotone step
of the *same parity*. Strict antitonicity makes consecutive even partial sums
strictly increase,

  `S_{2k} < S_{2(k+1)} = S_{2k} + (a_{2k} − a_{2k+1})`   (`even_step_lt`),

and the non-strict bound `S_{2(k+1)} ≤ L` then squeezes `S_{2k} < L`. Dually,
consecutive odd partial sums strictly decrease (`odd_step_lt`) and `L ≤ S_{2(k+1)+1}`
squeezes `L < S_{2k+1}`. The strict remainder bound and the open-interval
localization follow exactly as their non-strict analogues did, with `≤` upgraded to
`<`.

## What this adds over the parent

The parent gives `≤`/closed-interval control valid for every antitone null sequence.
This entry pins down *when* those are tight: never in the interior of the strictly
monotone regime. For a strictly antitone null `a` the partial sums never touch `L`
and `L` never touches an endpoint — the qualitative "the series brackets its limit"
becomes the strict "it brackets it with room to spare".

**Sorry count**: 0. **Axiom count**: 0 (only Lean/Mathlib foundational axioms).
-/
import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Normed
import Proofs.AlternatingSeriesBooleSummationOQ01OQ02

namespace AlternatingSeriesBooleSummationOQ01OQ02OQ01

open AlternatingSeriesBooleSummationOQ01 AlternatingSeriesBooleSummationOQ01OQ02
open Finset Filter Topology

variable {a : ℕ → ℝ}

/-! ## Strict parity steps

The two elementary "one extra step of the same parity" identities that upgrade the
non-strict bracketing to a strict one. Both hold from `altSum_succ` and strict
antitonicity alone — no convergence hypothesis is needed. -/

/-- **Even step is strictly increasing.**  For a strictly antitone sequence,
`altSum a 0 (2(k+1)) = altSum a 0 (2k) + (a_{2k} − a_{2k+1})`, and the increment is
positive because `a_{2k+1} < a_{2k}`. -/
theorem even_step_lt (ha : StrictAnti a) (k : ℕ) :
    altSum a 0 (2 * k) < altSum a 0 (2 * (k + 1)) := by
  have e1 : altSum a 0 (2 * k + 1) = altSum a 0 (2 * k) + a (2 * k) := by
    rw [altSum_succ a (Nat.zero_le _), pow_mul]; norm_num
  have e2 : altSum a 0 (2 * k + 1 + 1) = altSum a 0 (2 * k + 1) - a (2 * k + 1) := by
    have hp : ((-1 : ℝ) ^ (2 * k + 1)) = -1 := by rw [pow_succ, pow_mul]; norm_num
    rw [altSum_succ a (Nat.zero_le _), hp]; ring
  have hstep : altSum a 0 (2 * (k + 1))
      = altSum a 0 (2 * k) + (a (2 * k) - a (2 * k + 1)) := by
    have hidx : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    rw [hidx, e2, e1]; ring
  have hpos : 0 < a (2 * k) - a (2 * k + 1) := by
    have : a (2 * k + 1) < a (2 * k) := ha (by omega)
    linarith
  rw [hstep]; linarith

/-- **Odd step is strictly decreasing.**  For a strictly antitone sequence,
`altSum a 0 (2(k+1)+1) = altSum a 0 (2k+1) − (a_{2k+1} − a_{2k+2})`, and the decrement
is positive because `a_{2k+2} < a_{2k+1}`. -/
theorem odd_step_lt (ha : StrictAnti a) (k : ℕ) :
    altSum a 0 (2 * (k + 1) + 1) < altSum a 0 (2 * k + 1) := by
  have e2 : altSum a 0 (2 * k + 1 + 1) = altSum a 0 (2 * k + 1) - a (2 * k + 1) := by
    have hp : ((-1 : ℝ) ^ (2 * k + 1)) = -1 := by rw [pow_succ, pow_mul]; norm_num
    rw [altSum_succ a (Nat.zero_le _), hp]; ring
  have e3 : altSum a 0 (2 * k + 1 + 1 + 1)
      = altSum a 0 (2 * k + 1 + 1) + a (2 * k + 1 + 1) := by
    have hp : ((-1 : ℝ) ^ (2 * k + 1 + 1)) = 1 := by
      rw [pow_succ, pow_succ, pow_mul]; norm_num
    rw [altSum_succ a (Nat.zero_le _), hp]; ring
  have hstep : altSum a 0 (2 * (k + 1) + 1)
      = altSum a 0 (2 * k + 1) - (a (2 * k + 1) - a (2 * k + 1 + 1)) := by
    have hidx : 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 := by ring
    rw [hidx, e3, e2]; ring
  have hpos : 0 < a (2 * k + 1) - a (2 * k + 1 + 1) := by
    have : a (2 * k + 1 + 1) < a (2 * k + 1) := ha (by omega)
    linarith
  rw [hstep]; linarith

/-! ## Strict one-sided bracketing -/

/-- **Even partial sums are strictly below the limit.**  `altSum a 0 (2k) < L`.
One strict even step `S_{2k} < S_{2(k+1)}` combines with the parent's non-strict
even bound `S_{2(k+1)} ≤ L`. -/
theorem even_partial_lt (ha : StrictAnti a) {L : ℝ}
    (hL : Tendsto (fun m => altSum a 0 m) atTop (𝓝 L)) (k : ℕ) :
    altSum a 0 (2 * k) < L := by
  have hstep : altSum a 0 (2 * k) < altSum a 0 (2 * (k + 1)) := even_step_lt ha k
  have hle : altSum a 0 (2 * (k + 1)) ≤ L := even_partial_le ha.antitone hL (k + 1)
  linarith

/-- **Odd partial sums are strictly above the limit.**  `L < altSum a 0 (2k+1)`.
One strict odd step `S_{2(k+1)+1} < S_{2k+1}` combines with the parent's non-strict
odd bound `L ≤ S_{2(k+1)+1}`. -/
theorem lt_odd_partial (ha : StrictAnti a) {L : ℝ}
    (hL : Tendsto (fun m => altSum a 0 m) atTop (𝓝 L)) (k : ℕ) :
    L < altSum a 0 (2 * k + 1) := by
  have hstep : altSum a 0 (2 * (k + 1) + 1) < altSum a 0 (2 * k + 1) := odd_step_lt ha k
  have hle : L ≤ altSum a 0 (2 * (k + 1) + 1) := le_odd_partial ha.antitone hL (k + 1)
  linarith

/-! ## Strict remainder bound and open-interval localization -/

/-- **Strict alternating-series remainder bound.**  For a *strictly* antitone null
sequence with alternating sum `L`, the `m`-th partial sum approximates `L` to strictly
better than the `m`-th term: `|L − altSum a 0 m| < a m`.  The strictness is the content
here: the non-strict bound `≤ aₘ` (parent `remainder_bound`) is never attained in the
strictly monotone regime.  No null hypothesis on `a` is needed: convergence of the
partial sums already forces `aₘ > 0` inside the strict brackets. -/
theorem remainder_bound_strict (ha : StrictAnti a) {L : ℝ}
    (hL : Tendsto (fun m => altSum a 0 m) atTop (𝓝 L)) (m : ℕ) :
    |L - altSum a 0 m| < a m := by
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- m = 2k : S_{2k} < L < S_{2k} + a_{2k}
    have hkk : m = 2 * k := by omega
    subst hkk
    have h1 : altSum a 0 (2 * k) < L := even_partial_lt ha hL k
    have h2 : L < altSum a 0 (2 * k + 1) := lt_odd_partial ha hL k
    have hs : altSum a 0 (2 * k + 1) = altSum a 0 (2 * k) + a (2 * k) := by
      rw [altSum_succ a (Nat.zero_le _), pow_mul]; norm_num
    rw [hs] at h2
    rw [abs_lt]; constructor <;> linarith
  · -- m = 2k+1 : S_{2k+1} - a_{2k+1} < L < S_{2k+1}
    have hkk : m = 2 * k + 1 := by omega
    subst hkk
    have h2 : L < altSum a 0 (2 * k + 1) := lt_odd_partial ha hL k
    have h1 : altSum a 0 (2 * k + 1 + 1) < L := by
      have := even_partial_lt ha hL (k + 1)
      rwa [(by ring : 2 * (k + 1) = 2 * k + 1 + 1)] at this
    have hs : altSum a 0 (2 * k + 1 + 1) = altSum a 0 (2 * k + 1) - a (2 * k + 1) := by
      have hp : ((-1 : ℝ) ^ (2 * k + 1)) = -1 := by rw [pow_succ, pow_mul]; norm_num
      rw [altSum_succ a (Nat.zero_le _), hp]; ring
    rw [hs] at h1
    rw [abs_lt]; constructor <;> linarith

/-- **Strict two-sided bracketing.**  Consecutive partial sums straddle the limit with
strict inequalities on both sides: `(altSum a 0 m − L)·(altSum a 0 (m+1) − L) < 0`.
This sharpens the parent's `partial_bracket` (product `≤ 0`): for a strictly antitone
sequence neither factor can vanish. -/
theorem partial_bracket_strict (ha : StrictAnti a) {L : ℝ}
    (hL : Tendsto (fun m => altSum a 0 m) atTop (𝓝 L)) (m : ℕ) :
    (altSum a 0 m - L) * (altSum a 0 (m + 1) - L) < 0 := by
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hkk : m = 2 * k := by omega
    subst hkk
    have h1 : altSum a 0 (2 * k) < L := even_partial_lt ha hL k
    have h2 : L < altSum a 0 (2 * k + 1) := lt_odd_partial ha hL k
    exact mul_neg_of_neg_of_pos (by linarith) (by linarith)
  · have hkk : m = 2 * k + 1 := by omega
    subst hkk
    have h2 : L < altSum a 0 (2 * k + 1) := lt_odd_partial ha hL k
    have h1 : altSum a 0 (2 * k + 1 + 1) < L := by
      have := even_partial_lt ha hL (k + 1)
      rwa [(by ring : 2 * (k + 1) = 2 * k + 1 + 1)] at this
    exact mul_neg_of_pos_of_neg (by linarith) (by linarith)

/-- **Open-interval localization of the full alternating sum.**  Taking `m = 0` in the
strict bracketing (where `altSum a 0 0 = 0` and `altSum a 0 1 = a₀`) traps the whole
alternating series in the *open* interval: `L ∈ (0, a₀)`.  In particular `L` is
strictly positive and strictly below the leading term. -/
theorem sum_mem_Ioo (ha : StrictAnti a) {L : ℝ}
    (hL : Tendsto (fun m => altSum a 0 m) atTop (𝓝 L)) :
    L ∈ Set.Ioo (0 : ℝ) (a 0) := by
  have h0 : altSum a 0 0 = 0 := by simp [altSum]
  have hlow : altSum a 0 (2 * 0) < L := even_partial_lt ha hL 0
  have hup : L < altSum a 0 (2 * 0 + 1) := lt_odd_partial ha hL 0
  have hup' : altSum a 0 (2 * 0 + 1) = a 0 := by
    rw [altSum_succ a (Nat.zero_le _), h0]; norm_num
  rw [show 2 * 0 = 0 from rfl, h0] at hlow
  rw [hup'] at hup
  exact ⟨hlow, hup⟩

end AlternatingSeriesBooleSummationOQ01OQ02OQ01
