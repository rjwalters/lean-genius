/-
# Erdős Problem #1021 — OQ-01, Incomplete-01
## The exponent gap for ex(n, G_k), and o ⟹ O for the asymptotic classes used in OQ-01

Erdős Problem #1021 / OQ-01 asks whether `ex(n, G_k) = o(n^{3/2})` for every `k ≥ 4`.
That question is OPEN. This file does NOT resolve it. Instead it formalizes — with
**zero axioms and zero sorries** — the genuinely provable scaffolding that the parent
survey file `Erdos1021OQ01.lean` left as `sorry`/axiomatic placeholders:

1. **The o ⟹ O collapse.** The little-o relation used throughout the parent
   (`f n ≤ ε·g n` eventually, for every `ε > 0`) implies the big-O relation
   (`f n ≤ C·g n` eventually, for some `C > 0`). This is the clean, n=0-free core of
   the parent's `oq01_strictly_beyond_kst` placeholder: OQ-01 really does ask for
   something strictly inside the KST class `O(n^{3/2})`.

2. **The exponent gap `gap k = 1/(k-1)`.** The probabilistic lower bound has exponent
   `3/2 − 1/(k−1)`; the KST upper bound has exponent `3/2`. The difference `gap k`
   has a complete and verifiable structure:
   * `gap k > 0` for all `k ≥ 2` (the gap is genuinely open for every finite k),
   * `gap` is strictly decreasing in `k` (the gap shrinks as k grows),
   * `gap k → 0` (the gap closes in the limit), discharging the parent's
     `lower_bound_exponent_tendsto` sorry,
   * but `gap k ≠ 0` for every finite k (the gap never actually closes).

None of this proves OQ-01 — it is the honest, fully machine-checked boundary of what
is provable around the open question. The two genuinely hard objects (the KST upper
bound and the probabilistic lower bound) remain external inputs and are deliberately
NOT assumed here: every theorem below is about elementary real analysis.

## References
- Kővári, T., Sós, V., Turán, P. (1954). "On a problem of K. Zarankiewicz." Coll. Math. 3.
- Bondy, J.A., Simonovits, M. (1974). "Cycles of even length in graphs." JCTB 16.
- Alon, Krivelevich, Sudakov (2003), probabilistic lower bounds for bipartite ex(·).
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

namespace Erdos1021OQ01Incomplete01

open Filter Topology

/-! ## Part I: The asymptotic classes and the o ⟹ O collapse

We reproduce, self-containedly, the one-sided asymptotic relations the parent uses
(they are tailored to nonnegative extremal counts, hence no absolute values). -/

/-- `f = o(g)`: for every `ε > 0`, eventually `f n ≤ ε · g n`. -/
def isLittleO (f g : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, f n ≤ ε * g n

/-- `f ≪ g` (i.e. `f = O(g)`): eventually `f n ≤ C · g n` for some `C > 0`. -/
def isAsympBounded (f g : ℕ → ℝ) : Prop :=
  ∃ C > 0, ∃ N : ℕ, ∀ n ≥ N, f n ≤ C * g n

/-- **o ⟹ O.** If `f = o(g)` then `f = O(g)`: take `ε = 1`.
    This is the n=0-free heart of the parent's `oq01_strictly_beyond_kst`:
    OQ-01 (`ex(n,G_k) = o(n^{3/2})`) genuinely lands strictly inside the KST
    class `O(n^{3/2})`. -/
theorem littleO_imp_asympBounded {f g : ℕ → ℝ} (h : isLittleO f g) :
    isAsympBounded f g := by
  obtain ⟨N, hN⟩ := h 1 one_pos
  exact ⟨1, one_pos, N, hN⟩

/-- The converse fails: `O(g)` does not imply `o(g)`. Witness `f = g` with `g`
    eventually positive (here `g n = n^{3/2}`), so `f / g = 1 ↛ 0`. This separates
    the KST bound from the OQ-01 question. -/
theorem asympBounded_not_imp_littleO :
    ∃ f g : ℕ → ℝ,
      (∀ n, 0 ≤ g n) ∧ isAsympBounded f g ∧ ¬ isLittleO f g := by
  refine ⟨(fun n => (n : ℝ) ^ (3/2 : ℝ)), (fun n => (n : ℝ) ^ (3/2 : ℝ)), ?_, ?_, ?_⟩
  · intro n; positivity
  · exact ⟨1, one_pos, 0, fun n _ => by simp⟩
  · intro h
    obtain ⟨N, hN⟩ := h (1/2) (by norm_num)
    have hm := hN (N + 1) (Nat.le_succ N)
    have hpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) ^ (3/2 : ℝ) :=
      Real.rpow_pos_of_pos (by positivity) _
    nlinarith [hm, hpos]

/-! ## Part II: The exponent gap `gap k = 1/(k-1)`

The KST upper bound has exponent `3/2`; the probabilistic lower bound has exponent
`3/2 − 1/(k−1)`. Their difference is the "gap" function. -/

/-- The exponent gap between the KST upper bound and the probabilistic lower bound. -/
noncomputable def gap (k : ℕ) : ℝ := 1 / ((k : ℝ) - 1)

/-- The lower-bound exponent appearing in the probabilistic bound. -/
noncomputable def lowerExp (k : ℕ) : ℝ := 3 / 2 - gap k

/-- For `k ≥ 2` the gap is strictly positive: the bounds genuinely differ. -/
theorem gap_pos {k : ℕ} (hk : k ≥ 2) : 0 < gap k := by
  have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  unfold gap
  positivity

/-- For every finite `k ≥ 2` the gap is nonzero — it never actually closes. -/
theorem gap_ne_zero {k : ℕ} (hk : k ≥ 2) : gap k ≠ 0 :=
  ne_of_gt (gap_pos hk)

/-- The gap is strictly decreasing in `k` (for `k ≥ 2`): it shrinks as `k` grows. -/
theorem gap_strictly_decreasing {k₁ k₂ : ℕ} (h1 : 2 ≤ k₁) (h12 : k₁ < k₂) :
    gap k₂ < gap k₁ := by
  have hk1 : (0 : ℝ) < (k₁ : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (k₁ : ℝ) := by exact_mod_cast h1
    linarith
  have hlt : (k₁ : ℝ) - 1 < (k₂ : ℝ) - 1 := by
    have : (k₁ : ℝ) < (k₂ : ℝ) := by exact_mod_cast h12
    linarith
  unfold gap
  exact one_div_lt_one_div_of_lt hk1 hlt

/-- `1/(k-1) → 0` as `k → ∞`. The arithmetic core of the parent's
    `lower_bound_exponent_tendsto` sorry. -/
theorem gap_tendsto_zero : Tendsto gap atTop (𝓝 0) := by
  have hsub : Tendsto (fun k : ℕ => (k : ℝ) - 1) atTop atTop := by
    have h := tendsto_natCast_atTop_atTop (R := ℝ)
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1 : ℝ) h
  have h2 : Tendsto (fun k : ℕ => ((k : ℝ) - 1)⁻¹) atTop (𝓝 0) := hsub.inv_tendsto_atTop
  unfold gap
  simpa only [one_div] using h2

/-- The lower-bound exponent `3/2 − 1/(k−1) → 3/2` as `k → ∞`:
    the lower bound approaches the KST upper exponent. This discharges the parent's
    `lower_bound_exponent_tendsto`. -/
theorem lowerExp_tendsto : Tendsto lowerExp atTop (𝓝 (3 / 2)) := by
  have := (tendsto_const_nhds (x := (3 : ℝ) / 2)).sub gap_tendsto_zero
  simpa [lowerExp] using this

/-- For every `k ≥ 2` the lower exponent is strictly below the upper exponent `3/2`:
    the asymptotic gap is open for every finite `k`. -/
theorem lowerExp_lt_upper {k : ℕ} (hk : k ≥ 2) : lowerExp k < 3 / 2 := by
  have := gap_pos hk
  unfold lowerExp
  linarith

/-- The lower exponent is strictly increasing in `k` (it climbs toward `3/2`). -/
theorem lowerExp_strictly_increasing {k₁ k₂ : ℕ} (h1 : 2 ≤ k₁) (h12 : k₁ < k₂) :
    lowerExp k₁ < lowerExp k₂ := by
  have := gap_strictly_decreasing h1 h12
  unfold lowerExp
  linarith

/-! ## Part III: Summary

What is proved here (0 axioms, 0 sorries):
* `littleO_imp_asympBounded` : `o(g) ⟹ O(g)` (parent `oq01_strictly_beyond_kst` core).
* `asympBounded_not_imp_littleO` : `O(g) ⇏ o(g)` (KST bound ≠ OQ-01 question).
* `gap_pos`, `gap_ne_zero` : the exponent gap is positive for every finite `k ≥ 2`.
* `gap_strictly_decreasing` / `lowerExp_strictly_increasing` : the gap shrinks monotonically.
* `gap_tendsto_zero` / `lowerExp_tendsto` : the gap closes in the limit (parent
  `lower_bound_exponent_tendsto`).
* `lowerExp_lt_upper` : the gap never closes for finite `k`.

What is NOT proved (genuinely open / external):
* OQ-01 itself: `ex(n, G_k) = o(n^{3/2})` for `k ≥ 4`.
* The KST upper bound and the probabilistic lower bound (deep inputs, not assumed here).
-/

end Erdos1021OQ01Incomplete01
