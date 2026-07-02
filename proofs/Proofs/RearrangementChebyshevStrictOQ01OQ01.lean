/-
# Chebyshev's sum inequality: explicit lower bound and strict form

Mathlib proves Chebyshev's sum inequality
(`MonovaryOn.sum_mul_sum_le_card_mul_sum`): when `f` and `g` monovary on a finite
set `s`,
  `(∑ i ∈ s, f i) * (∑ i ∈ s, g i) ≤ #s * ∑ i ∈ s, f i * g i`.
The sibling entry `rearrangement-inequality-oq-01` records the exact **equality
case** via the discrete covariance identity. What neither records is a *quantitative*
statement: **how far** from equality are we? This file answers that.

The engine is again the covariance identity (valid for any real `f, g`, no order
hypothesis):
  `∑ i ∈ s, ∑ j ∈ s, (f i - f j) * (g i - g j)
      = 2 * (#s * (∑ i ∈ s, f i * g i) - (∑ i ∈ s, f i) * (∑ i ∈ s, g i))`.

When `f, g` monovary every summand `(f i - f j)(g i - g j)` is `≥ 0`, so the
"Chebyshev gap"
  `G := #s * (∑ f·g) - (∑ f)(∑ g)`
equals *half* a sum of nonnegative terms. Consequently `G` is bounded below by half
of **any** single term, and hence by half the **maximum pairwise defect**
  `max_{i,j ∈ s} (f i - f j)(g i - g j)`.
This is an explicit, computable lower bound quantifying the distance from equality.

Results (all `0`-axiom):
* `covariance_identity` — the two-index algebraic identity (no order hypothesis);
* `term_nonneg` / `term_pos` — sign of a single summand under monovariance;
* `term_le_double_sum` — a single term is dominated by the full double sum;
* `half_term_le_gap` — `½ (f i₀ - f j₀)(g i₀ - g j₀) ≤ G` for every pair `i₀,j₀ ∈ s`;
* `half_maxDefect_le_gap` — the sharp form: `½ · (max pairwise defect) ≤ G`;
* `gap_pos` / `gap_pos_of_exists` — **strict** Chebyshev: the gap is positive as
  soon as `f` and `g` each take two distinct values on `s` at a common pair.
-/
import Mathlib

open Finset

namespace RearrangementChebyshevStrict

variable {ι : Type*} {s : Finset ι} {f g : ι → ℝ}

/-- **Discrete covariance identity.** For any real-valued `f, g` on a finite set `s`,
the symmetric double sum `∑ᵢ∑ⱼ (fᵢ - fⱼ)(gᵢ - gⱼ)` equals
`2 · (#s · ∑ fᵢgᵢ − (∑ fᵢ)(∑ gᵢ))`. No order hypotheses. -/
theorem covariance_identity :
    ∑ i ∈ s, ∑ j ∈ s, (f i - f j) * (g i - g j)
      = 2 * ((s.card : ℝ) * (∑ i ∈ s, f i * g i)
        - (∑ i ∈ s, f i) * (∑ i ∈ s, g i)) := by
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- Each summand of the covariance double sum is nonnegative when `f` and `g` monovary. -/
theorem term_nonneg (hfg : MonovaryOn f g s) {i j : ι} (hi : i ∈ s) (hj : j ∈ s) :
    0 ≤ (f i - f j) * (g i - g j) := by
  rcases lt_trichotomy (g i) (g j) with h | h | h
  · have hf : f i ≤ f j := hfg hi hj h
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ f j - f i) (by linarith : (0:ℝ) ≤ g j - g i)]
  · have : g i - g j = 0 := by linarith
    rw [this, mul_zero]
  · have hf : f j ≤ f i := hfg hj hi h
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ f i - f j) (by linarith : (0:ℝ) ≤ g i - g j)]

/-- A single covariance summand is dominated by the full double sum (all summands are
nonnegative under monovariance). -/
theorem term_le_double_sum (hfg : MonovaryOn f g s) {i₀ j₀ : ι}
    (hi : i₀ ∈ s) (hj : j₀ ∈ s) :
    (f i₀ - f j₀) * (g i₀ - g j₀)
      ≤ ∑ i ∈ s, ∑ j ∈ s, (f i - f j) * (g i - g j) := by
  calc
    (f i₀ - f j₀) * (g i₀ - g j₀)
        ≤ ∑ j ∈ s, (f i₀ - f j) * (g i₀ - g j) :=
          Finset.single_le_sum (fun j hj' => term_nonneg hfg hi hj') hj
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, (f i - f j) * (g i - g j) :=
          Finset.single_le_sum
            (fun i hi' => Finset.sum_nonneg fun j hj' => term_nonneg hfg hi' hj') hi

/-- **Explicit per-pair lower bound.** For monovarying `f, g` and any pair `i₀, j₀ ∈ s`,
half the pairwise defect `(f i₀ - f j₀)(g i₀ - g j₀)` bounds the Chebyshev gap
`#s · ∑ f·g − (∑ f)(∑ g)` from below. -/
theorem half_term_le_gap (hfg : MonovaryOn f g s) {i₀ j₀ : ι}
    (hi : i₀ ∈ s) (hj : j₀ ∈ s) :
    (1 / 2) * ((f i₀ - f j₀) * (g i₀ - g j₀))
      ≤ (s.card : ℝ) * (∑ i ∈ s, f i * g i) - (∑ i ∈ s, f i) * (∑ i ∈ s, g i) := by
  have hid := covariance_identity (s := s) (f := f) (g := g)
  have hle := term_le_double_sum hfg hi hj
  linarith

/-- **Sharp explicit lower bound.** For monovarying `f, g` on a nonempty `s`, half the
**maximum pairwise defect** `max_{i,j ∈ s} (f i - f j)(g i - g j)` bounds the Chebyshev
gap from below. This is the tightest bound of `half_term_le_gap`, taken over all pairs. -/
theorem half_maxDefect_le_gap (hfg : MonovaryOn f g s) (hne : s.Nonempty) :
    (1 / 2) * ((s ×ˢ s).sup' (hne.product hne)
        (fun p : ι × ι => (f p.1 - f p.2) * (g p.1 - g p.2)))
      ≤ (s.card : ℝ) * (∑ i ∈ s, f i * g i) - (∑ i ∈ s, f i) * (∑ i ∈ s, g i) := by
  have hsup :
      (s ×ˢ s).sup' (hne.product hne)
          (fun p : ι × ι => (f p.1 - f p.2) * (g p.1 - g p.2))
        ≤ ∑ i ∈ s, ∑ j ∈ s, (f i - f j) * (g i - g j) := by
    apply Finset.sup'_le
    intro p hp
    rw [Finset.mem_product] at hp
    exact term_le_double_sum hfg hp.1 hp.2
  have hid := covariance_identity (s := s) (f := f) (g := g)
  linarith

/-- A single covariance summand is **strictly** positive when `f` and `g` each separate
the two indices (they monovary, so they must move in the same direction). -/
theorem term_pos (hfg : MonovaryOn f g s) {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (hf : f i ≠ f j) (hg : g i ≠ g j) : 0 < (f i - f j) * (g i - g j) := by
  rcases lt_trichotomy (g i) (g j) with h | h | h
  · have hle : f i ≤ f j := hfg hi hj h
    have hlt : f i < f j := lt_of_le_of_ne hle hf
    nlinarith [mul_pos (by linarith : (0:ℝ) < f j - f i) (by linarith : (0:ℝ) < g j - g i)]
  · exact absurd h hg
  · have hle : f j ≤ f i := hfg hj hi h
    have hlt : f j < f i := lt_of_le_of_ne hle (Ne.symm hf)
    nlinarith [mul_pos (by linarith : (0:ℝ) < f i - f j) (by linarith : (0:ℝ) < g i - g j)]

/-- **Strict Chebyshev's sum inequality.** If `f, g` monovary on `s` and there is a
pair `i, j ∈ s` at which both `f` and `g` take distinct values, then Chebyshev's
inequality is strict. -/
theorem gap_pos (hfg : MonovaryOn f g s) {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (hf : f i ≠ f j) (hg : g i ≠ g j) :
    (∑ i ∈ s, f i) * (∑ i ∈ s, g i) < (s.card : ℝ) * (∑ i ∈ s, f i * g i) := by
  have h1 := half_term_le_gap hfg hi hj
  have h2 := term_pos hfg hi hj hf hg
  linarith

/-- **Strict Chebyshev, existential form.** Monovariance plus the existence of a single
pair on which both functions are non-constant forces strict inequality. -/
theorem gap_pos_of_exists (hfg : MonovaryOn f g s)
    (h : ∃ i ∈ s, ∃ j ∈ s, f i ≠ f j ∧ g i ≠ g j) :
    (∑ i ∈ s, f i) * (∑ i ∈ s, g i) < (s.card : ℝ) * (∑ i ∈ s, f i * g i) := by
  obtain ⟨i, hi, j, hj, hf, hg⟩ := h
  exact gap_pos hfg hi hj hf hg

end RearrangementChebyshevStrict
