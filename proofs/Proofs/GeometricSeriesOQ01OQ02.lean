import Mathlib
import Proofs.GeometricSeriesOQ01

/-
# Cesàro (C,1) Regularity: convergent ⟹ Cesàro-summable to the same sum

## What This Proves
The general **regularity** (a.k.a. consistency) theorem of (C,1) summation,
the open question OQ-02 of the chain rooted at `geometric-series-oq-01`:

> If a series `∑ aₙ` converges to `s`, then its Cesàro mean converges to `s`.

Concretely, with partial sums `Sₖ = a₀ + ⋯ + a_{k-1}` and Cesàro means
`σₙ = (S₁ + ⋯ + Sₙ)/n`:

1. **Regularity (the OQ)**: `Sₙ → s  ⟹  σₙ → s`.
2. **Series-level corollary**: `HasSum a s  ⟹  CesaroSummable a s`.
3. **Strictness**: Grandi's series `1 − 1 + 1 − ⋯` is Cesàro summable to `1/2`
   yet *not* summable — so (C,1) summation is a *strict* extension of ordinary
   convergence (the converse of regularity fails).

## Relationship to the parent entry
`geometric-series-oq-01` proves the *concrete* Grandi instance by hand
(`grandiCesaro_tendsto`, via an explicit `|σₙ − 1/2| ≤ 1/(2n)` bound). This
entry proves the **general** regularity theorem (which subsumes such bespoke
computations) and reuses the parent's bound to populate the strictness example.

## Approach
- **Foundation (from Mathlib):** `Filter.Tendsto.cesaro` — the Cesàro mean of a
  convergent sequence converges to the same limit. The key observation is that
  the correct sequence to average is the *partial-sum* sequence, not the terms.
- **Original contribution:** packaging regularity at the series level, the
  `HasSum` corollary, and the strict-extension witness via Grandi.
-/

namespace GeometricSeriesOQ01OQ02

open Finset Filter Topology

/-- Partial sums of a series: `partialSum a k = a₀ + a₁ + ⋯ + a_{k-1}`. -/
def partialSum (a : ℕ → ℝ) (k : ℕ) : ℝ := ∑ i ∈ Finset.range k, a i

/-- The (C,1) / Cesàro mean of a series: the average of its first `n` *nonempty*
    partial sums, `σₙ = (S₁ + S₂ + ⋯ + Sₙ) / n`. -/
def cesaroMean (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, partialSum a (k + 1)

/-- A series is **Cesàro `(C,1)`-summable to `σ`** when its sequence of Cesàro
    means converges to `σ`. -/
def CesaroSummable (a : ℕ → ℝ) (σ : ℝ) : Prop :=
  Tendsto (cesaroMean a) atTop (𝓝 σ)

-- ============================================================
-- PART 1: Regularity (the open question)
-- ============================================================

/-- **(C,1) regularity.** If the partial sums of `∑ aₙ` converge to `s`, then the
    Cesàro means converge to the *same* `s`.

    This is a corollary of Mathlib's `Filter.Tendsto.cesaro` applied to the
    (shifted) partial-sum sequence `k ↦ S_{k+1}`. -/
theorem cesaro_regularity {a : ℕ → ℝ} {s : ℝ}
    (h : Tendsto (partialSum a) atTop (𝓝 s)) : CesaroSummable a s := by
  have h1 : Tendsto (fun k => partialSum a (k + 1)) atTop (𝓝 s) :=
    h.comp (tendsto_add_atTop_nat 1)
  exact h1.cesaro

/-- **Regularity at the level of the series sum.** If `∑ aₙ` actually sums to `s`
    (`HasSum a s`), then it is Cesàro summable to `s`. -/
theorem cesaroSummable_of_hasSum {a : ℕ → ℝ} {s : ℝ} (h : HasSum a s) :
    CesaroSummable a s :=
  cesaro_regularity h.tendsto_sum_nat

/-- A `Summable` real series is Cesàro summable (to its ordinary sum). -/
theorem cesaroSummable_of_summable {a : ℕ → ℝ} (h : Summable a) :
    CesaroSummable a (∑' n, a n) :=
  cesaroSummable_of_hasSum h.hasSum

-- ============================================================
-- PART 2: Strictness — (C,1) strictly extends convergence
-- ============================================================

/-- The Cesàro mean of Grandi's series `(-1)ⁿ` coincides, as a function of `n`,
    with the parent entry's bespoke `grandiCesaro`. -/
theorem cesaroMean_grandi_eq :
    cesaroMean (fun n => (-1 : ℝ) ^ n) = GeometricSeriesOQ01.grandiCesaro := by
  funext n
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [cesaroMean, GeometricSeriesOQ01.grandiCesaro]
  · simp only [cesaroMean, partialSum, GeometricSeriesOQ01.grandiCesaro,
      if_neg hn.ne']
    rw [div_eq_inv_mul]

/-- **Grandi's series is Cesàro summable to `1/2`.** Reuses the parent entry's
    explicit limit computation through `cesaroMean_grandi_eq`. -/
theorem grandi_cesaroSummable : CesaroSummable (fun n => (-1 : ℝ) ^ n) (1 / 2) := by
  unfold CesaroSummable
  rw [cesaroMean_grandi_eq]
  exact GeometricSeriesOQ01.grandiCesaro_tendsto

/-- Grandi's series is not summable (the ordinary sum does not exist). -/
theorem grandi_not_summable : ¬ Summable (fun n : ℕ => (-1 : ℝ) ^ n) :=
  GeometricSeriesOQ01.not_summable_grandi

/-- **(C,1) summation strictly extends ordinary convergence.** Grandi's series is
    Cesàro summable to `1/2` yet not summable, so the converse of regularity
    fails: Cesàro summability does *not* imply convergence. -/
theorem cesaro_strictly_extends_convergence :
    CesaroSummable (fun n => (-1 : ℝ) ^ n) (1 / 2) ∧
      ¬ Summable (fun n : ℕ => (-1 : ℝ) ^ n) :=
  ⟨grandi_cesaroSummable, grandi_not_summable⟩

-- ============================================================
-- PART 3: Examples
-- ============================================================

/-- A convergent series (here the constant-zero series) is Cesàro summable. -/
example : CesaroSummable (fun _ : ℕ => (0 : ℝ)) 0 :=
  cesaroSummable_of_hasSum hasSum_zero

#check @cesaro_regularity
#check @cesaroSummable_of_hasSum
#check @grandi_cesaroSummable
#check @cesaro_strictly_extends_convergence

end GeometricSeriesOQ01OQ02
