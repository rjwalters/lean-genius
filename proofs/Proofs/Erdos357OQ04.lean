/-
  Erdős Problem #357 — OQ-04
  The little-o ⇔ ratio-limit equivalence, generalized (via the Mathlib asymptotic API).

  Context. The parent gallery entry (Proofs/Erdos357Problem.lean) states the main
  Erdős #357 conjecture in two equivalent forms and proves their equivalence in
  `conjecture_equiv`:

      Erdos357Conjecture     :  (fun n ↦ (f n : ℝ)) =o[atTop] (fun n ↦ (n : ℝ))
      Erdos357ConjectureAlt  :  Tendsto (fun n ↦ (f n : ℝ) / n) atTop (𝓝 0)

  That proof is a one-off: it is stated for the specific counting function `f` and
  unfolds `isLittleO_iff_tendsto'` inline with the ad-hoc side condition that the
  denominator `n` is eventually nonzero.

  This file isolates the reusable content behind that argument. The only fact used
  is that `(n : ℝ)` is eventually nonzero along `atTop`, so the vacuous side
  condition of `Asymptotics.isLittleO_iff_tendsto'` is discharged once and for all,
  for an ARBITRARY sequence `u : ℕ → ℝ` (Section 1). We then record two consequences
  that the parent file's own OPEN conjectures need but do not have:

  * an ε–N characterization of `u =o[atTop] id` for nonnegative `u`
    (`littleO_natCast_iff_eventually_le`), which turns the asymptotic statement into
    the concrete "eventually `u n ≤ ε·n`" form that density arguments are phrased in;

  * the resulting dual formulation of the parent's OPEN infinite-set density-zero
    conjecture (`InfiniteDensityZeroConjecture`), giving that conjecture the same
    little-o ⇔ ratio-limit ⇔ ε–N trichotomy that `conjecture_equiv` gave the finite
    function `f` (Section 2).

  Nothing here re-proves `conjecture_equiv`; it generalizes the mechanism and applies
  it to the density side, which the parent left only in ratio-limit form.

  Fully machine-checked: 0 axioms, 0 sorries, no `native_decide`.
-/
import Mathlib

open Filter Asymptotics Topology

namespace Erdos357OQ04

/- ## Section 1: The general equivalence -/

/--
**General little-o ⇔ ratio-limit equivalence.**

For *any* sequence `u : ℕ → ℝ`, comparison against the identity `n` in the
little-o sense is equivalent to the normalized ratio tending to `0`:

  `u =o[atTop] (fun n ↦ (n : ℝ))  ↔  Tendsto (fun n ↦ u n / n) atTop (𝓝 0)`.

This is `Asymptotics.isLittleO_iff_tendsto'` specialized to the identity denominator,
with its side condition discharged by the fact that `(n : ℝ)` is eventually nonzero
along `atTop`. The parent file proves exactly this statement for `u = f`; here it is
stated once for all `u`, so downstream growth/density questions can cite it directly.
-/
theorem littleO_natCast_iff_ratio_tendsto (u : ℕ → ℝ) :
    (u =o[atTop] fun n => (n : ℝ)) ↔
      Tendsto (fun n => u n / n) atTop (𝓝 0) := by
  have h : ∀ᶠ n : ℕ in atTop, (n : ℝ) = 0 → u n = 0 := by
    filter_upwards [eventually_gt_atTop 0] with n hn h0
    rw [Nat.cast_eq_zero] at h0
    omega
  exact isLittleO_iff_tendsto' h

/--
**ε–N characterization of sublinear growth.**

For a *nonnegative* sequence `u`, being little-o of the identity is equivalent to the
concrete ε–N statement: for every `ε > 0`, eventually `u n ≤ ε · n`. This is the form
in which "density tends to `0`" is usually attacked, so it is the practically useful
face of the little-o statement.
-/
theorem littleO_natCast_iff_eventually_le (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) :
    (u =o[atTop] fun n => (n : ℝ)) ↔
      ∀ ε, 0 < ε → ∀ᶠ n in atTop, u n ≤ ε * n := by
  rw [isLittleO_iff]
  refine ⟨fun h ε hε => ?_, fun h c hc => ?_⟩
  · filter_upwards [h hε] with n hn
    rwa [Real.norm_of_nonneg (hu n), Real.norm_of_nonneg (Nat.cast_nonneg n)] at hn
  · filter_upwards [h c hc] with n hn
    rwa [Real.norm_of_nonneg (hu n), Real.norm_of_nonneg (Nat.cast_nonneg n)]

/--
The full trichotomy for a nonnegative sequence: little-o, ratio-limit, and ε–N forms
all coincide. Combines the two lemmas above.
-/
theorem sublinear_tfae (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) :
    (Tendsto (fun n => u n / n) atTop (𝓝 0)) ↔
      ∀ ε, 0 < ε → ∀ᶠ n in atTop, u n ≤ ε * n := by
  rw [← littleO_natCast_iff_ratio_tendsto]
  exact littleO_natCast_iff_eventually_le u hu

/- ## Section 2: Application to the Erdős #357 density conjecture

The parent file states the OPEN "infinite-set density-zero" conjecture only in
ratio-limit form:

    InfiniteDensityZeroConjecture :
      ∀ A, StrictMono A → HasDistinctSums A →
        Tendsto (fun n ↦ #{k | A k ≤ n} / (n : ℝ)) atTop (𝓝 0)

We reconstruct its counting function locally (as `countLE`) and give it the same
little-o ⇔ ratio-limit ⇔ ε–N formulations that `conjecture_equiv` provides for the
finite function `f`. -/

/-- The counting function `#{k | A k ≤ n}` of a sequence `A`, matching the parent
file's density statement. -/
noncomputable def countLE (A : ℕ → ℕ) (n : ℕ) : ℕ := Nat.card {k | A k ≤ n}

/--
**Density-zero ⇔ little-o** for the counting function of any sequence `A`.
The dual of `conjecture_equiv`, on the density side.
-/
theorem density_zero_iff_littleO (A : ℕ → ℕ) :
    Tendsto (fun n => (countLE A n : ℝ) / n) atTop (𝓝 0) ↔
      (fun n => (countLE A n : ℝ)) =o[atTop] fun n => (n : ℝ) :=
  (littleO_natCast_iff_ratio_tendsto _).symm

/--
**Density-zero ⇔ ε–N** for the counting function: the OPEN conjecture that the
density tends to `0` is *exactly* the statement that for every `ε > 0` the count is
eventually below `ε · n`. This is the concrete handle for attacking the density
conjecture.
-/
theorem density_zero_iff_eventually_le (A : ℕ → ℕ) :
    Tendsto (fun n => (countLE A n : ℝ) / n) atTop (𝓝 0) ↔
      ∀ ε, 0 < ε → ∀ᶠ n in atTop, (countLE A n : ℝ) ≤ ε * n :=
  sublinear_tfae _ (fun n => Nat.cast_nonneg _)

end Erdos357OQ04
