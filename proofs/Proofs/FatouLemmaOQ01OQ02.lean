import Proofs.FatouLemma
import Mathlib.Tactic

/-
# Fatou's Lemma (OQ-01-OQ-02): The Escaping Mass Has No Integrable Majorant

## Open Question (from fatou-lemma-oq-01)

The parent entry exhibits the **escaping-mass sequence**
`escaping n = 𝟙_[n,n+1)` (a unit bump marching off to `+∞`) as a witness to the
strict inequality in Fatou's lemma: `∫⁻ liminfₙ escaping n = 0 < 1 = liminfₙ ∫⁻ escaping n`.

A natural follow-up — and the *obstruction* half referenced by the child entry
`fatou-lemma-oq-01-oq-02-oq-01` (the elementary Fatou ⇒ Dominated Convergence
derivation): **why can't the Dominated Convergence Theorem rescue the escaping
mass?** DCT requires a single integrable majorant `g` with `escaping n ≤ g` for
all `n`. This file proves no such `g` exists.

## Result

`escaping_no_integrable_majorant`: if `g : ℝ → ℝ≥0∞` dominates every bump
pointwise (`∀ n, escaping n ≤ g`), then `∫⁻ g = ∞`.

The mechanism is transparent: the bumps `[n, n+1)` for `n = 0, 1, 2, …` tile the
ray `[0, ∞)`, so any common majorant is `≥ 1` on all of `[0, ∞)`, a set of
infinite Lebesgue measure. Hence DCT's integrability hypothesis fails for the
escaping sequence — pinpointing exactly which hypothesis breaks where Fatou's
inequality is strict.

Fully verified: 0 sorries, 0 `axiom` declarations, no `native_decide`. Built on
the parent's `escaping` definition and Mathlib's Lebesgue-integral API.
-/

open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace FatouLemma

/-- Any function `g` dominating every bump `escaping n = 𝟙_[n,n+1)` is at least
`1` on the whole ray `[0, ∞)`: for `x ≥ 0`, the bump indexed by `n = ⌊x⌋₊`
covers `x` (since `⌊x⌋₊ ≤ x < ⌊x⌋₊ + 1`), so `1 = escaping ⌊x⌋₊ x ≤ g x`. -/
theorem one_le_of_majorizes_escaping
    {g : ℝ → ℝ≥0∞} (hg : ∀ n : ℕ, escaping n ≤ g) {x : ℝ} (hx : 0 ≤ x) :
    1 ≤ g x := by
  set n := ⌊x⌋₊ with hn
  have hmem : x ∈ Set.Ico (n : ℝ) (n + 1) :=
    ⟨Nat.floor_le hx, Nat.lt_floor_add_one x⟩
  have hesc : escaping n x = 1 := by
    rw [escaping, Set.indicator_of_mem hmem]; rfl
  calc (1 : ℝ≥0∞) = escaping n x := hesc.symm
    _ ≤ g x := hg n x

/-- **`fatou-lemma-oq-01-oq-02`: the escaping-mass sequence has no integrable
majorant.** If `g : ℝ → ℝ≥0∞` dominates every bump `escaping n = 𝟙_[n,n+1)`
pointwise, then `∫⁻ g = ∞`. This is the obstruction explaining why the
Dominated Convergence Theorem cannot apply to the escaping mass: any common
majorant is `≥ 1` on all of `[0, ∞)`, whose Lebesgue measure is infinite. -/
theorem escaping_no_integrable_majorant
    {g : ℝ → ℝ≥0∞} (hg : ∀ n : ℕ, escaping n ≤ g) :
    ∫⁻ x, g x = ∞ := by
  -- `g` dominates the indicator of `[0, ∞)`.
  have hle : (Set.Ici (0 : ℝ)).indicator 1 ≤ g := by
    intro x
    by_cases hx : x ∈ Set.Ici (0 : ℝ)
    · rw [Set.indicator_of_mem hx]
      exact one_le_of_majorizes_escaping hg hx
    · rw [Set.indicator_of_notMem hx]; exact zero_le _
  have hmono : ∫⁻ x, (Set.Ici (0 : ℝ)).indicator 1 x ≤ ∫⁻ x, g x :=
    lintegral_mono hle
  rwa [lintegral_indicator_one measurableSet_Ici, Real.volume_Ici, top_le_iff] at hmono

end FatouLemma
