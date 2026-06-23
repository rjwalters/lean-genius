/-
# Glivenko–Cantelli Bracketing: `bracketingGrid_exists` is FALSE
(laws-of-large-numbers-oq-04-oq-03 — Session S10, 2026-05-29)

## Summary of the finding

The companion file `LawsOfLargeNumbersOQ04OQ03Bracketing.lean` reduces the uniform
Glivenko–Cantelli theorem to a *single* axiom, `bracketingGrid_exists`, which the
gallery and prior sessions describe as a "true-but-unproved, purely real-analytic
lemma" whose natural Mathlib home is `Monotone.exists_increasing_continuity_seq`.
Nine sessions of planning (S8–S9b roadmaps, S10 "greedy ε-cover" target) treated
discharging this axiom as the remaining work.

**This file proves that `bracketingGrid_exists` is FALSE.** It is not a hard lemma
awaiting a clever proof; its statement is refutable. Consequently the greedy
ε-cover target is unreachable, and the downstream `glivenko_cantelli_uniform`
(proved in the companion) is derived from a false premise — adding the axiom in
fact makes the `GlivenkoCantelli` namespace inconsistent.

## Why the axiom is false

A `BracketingGrid F ε` (companion §2.1) requires a strictly increasing finite
node sequence `q₀ < ⋯ < q_{k+1}` with

  * `left_le`  : `F (q₀) ≤ ε`
  * `right_ge` : `F (q_{k+1}) ≥ 1 − ε`
  * `step_le`  : `F (qⱼ₊₁) − F (qⱼ) ≤ ε`  for every adjacent pair.

There is **no atomless / continuity hypothesis on the underlying distribution**.
But `step_le` is unsatisfiable whenever the CDF has an atom of mass `> ε`: any two
points straddling the atom differ in `F`-value by at least the atom's mass, so no
chain of `≤ ε` steps can climb from `≤ ε` to `≥ 1 − ε` across it.

The cleanest witness is a single Dirac point mass `δ₀`. Its CDF is the step
function `1_{x ≥ 0}`, taking only the values `{0, 1}` with a jump of size `1`. For
`ε = 1/4 < 1/2`, every adjacent `step_le` forces `F (qⱼ₊₁) = F (qⱼ)` (the only
`F`-gap that is `≤ 1/4` is `0`), so `F` is constant along the grid — contradicting
`F (q₀) ≤ 1/4` together with `F (q_{k+1}) ≥ 3/4`.

## Structure of this file

  * §A — `bracketingGrid_value_impossible`: an abstract, probability-free
    obstruction. Any monotone `F` whose values lie in `{0, 1/2, 1}` admits no
    `BracketingGrid F ε` with `ε < 1/2`. (The set `{0, 1/2, 1}` covers both the
    two-point and the single-Dirac witnesses; its minimal positive gap is `1/2`.)
  * §B — `bracketingGrid_exists_false`: instantiates §A at the Dirac CDF, using
    `bracketingGrid_exists` itself to manufacture a grid and then refuting it,
    deriving `False`. This is a machine-checkable proof that the axiom is
    inconsistent with Mathlib.

The existing verified chain (the two integration lemmas in
`LawsOfLargeNumbersOQ04OQ03.lean`) is untouched and remains sound; only the
bracketing axiom and the uniform-convergence theorem built on it are affected.

The correct fix is to redesign `BracketingGrid` to track *left limits*
`F (qⱼ⁻)` at the nodes (the standard quantile construction), so that atoms are
placed at their own cells and bounded via both one-sided values. That redesign is
out of scope for this disproof; see the session knowledge note.
-/

import Proofs.LawsOfLargeNumbersOQ04OQ03Bracketing

namespace GlivenkoCantelli

open MeasureTheory ProbabilityTheory Set

-- ============================================================================
-- §A: Abstract structural obstruction (no probability)
-- ============================================================================

/-- Adjacent grid `F`-values coincide. Because the value set `{0, 1/2, 1}` has
    minimal positive gap `1/2`, a step bound `ε < 1/2` plus monotonicity forces
    each consecutive pair of grid nodes to share the same `F`-value. -/
theorem bracketingGrid_adjacent_eq
    {F : ℝ → ℝ} (hmono : Monotone F) {ε : ℝ} (hε : ε < 1 / 2)
    {G : BracketingGrid F ε}
    (hval : ∀ j : Fin (G.k + 2), F (G.q j) = 0 ∨ F (G.q j) = 1 / 2 ∨ F (G.q j) = 1)
    (j : Fin (G.k + 1)) :
    F (G.q j.succ) = F (G.q j.castSucc) := by
  have hstep := G.step_le j
  have hlt : G.q j.castSucc < G.q j.succ := G.mono Fin.castSucc_lt_succ
  have hle : F (G.q j.castSucc) ≤ F (G.q j.succ) := hmono hlt.le
  refine le_antisymm ?_ hle
  rcases hval j.succ with h1 | h1 | h1 <;> rcases hval j.castSucc with h2 | h2 | h2 <;>
    rw [h1, h2] at hstep hle ⊢ <;> linarith

/-- The grid `F`-value is constant, equal to `F (q₀)` at every node. -/
theorem bracketingGrid_const
    {F : ℝ → ℝ} (hmono : Monotone F) {ε : ℝ} (hε : ε < 1 / 2)
    {G : BracketingGrid F ε}
    (hval : ∀ j : Fin (G.k + 2), F (G.q j) = 0 ∨ F (G.q j) = 1 / 2 ∨ F (G.q j) = 1)
    (i : Fin (G.k + 2)) :
    F (G.q i) = F (G.q 0) := by
  refine Fin.induction ?_ ?_ i
  · rfl
  · intro i ih
    rw [bracketingGrid_adjacent_eq hmono hε hval i]
    exact ih

/-- **Abstract obstruction.** No `BracketingGrid F ε` exists when `F` is monotone,
    its values lie in `{0, 1/2, 1}`, and `ε < 1/2`. The boundary requirements
    `F (q₀) ≤ ε < 1/2` and `F (q_last) ≥ 1 − ε > 1/2` are incompatible once the
    grid `F`-value is forced to be constant. -/
theorem bracketingGrid_value_impossible
    {F : ℝ → ℝ} (hmono : Monotone F) {ε : ℝ} (hε : ε < 1 / 2)
    (hval : ∀ x : ℝ, F x = 0 ∨ F x = 1 / 2 ∨ F x = 1)
    (G : BracketingGrid F ε) : False := by
  have hconst : F (G.q (Fin.last (G.k + 1))) = F (G.q 0) :=
    bracketingGrid_const hmono hε (G := G) (fun j => hval (G.q j)) (Fin.last (G.k + 1))
  have hleft : F (G.q 0) ≤ ε := G.left_le
  have hright : F (G.q (Fin.last (G.k + 1))) ≥ 1 - ε := G.right_ge
  rw [hconst] at hright
  linarith

-- ============================================================================
-- §B: Realization as a CDF — the axiom is therefore false
-- ============================================================================

/-- The CDF of a single Dirac mass at `0` (with `Xᵢ = projection`) is the step
    function `1_{x ≥ 0}`. -/
theorem trueCDF_dirac_zero (x : ℝ) :
    trueCDF (fun _ (ω : ℝ) => ω) (Measure.dirac (0 : ℝ)) x
      = if (0 : ℝ) ≤ x then (1 : ℝ) else 0 := by
  have hdef : trueCDF (fun _ (ω : ℝ) => ω) (Measure.dirac (0 : ℝ)) x
      = ((Measure.dirac (0 : ℝ)) (Set.Iic x)).toReal := rfl
  rw [hdef, Measure.dirac_apply' (0 : ℝ) measurableSet_Iic]
  by_cases h : (0 : ℝ) ≤ x
  · rw [Set.indicator_of_mem (Set.mem_Iic.mpr h), Pi.one_apply, ENNReal.toReal_one,
        if_pos h]
  · rw [Set.indicator_of_notMem (by simpa [Set.mem_Iic] using h), ENNReal.toReal_zero,
        if_neg h]

/-- **`bracketingGrid_exists` is false.** Instantiating the axiom at the Dirac CDF
    produces a `BracketingGrid` whose existence §A refutes, yielding `False`. The
    axiom is thus inconsistent with Mathlib, and any theorem (notably
    `glivenko_cantelli_uniform`) depending on it is vacuously derived. -/
theorem bracketingGrid_exists_false : False := by
  have hmeas : ∀ i, Measurable ((fun (_ : ℕ) (ω : ℝ) => ω) i) := fun _ => measurable_id
  have h14 : (0 : ℝ) < 1 / 4 := by norm_num
  obtain ⟨G⟩ := bracketingGrid_exists
    (Ω := ℝ) (μ := Measure.dirac (0 : ℝ)) (X := fun _ (ω : ℝ) => ω) hmeas h14
  refine bracketingGrid_value_impossible
    (trueCDF_monotone (μ := Measure.dirac (0 : ℝ)) (fun _ (ω : ℝ) => ω))
    (by norm_num : (1 : ℝ) / 4 < 1 / 2) (fun x => ?_) G
  rw [trueCDF_dirac_zero x]
  by_cases h : (0 : ℝ) ≤ x
  · exact Or.inr (Or.inr (if_pos h))
  · exact Or.inl (if_neg h)

end GlivenkoCantelli
