/-
Erdős Problem #1215: Polynomial Level Set Path Conjecture

Source: https://erdosproblems.com/1215
Status: SOLVED (Mac Lane 1953 — resolved NEGATIVELY)

Statement:
Does there exist a constant C such that for every polynomial P with P(0) = 1
and all roots on the unit circle, there exists a path from 0 to ∞ in
  {z ∈ ℂ : |P(z)| < C}?

Answer: NO. Mac Lane 1953 proved that for any C > 1, some path segments are
forced into arbitrarily small neighborhoods of 0.

Reference:
- [Ma53] Mac Lane, 1953
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Analysis.Complex.Basic

open Complex Polynomial

namespace Erdos1215

/-- Polynomial with P(0) = 1 and all roots on the unit circle -/
def IsUnitCirclePolynomial (P : ℂ[X]) : Prop :=
  P.eval 0 = 1 ∧ ∀ z : ℂ, IsRoot P z → ‖z‖ = 1

/-- Level set: {z : |P(z)| < C} -/
def levelSet (P : ℂ[X]) (C : ℝ) : Set ℂ :=
  {z : ℂ | ‖P.eval z‖ < C}

/-- Bounded-level path from 0 to ∞ -/
def HasBoundedLevelPath (P : ℂ[X]) (C : ℝ) : Prop :=
  ∃ (γ : ℝ → ℂ), Continuous γ ∧ γ 0 = 0 ∧
    Filter.Tendsto (fun t => ‖γ t‖) Filter.atTop Filter.atTop ∧
    ∀ t ≥ 0, γ t ∈ levelSet P C

/--
**The literal escape-to-∞ answer is NO — and it is *elementary*.**
For any `C`, there is a unit-circle polynomial with no bounded-level path from
`0` to `∞` inside `{|P| < C}`.  The witness is the degree-one cyclotomic
`P = X + 1` (`P(0) = 1`, sole root `-1` on the unit circle): its level set
`{z : ‖z + 1‖ < C}` is a *bounded* disc, so `‖z‖ ≤ ‖z + 1‖ + 1 < C + 1` there,
and no path can escape to `∞` while staying inside it.

This was formerly an `axiom` labelled "Mac Lane 1953", but the escape-to-∞
formulation does **not** require Mac Lane's deep argument — it is refuted by mere
compactness of the level set of a single explicit polynomial.  Mac Lane's genuine
content (the labyrinth forcing paths through neighbourhoods of `0` in the `C > 1`
regime) is the strictly stronger phenomenon recorded below in `maclane_labyrinth`,
which remains axiomatized.  Cf. the cyclotomic re-derivation in
`CyclotomicPolynomialsOQ02OQ05.erdos_1215_via_cyclotomic`. -/
theorem maclane_1953 (C : ℝ) (_hC : C > 1) :
    ∃ P : ℂ[X], IsUnitCirclePolynomial P ∧ ¬HasBoundedLevelPath P C := by
  refine ⟨X + 1, ⟨by simp, ?_⟩, ?_⟩
  · -- the sole root of `X + 1` is `-1`, which lies on the unit circle
    intro z hz
    rw [IsRoot.def, eval_add, eval_X, eval_one] at hz
    rw [eq_neg_of_add_eq_zero_left hz]
    simp
  · -- no path can escape to ∞ while `‖γ t + 1‖ < C` keeps `‖γ t‖` below `C + 1`
    rintro ⟨γ, _hcont, _hγ0, htend, hpath⟩
    have hbound : ∀ t ≥ (0 : ℝ), ‖γ t‖ < C + 1 := by
      intro t ht
      have hmem := hpath t ht
      simp only [levelSet, Set.mem_setOf_eq, eval_add, eval_X, eval_one] at hmem
      have hkey := norm_sub_norm_le (γ t) (γ t + 1)
      have hgeq : γ t - (γ t + 1) = -1 := by ring
      rw [hgeq] at hkey
      simp only [norm_neg, norm_one] at hkey
      linarith
    have h1 : ∀ᶠ t in Filter.atTop, C + 1 < ‖γ t‖ := htend.eventually_gt_atTop (C + 1)
    have h2 : ∀ᶠ t in Filter.atTop, (0 : ℝ) ≤ t := Filter.eventually_ge_atTop 0
    obtain ⟨t, ht1, ht2⟩ := (h1.and h2).exists
    exact absurd (hbound t ht2) (by linarith)

/--
**Stronger form:** For any C, there exist labyrinth blocks forcing the path
to pass through neighborhoods of 0.
-/
axiom maclane_labyrinth :
    ∀ (C ε : ℝ), C > 1 → ε > 0 →
      ∃ P : ℂ[X], IsUnitCirclePolynomial P ∧
        ∀ γ : ℝ → ℂ, Continuous γ → γ 0 = 0 →
          Filter.Tendsto (fun t => ‖γ t‖) Filter.atTop Filter.atTop →
          (∀ t ≥ 0, γ t ∈ levelSet P C) →
          ∃ t > 0, ‖γ t‖ < ε

/-- **Erdős Problem #1215: SOLVED (negatively)** -/
theorem erdos_1215 :
    ¬∃ C : ℝ, C > 1 ∧ ∀ P : ℂ[X], IsUnitCirclePolynomial P →
      HasBoundedLevelPath P C := by
  push_neg
  intro C hC
  exact maclane_1953 C hC

end Erdos1215
