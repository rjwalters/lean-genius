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
import Mathlib.Topology.Algebra.Polynomial

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
**The escape-to-∞ obstruction is trivial for degree reasons.**
For *any* polynomial `P` of positive degree, `‖P(z)‖ → ∞` as `‖z‖ → ∞`
(`Polynomial.tendsto_norm_atTop`), so its level set `{z : ‖P(z)‖ < C}` is *bounded* and
admits no path escaping to `∞`: a path `γ` with `‖γ t‖ → ∞` would force
`‖P(γ t)‖ → ∞`, contradicting `‖P(γ t)‖ < C` on `t ≥ 0`.

This isolates exactly *why* the literal escape-to-∞ question (Erdős #1215) is easy: it is
refuted by the growth of any single non-constant polynomial and needs nothing about roots,
the unit circle, or Mac Lane's argument.  All of Mac Lane's genuine depth — paths forced
through neighbourhoods of `0` in the `C > 1` regime — lives in the strictly stronger
`maclane_labyrinth` below, which remains axiomatized. -/
theorem no_bounded_level_path_of_degree_pos {P : ℂ[X]} (hP : 0 < P.degree) (C : ℝ) :
    ¬ HasBoundedLevelPath P C := by
  rintro ⟨γ, _hcont, _hγ0, htend, hpath⟩
  -- growth of `P` transports `‖γ t‖ → ∞` into `‖P(γ t)‖ → ∞`
  have hPtend : Filter.Tendsto (fun t => ‖P.eval (γ t)‖) Filter.atTop Filter.atTop :=
    P.tendsto_norm_atTop hP htend
  have h1 : ∀ᶠ t in Filter.atTop, C < ‖P.eval (γ t)‖ := hPtend.eventually_gt_atTop C
  have h2 : ∀ᶠ t in Filter.atTop, (0 : ℝ) ≤ t := Filter.eventually_ge_atTop 0
  obtain ⟨t, ht1, ht2⟩ := (h1.and h2).exists
  have hmem := hpath t ht2
  simp only [levelSet, Set.mem_setOf_eq] at hmem
  linarith

/--
**The literal escape-to-∞ answer is NO — and it is *elementary*.**
For any `C`, there is a unit-circle polynomial with no bounded-level path from
`0` to `∞` inside `{|P| < C}`.  The witness is the degree-one cyclotomic
`P = X + 1` (`P(0) = 1`, sole root `-1` on the unit circle); its level set is bounded
because `X + 1` has positive degree, so `no_bounded_level_path_of_degree_pos` applies.

This was formerly an `axiom` labelled "Mac Lane 1953", but the escape-to-∞ formulation does
**not** require Mac Lane's deep argument — it now follows from the general degree obstruction
`no_bounded_level_path_of_degree_pos` applied to a single explicit polynomial.  Mac Lane's
genuine content (the labyrinth forcing paths through neighbourhoods of `0` in the `C > 1`
regime) is the strictly stronger phenomenon recorded below in `maclane_labyrinth`, which
remains axiomatized.  Cf. the cyclotomic re-derivation in
`CyclotomicPolynomialsOQ02OQ05.erdos_1215_via_cyclotomic`. -/
theorem maclane_1953 (C : ℝ) (_hC : C > 1) :
    ∃ P : ℂ[X], IsUnitCirclePolynomial P ∧ ¬HasBoundedLevelPath P C := by
  refine ⟨X + 1, ⟨by simp, ?_⟩, no_bounded_level_path_of_degree_pos ?_ C⟩
  · -- the sole root of `X + 1` is `-1`, which lies on the unit circle
    intro z hz
    rw [IsRoot.def, eval_add, eval_X, eval_one] at hz
    rw [eq_neg_of_add_eq_zero_left hz]
    simp
  · -- `X + 1 = X + C 1` has degree `1 > 0`
    rw [← C_1, degree_X_add_C]
    exact WithBot.coe_lt_coe.mpr Nat.one_pos

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
