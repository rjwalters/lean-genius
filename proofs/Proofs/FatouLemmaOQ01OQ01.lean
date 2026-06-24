import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Tactic

/-
# Reverse Fatou and the Strictness of the Limsup Inequality

## What This Proves

The parent entry (`fatou-lemma-oq-01`) records the *forward* Fatou inequality
`∫⁻ liminfₙ fₙ ≤ liminfₙ ∫⁻ fₙ` together with the escaping-mass witness proving
that it is strict. This entry supplies the **opposite bracket**: the *reverse*
Fatou inequality and its own strict witness, completing the liminf/limsup pair
that sandwiches the dominated convergence theorem
```
  ∫⁻ liminfₙ fₙ ≤ liminfₙ ∫⁻ fₙ ≤ limsupₙ ∫⁻ fₙ ≤ ∫⁻ limsupₙ fₙ,
```
where the outer two inequalities are the two Fatou lemmas. Equality of the inner
two (i.e. convergence of `∫⁻ fₙ`) is exactly what the dominated convergence
theorem delivers when the bracket collapses.

**Reverse Fatou.** If `fₙ ≤ g` almost everywhere with `g` integrable
(`∫⁻ g ≠ ∞`), then
```
  limsupₙ ∫⁻ fₙ ≤ ∫⁻ limsupₙ fₙ.
```
The integrable majorant is *essential* — without it the inequality can fail
(this is the dual of how the escaping mass evades the forward bound). We restate
Mathlib's `MeasureTheory.limsup_lintegral_le` as the headline
`reverse_fatou_lintegral`.

The mathematical substance is the **alternating two-point witness** proving that
reverse Fatou is *genuinely strict* even in the presence of the integrable
majorant:

* `alt n` is an indicator on the two-point space `Fin 2` with counting measure
  that flips which point is lit on each step: point `0` is lit on even steps,
  point `1` on odd steps. It is dominated by the integrable constant `1`.

* `alt_lintegral` — *exactly one* point is lit at every step, so each integral is
  `∫⁻ alt n = 1`; hence `limsupₙ ∫⁻ alt n = 1`.

* `limsup_alt` — *each* point is lit infinitely often, so the pointwise limsup is
  `1` at both points; hence `∫⁻ limsupₙ alt n = 2`.

* `reverse_fatou_strict_on_alt` — the strict gap:
  `limsupₙ ∫⁻ alt n = 1 < 2 = ∫⁻ limsupₙ alt n`.

The mass that the forward witness loses *to infinity*, the reverse witness loses
*to oscillation*: it never settles, so the limsup of the integrals (which only
sees one lit point at a time) undershoots the integral of the limsup (which sees
both points lit). This is the dual obstruction explaining why reverse Fatou, like
forward Fatou, is only an inequality.

## Why It Is Not in Mathlib

Mathlib records the inequality `limsup_lintegral_le` but no witness that it is
strict. The alternating two-point sequence, the one-lit-point integral
computation, the both-points-lit limsup computation, and the strict-gap
conclusion are the new content, dual to the parent's escaping-mass witness for
forward Fatou.

## Axiom Status

Fully verified, 0 sorries, 0 `axiom` declarations, no `native_decide`. Relies
only on Mathlib's measure theory and the foundational axioms `propext`,
`Classical.choice`, `Quot.sound`.
-/

open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace FatouLemmaOQ01OQ01

/-! ## Reverse Fatou (Mathlib restatement) -/

/-- **Reverse Fatou's lemma.** For measurable nonnegative functions
`fₙ : α → ℝ≥0∞` dominated almost everywhere by an integrable majorant `g`
(`∫⁻ g ≠ ∞`), the limsup of the integrals is at most the integral of the
pointwise limsup. This is `MeasureTheory.limsup_lintegral_le`, restated as the
headline form. It is the upper bracket dual to forward Fatou's lower bracket. -/
theorem reverse_fatou_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ≥0∞} (g : α → ℝ≥0∞) (hf : ∀ n, Measurable (f n))
    (h_bound : ∀ n, f n ≤ᵐ[μ] g) (h_fin : ∫⁻ a, g a ∂μ ≠ ∞) :
    limsup (fun n => ∫⁻ a, f n a ∂μ) atTop ≤ ∫⁻ a, limsup (fun n => f n a) atTop ∂μ :=
  limsup_lintegral_le g hf h_bound h_fin

/-! ## The alternating two-point sequence on `(Fin 2, count)` -/

/-- The alternating indicator on the two-point space: at step `n`, the point `i`
is lit (value `1`) exactly when `n + i` is even, and dark (value `0`) otherwise.
So point `0` is lit on even steps and point `1` on odd steps — the two points
flash in alternation, with exactly one lit at any time. -/
def alt (n : ℕ) (i : Fin 2) : ℝ≥0∞ := if Even (n + (i : ℕ)) then 1 else 0

/-- Each `alt n` is measurable (the two-point space carries the discrete
σ-algebra, so every function out of it is measurable). -/
theorem alt_measurable (n : ℕ) : Measurable (alt n) := Measurable.of_discrete

/-- Each `alt n` is bounded above by the constant `1`. -/
theorem alt_le_one (n : ℕ) (i : Fin 2) : alt n i ≤ 1 := by
  unfold alt; split <;> simp

/-- **One lit point per step.** At every step exactly one of the two points is
lit, so the counting-measure integral is `∫⁻ alt n = 1`. This is the conserved
unit mass that the oscillation will hide from the limsup. -/
theorem alt_lintegral (n : ℕ) :
    ∫⁻ i, alt n i ∂(Measure.count : Measure (Fin 2)) = 1 := by
  rw [lintegral_fintype, Fin.sum_univ_two, Measure.count_singleton, Measure.count_singleton,
    mul_one, mul_one]
  rcases Nat.even_or_odd n with he | ho
  · -- `n` even: point `0` lit, point `1` dark
    have h1 : ¬ Even (n + 1) := by rw [Nat.even_add_one]; exact not_not.mpr he
    simp [alt, he, h1]
  · -- `n` odd: point `0` dark, point `1` lit
    have h0 : ¬ Even n := by simpa using ho
    simp [alt, h0, ho.add_one]

/-- For any constant `c`, the predicate `Even (n + c)` holds for arbitrarily
large `n`: this drives the "each point lit infinitely often" computation. -/
theorem frequently_even_add (c : ℕ) : ∃ᶠ n in atTop, Even (n + c) := by
  rw [frequently_atTop]
  intro a
  exact ⟨2 * a + c, by omega, ⟨a + c, by omega⟩⟩

/-- **Each point lit infinitely often.** The pointwise limsup of `n ↦ alt n i`
is `1` at *both* points: each point is lit on infinitely many steps (giving the
lower bound `1`) and never exceeds `1` (giving the upper bound). This is the dual
of the forward witness's "eventually `0`" computation: here the sequence never
settles. -/
theorem limsup_alt (i : Fin 2) : limsup (fun n => alt n i) atTop = 1 := by
  refine le_antisymm ?_ ?_
  · -- upper bound: every term is `≤ 1`
    exact limsup_le_of_le (h := Eventually.of_forall fun n => alt_le_one n i)
  · -- lower bound: the value `1` is attained infinitely often
    refine le_limsup_of_frequently_le ?_
    refine (frequently_even_add (i : ℕ)).mono fun n hn => ?_
    simp [alt, hn]

/-! ## The headline result: reverse Fatou is strict -/

/-- **Reverse Fatou's inequality is genuinely strict.** On the alternating
two-point example,
```
  limsupₙ ∫⁻ alt n = 1  <  2 = ∫⁻ limsupₙ alt n,
```
even though the sequence is dominated by the integrable constant `1`
(`∫⁻ 1 ∂count = 2 < ∞` on the two-point space). Each integral sees only the
single lit point (left side `= 1`), but the pointwise limsup lights *both* points
(right side `= 2`), because each point is lit infinitely often. This is the
witness — absent from Mathlib — that reverse Fatou cannot be upgraded to an
equality: an integrable majorant rules out escape to infinity but not loss to
oscillation. -/
theorem reverse_fatou_strict_on_alt :
    limsup (fun n => ∫⁻ i, alt n i ∂(Measure.count : Measure (Fin 2))) atTop
      < ∫⁻ i, limsup (fun n => alt n i) atTop ∂(Measure.count : Measure (Fin 2)) := by
  have hL : limsup (fun n => ∫⁻ i, alt n i ∂(Measure.count : Measure (Fin 2))) atTop = 1 := by
    simp only [alt_lintegral, limsup_const]
  have hR : ∫⁻ i, limsup (fun n => alt n i) atTop ∂(Measure.count : Measure (Fin 2)) = 2 := by
    rw [lintegral_congr limsup_alt, lintegral_fintype, Fin.sum_univ_two,
      Measure.count_singleton, Measure.count_singleton]
    simp only [mul_one]
    exact one_add_one_eq_two
  rw [hL, hR]
  exact ENNReal.one_lt_two

/-- The witness genuinely satisfies the hypotheses of `reverse_fatou_lintegral`:
each `alt n` is dominated everywhere by the integrable constant majorant `1`,
with `∫⁻ 1 ∂count = 2 ≠ ∞` on the two-point space. Together with
`reverse_fatou_strict_on_alt` this shows the inequality is strict *within* the
hypotheses, not by violating them. -/
theorem alt_dominated_by_integrable :
    (∀ n, alt n ≤ᵐ[(Measure.count : Measure (Fin 2))] (fun _ => (1 : ℝ≥0∞))) ∧
      ∫⁻ _i : Fin 2, (1 : ℝ≥0∞) ∂(Measure.count : Measure (Fin 2)) ≠ ∞ := by
  refine ⟨fun n => Eventually.of_forall fun i => alt_le_one n i, ?_⟩
  rw [lintegral_fintype, Fin.sum_univ_two, Measure.count_singleton, Measure.count_singleton]
  simp only [mul_one]
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, ENNReal.one_ne_top⟩

end FatouLemmaOQ01OQ01
