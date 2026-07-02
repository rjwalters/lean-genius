/-
  Weighted-Finset Second Moment: Cauchy–Schwarz and Chebyshev

  Open question OQ-04-OQ-03 (parent: prob-method-second-moment-oq-04).

  The parent line of work (`ProbMethodSecondMoment.lean`,
  `ProbMethodSecondMomentOQ02.lean`, `ProbMethodSecondMomentOQ04.lean`) develops
  the second-moment method over a finite sample space `s : Finset α` with the
  *uniform counting measure* — every point has weight `1`, so "expectation" is the
  plain average and "probability" is a fraction of cardinalities.

  This file generalizes the measure to an arbitrary nonnegative **weight**
  `w : α → ℚ`, replacing cardinalities `#s` by weighted sums `∑ w a` and averages
  by weighted averages `(∑ w a · X a)/(∑ w a)`. It captures non-uniform discrete
  distributions (importance weights, biased sampling) while deliberately staying
  in the elementary `Finset` / `BigOperators` world — no `MeasureTheory`, no real
  analysis, everything over `ℚ`.

  ## Results

  * `weighted_cauchy_schwarz` — the weighted discrete Cauchy–Schwarz inequality
        (∑ w·X)²  ≤  (∑ w)·(∑ w·X²),
    the "engine" of the second-moment method. Proved division-free from the single
    nonnegative sum `∑ w·(Sw·X − SwX)² ≥ 0`, whose expansion equals
    `Sw·(Sw·SwX2 − SwX²)`; positivity of the total weight `Sw` then clears it.

  * `weighted_chebyshev_key` / `weighted_chebyshev` — the weighted one- (here two-)
    sided Chebyshev bound
        P_w(|X − μ| ≥ a)  ≤  Var_w(X) / a²      (a > 0),
    with `μ` the weighted mean, all "probabilities" being weighted fractions.

  * `cauchy_schwarz_uniform` / `chebyshev_uniform` — the specializations to the
    uniform weight `w ≡ 1`, recovering the parent's counting-measure statements
        (∑ X)² ≤ #s·(∑ X²)   and   #tail/#s ≤ (weighted-with-1 variance)/a²,
    confirming the generalization is conservative.

  No `axiom`, no `sorry`, no `native_decide`.
-/
import Mathlib

set_option linter.unusedVariables false

namespace ProbMethod.SecondMoment.Weighted

open Finset BigOperators

variable {α : Type*}

/-! ## Weighted Cauchy–Schwarz (the engine) -/

/-- **Weighted discrete Cauchy–Schwarz.** For a nonnegative weight `w` with
positive total weight `∑ w`, and any `X : α → ℚ`,

    (∑ w·X)²  ≤  (∑ w)·(∑ w·X²).

The uniform case `w ≡ 1` is `cauchy_schwarz_uniform` below. The proof is
division-free: the single nonnegative sum `∑ w·(Sw·X − SwX)²` expands to
`Sw·(Sw·SwX2 − SwX²)`, and `Sw > 0` clears the factor. -/
theorem weighted_cauchy_schwarz (s : Finset α) (w X : α → ℚ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hS : 0 < ∑ i ∈ s, w i) :
    (∑ i ∈ s, w i * X i) ^ 2 ≤ (∑ i ∈ s, w i) * (∑ i ∈ s, w i * X i ^ 2) := by
  set Sw := ∑ i ∈ s, w i with hSw
  set SwX := ∑ i ∈ s, w i * X i with hSwX
  set SwX2 := ∑ i ∈ s, w i * X i ^ 2 with hSwX2
  -- The tilted sum of squares is nonnegative termwise.
  have hnn : 0 ≤ ∑ i ∈ s, w i * (Sw * X i - SwX) ^ 2 :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi) (sq_nonneg _))
  -- ... and expands to `Sw · (Sw · SwX2 − SwX²)`.
  have hexp : ∑ i ∈ s, w i * (Sw * X i - SwX) ^ 2 = Sw * (Sw * SwX2 - SwX ^ 2) := by
    have hterm : ∑ i ∈ s, w i * (Sw * X i - SwX) ^ 2
        = ∑ i ∈ s, (Sw ^ 2 * (w i * X i ^ 2)
            - 2 * Sw * SwX * (w i * X i) + SwX ^ 2 * w i) :=
      Finset.sum_congr rfl (fun i _ => by ring)
    rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← hSw, ← hSwX, ← hSwX2]
    ring
  rw [hexp] at hnn
  -- Clear the positive factor Sw.
  have hD : 0 ≤ Sw * SwX2 - SwX ^ 2 := by nlinarith [hnn, hS]
  linarith [hD]

/-- **Uniform Cauchy–Schwarz.** The counting-measure special case `w ≡ 1`:

    (∑ X)²  ≤  #s · (∑ X²).

Recovers the parent's uniform second-moment engine. -/
theorem cauchy_schwarz_uniform (s : Finset α) (X : α → ℚ) (hs : s.Nonempty) :
    (∑ i ∈ s, X i) ^ 2 ≤ (s.card : ℚ) * (∑ i ∈ s, X i ^ 2) := by
  have hStot : 0 < ∑ i ∈ s, (1 : ℚ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]; exact_mod_cast hs.card_pos
  have h := weighted_cauchy_schwarz s (fun _ => 1) X (fun _ _ => zero_le_one) hStot
  simp only [one_mul] at h
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact h

/-! ## Weighted Chebyshev -/

/-- **Weighted Chebyshev, cleared form.** For a nonnegative weight `w`, any
center `μ`, and `a > 0`, the weight carried by the deviation event
`{ i : |X i − μ| ≥ a }` obeys

    (∑_{|X−μ|≥a} w) · a²  ≤  ∑ w·(X − μ)².

This is the division-free heart: on the tail each `w i·(X i − μ)² ≥ w i·a²`,
and the remaining points contribute nonnegatively. -/
theorem weighted_chebyshev_key (s : Finset α) (w X : α → ℚ) (μ a : ℚ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (ha : 0 < a) :
    (∑ i ∈ s.filter (fun i => a ≤ |X i - μ|), w i) * a ^ 2
      ≤ ∑ i ∈ s, w i * (X i - μ) ^ 2 := by
  have hsub : s.filter (fun i => a ≤ |X i - μ|) ⊆ s := Finset.filter_subset _ _
  calc (∑ i ∈ s.filter (fun i => a ≤ |X i - μ|), w i) * a ^ 2
      = ∑ i ∈ s.filter (fun i => a ≤ |X i - μ|), w i * a ^ 2 := by rw [Finset.sum_mul]
    _ ≤ ∑ i ∈ s.filter (fun i => a ≤ |X i - μ|), w i * (X i - μ) ^ 2 := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        have hfi : a ≤ |X i - μ| := (Finset.mem_filter.mp hi).2
        have hwi : 0 ≤ w i := hw i (hsub hi)
        have hsq : a ^ 2 ≤ (X i - μ) ^ 2 := by
          have h1 : a ^ 2 ≤ |X i - μ| ^ 2 := by
            nlinarith [hfi, ha.le, abs_nonneg (X i - μ)]
          rwa [sq_abs] at h1
        exact mul_le_mul_of_nonneg_left hsq hwi
    _ ≤ ∑ i ∈ s, w i * (X i - μ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun i hi _ => mul_nonneg (hw i hi) (sq_nonneg _))

/-- Weighted mean: `(∑ w·X)/(∑ w)`. -/
def wmean (s : Finset α) (w X : α → ℚ) : ℚ :=
  (∑ i ∈ s, w i * X i) / (∑ i ∈ s, w i)

/-- Weighted variance: the weighted average squared deviation from the weighted mean. -/
def wvar (s : Finset α) (w X : α → ℚ) : ℚ :=
  (∑ i ∈ s, w i * (X i - wmean s w X) ^ 2) / (∑ i ∈ s, w i)

/-- Weighted two-sided tail "probability": the fraction of total weight carried by
points deviating from the weighted mean by at least `a`. -/
def wtailProb (s : Finset α) (w X : α → ℚ) (a : ℚ) : ℚ :=
  (∑ i ∈ s.filter (fun i => a ≤ |X i - wmean s w X|), w i) / (∑ i ∈ s, w i)

/-- **Weighted Chebyshev inequality.** With `μ = wmean s w X` the weighted mean and
`Var_w = wvar s w X` the weighted variance, for `a > 0` and positive total weight,

    P_w(|X − μ| ≥ a)  ≤  Var_w(X) / a². -/
theorem weighted_chebyshev (s : Finset α) (w X : α → ℚ) (a : ℚ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hS : 0 < ∑ i ∈ s, w i) (ha : 0 < a) :
    wtailProb s w X a ≤ wvar s w X / a ^ 2 := by
  have ha2 : (0 : ℚ) < a ^ 2 := pow_pos ha 2
  have hkey := weighted_chebyshev_key s w X (wmean s w X) a hw ha
  rw [wtailProb, wvar, div_div]
  rw [div_le_div_iff hS (by positivity)]
  -- goal: (∑_tail w) * (Sw * a²) ≤ (∑ w (X-μ)²) * Sw
  have hSnn : 0 ≤ ∑ i ∈ s, w i := hS.le
  calc (∑ i ∈ s.filter (fun i => a ≤ |X i - wmean s w X|), w i) * ((∑ i ∈ s, w i) * a ^ 2)
      = ((∑ i ∈ s.filter (fun i => a ≤ |X i - wmean s w X|), w i) * a ^ 2) * (∑ i ∈ s, w i) := by
        ring
    _ ≤ (∑ i ∈ s, w i * (X i - wmean s w X) ^ 2) * (∑ i ∈ s, w i) :=
        mul_le_mul_of_nonneg_right hkey hSnn

/-- **Uniform Chebyshev.** The counting-measure special case `w ≡ 1` of
`weighted_chebyshev`: the ordinary fraction of points deviating by at least `a`
is bounded by the (uniform) variance over `a²`. -/
theorem chebyshev_uniform (s : Finset α) (X : α → ℚ) (a : ℚ)
    (hs : s.Nonempty) (ha : 0 < a) :
    wtailProb s (fun _ => 1) X a ≤ wvar s (fun _ => 1) X / a ^ 2 := by
  have hStot : 0 < ∑ i ∈ s, (1 : ℚ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]; exact_mod_cast hs.card_pos
  exact weighted_chebyshev s (fun _ => 1) X a (fun _ _ => zero_le_one) hStot ha

end ProbMethod.SecondMoment.Weighted
