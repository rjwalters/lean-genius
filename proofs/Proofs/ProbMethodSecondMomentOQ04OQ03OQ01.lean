/-
  Weighted-Finset Paley–Zygmund: the second-moment lower-tail bound

  Open question OQ-04-OQ-03-OQ-01
  (parent: prob-method-second-moment-oq-04-oq-03).

  The parent file `ProbMethodSecondMomentOQ04OQ03.lean` generalises the
  counting-measure second-moment method to an arbitrary nonnegative weight
  `w : α → ℚ` over a finite index set `s : Finset α`, proving the *upper*-tail
  side of the story:

    * `weighted_cauchy_schwarz`  (∑ w·X)² ≤ (∑ w)·(∑ w·X²)
    * `weighted_chebyshev`       P_w(|X − μ| ≥ a) ≤ Var_w(X)/a².

  Chebyshev controls how much weight sits *far* from the mean. Its natural
  companion — and the missing half of the second-moment method as it is used in
  the probabilistic method (Alon–Spencer, *The Probabilistic Method*, §4.3) — is
  the **Paley–Zygmund inequality**, which lower-bounds the weight sitting *above*
  a fraction of the mean:

    for a nonnegative `X`, `0 ≤ θ ≤ 1`, and the weighted mean `μ = (∑ w·X)/(∑ w)`,

        P_w(X > θ·μ)  ≥  (1 − θ)² · μ² / E_w[X²].

  Where Chebyshev says "the tail is thin", Paley–Zygmund says "the head is fat":
  if the second moment is not much larger than the square of the mean, then a
  constant fraction of the weight lies near the mean. This is the standard tool
  for proving that a nonnegative random variable is positive with constant
  probability (e.g. threshold phenomena in random graphs).

  This file proves the weighted Paley–Zygmund inequality, staying in exactly the
  same elementary `Finset` / `BigOperators` world as the parent — everything over
  `ℚ`, no `MeasureTheory`, no real analysis. The engine is a hypothesis-free
  weighted Cauchy–Schwarz (`wcs_raw`), the same tilted-square identity used by
  the parent but with the positive-total-weight side condition removed so it also
  applies to the tail sub-sum.

  ## Results

  * `wcs_raw` — weighted Cauchy–Schwarz with no positivity side condition:
        (∑ w·X)² ≤ (∑ w)·(∑ w·X²)  for  w ≥ 0.

  * `weighted_paley_zygmund_key` — the division-free heart:
        (1 − θ)² · (∑ w·X)²  ≤  (∑_{X > θμ} w) · (∑ w·X²),
    where the threshold event `{X > θμ}` is written `θ·(∑ w·X) < (∑ w)·X` to keep
    the defining predicate division-free.

  * `weighted_paley_zygmund` — the probability form
        P_w(X > θ·μ)  ≥  (1 − θ)² · μ² / E_w[X²]
    (needs a strictly positive weighted second moment to divide).

  * `paley_zygmund_uniform` — the counting-measure specialization `w ≡ 1`:
        (1 − θ)² · (∑ X)²  ≤  (#{i : θ·∑X < #s·X i}) · (∑ X²).

  No `axiom`, no `sorry`, no `native_decide`.
-/
import Mathlib

set_option linter.unusedVariables false

namespace ProbMethod.SecondMoment.Weighted

open Finset BigOperators

variable {α : Type*}

/-! ## Hypothesis-free weighted Cauchy–Schwarz -/

/-- **Weighted Cauchy–Schwarz, no side condition.** For a nonnegative weight `w`
and any `X : α → ℚ`,

    (∑ w·X)²  ≤  (∑ w)·(∑ w·X²).

Unlike `ProbMethodSecondMomentOQ04OQ03.weighted_cauchy_schwarz`, this drops the
`0 < ∑ w` hypothesis: when the total weight is zero every `w i` vanishes and both
sides are `0`. Removing the side condition lets us apply Cauchy–Schwarz to the
tail sub-sum in Paley–Zygmund, where the sub-sum's total weight is unknown. -/
theorem wcs_raw (s : Finset α) (w X : α → ℚ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * X i) ^ 2 ≤ (∑ i ∈ s, w i) * (∑ i ∈ s, w i * X i ^ 2) := by
  set Sw := ∑ i ∈ s, w i with hSw
  set SwX := ∑ i ∈ s, w i * X i with hSwX
  set SwX2 := ∑ i ∈ s, w i * X i ^ 2 with hSwX2
  -- Tilted sum of squares is nonnegative and expands to `Sw·(Sw·SwX2 − SwX²)`.
  have hnn : 0 ≤ ∑ i ∈ s, w i * (Sw * X i - SwX) ^ 2 :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi) (sq_nonneg _))
  have hexp : ∑ i ∈ s, w i * (Sw * X i - SwX) ^ 2 = Sw * (Sw * SwX2 - SwX ^ 2) := by
    have hterm : ∑ i ∈ s, w i * (Sw * X i - SwX) ^ 2
        = ∑ i ∈ s, (Sw ^ 2 * (w i * X i ^ 2)
            - 2 * Sw * SwX * (w i * X i) + SwX ^ 2 * w i) :=
      Finset.sum_congr rfl (fun i _ => by ring)
    rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← hSw, ← hSwX, ← hSwX2]
    ring
  rw [hexp] at hnn
  -- Split on whether the total weight is zero.
  rcases eq_or_lt_of_le (Finset.sum_nonneg hw) with hSw0 | hSwpos
  · -- Sw = 0 ⇒ every weight is 0 ⇒ SwX = 0.
    have hall : ∀ i ∈ s, w i = 0 := (Finset.sum_eq_zero_iff_of_nonneg hw).mp hSw0.symm
    have hSwX0 : SwX = 0 := Finset.sum_eq_zero (fun i hi => by rw [hall i hi]; ring)
    have hSw0' : Sw = 0 := hSw0.symm
    rw [hSwX0, hSw0']; simp
  · -- Sw > 0 ⇒ clear the positive factor.
    have hD : 0 ≤ Sw * SwX2 - SwX ^ 2 := by nlinarith [hnn, hSwpos]
    linarith [hD]

/-! ## Weighted Paley–Zygmund -/

/-- **Weighted Paley–Zygmund, cleared (division-free) form.** For a nonnegative
weight `w`, a nonnegative `X`, positive total weight, and `0 ≤ θ ≤ 1`,

    (1 − θ)² · (∑ w·X)²  ≤  (∑_{i : θ·(∑ w·X) < (∑ w)·X i} w i) · (∑ w·X²).

The threshold set `{ θ·(∑ w·X) < (∑ w)·X i }` is the division-free rendering of
`{ X i > θ·μ }` with `μ = (∑ w·X)/(∑ w)`. The proof: the head weight carries at
least `(1 − θ)·(∑ w·X)` of the weighted sum of `X` (the tail contributes at most
`θ·(∑ w·X)`), and weighted Cauchy–Schwarz on the head turns that linear lower
bound into the quadratic one. -/
theorem weighted_paley_zygmund_key (s : Finset α) (w X : α → ℚ) (θ : ℚ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hX : ∀ i ∈ s, 0 ≤ X i)
    (hS : 0 < ∑ i ∈ s, w i) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1 - θ) ^ 2 * (∑ i ∈ s, w i * X i) ^ 2
      ≤ (∑ i ∈ s.filter (fun i => θ * (∑ j ∈ s, w j * X j) < (∑ j ∈ s, w j) * X i), w i)
          * (∑ i ∈ s, w i * X i ^ 2) := by
  set Sw := ∑ i ∈ s, w i with hSw
  set SwX := ∑ i ∈ s, w i * X i with hSwX
  set A := s.filter (fun i => θ * SwX < Sw * X i) with hAdef
  set B := s.filter (fun i => ¬ (θ * SwX < Sw * X i)) with hBdef
  have hAsub : A ⊆ s := Finset.filter_subset _ _
  have hBsub : B ⊆ s := Finset.filter_subset _ _
  have hSwX_nn : 0 ≤ SwX :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi) (hX i hi))
  -- (1) Complement `B = {X ≤ θμ}` carries little weighted mass: ∑_B w·X ≤ θ·SwX.
  have hθSwX_nn : 0 ≤ θ * SwX := mul_nonneg hθ0 hSwX_nn
  have htail : Sw * (∑ i ∈ B, w i * X i) ≤ Sw * (θ * SwX) := by
    calc Sw * (∑ i ∈ B, w i * X i)
        = ∑ i ∈ B, w i * (Sw * X i) := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
      _ ≤ ∑ i ∈ B, w i * (θ * SwX) := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          have hi_s : i ∈ s := hBsub hi
          have hle : Sw * X i ≤ θ * SwX := not_lt.mp (Finset.mem_filter.mp hi).2
          exact mul_le_mul_of_nonneg_left hle (hw i hi_s)
      _ = (∑ i ∈ B, w i) * (θ * SwX) := by rw [Finset.sum_mul]
      _ ≤ Sw * (θ * SwX) := by
          apply mul_le_mul_of_nonneg_right _ hθSwX_nn
          rw [hSw]
          exact Finset.sum_le_sum_of_subset_of_nonneg hBsub
            (fun i hi _ => hw i hi)
  have htail' : (∑ i ∈ B, w i * X i) ≤ θ * SwX :=
    le_of_mul_le_mul_left htail hS
  -- (2) Hence the head carries a linear lower bound: (1−θ)·SwX ≤ ∑_A w·X.
  have hsplit : (∑ i ∈ A, w i * X i) + (∑ i ∈ B, w i * X i) = SwX := by
    rw [hSwX]; exact Finset.sum_filter_add_sum_filter_not s _ _
  have hhead : (1 - θ) * SwX ≤ ∑ i ∈ A, w i * X i := by
    have : ∑ i ∈ A, w i * X i = SwX - (∑ i ∈ B, w i * X i) := by linarith [hsplit]
    rw [this]; nlinarith [htail']
  have hhead_nn : 0 ≤ (1 - θ) * SwX := mul_nonneg (by linarith) hSwX_nn
  -- (3) Cauchy–Schwarz on the head set A, then extend the X² sum back to s.
  have hcs : (∑ i ∈ A, w i * X i) ^ 2
      ≤ (∑ i ∈ A, w i) * (∑ i ∈ A, w i * X i ^ 2) :=
    wcs_raw A w X (fun i hi => hw i (hAsub hi))
  have hext : (∑ i ∈ A, w i * X i ^ 2) ≤ (∑ i ∈ s, w i * X i ^ 2) :=
    Finset.sum_le_sum_of_subset_of_nonneg hAsub
      (fun i hi _ => mul_nonneg (hw i hi) (sq_nonneg _))
  have hAw_nn : 0 ≤ ∑ i ∈ A, w i :=
    Finset.sum_nonneg (fun i hi => hw i (hAsub hi))
  -- (4) Chain: (1−θ)²·SwX² ≤ (∑_A wX)² ≤ (∑_A w)(∑_A wX²) ≤ (∑_A w)(∑_s wX²).
  calc (1 - θ) ^ 2 * SwX ^ 2
      = ((1 - θ) * SwX) ^ 2 := by ring
    _ ≤ (∑ i ∈ A, w i * X i) ^ 2 := by
        apply pow_le_pow_left₀ hhead_nn hhead
    _ ≤ (∑ i ∈ A, w i) * (∑ i ∈ A, w i * X i ^ 2) := hcs
    _ ≤ (∑ i ∈ A, w i) * (∑ i ∈ s, w i * X i ^ 2) :=
        mul_le_mul_of_nonneg_left hext hAw_nn

/-- Weighted mean `(∑ w·X)/(∑ w)`, matching the parent file's `wmean`. -/
def wmean (s : Finset α) (w X : α → ℚ) : ℚ :=
  (∑ i ∈ s, w i * X i) / (∑ i ∈ s, w i)

/-- Weighted lower-tail "probability": the fraction of total weight carried by
points with `X i > θ·μ`, `μ` the weighted mean. The defining predicate is the
division-free `θ·(∑ w·X) < (∑ w)·X i`, equivalent to `X i > θ·μ` when `∑ w > 0`. -/
def wHeadProb (s : Finset α) (w X : α → ℚ) (θ : ℚ) : ℚ :=
  (∑ i ∈ s.filter (fun i => θ * (∑ j ∈ s, w j * X j) < (∑ j ∈ s, w j) * X i), w i)
    / (∑ i ∈ s, w i)

/-- **Weighted Paley–Zygmund inequality (probability form).** With `μ = wmean`
the weighted mean and `E_w[X²] = (∑ w·X²)/(∑ w)` the weighted second moment, for
`0 ≤ θ ≤ 1`, positive total weight, nonnegative `X`, and positive weighted second
moment,

    P_w(X > θ·μ)  ≥  (1 − θ)² · μ² / E_w[X²].

Written with `wHeadProb` on the left. This is the lower-tail companion to the
parent's `weighted_chebyshev`. -/
theorem weighted_paley_zygmund (s : Finset α) (w X : α → ℚ) (θ : ℚ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hX : ∀ i ∈ s, 0 ≤ X i)
    (hS : 0 < ∑ i ∈ s, w i) (hSX2 : 0 < ∑ i ∈ s, w i * X i ^ 2)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1 - θ) ^ 2 * wmean s w X ^ 2 / ((∑ i ∈ s, w i * X i ^ 2) / (∑ i ∈ s, w i))
      ≤ wHeadProb s w X θ := by
  set Sw := ∑ i ∈ s, w i with hSw
  set SwX := ∑ i ∈ s, w i * X i with hSwX
  set SwX2 := ∑ i ∈ s, w i * X i ^ 2 with hSwX2
  set Aw := ∑ i ∈ s.filter (fun i => θ * SwX < Sw * X i), w i with hAw
  have hkey : (1 - θ) ^ 2 * SwX ^ 2 ≤ Aw * SwX2 :=
    weighted_paley_zygmund_key s w X θ hw hX hS hθ0 hθ1
  -- LHS = (1−θ)²·(SwX/Sw)² / (SwX2/Sw) = (1−θ)²·SwX² / (Sw·SwX2).
  have hErw : (1 - θ) ^ 2 * wmean s w X ^ 2 / (SwX2 / Sw)
      = (1 - θ) ^ 2 * SwX ^ 2 / (Sw * SwX2) := by
    rw [wmean, ← hSwX, ← hSw]
    field_simp
  rw [hErw, wHeadProb, ← hSwX, ← hSw, ← hAw]
  rw [div_le_div_iff₀ (by positivity) hS]
  -- goal: (1−θ)²·SwX² · Sw ≤ Aw · (Sw·SwX2)
  nlinarith [hkey, hS.le, mul_nonneg hS.le hSX2.le]

/-! ## Uniform (counting-measure) specialization -/

/-- **Uniform Paley–Zygmund.** The counting-measure special case `w ≡ 1` of
`weighted_paley_zygmund_key`:

    (1 − θ)² · (∑ X)²  ≤  (#{i ∈ s : θ·∑X < #s·X i}) · (∑ X²),

recovering the classical Paley–Zygmund lower-tail bound over a uniform finite
sample space. -/
theorem paley_zygmund_uniform (s : Finset α) (X : α → ℚ) (θ : ℚ)
    (hX : ∀ i ∈ s, 0 ≤ X i) (hs : s.Nonempty) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1 - θ) ^ 2 * (∑ i ∈ s, X i) ^ 2
      ≤ ((s.filter (fun i => θ * (∑ j ∈ s, X j) < (s.card : ℚ) * X i)).card : ℚ)
          * (∑ i ∈ s, X i ^ 2) := by
  have hStot : 0 < ∑ i ∈ s, (1 : ℚ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]; exact_mod_cast hs.card_pos
  have h := weighted_paley_zygmund_key s (fun _ => 1) X θ
    (fun _ _ => zero_le_one) hX hStot hθ0 hθ1
  simp only [one_mul] at h
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  -- rewrite the total weight `∑ 1 = #s` inside the filter predicate and the head count
  have hcard : (∑ i ∈ s, (1 : ℚ)) = (s.card : ℚ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hcard] at h
  simpa using h

end ProbMethod.SecondMoment.Weighted
