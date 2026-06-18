/-
# Besicovitch (n = 2): ℚ-linear independence of {1, √2, √3, √6}  (OQ-02)

Open Question (`sqrt2-plus-sqrt3-irrational-oq-02`):

  Formalize **Besicovitch's theorem (1940)**: the square roots of distinct
  squarefree positive integers are linearly independent over ℚ.  This gives the
  complete characterization
        ∑ᵢ rᵢ √aᵢ ∈ ℚ   ⟺   rᵢ = 0  for every aᵢ > 1.

## STATUS — verified, axiom-free: the complete n = 2 instance

The general theorem reduces (see the sibling file
`Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ02`) to a single non-trivial *induction
heart*: adjoining a new prime square root strictly enlarges the multiquadratic
field, equivalently `√3 ∉ ℚ(√2)`.  That file leaves the heart as `sorry`.

This file discharges the **smallest non-trivial case completely and without any
axioms**: it proves

  * `sqrt3_not_in_Qsqrt2`  — `√3` is not of the form `e + f√2` with `e, f ∈ ℚ`
    (the n = 2 induction heart), and

  * `linearIndependent_one_sqrt2_sqrt3_sqrt6` — for rationals `a, b, c, d`,
        a + b√2 + c√3 + d√6 = 0  ⟹  a = b = c = d = 0,

i.e. `{1, √2, √3, √6}` is ℚ-linearly independent.  This is exactly the
"complete characterization" of the open question, specialized to the radicands
`{1, 2, 3, 6}` (`= {√d : d | 6 squarefree}`), and is the concrete certificate
the general (still-`sorry`) reduction lacks.

The proof is elementary (no field-theory tower): regroup `α := a + b√2 + c√3 +
d√6` as `(a + b√2) + √3·(c + d√2)`, multiply by the ℚ(√2)-conjugate `(c − d√2)`
to isolate `√3·(c² − 2d²)`, and conclude with `√3 ∉ ℚ(√2)`.  All irrationality
inputs use kernel `decide` (`¬ IsSquare n` for `n ∈ {3, 6}`), so the file is
genuinely axiom-free — no `native_decide`, hence no `Lean.ofReduceBool`.

Tags: number-theory, field-theory, multiquadratic, besicovitch, linear-independence
-/

import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace Sqrt2PlusSqrt3IrrationalOQ02

open Real

/-- `√3` is irrational (3 is not a perfect square). Axiom-free via kernel `decide`. -/
theorem irrational_sqrt_three : Irrational (Real.sqrt 3) :=
  irrational_sqrt_ofNat_iff.mpr (by decide)

/-- `√6` is irrational (6 is not a perfect square). Axiom-free via kernel `decide`. -/
theorem irrational_sqrt_six : Irrational (Real.sqrt 6) :=
  irrational_sqrt_ofNat_iff.mpr (by decide)

/-- No rational is a square root of `2`. (`√2` irrational, stated over ℚ.) -/
theorem rat_sq_ne_two (q : ℚ) : q ^ 2 ≠ 2 := by
  intro hq
  have h1 : ((q : ℝ)) ^ 2 = 2 := by exact_mod_cast hq
  have h2 : Real.sqrt 2 = |(q : ℝ)| := by rw [← h1, Real.sqrt_sq_eq_abs]
  rw [← Rat.cast_abs] at h2
  exact irrational_sqrt_two ⟨|q|, h2.symm⟩

/-- `{1, √2}` is ℚ-linearly independent: `p + q√2 = 0` forces `p = q = 0`. -/
theorem linearIndependent_one_sqrt2 (p q : ℚ)
    (h : (p : ℝ) + (q : ℝ) * Real.sqrt 2 = 0) : p = 0 ∧ q = 0 := by
  by_cases hq : q = 0
  · subst hq
    simp only [Rat.cast_zero, zero_mul, add_zero] at h
    exact ⟨by exact_mod_cast h, rfl⟩
  · exfalso
    apply irrational_sqrt_two
    refine ⟨-p / q, ?_⟩
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
    rw [Rat.cast_div, Rat.cast_neg, div_eq_iff hqR]
    linear_combination -h

/-- **n = 2 induction heart.** `√3` is not a ℚ-linear combination of `1` and `√2`;
equivalently `√3 ∉ ℚ(√2)`. This is the smallest non-trivial case of the
multiquadratic degree-doubling step underlying Besicovitch's theorem. -/
theorem sqrt3_not_in_Qsqrt2 :
    ¬ ∃ e f : ℚ, Real.sqrt 3 = (e : ℝ) + (f : ℝ) * Real.sqrt 2 := by
  rintro ⟨e, f, hef⟩
  have h2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  -- Square `√3 = e + f√2`:  e² + 2f² + 2ef·√2 = 3.
  have key : (e : ℝ) ^ 2 + 2 * (f : ℝ) ^ 2 + 2 * (e : ℝ) * (f : ℝ) * Real.sqrt 2 = 3 := by
    have hexp : ((e : ℝ) + (f : ℝ) * Real.sqrt 2) ^ 2
        = (e : ℝ) ^ 2 + 2 * (f : ℝ) ^ 2 + 2 * (e : ℝ) * (f : ℝ) * Real.sqrt 2 := by
      linear_combination (f : ℝ) ^ 2 * h2sq
    rw [← hexp, ← hef, h3sq]
  by_cases hf : f = 0
  · -- √3 = e ∈ ℚ : contradicts irrationality of √3.
    subst hf
    have h3 : Real.sqrt 3 = (e : ℝ) := by rw [hef]; push_cast; ring
    exact irrational_sqrt_three ⟨e, h3.symm⟩
  · by_cases he : e = 0
    · -- √3 = f√2, so √6 = 2f ∈ ℚ : contradicts irrationality of √6.
      subst he
      have hef0 : Real.sqrt 3 = (f : ℝ) * Real.sqrt 2 := by rw [hef]; push_cast; ring
      have hsix : Real.sqrt 6 = 2 * (f : ℝ) := by
        have hm : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
          rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
        calc Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := hm.symm
          _ = Real.sqrt 2 * ((f : ℝ) * Real.sqrt 2) := by rw [hef0]
          _ = (f : ℝ) * Real.sqrt 2 ^ 2 := by ring
          _ = (f : ℝ) * 2 := by rw [h2sq]
          _ = 2 * (f : ℝ) := by ring
      exact irrational_sqrt_six ⟨2 * f, by push_cast; rw [hsix]⟩
    · -- e, f ≠ 0 : √2 = (3 − e² − 2f²)/(2ef) ∈ ℚ : contradicts irrationality of √2.
      exfalso
      apply irrational_sqrt_two
      refine ⟨(3 - e ^ 2 - 2 * f ^ 2) / (2 * e * f), ?_⟩
      have hef2 : (2 * (e : ℝ) * (f : ℝ)) ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast he)) (by exact_mod_cast hf)
      have hmul2 : Real.sqrt 2 * (2 * (e : ℝ) * (f : ℝ))
          = 3 - (e : ℝ) ^ 2 - 2 * (f : ℝ) ^ 2 := by linear_combination key
      have hwit : (((3 - e ^ 2 - 2 * f ^ 2) / (2 * e * f) : ℚ) : ℝ) * (2 * (e : ℝ) * (f : ℝ))
          = 3 - (e : ℝ) ^ 2 - 2 * (f : ℝ) ^ 2 := by
        push_cast
        rw [div_mul_cancel₀ _ hef2]
      exact mul_right_cancel₀ hef2 (hwit.trans hmul2.symm)

/-- **Besicovitch, n = 2 (main result).** `{1, √2, √3, √6}` is ℚ-linearly
independent: if `a + b√2 + c√3 + d√6 = 0` with `a, b, c, d ∈ ℚ`, then all four
coefficients vanish.  Equivalently `[ℚ(√2, √3) : ℚ] = 4`, and the open
question's characterization `∑ rᵢ√aᵢ ∈ ℚ ⟺ rᵢ = 0` holds for radicands
`{1, 2, 3, 6}`. -/
theorem linearIndependent_one_sqrt2_sqrt3_sqrt6 (a b c d : ℚ)
    (h : (a : ℝ) + (b : ℝ) * Real.sqrt 2 + (c : ℝ) * Real.sqrt 3
        + (d : ℝ) * Real.sqrt 6 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have h2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h6 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  -- Regroup over ℚ(√2):  (a + b√2) + √3·(c + d√2) = 0.
  have h1 : ((a : ℝ) + (b : ℝ) * Real.sqrt 2)
      + Real.sqrt 3 * ((c : ℝ) + (d : ℝ) * Real.sqrt 2) = 0 := by
    rw [h6] at h; linear_combination h
  by_cases hcd : c = 0 ∧ d = 0
  · -- Coefficient of √3 vanishes:  a + b√2 = 0.
    obtain ⟨hc, hd⟩ := hcd
    subst hc; subst hd
    push_cast at h1
    have h1' : (a : ℝ) + (b : ℝ) * Real.sqrt 2 = 0 := by linear_combination h1
    obtain ⟨ha, hb⟩ := linearIndependent_one_sqrt2 a b h1'
    exact ⟨ha, hb, rfl, rfl⟩
  · -- Otherwise the ℚ(√2)-conjugate isolates √3 ∈ ℚ(√2), a contradiction.
    exfalso
    -- `c² − 2d² ≠ 0` since 2 is not a rational square.
    have hg : (c ^ 2 - 2 * d ^ 2 : ℚ) ≠ 0 := by
      intro hg0
      rcases eq_or_ne d 0 with hd | hd
      · subst hd
        apply hcd
        refine ⟨?_, rfl⟩
        have hc2 : c ^ 2 = 0 := by simpa using hg0
        exact sq_eq_zero_iff.mp hc2
      · apply rat_sq_ne_two (c / d)
        rw [div_pow, div_eq_iff (pow_ne_zero 2 hd)]
        linarith [hg0]
    have hgR : ((c : ℝ) ^ 2 - 2 * (d : ℝ) ^ 2) ≠ 0 := by exact_mod_cast hg
    -- Multiply `h1` by the conjugate `(c − d√2)` to isolate `√3·(c² − 2d²)`.
    have hmul : Real.sqrt 3 * ((c : ℝ) ^ 2 - 2 * (d : ℝ) ^ 2)
        = (2 * (b : ℝ) * (d : ℝ) - (a : ℝ) * (c : ℝ))
          + ((a : ℝ) * (d : ℝ) - (b : ℝ) * (c : ℝ)) * Real.sqrt 2 := by
      linear_combination ((c : ℝ) - (d : ℝ) * Real.sqrt 2) * h1
        + ((b : ℝ) * (d : ℝ) + (d : ℝ) ^ 2 * Real.sqrt 3) * h2sq
    -- Hence `√3 = e + f√2 ∈ ℚ(√2)`, contradicting `sqrt3_not_in_Qsqrt2`.
    apply sqrt3_not_in_Qsqrt2
    set e : ℚ := (2 * b * d - a * c) / (c ^ 2 - 2 * d ^ 2) with he_def
    set f : ℚ := (a * d - b * c) / (c ^ 2 - 2 * d ^ 2) with hf_def
    refine ⟨e, f, ?_⟩
    have heG : (e : ℝ) * ((c : ℝ) ^ 2 - 2 * (d : ℝ) ^ 2)
        = 2 * (b : ℝ) * (d : ℝ) - (a : ℝ) * (c : ℝ) := by
      rw [he_def]; push_cast; rw [div_mul_cancel₀ _ hgR]
    have hfG : (f : ℝ) * ((c : ℝ) ^ 2 - 2 * (d : ℝ) ^ 2)
        = (a : ℝ) * (d : ℝ) - (b : ℝ) * (c : ℝ) := by
      rw [hf_def]; push_cast; rw [div_mul_cancel₀ _ hgR]
    have key2 : Real.sqrt 3 * ((c : ℝ) ^ 2 - 2 * (d : ℝ) ^ 2)
        = ((e : ℝ) + (f : ℝ) * Real.sqrt 2) * ((c : ℝ) ^ 2 - 2 * (d : ℝ) ^ 2) := by
      rw [hmul]
      have hexp : ((e : ℝ) + (f : ℝ) * Real.sqrt 2) * ((c : ℝ) ^ 2 - 2 * (d : ℝ) ^ 2)
          = (e : ℝ) * ((c : ℝ) ^ 2 - 2 * (d : ℝ) ^ 2)
            + ((f : ℝ) * ((c : ℝ) ^ 2 - 2 * (d : ℝ) ^ 2)) * Real.sqrt 2 := by ring
      rw [hexp, heG, hfG]
    exact mul_right_cancel₀ hgR key2

end Sqrt2PlusSqrt3IrrationalOQ02
