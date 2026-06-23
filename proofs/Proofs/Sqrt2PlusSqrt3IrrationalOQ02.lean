/-
# Besicovitch (n = 2): ℚ-linear independence of {1, √2, √3, √6}  (OQ-02)

Open Question (`sqrt2-plus-sqrt3-irrational-oq-02`):

  Formalize **Besicovitch's theorem (1940)**: the square roots of distinct
  squarefree positive integers are linearly independent over ℚ.  This gives the
  complete characterization
        ∑ᵢ rᵢ √aᵢ ∈ ℚ   ⟺   rᵢ = 0  for every aᵢ > 1.

## STATUS — verified, axiom-free: the n = 2 instance + general biquadratic case

This file now proves two things, both verified and axiom-free:

  1. the concrete `{1, √2, √3, √6}` instance (the original deliverable), and
  2. its uniform **generalization** `linearIndependent_one_sqrt_sqrt_sqrt`: for
     *any* coprime squarefree `a, b > 1`, the set `{1, √a, √b, √(ab)}` is
     ℚ-linearly independent, i.e. `[ℚ(√a, √b) : ℚ] = 4`.  This covers infinitely
     many multiquadratic biquadratic fields with a single proof, replacing the
     radicand-specific irrationality inputs by `irrational_sqrt_natCast_iff`
     (`√n` irrational ⟺ `n` not a perfect square) together with the elementary
     `not_isSquare_of_squarefree`.  The `{2, 3}` case is recovered as a corollary
     (`linearIndependent_one_sqrt2_sqrt3_sqrt6'`), confirming non-vacuity.

The general theorem is the genuine n = 2 layer of Besicovitch's induction: the
degree-doubling step `√b ∉ ℚ(√a)` proved uniformly in the two radicands.

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
to isolate `√3·(c² − 2d²)`, and conclude with `√3 ∉ ℚ(√2)`.  The irrationality
inputs (`¬ IsSquare n` for `n ∈ {3, 6}`) are discharged by an elementary divisor
bound (`r ∣ n → r ≤ n`) plus a finite case split (`interval_cases`/`omega`),
*not* by kernel `decide` (which gets stuck on `Nat.sqrt`) and not by
`native_decide`.  The file is therefore genuinely axiom-free — no
`Lean.ofReduceBool`, only the standard `propext`/`Classical.choice`/`Quot.sound`.

Tags: number-theory, field-theory, multiquadratic, besicovitch, linear-independence
-/

import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Sqrt2PlusSqrt3IrrationalOQ02

open Real

/-- `√3` is irrational (`3` is not a perfect square). Axiom-free: `¬ IsSquare 3`
is discharged by an elementary divisor bound (`r ∣ 3 → r ≤ 3`) and a finite case
split, avoiding kernel `decide` (which gets stuck on `Nat.sqrt`). -/
theorem irrational_sqrt_three : Irrational (Real.sqrt 3) :=
  irrational_sqrt_ofNat_iff.mpr (by
    rintro ⟨r, hr⟩
    have hle : r ≤ 3 := Nat.le_of_dvd (by norm_num) ⟨r, hr⟩
    interval_cases r <;> omega)

/-- `√6` is irrational (`6` is not a perfect square). Axiom-free: `¬ IsSquare 6`
is discharged by an elementary divisor bound (`r ∣ 6 → r ≤ 6`) and a finite case
split, avoiding kernel `decide` (which gets stuck on `Nat.sqrt`). -/
theorem irrational_sqrt_six : Irrational (Real.sqrt 6) :=
  irrational_sqrt_ofNat_iff.mpr (by
    rintro ⟨r, hr⟩
    have hle : r ≤ 6 := Nat.le_of_dvd (by norm_num) ⟨r, hr⟩
    interval_cases r <;> omega)

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

/-! ## General coprime-squarefree pair: `{1, √a, √b, √(ab)}`

The specific result above (`a = 2, b = 3`) is the smallest instance of a uniform
phenomenon: for **any** two coprime squarefree integers `a, b > 1` the four reals
`1, √a, √b, √(ab)` are ℚ-linearly independent, i.e. `[ℚ(√a, √b) : ℚ] = 4`.  This
covers infinitely many multiquadratic biquadratic fields with a single proof,
replacing the radicand-specific irrationality inputs by the squarefree hypothesis
via `irrational_sqrt_natCast_iff`.  The algebra is identical — regroup over
`ℚ(√a)` and multiply by the conjugate `(r − s√a)` to isolate `√b·(r² − a s²)` —
the same `linear_combination` certificate works verbatim with `a, b` symbolic. -/

/-- A squarefree natural number `> 1` is not a perfect square. -/
theorem not_isSquare_of_squarefree {n : ℕ} (hsf : Squarefree n) (hn : n ≠ 1) :
    ¬ IsSquare n := by
  rintro ⟨r, hr⟩
  have hru : IsUnit r := hsf r ⟨1, by rw [hr, mul_one]⟩
  rw [Nat.isUnit_iff] at hru
  exact hn (by rw [hr, hru, mul_one])

/-- `√n` is irrational for any squarefree `n > 1`.  Axiom-free: combines
`irrational_sqrt_natCast_iff` with `not_isSquare_of_squarefree`. -/
theorem irrational_sqrt_of_squarefree {n : ℕ} (hsf : Squarefree n) (hn : n ≠ 1) :
    Irrational (Real.sqrt n) :=
  irrational_sqrt_natCast_iff.mpr (not_isSquare_of_squarefree hsf hn)

/-- **General induction heart.** For coprime squarefree `a, b > 1`, `√b` is not a
ℚ-linear combination of `1` and `√a`; equivalently `√b ∉ ℚ(√a)`.  Stated with the
three irrationality facts as hypotheses (each supplied by
`irrational_sqrt_of_squarefree`). -/
theorem sqrtb_not_in_Qsqrta {a b : ℕ}
    (ha_irr : Irrational (Real.sqrt a)) (hb_irr : Irrational (Real.sqrt b))
    (hab_irr : Irrational (Real.sqrt ((a : ℝ) * (b : ℝ)))) :
    ¬ ∃ e f : ℚ, Real.sqrt b = (e : ℝ) + (f : ℝ) * Real.sqrt a := by
  rintro ⟨e, f, hef⟩
  have hasq : Real.sqrt (a : ℝ) ^ 2 = (a : ℝ) := Real.sq_sqrt (by positivity)
  have hbsq : Real.sqrt (b : ℝ) ^ 2 = (b : ℝ) := Real.sq_sqrt (by positivity)
  -- Square `√b = e + f√a`:  e² + a·f² + 2ef·√a = b.
  have key : (e : ℝ) ^ 2 + (a : ℝ) * (f : ℝ) ^ 2 + 2 * (e : ℝ) * (f : ℝ) * Real.sqrt a
      = (b : ℝ) := by
    have hexp : ((e : ℝ) + (f : ℝ) * Real.sqrt a) ^ 2
        = (e : ℝ) ^ 2 + (a : ℝ) * (f : ℝ) ^ 2 + 2 * (e : ℝ) * (f : ℝ) * Real.sqrt a := by
      linear_combination (f : ℝ) ^ 2 * hasq
    rw [← hexp, ← hef]; exact hbsq
  by_cases hf : f = 0
  · -- √b = e ∈ ℚ : contradicts irrationality of √b.
    subst hf
    have hb0 : Real.sqrt b = (e : ℝ) := by rw [hef]; push_cast; ring
    exact hb_irr ⟨e, hb0.symm⟩
  · by_cases he : e = 0
    · -- √b = f√a, so √(ab) = f·a ∈ ℚ : contradicts irrationality of √(ab).
      subst he
      have hef0 : Real.sqrt b = (f : ℝ) * Real.sqrt a := by rw [hef]; push_cast; ring
      have hmul : Real.sqrt ((a : ℝ) * (b : ℝ)) = Real.sqrt a * Real.sqrt b :=
        Real.sqrt_mul (by positivity) _
      have hval : Real.sqrt ((a : ℝ) * (b : ℝ)) = (f : ℝ) * (a : ℝ) := by
        rw [hmul, hef0]
        have hcollapse : Real.sqrt a * ((f : ℝ) * Real.sqrt a)
            = (f : ℝ) * Real.sqrt a ^ 2 := by ring
        rw [hcollapse, hasq]
      exact hab_irr ⟨f * (a : ℚ), by push_cast; rw [hval]⟩
    · -- e, f ≠ 0 : √a = (b − e² − a·f²)/(2ef) ∈ ℚ : contradicts irrationality of √a.
      exfalso
      apply ha_irr
      refine ⟨((b : ℚ) - e ^ 2 - (a : ℚ) * f ^ 2) / (2 * e * f), ?_⟩
      have hef2 : (2 * (e : ℝ) * (f : ℝ)) ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast he)) (by exact_mod_cast hf)
      have hmul2 : Real.sqrt a * (2 * (e : ℝ) * (f : ℝ))
          = (b : ℝ) - (e : ℝ) ^ 2 - (a : ℝ) * (f : ℝ) ^ 2 := by linear_combination key
      have hwit : ((((b : ℚ) - e ^ 2 - (a : ℚ) * f ^ 2) / (2 * e * f) : ℚ) : ℝ)
            * (2 * (e : ℝ) * (f : ℝ))
          = (b : ℝ) - (e : ℝ) ^ 2 - (a : ℝ) * (f : ℝ) ^ 2 := by
        push_cast
        rw [div_mul_cancel₀ _ hef2]
      exact mul_right_cancel₀ hef2 (hwit.trans hmul2.symm)

/-- **Besicovitch, general biquadratic case.** For coprime squarefree `a, b > 1`,
`{1, √a, √b, √(ab)}` is ℚ-linearly independent: `p + q√a + r√b + s√(ab) = 0` with
rational `p, q, r, s` forces `p = q = r = s = 0`.  Equivalently
`[ℚ(√a, √b) : ℚ] = 4`.  The merged `{2, 3}` result is the instance `a = 2, b = 3`. -/
theorem linearIndependent_one_sqrt_sqrt_sqrt {a b : ℕ}
    (hsa : Squarefree a) (hsb : Squarefree b)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hcop : a.Coprime b)
    (p q r s : ℚ)
    (h : (p : ℝ) + (q : ℝ) * Real.sqrt a + (r : ℝ) * Real.sqrt b
        + (s : ℝ) * Real.sqrt ((a : ℝ) * (b : ℝ)) = 0) :
    p = 0 ∧ q = 0 ∧ r = 0 ∧ s = 0 := by
  have ha_irr := irrational_sqrt_of_squarefree hsa ha1
  have hb_irr := irrational_sqrt_of_squarefree hsb hb1
  have hab_irr : Irrational (Real.sqrt ((a : ℝ) * (b : ℝ))) := by
    have hsab : Squarefree (a * b) := (Nat.squarefree_mul hcop).mpr ⟨hsa, hsb⟩
    have hab1 : a * b ≠ 1 := fun hh => ha1 (Nat.eq_one_of_dvd_one ⟨b, hh.symm⟩)
    have hI := irrational_sqrt_of_squarefree hsab hab1
    rwa [Nat.cast_mul] at hI
  have h2sq : Real.sqrt (a : ℝ) ^ 2 = (a : ℝ) := Real.sq_sqrt (by positivity)
  have hab : Real.sqrt ((a : ℝ) * (b : ℝ)) = Real.sqrt a * Real.sqrt b :=
    Real.sqrt_mul (by positivity) _
  -- Regroup over ℚ(√a):  (p + q√a) + √b·(r + s√a) = 0.
  have h1 : ((p : ℝ) + (q : ℝ) * Real.sqrt a)
      + Real.sqrt b * ((r : ℝ) + (s : ℝ) * Real.sqrt a) = 0 := by
    rw [hab] at h; linear_combination h
  -- No rational squares to `a` (`√a` irrational).
  have rat_sq : ∀ x : ℚ, x ^ 2 ≠ (a : ℚ) := by
    intro x hx
    have hxR : (x : ℝ) ^ 2 = (a : ℝ) := by exact_mod_cast hx
    have hsab : Real.sqrt (a : ℝ) = |(x : ℝ)| := by rw [← hxR, Real.sqrt_sq_eq_abs]
    rw [← Rat.cast_abs] at hsab
    exact ha_irr ⟨|x|, hsab.symm⟩
  by_cases hrs : r = 0 ∧ s = 0
  · -- Coefficient of √b vanishes:  p + q√a = 0.
    obtain ⟨hr, hs⟩ := hrs
    subst hr; subst hs
    push_cast at h1
    have h1' : (p : ℝ) + (q : ℝ) * Real.sqrt a = 0 := by linear_combination h1
    by_cases hq : q = 0
    · subst hq
      simp only [Rat.cast_zero, zero_mul, add_zero] at h1'
      exact ⟨by exact_mod_cast h1', rfl, rfl, rfl⟩
    · exfalso
      apply ha_irr
      refine ⟨-p / q, ?_⟩
      have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
      rw [Rat.cast_div, Rat.cast_neg, div_eq_iff hqR]
      linear_combination -h1'
  · -- Otherwise the ℚ(√a)-conjugate isolates √b ∈ ℚ(√a), a contradiction.
    exfalso
    have hg : (r ^ 2 - (a : ℚ) * s ^ 2 : ℚ) ≠ 0 := by
      intro hg0
      rcases eq_or_ne s 0 with hs | hs
      · subst hs
        apply hrs
        refine ⟨?_, rfl⟩
        have hr2 : r ^ 2 = 0 := by simpa using hg0
        exact sq_eq_zero_iff.mp hr2
      · apply rat_sq (r / s)
        rw [div_pow, div_eq_iff (pow_ne_zero 2 hs)]
        linarith [hg0]
    have hgR : ((r : ℝ) ^ 2 - (a : ℝ) * (s : ℝ) ^ 2) ≠ 0 := by exact_mod_cast hg
    -- Multiply `h1` by the conjugate `(r − s√a)` to isolate `√b·(r² − a s²)`.
    have hmul : Real.sqrt b * ((r : ℝ) ^ 2 - (a : ℝ) * (s : ℝ) ^ 2)
        = ((a : ℝ) * (q : ℝ) * (s : ℝ) - (p : ℝ) * (r : ℝ))
          + ((p : ℝ) * (s : ℝ) - (q : ℝ) * (r : ℝ)) * Real.sqrt a := by
      linear_combination ((r : ℝ) - (s : ℝ) * Real.sqrt a) * h1
        + ((q : ℝ) * (s : ℝ) + (s : ℝ) ^ 2 * Real.sqrt b) * h2sq
    apply sqrtb_not_in_Qsqrta ha_irr hb_irr hab_irr
    set E : ℚ := ((a : ℚ) * q * s - p * r) / (r ^ 2 - (a : ℚ) * s ^ 2) with hE_def
    set F : ℚ := (p * s - q * r) / (r ^ 2 - (a : ℚ) * s ^ 2) with hF_def
    refine ⟨E, F, ?_⟩
    have hEG : (E : ℝ) * ((r : ℝ) ^ 2 - (a : ℝ) * (s : ℝ) ^ 2)
        = (a : ℝ) * (q : ℝ) * (s : ℝ) - (p : ℝ) * (r : ℝ) := by
      rw [hE_def]; push_cast; rw [div_mul_cancel₀ _ hgR]
    have hFG : (F : ℝ) * ((r : ℝ) ^ 2 - (a : ℝ) * (s : ℝ) ^ 2)
        = (p : ℝ) * (s : ℝ) - (q : ℝ) * (r : ℝ) := by
      rw [hF_def]; push_cast; rw [div_mul_cancel₀ _ hgR]
    have key2 : Real.sqrt b * ((r : ℝ) ^ 2 - (a : ℝ) * (s : ℝ) ^ 2)
        = ((E : ℝ) + (F : ℝ) * Real.sqrt a) * ((r : ℝ) ^ 2 - (a : ℝ) * (s : ℝ) ^ 2) := by
      rw [hmul]
      have hexp : ((E : ℝ) + (F : ℝ) * Real.sqrt a) * ((r : ℝ) ^ 2 - (a : ℝ) * (s : ℝ) ^ 2)
          = (E : ℝ) * ((r : ℝ) ^ 2 - (a : ℝ) * (s : ℝ) ^ 2)
            + ((F : ℝ) * ((r : ℝ) ^ 2 - (a : ℝ) * (s : ℝ) ^ 2)) * Real.sqrt a := by ring
      rw [hexp, hEG, hFG]
    exact mul_right_cancel₀ hgR key2

/-- The merged `{2, 3}` result recovered as the instance `a = 2, b = 3` of the
general theorem, confirming the two are consistent (and the general statement is
non-vacuous). -/
theorem linearIndependent_one_sqrt2_sqrt3_sqrt6' (a b c d : ℚ)
    (h : (a : ℝ) + (b : ℝ) * Real.sqrt 2 + (c : ℝ) * Real.sqrt 3
        + (d : ℝ) * Real.sqrt 6 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have h6 : Real.sqrt ((2 : ℝ) * (3 : ℝ)) = Real.sqrt 6 := by
    rw [show ((2 : ℝ) * (3 : ℝ)) = 6 from by norm_num]
  exact linearIndependent_one_sqrt_sqrt_sqrt Nat.prime_two.squarefree
    Nat.prime_three.squarefree (by norm_num) (by norm_num) (by decide)
    a b c d (by push_cast; rw [h6]; linear_combination h)

end Sqrt2PlusSqrt3IrrationalOQ02
