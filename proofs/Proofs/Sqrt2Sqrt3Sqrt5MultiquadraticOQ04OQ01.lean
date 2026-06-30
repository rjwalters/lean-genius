/-
# ℚ-linear independence of `{√2, √3, √5}` and distinctness of the eight conjugates

(OQ-04-OQ-01 of `sqrt2-plus-sqrt3-plus-sqrt5-irrational`)

The parent open question OQ-04 (`Sqrt2Sqrt3Sqrt5MultiquadraticOQ04`) supplies the
explicit degree-8 minimal polynomial `p(x) = x⁸ - 40x⁶ + 352x⁴ - 960x² + 576`
of `α = √2 + √3 + √5`, proving that all eight sign-conjugates `±√2 ± √3 ± √5`
are roots and hence `[ℚ(α):ℚ] ≤ 8`.  That file explicitly flags as *open/hard*:

> ℚ-linear independence of `{√2, √3, √5}`, full pairwise distinctness of the
> eight conjugates.

This file closes exactly that gap, **elementarily and without `native_decide`**:

* `linearIndependent` — the three surds `√2, √3, √5` are linearly independent over
  `ℚ`: if `a·√2 + b·√3 + c·√5 = 0` with `a, b, c ∈ ℚ` then `a = b = c = 0`.
* `conjugates_distinct` — consequently the map
  `(ε₁, ε₂, ε₃) ↦ ε₁√2 + ε₂√3 + ε₃√5` is injective on rational sign vectors, so
  the eight conjugates `±√2 ± √3 ± √5` are pairwise distinct.

## Method

Everything reduces to the irrationality of `√6, √10, √15` (composite
non-squares), which Mathlib supplies via `irrational_sqrt_natCast_iff`.

* `sqrt_irrat_lin` packages the contradiction "if `k·√m = r` with `k, r ∈ ℚ`,
  `k ≠ 0` and `m` a non-square, then `√m = r/k ∈ ℚ` — impossible."
* `two_term_zero` handles a two-surd relation `p·√M + q·√N = 0`: multiplying by
  `√M` turns it into `q·√(MN) = -M·p`, killing `q` via `sqrt_irrat_lin`
  (`MN` not a square), then `p` since `√M > 0`.
* `linearIndependent` squares `a·√2 = -(b·√3 + c·√5)` to expose the cross term
  `2bc·√15`; non-squareness of `15` forces `bc = 0`, and the two resulting
  two-surd relations are dispatched by `two_term_zero` (`M·N ∈ {6, 10}`).

Every algebraic identity is discharged by `linear_combination` over the square
relations `(√k)² = k` — no `native_decide`, no axioms beyond Lean's core.

## Honest scope

This is the `ℚ`-linear independence of the three generators, equivalently the
separability/distinctness of the eight conjugate embeddings.  It does **not**
formalize the full degree-8 basis `{1, √2, √3, √5, √6, √10, √15, √30}`,
irreducibility of `p`, or the Galois group `(ℤ/2ℤ)³`.  Combined with the parent's
`[ℚ(α):ℚ] ≤ 8`, the eight distinct conjugates give eight distinct real
embeddings, which is the standard route to `[ℚ(α):ℚ] = 8` (not formalized here).
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

open Real

namespace Sqrt2Sqrt3Sqrt5MultiquadraticOQ04OQ01

/-- **Irrationality packaging.** If `k·√m = r` with `k, r` rational, `k ≠ 0`, and
`m` is not a perfect square, we reach a contradiction: `√m` would equal the
rational `r/k`. -/
private theorem sqrt_irrat_lin {m : ℕ} (hm : ¬ IsSquare m) (k r : ℚ) (hk : k ≠ 0)
    (h : (k : ℝ) * Real.sqrt (m : ℝ) = (r : ℝ)) : False := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hsqrt : Real.sqrt (m : ℝ) = ((r / k : ℚ) : ℝ) := by
    rw [Rat.cast_div, eq_div_iff hk', mul_comm]; exact h
  exact (irrational_sqrt_natCast_iff.mpr hm) ⟨r / k, hsqrt.symm⟩

/-- `6` is not a perfect square (the kernel cannot `decide` this through
`Nat.sqrt`, so we check the finitely many candidates directly). -/
private theorem ns6 : ¬ IsSquare (6 : ℕ) := by
  rintro ⟨r, hr⟩
  have : r ≤ 6 := Nat.le_of_dvd (by norm_num) ⟨r, hr⟩
  interval_cases r <;> omega

/-- `10` is not a perfect square. -/
private theorem ns10 : ¬ IsSquare (10 : ℕ) := by
  rintro ⟨r, hr⟩
  have : r ≤ 10 := Nat.le_of_dvd (by norm_num) ⟨r, hr⟩
  interval_cases r <;> omega

/-- `15` is not a perfect square. -/
private theorem ns15 : ¬ IsSquare (15 : ℕ) := by
  rintro ⟨r, hr⟩
  have : r ≤ 15 := Nat.le_of_dvd (by norm_num) ⟨r, hr⟩
  interval_cases r <;> omega

/-- **Two-surd relation.** For naturals `M ≥ 1`, `N` with `M·N` not a perfect
square, a relation `p·√M + q·√N = 0` over `ℚ` forces `p = q = 0`. -/
private theorem two_term_zero {M N : ℕ} (hM : 1 ≤ M) (hMN : ¬ IsSquare (M * N))
    (p q : ℚ)
    (h : (p : ℝ) * Real.sqrt (M : ℝ) + (q : ℝ) * Real.sqrt (N : ℝ) = 0) :
    p = 0 ∧ q = 0 := by
  have hMpos : (0 : ℝ) ≤ (M : ℝ) := by positivity
  have hmm : Real.sqrt (M : ℝ) * Real.sqrt (N : ℝ) = Real.sqrt ((M : ℝ) * (N : ℝ)) :=
    (Real.sqrt_mul hMpos (N : ℝ)).symm
  have hsqM : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) := Real.mul_self_sqrt hMpos
  -- First kill `q`: multiplying `h` by `√M` gives `q·√(MN) = -M·p`.
  have hq : q = 0 := by
    by_contra hq
    refine sqrt_irrat_lin (m := M * N) hMN q (-(M : ℚ) * p) hq ?_
    push_cast
    linear_combination (Real.sqrt (M : ℝ)) * h - (p : ℝ) * hsqM - (q : ℝ) * hmm
  -- Now `p·√M = 0` and `√M > 0`, so `p = 0`.
  refine ⟨?_, hq⟩
  have hMrpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hsqrtpos : (0 : ℝ) < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hMrpos
  have hpM : (p : ℝ) * Real.sqrt (M : ℝ) = 0 := by
    rw [hq] at h; push_cast at h; linarith [h]
  rcases mul_eq_zero.mp hpM with h1 | h2
  · exact_mod_cast h1
  · exact absurd h2 (ne_of_gt hsqrtpos)

/-- **`√2, √3, √5` are linearly independent over `ℚ`.** If
`a·√2 + b·√3 + c·√5 = 0` with `a, b, c ∈ ℚ`, then `a = b = c = 0`. -/
theorem linearIndependent (a b c : ℚ)
    (h : (a : ℝ) * Real.sqrt 2 + (b : ℝ) * Real.sqrt 3 + (c : ℝ) * Real.sqrt 5 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have sq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have sq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have sq5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h35 : Real.sqrt 3 * Real.sqrt 5 = Real.sqrt 15 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]; norm_num
  -- Squaring `a·√2 = -(b·√3 + c·√5)` exposes the cross term `2bc·√15`.
  have key : 2 * (b : ℝ) * (c : ℝ) * Real.sqrt 15
      = 2 * (a : ℝ) ^ 2 - 3 * (b : ℝ) ^ 2 - 5 * (c : ℝ) ^ 2 := by
    have e1 : ((a : ℝ) * Real.sqrt 2) ^ 2
        = ((b : ℝ) * Real.sqrt 3 + (c : ℝ) * Real.sqrt 5) ^ 2 := by
      have hh : (a : ℝ) * Real.sqrt 2
          = -((b : ℝ) * Real.sqrt 3 + (c : ℝ) * Real.sqrt 5) := by linarith [h]
      rw [hh]; ring
    linear_combination -e1 + (a : ℝ) ^ 2 * sq2 - (b : ℝ) ^ 2 * sq3
      - (c : ℝ) ^ 2 * sq5 - 2 * (b : ℝ) * (c : ℝ) * h35
  -- `15` is not a square, so the only way out is `bc = 0`.
  have hbc : b * c = 0 := by
    by_contra hbc
    have hk : (2 * b * c : ℚ) ≠ 0 := fun hh => hbc (by linear_combination (1 / 2 : ℚ) * hh)
    refine sqrt_irrat_lin (m := 15) ns15 (2 * b * c)
      (2 * a ^ 2 - 3 * b ^ 2 - 5 * c ^ 2) hk ?_
    push_cast
    linear_combination key
  rcases mul_eq_zero.mp hbc with hb | hc
  · -- `b = 0`: reduce to `a·√2 + c·√5 = 0`.
    have h' : (a : ℝ) * Real.sqrt ((2 : ℕ) : ℝ) + (c : ℝ) * Real.sqrt ((5 : ℕ) : ℝ) = 0 := by
      rw [hb] at h; push_cast at h ⊢; linarith [h]
    obtain ⟨ha, hc⟩ := two_term_zero (M := 2) (N := 5) (by norm_num) ns10 a c h'
    exact ⟨ha, hb, hc⟩
  · -- `c = 0`: reduce to `a·√2 + b·√3 = 0`.
    have h' : (a : ℝ) * Real.sqrt ((2 : ℕ) : ℝ) + (b : ℝ) * Real.sqrt ((3 : ℕ) : ℝ) = 0 := by
      rw [hc] at h; push_cast at h ⊢; linarith [h]
    obtain ⟨ha, hb⟩ := two_term_zero (M := 2) (N := 3) (by norm_num) ns6 a b h'
    exact ⟨ha, hb, hc⟩

/-- **The eight conjugates are pairwise distinct.** More generally, the map
sending a rational sign vector `(ε₁, ε₂, ε₃)` to `ε₁√2 + ε₂√3 + ε₃√5` is
injective: equal values force equal coefficients.  Specializing each `εᵢ, δᵢ` to
`±1` shows the eight sign-conjugates `±√2 ± √3 ± √5` are pairwise distinct. -/
theorem conjugates_distinct (e₁ e₂ e₃ d₁ d₂ d₃ : ℚ)
    (h : (e₁ : ℝ) * Real.sqrt 2 + (e₂ : ℝ) * Real.sqrt 3 + (e₃ : ℝ) * Real.sqrt 5
       = (d₁ : ℝ) * Real.sqrt 2 + (d₂ : ℝ) * Real.sqrt 3 + (d₃ : ℝ) * Real.sqrt 5) :
    e₁ = d₁ ∧ e₂ = d₂ ∧ e₃ = d₃ := by
  obtain ⟨h1, h2, h3⟩ := linearIndependent (e₁ - d₁) (e₂ - d₂) (e₃ - d₃)
    (by push_cast; linear_combination h)
  exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2, sub_eq_zero.mp h3⟩

/-- Concrete instance: `α = √2 + √3 + √5` differs from its conjugate
`√2 + √3 - √5` (the simplest nontrivial sign flip). -/
theorem alpha_ne_conjugate :
    Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5 ≠ Real.sqrt 2 + Real.sqrt 3 - Real.sqrt 5 := by
  intro h
  -- Cast to the `±1` sign-vector form and apply `conjugates_distinct`.
  have h' : ((1 : ℚ) : ℝ) * Real.sqrt 2 + ((1 : ℚ) : ℝ) * Real.sqrt 3
        + ((1 : ℚ) : ℝ) * Real.sqrt 5
      = ((1 : ℚ) : ℝ) * Real.sqrt 2 + ((1 : ℚ) : ℝ) * Real.sqrt 3
        + ((-1 : ℚ) : ℝ) * Real.sqrt 5 := by push_cast; linarith [h]
  have := (conjugates_distinct 1 1 1 1 1 (-1) h').2.2
  norm_num at this

end Sqrt2Sqrt3Sqrt5MultiquadraticOQ04OQ01
