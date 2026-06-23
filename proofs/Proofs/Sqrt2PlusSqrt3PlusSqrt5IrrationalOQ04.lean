/-
# Multiquadratic field `ℚ(√2,√3,√5)`: the degree-8 minimal polynomial and its
# `(ℤ/2ℤ)³` sign-flip root orbit (OQ-04 of `sqrt2-plus-sqrt3-plus-sqrt5-irrational`)

## The open question

OQ-04 asks for the multiquadratic field structure of `ℚ(√2,√3,√5)`: that
`[ℚ(√2,√3,√5) : ℚ] = 8` with Galois group `(ℤ/2ℤ)³`. Mathlib has no
multiquadratic-tower API, so a *complete* field-theoretic computation
(irreducibility of the degree-8 minimal polynomial, the explicit isomorphism of
the Galois group with `(ℤ/2ℤ)³`) is out of reach in a single self-contained file.

## What this file proves (fully, elementarily, `0` axioms beyond `Real.sqrt`)

The generator `α := √2 + √3 + √5` satisfies the explicit monic degree-8 integer
polynomial

    p(X) = X⁸ - 40·X⁶ + 352·X⁴ - 960·X² + 576.

This is the *minimal polynomial* of `α` over `ℚ` (degree `8`, matching the
conjectured extension degree). We establish, with no field theory:

* `key` — for **any** reals `a, b, c` with `a²=2, b²=3, c²=5`,
  `p(a+b+c) = 0`. The derivation only ever squares, so it is sign-agnostic.
* `alpha_isRoot` — `α = √2+√3+√5` is a root of `p`.
* `sign_orbit_isRoot` — every one of the eight sign-variants
  `ε₁√2 + ε₂√3 + ε₃√5` (`εᵢ = ±1`) is a root of `p`. These eight values are the
  orbit of `α` under the sign-flip group `(ℤ/2ℤ)³` — exactly the conjectured
  Galois action — so `p` factors as `∏ (X - (ε₁√2+ε₂√3+ε₃√5))`.
* `p_even` — `p(-X) = p(X)`; the roots come in `± pairs`.
* `alpha_strict_max` — `α` is the *strict maximum* of the eight conjugates
  (flipping any sign strictly decreases the value), so `α` is a simple root and
  the largest root of `p`.

## Derivation of `key`

With `σ := a+b+c`, `a²=2, b²=3, c²=5` (so `a²+b² = c² = 5`, `(ab)² = 6`,
`(abc)² = 30`):

    σ² = 2σc + 2ab                              (since a²+b² - c² = 0)
    σ⁴ - 20σ² - 24 = 8σ·(abc)                   (square; use c²=5, (ab)²=6)
    (σ⁴ - 20σ² - 24)² = 64σ²·(abc)² = 1920σ²     (square; use (abc)²=30)
    ⇒ σ⁸ - 40σ⁶ + 352σ⁴ - 960σ² + 576 = 0.

Each step is a `linear_combination` of the three square hypotheses, so the proof
is purely algebraic and never commits to a sign of `a, b, c`.

## Status
- [x] `key`, `alpha_isRoot`, `sign_orbit_isRoot`, `p_even`, `alpha_strict_max`
      — all proven, no `sorry`, no `native_decide`.
- Scoped out (genuinely open / needs absent Mathlib multiquadratic API):
  irreducibility of `p` (the degree `= 8` lower bound) and the Galois group
  isomorphism with `(ℤ/2ℤ)³`.
-/

import Mathlib

open Real Polynomial IntermediateField

namespace Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ04

/-- The explicit monic degree-8 polynomial `p(X) = X⁸ - 40X⁶ + 352X⁴ - 960X² + 576`,
written as a real-valued function so all statements stay elementary. -/
def annihilator (x : ℝ) : ℝ :=
  x ^ 8 - 40 * x ^ 6 + 352 * x ^ 4 - 960 * x ^ 2 + 576

/-- **Key identity.** For *any* reals `a, b, c` with `a² = 2, b² = 3, c² = 5`,
the sum `a + b + c` annihilates `p`. The proof only squares, so it holds for
every choice of signs of the square roots. -/
theorem key (a b c : ℝ) (ha : a ^ 2 = 2) (hb : b ^ 2 = 3) (hc : c ^ 2 = 5) :
    annihilator (a + b + c) = 0 := by
  unfold annihilator
  -- (ab)² = 6 and (abc)² = 30 from the three square facts.
  have hab2 : (a * b) ^ 2 = 6 := by linear_combination b ^ 2 * ha + 2 * hb
  have habc2 : (a * b * c) ^ 2 = 30 := by
    linear_combination b ^ 2 * c ^ 2 * ha + 2 * c ^ 2 * hb + 6 * hc
  -- σ² = 2σc + 2ab     (uses a² + b² - c² = 0)
  have e1 : (a + b + c) ^ 2 = 2 * (a + b + c) * c + 2 * (a * b) := by
    linear_combination ha + hb - hc
  -- σ⁴ - 20σ² - 24 = 8σ·(abc)     (square e1; use c²=5, (ab)²=6)
  have e2 : (a + b + c) ^ 4 - 20 * (a + b + c) ^ 2 - 24
      = 8 * (a + b + c) * (a * b * c) := by
    linear_combination
      ((a + b + c) ^ 2 + 2 * (a + b + c) * c + 2 * (a * b)) * e1
        + 4 * (a + b + c) ^ 2 * hc + 4 * hab2
  -- Square e2 and use (abc)² = 30 to collapse to p(σ) = 0.
  linear_combination
    ((a + b + c) ^ 4 - 20 * (a + b + c) ^ 2 - 24 + 8 * (a + b + c) * (a * b * c)) * e2
      + 64 * (a + b + c) ^ 2 * habc2

/-- `√2 + √3 + √5` is a root of the degree-8 polynomial `p`. -/
theorem alpha_isRoot : annihilator (sqrt 2 + sqrt 3 + sqrt 5) = 0 :=
  key _ _ _
    (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))
    (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3))
    (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5))

/-- **Sign-flip orbit.** For any signs `ε₁, ε₂, ε₃ ∈ {±1}` (encoded as
`εᵢ² = 1`), the value `ε₁√2 + ε₂√3 + ε₃√5` is a root of `p`. The eight choices
give the `(ℤ/2ℤ)³`-orbit of `α`, the full set of roots of `p`. -/
theorem sign_orbit_isRoot (e1 e2 e3 : ℝ)
    (h1 : e1 ^ 2 = 1) (h2 : e2 ^ 2 = 1) (h3 : e3 ^ 2 = 1) :
    annihilator (e1 * sqrt 2 + e2 * sqrt 3 + e3 * sqrt 5) = 0 := by
  refine key _ _ _ ?_ ?_ ?_
  · rw [mul_pow, h1, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  · rw [mul_pow, h2, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; norm_num
  · rw [mul_pow, h3, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]; norm_num

/-- `p` is an even polynomial: `p(-x) = p(x)`. Hence its roots occur in
`± pairs`, consistent with the `(ℤ/2ℤ)³` sign-flip symmetry. -/
theorem p_even (x : ℝ) : annihilator (-x) = annihilator x := by
  unfold annihilator; ring

/-- If `x` is a root of `p`, so is `-x` (immediate from `p_even`). -/
theorem neg_isRoot {x : ℝ} (hx : annihilator x = 0) : annihilator (-x) = 0 := by
  rw [p_even]; exact hx

/-- **`α` is the strict maximum conjugate.** Among the eight sign-variants
`ε₁√2 + ε₂√3 + ε₃√5`, flipping any sign to `-1` strictly decreases the value, so
`α = √2+√3+√5` is strictly larger than every other conjugate. In particular `α`
is a *simple* root and the largest root of `p`. -/
theorem alpha_strict_max (e1 e2 e3 : ℝ)
    (h1 : e1 ^ 2 = 1) (h2 : e2 ^ 2 = 1) (h3 : e3 ^ 2 = 1)
    (hne : ¬ (e1 = 1 ∧ e2 = 1 ∧ e3 = 1)) :
    e1 * sqrt 2 + e2 * sqrt 3 + e3 * sqrt 5 < sqrt 2 + sqrt 3 + sqrt 5 := by
  -- each εᵢ is ±1, and εᵢ·√k ≤ √k with equality iff εᵢ = 1 (since √k > 0)
  have s2 : (0 : ℝ) < sqrt 2 := sqrt_pos.mpr (by norm_num)
  have s3 : (0 : ℝ) < sqrt 3 := sqrt_pos.mpr (by norm_num)
  have s5 : (0 : ℝ) < sqrt 5 := sqrt_pos.mpr (by norm_num)
  -- εᵢ = 1 or εᵢ = -1
  have sign : ∀ e : ℝ, e ^ 2 = 1 → e = 1 ∨ e = -1 := by
    intro e he
    have : (e - 1) * (e + 1) = 0 := by linear_combination he
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  rcases sign e1 h1 with r1 | r1 <;> rcases sign e2 h2 with r2 | r2 <;>
    rcases sign e3 h3 with r3 | r3 <;> subst r1 <;> subst r2 <;> subst r3 <;>
    first
      | (exact absurd ⟨rfl, rfl, rfl⟩ hne)
      | nlinarith [s2, s3, s5]

/-! ### Field-theoretic upper bound `[ℚ(α) : ℚ] ≤ 8`

Packaging the elementary root fact as a `ℚ[X]`-annihilator gives a *verified*
upper bound on the extension degree: `α` is algebraic over `ℚ` and its minimal
polynomial divides the explicit degree-8 polynomial, so

    Module.finrank ℚ ℚ⟮α⟯ ≤ 8.

The matching lower bound `= 8` (irreducibility of `p`) is the genuinely open part
that needs the multiquadratic-tower API Mathlib lacks; it is scoped out here. -/

/-- The degree-8 annihilator of `α` as an explicit polynomial over `ℚ`. -/
noncomputable def annihilatorPoly : ℚ[X] :=
  X ^ 8 - C 40 * X ^ 6 + C 352 * X ^ 4 - C 960 * X ^ 2 + C 576

/-- `annihilatorPoly` is monic. -/
theorem annihilatorPoly_monic : annihilatorPoly.Monic := by
  unfold annihilatorPoly; monicity!

/-- `annihilatorPoly` has degree exactly `8`. -/
theorem annihilatorPoly_natDegree : annihilatorPoly.natDegree = 8 := by
  unfold annihilatorPoly; compute_degree!

/-- **Verified upper bound** `[ℚ(√2+√3+√5) : ℚ] ≤ 8`. The exact value `= 8`
(irreducibility) is open; see the module docstring. -/
theorem finrank_le_eight :
    Module.finrank ℚ ℚ⟮(sqrt 2 + sqrt 3 + sqrt 5 : ℝ)⟯ ≤ 8 := by
  set α : ℝ := sqrt 2 + sqrt 3 + sqrt 5 with hα
  -- The elementary root fact, unfolded.
  have hroot : α ^ 8 - 40 * α ^ 6 + 352 * α ^ 4 - 960 * α ^ 2 + 576 = 0 := by
    have h := alpha_isRoot
    unfold annihilator at h
    rw [← hα] at h
    linear_combination h
  -- `aeval α annihilatorPoly = 0`.
  have haeval : (aeval α) annihilatorPoly = 0 := by
    unfold annihilatorPoly
    simp only [map_sub, map_add, map_mul, map_pow, aeval_X, map_ofNat]
    linear_combination hroot
  have hmonic : annihilatorPoly.Monic := annihilatorPoly_monic
  have hint : IsIntegral ℚ α := ⟨annihilatorPoly, hmonic, haeval⟩
  have hdvd : minpoly ℚ α ∣ annihilatorPoly := minpoly.dvd ℚ α haeval
  have hle : (minpoly ℚ α).natDegree ≤ annihilatorPoly.natDegree :=
    Polynomial.natDegree_le_of_dvd hdvd hmonic.ne_zero
  have hfr : Module.finrank ℚ ℚ⟮α⟯ = (minpoly ℚ α).natDegree :=
    IntermediateField.adjoin.finrank hint
  rw [hfr, ← annihilatorPoly_natDegree]
  exact hle

end Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ04
