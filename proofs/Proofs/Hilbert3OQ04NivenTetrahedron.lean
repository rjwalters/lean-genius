/-
# Hilbert's Third Problem (oq-04): The Tetrahedral Angle is an Irrational Multiple of π

The dihedral angle of a regular tetrahedron is `θ = arccos(1/3) ≈ 70.53°`.  A key
step in Hilbert's third problem (the negative solution to the scissors-congruence
question for the cube and the regular tetrahedron) is that this angle is **not** a
rational multiple of `π`.  Equivalently, `arccos(1/3) / π` is irrational.

In the gallery's main Hilbert-3 development
(`Proofs/Hilbert3ScissorsCongruence.lean`) this fact was taken as an axiom:

  `axiom tetrahedron_angle_not_rational_pi : ¬ isRationalMultipleOfPi tetrahedronDihedralAngle`

This file **eliminates that axiom**.  Mathlib now contains Niven's theorem
(`niven`, in `Mathlib.NumberTheory.Niven`), which states that the only rational
values taken by `cos` at rational multiples of `π` are `{-1, -1/2, 0, 1/2, 1}`.
Since `cos (arccos (1/3)) = 1/3` is rational and lies outside that set, the angle
`arccos (1/3)` cannot be a rational multiple of `π`.

Everything below is fully machine-checked with no `axiom`/`sorry` and no
structure-encoded assumptions; the proof rests only on Mathlib (which proves
Niven's theorem via the integrality of `2 cos(qπ)`).

## Results
* `cos_arccos_one_third` : `cos (arccos (1/3)) = 1/3`.
* `arccos_one_third_not_rat_mul_pi` : `arccos (1/3)` is not of the form `r * π` for `r : ℚ`.
* `irrational_arccos_one_third_div_pi` : `arccos (1/3) / π` is irrational.
* `tetrahedron_angle_not_rational_pi` : the discharged Hilbert-3 axiom, stated against
  the same predicate `isRationalMultipleOfPi` used there.

## References
* I. Niven, *Irrational Numbers*, Carus Mathematical Monographs 11 (1956).
* Hilbert's third problem; Dehn invariant.
-/

import Mathlib.NumberTheory.Niven
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

namespace Hilbert3OQ04

open Real

/-- The cosine of the tetrahedral dihedral angle is `1/3`. -/
theorem cos_arccos_one_third : Real.cos (Real.arccos (1 / 3)) = 1 / 3 := by
  rw [Real.cos_arccos] <;> norm_num

/-- **Niven applied to the tetrahedral angle.**  The dihedral angle `arccos (1/3)`
of a regular tetrahedron is not a rational multiple of `π`.

If it were, `cos (arccos (1/3)) = 1/3` would be one of the five Niven values
`{-1, -1/2, 0, 1/2, 1}`, which it is not. -/
theorem arccos_one_third_not_rat_mul_pi :
    ¬ ∃ r : ℚ, Real.arccos (1 / 3) = (r : ℝ) * Real.pi := by
  intro hθ
  have hcos : ∃ q : ℚ, Real.cos (Real.arccos (1 / 3)) = (q : ℝ) :=
    ⟨1 / 3, by rw [cos_arccos_one_third]; norm_num⟩
  have hmem := niven hθ hcos
  rw [cos_arccos_one_third] at hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h | h | h <;> norm_num at h

/-- The dihedral angle of a regular tetrahedron, measured in units of `π`, is
irrational:  `arccos (1/3) / π ∉ ℚ`. -/
theorem irrational_arccos_one_third_div_pi :
    Irrational (Real.arccos (1 / 3) / Real.pi) := by
  rintro ⟨r, hr⟩
  -- `hr : (r : ℝ) = arccos (1/3) / π`
  refine arccos_one_third_not_rat_mul_pi ⟨r, ?_⟩
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [eq_comm, div_eq_iff hpi] at hr
  exact hr

/-- The scissors-congruence predicate used in `Proofs/Hilbert3ScissorsCongruence.lean`:
`θ` is a rational multiple of `π` when `θ * q = p * π` for integers `p`, `q` with `q ≠ 0`. -/
def isRationalMultipleOfPi (θ : ℝ) : Prop :=
  ∃ (p : ℤ) (q : ℤ), q ≠ 0 ∧ θ * q = p * Real.pi

/-- **Axiom elimination.**  The Hilbert-3 axiom
`tetrahedron_angle_not_rational_pi` is in fact a theorem: the tetrahedral angle
`arccos (1/3)` is not a rational multiple of `π`. -/
theorem tetrahedron_angle_not_rational_pi :
    ¬ isRationalMultipleOfPi (Real.arccos (1 / 3)) := by
  rintro ⟨p, q, hq, hpq⟩
  refine arccos_one_third_not_rat_mul_pi ⟨(p : ℚ) / (q : ℚ), ?_⟩
  have hqR : (q : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hq
  push_cast
  rw [div_mul_eq_mul_div, eq_div_iff hqR]
  linear_combination hpq

end Hilbert3OQ04
