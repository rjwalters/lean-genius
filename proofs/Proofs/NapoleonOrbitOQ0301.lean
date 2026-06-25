import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-
# Napoleon's Theorem — OQ-03-OQ-01: Orbit structure of the iterated outer construction

## Research problem: napoleons-theorem-oq-03-oq-01

The parent entry `napoleons-theorem-oq-03` studies the *composition* of the outer
and inner Napoleon constructions and shows it annihilates a triangle's shape
(collapse to the centroid).  This leaf instead iterates the **single** outer
construction `T_out` and pins down the resulting orbit.

Let `T_out : ℂ³ → ℂ³` send a triangle `(z₀, z₁, z₂)` to its outer Napoleon triangle
`(G₀, G₁, G₂)`, where `Gₖ` is the center of the outer equilateral triangle on the
side opposite `zₖ`:

  `Gₖ = napCenter (the two vertices other than zₖ)`,
  `napCenter b c = (b+c)/2 + (i√3/6)·(c−b)`.

Write `g = (z₀+z₁+z₂)/3` for the centroid.  We prove:

1. **Centroid preserved** (`sum_Tout`, `centroid_Tout`): `T_out` does not move the
   centroid — the vertex sum is invariant.
2. **Point-reflection law** (`Tout_iterate_two_fst/snd/thd`): the *doubled* outer
   triangle `H = T_out²(z)` is the half-turn (180° rotation) of the *single*
   outer triangle about the common centroid: `Hₖ = 2g − Gₖ`.
3. **Period two** (`Tout_cube`, `Tout_iterate_four_eq_two`, `Tout_pow_four_eq_two`):
   `T_out³ = T_out`, hence `T_out⁴ = T_out²`; the orbit `T_out^n(z)` for `n ≥ 1` is
   periodic with period (dividing) two.
4. **Doubling is not idempotent** (`Tout_iterate_two_ne_self`): whenever the outer
   Napoleon triangle is nondegenerate (a vertex differs from the centroid),
   `T_out²(z) ≠ T_out(z)` — sharply contrasting the parent's outer∘inner collapse.

## Proof method

Every Napoleon vertex map is ℂ-affine, so each identity is a ℂ-polynomial
statement.  The only non-ring fact is that the displacement coefficient
`a = i√3/6` satisfies `a² = −1/12` (`disp_sq`).  The half-turn equivariance
(`napCenter_halfTurn`) is a pure `ring` identity (the coefficient cancels), and the
period-two structure is assembled from that and the reflection law — no degree-4
brute force, no real/imaginary splitting.
-/

namespace NapoleonOrbitOQ0301

open Complex Real

-- ============================================================
-- PART 0: Definitions
-- ============================================================

/-- The center of the outer equilateral triangle erected on the segment `(b, c)`:
    `(b+c)/2 + (i√3/6)·(c−b)`. -/
noncomputable def napCenter (b c : ℂ) : ℂ :=
  (b + c) / 2 + I * (↑(Real.sqrt 3) : ℂ) / 6 * (c - b)

/-- One outer Napoleon step on a triangle `z = (z₀, z₁, z₂)`: the `k`-th output
    vertex is the center of the equilateral triangle on the side opposite `zₖ`. -/
noncomputable def Tout (z : ℂ × ℂ × ℂ) : ℂ × ℂ × ℂ :=
  (napCenter z.2.1 z.2.2, napCenter z.2.2 z.1, napCenter z.1 z.2.1)

/-- Centroid of a triple of points. -/
noncomputable def centroid (z : ℂ × ℂ × ℂ) : ℂ := (z.1 + z.2.1 + z.2.2) / 3

@[simp] theorem Tout_fst (z : ℂ × ℂ × ℂ) : (Tout z).1 = napCenter z.2.1 z.2.2 := rfl
@[simp] theorem Tout_snd_fst (z : ℂ × ℂ × ℂ) : (Tout z).2.1 = napCenter z.2.2 z.1 := rfl
@[simp] theorem Tout_snd_snd (z : ℂ × ℂ × ℂ) : (Tout z).2.2 = napCenter z.1 z.2.1 := rfl

-- ============================================================
-- PART 1: The displacement-square identity (the only non-ring fact)
-- ============================================================

/-- `√3` squared, lifted to ℂ. -/
theorem sqrt3_sq : (↑(Real.sqrt 3) : ℂ) ^ 2 = (3 : ℂ) := by
  have h : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [← Complex.ofReal_pow, h]; norm_num

/-- The Napoleon displacement coefficient `a = i√3/6` squares to `−1/12`. -/
theorem disp_sq : (I * (↑(Real.sqrt 3) : ℂ) / 6) ^ 2 = -1 / 12 := by
  rw [div_pow, mul_pow, Complex.I_sq, sqrt3_sq]; norm_num

-- ============================================================
-- PART 2: Centroid is preserved
-- ============================================================

/-- The outer Napoleon step preserves the vertex sum (hence the centroid). -/
theorem sum_Tout (z : ℂ × ℂ × ℂ) :
    (Tout z).1 + (Tout z).2.1 + (Tout z).2.2 = z.1 + z.2.1 + z.2.2 := by
  simp only [Tout_fst, Tout_snd_fst, Tout_snd_snd, napCenter]; ring

/-- The outer Napoleon step preserves the centroid. -/
theorem centroid_Tout (z : ℂ × ℂ × ℂ) : centroid (Tout z) = centroid z := by
  simp only [centroid]; rw [sum_Tout]

-- ============================================================
-- PART 3: Half-turn equivariance of `napCenter`
-- ============================================================

/-- `napCenter` is equivariant under the half-turn `x ↦ 2g − x` about any center `g`:
    reflecting both endpoints through `g` reflects the center through `g`.  Pure
    `ring` identity — the displacement coefficient cancels. -/
theorem napCenter_halfTurn (g b c : ℂ) :
    napCenter (2 * g - b) (2 * g - c) = 2 * g - napCenter b c := by
  simp only [napCenter]; ring

-- ============================================================
-- PART 4: The point-reflection law  Hₖ = 2g − Gₖ
-- ============================================================

/-- First vertex of the doubled outer triangle is the half-turn of the first vertex
    of the single outer triangle about the centroid. -/
theorem Tout_iterate_two_fst (z : ℂ × ℂ × ℂ) :
    (Tout (Tout z)).1 = 2 * centroid z - (Tout z).1 := by
  simp only [Tout_fst, Tout_snd_fst, Tout_snd_snd, napCenter, centroid]
  linear_combination (z.2.1 + z.2.2 - 2 * z.1) * disp_sq

/-- Second vertex: the half-turn law. -/
theorem Tout_iterate_two_snd (z : ℂ × ℂ × ℂ) :
    (Tout (Tout z)).2.1 = 2 * centroid z - (Tout z).2.1 := by
  simp only [Tout_fst, Tout_snd_fst, Tout_snd_snd, napCenter, centroid]
  linear_combination (z.2.2 + z.1 - 2 * z.2.1) * disp_sq

/-- Third vertex: the half-turn law. -/
theorem Tout_iterate_two_thd (z : ℂ × ℂ × ℂ) :
    (Tout (Tout z)).2.2 = 2 * centroid z - (Tout z).2.2 := by
  simp only [Tout_fst, Tout_snd_fst, Tout_snd_snd, napCenter, centroid]
  linear_combination (z.1 + z.2.1 - 2 * z.2.2) * disp_sq

/-- Packaged: the doubled outer triangle `T_out²(z)` is the half-turn of the single
    outer triangle `T_out(z)` about the common centroid. -/
theorem Tout_iterate_two (z : ℂ × ℂ × ℂ) :
    Tout (Tout z) =
      (2 * centroid z - (Tout z).1,
       2 * centroid z - (Tout z).2.1,
       2 * centroid z - (Tout z).2.2) := by
  rw [Prod.ext_iff, Prod.ext_iff]
  exact ⟨Tout_iterate_two_fst z, Tout_iterate_two_snd z, Tout_iterate_two_thd z⟩

-- ============================================================
-- PART 5: Period two — T_out³ = T_out, hence T_out⁴ = T_out²
-- ============================================================

/-- **Period two.**  Applying the outer Napoleon construction three times equals
    applying it once: `T_out³ = T_out`.  Proof: `T_out²(z)` is the half-turn of
    `T_out(z)` about the centroid (PART 4); applying `T_out` once more, half-turn
    equivariance (PART 3) turns it back, recovering `T_out(z)`. -/
theorem Tout_cube (z : ℂ × ℂ × ℂ) : Tout (Tout (Tout z)) = Tout z := by
  have h1 := Tout_iterate_two_fst z
  have h2 := Tout_iterate_two_snd z
  have h3 := Tout_iterate_two_thd z
  rw [Prod.ext_iff, Prod.ext_iff]
  refine ⟨?_, ?_, ?_⟩
  · rw [Tout_fst, h2, h3, napCenter_halfTurn, ← Tout_fst (Tout z), h1]; ring
  · rw [Tout_snd_fst, h3, h1, napCenter_halfTurn, ← Tout_snd_fst (Tout z), h2]; ring
  · rw [Tout_snd_snd, h1, h2, napCenter_halfTurn, ← Tout_snd_snd (Tout z), h3]; ring

/-- `T_out⁴ = T_out²`: the orbit stabilises into a period-two cycle. -/
theorem Tout_iterate_four_eq_two (z : ℂ × ℂ × ℂ) :
    Tout (Tout (Tout (Tout z))) = Tout (Tout z) :=
  Tout_cube (Tout z)

/-- Iterate form: `T_out^[4] = T_out^[2]`. -/
theorem Tout_pow_four_eq_two : Tout^[4] = Tout^[2] := by
  funext z
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
  exact Tout_iterate_four_eq_two z

-- ============================================================
-- PART 6: Doubling is not idempotent (period exactly two on nondegenerate input)
-- ============================================================

/-- If the outer Napoleon triangle is nondegenerate — its first vertex differs from
    the centroid — then the doubled construction genuinely differs from the single
    one: `T_out²(z) ≠ T_out(z)`.  Equality would force every outer vertex onto the
    centroid (the Napoleon triangle collapsing to a point).  This contrasts sharply
    with the parent entry's outer∘inner collapse, which always degenerates. -/
theorem Tout_iterate_two_ne_self (z : ℂ × ℂ × ℂ)
    (h : (Tout z).1 ≠ centroid z) : Tout (Tout z) ≠ Tout z := by
  intro hc
  apply h
  have e : (Tout (Tout z)).1 = (Tout z).1 := by rw [hc]
  rw [Tout_iterate_two_fst z] at e
  linear_combination (-1 / 2 : ℂ) * e

-- ============================================================
-- PART 7: Concrete sanity check
-- ============================================================

/-- On the degenerate triangle `(0, 0, 0)` every Napoleon vertex is the centroid `0`,
    so the orbit is constant and `T_out²` does equal `T_out` (the nondegeneracy
    hypothesis of `Tout_iterate_two_ne_self` is necessary). -/
theorem Tout_zero : Tout (0, 0, 0) = (0, 0, 0) := by
  simp only [Tout, napCenter]; norm_num

end NapoleonOrbitOQ0301
