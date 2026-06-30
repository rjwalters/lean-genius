import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-
# Napoleon's Theorem — OQ-03: Spectral Complementarity and Shape Annihilation

## Research Problem: napoleons-theorem-oq-03

The sibling file `NapoleonsTheoremOQ02.lean` recasts Napoleon's theorem in the
**discrete Fourier basis**: the outer Napoleon construction acts diagonally on the
3-point DFT of the vertices as

  X₀ ↦ X₀   (centroid preserved),   X₁ ↦ -X₁,   X₂ ↦ 0   (frequency-2 zeroed),

and the inner construction acts as

  X₀ ↦ X₀,   X₁ ↦ 0   (frequency-1 zeroed),   X₂ ↦ -X₂.

So the two constructions are **complementary spectral filters**: each kills exactly
one of the two non-DC frequencies and negates the other.

## What This File Proves (the open question)

OQ-02 states each filter's action *separately*. The natural structural follow-up:
**what happens when you compose them?**

Spectrally the answer is immediate. Composing outer ∘ inner sends

  X₁ ↦ 0 (inner) ↦ -0 = 0 (outer),     X₂ ↦ -X₂ (inner) ↦ 0 (outer),

so *both* non-DC frequencies vanish, leaving only X₀.  A triangle with X₁ = X₂ = 0
is the **constant triangle**: its three vertices coincide at the centroid
X₀/3 = (z₁+z₂+z₃)/3.  The same holds for inner ∘ outer.

In other words: **performing both Napoleon constructions, in either order,
annihilates the triangle's shape entirely — the result degenerates to the single
point at the original centroid.**  This is the sharp structural statement of the
complementarity that OQ-02 only hinted at.

## Self-contained

The vertex definitions (`napoleonCenter`, `G₁ … G₃`, `innerNapoleonCenter`,
`G₁' … G₃'`) are reproduced here verbatim from the parent `NapoleonsTheorem.lean`
so this file stands alone.

## Proof method

Every Napoleon vertex map is ℂ-affine in the input vertices, so each composed
vertex is a ℂ-polynomial identity.  The *only* non-ring fact needed is that the
common displacement coefficient `a = i√3/6` satisfies `a² = -1/12` (`disp_sq`
below, from `Complex.I_sq` and `sqrt3_sq`).  Each collapse is then closed by a
single deterministic `linear_combination (…) * disp_sq` — no case analysis, no
real/imaginary splitting.
-/

namespace NapoleonsTheoremOQ03

open Complex Real

-- ============================================================
-- PART 0: Napoleon vertex definitions (reproduced from parent)
-- ============================================================

/-- The centroid of the **outer** equilateral triangle erected on side (b, c):
    `(b+c)/2 + i√3/6·(c-b)`. -/
noncomputable def napoleonCenter (b c : ℂ) : ℂ :=
  (b + c) / 2 + I * (↑(Real.sqrt 3) : ℂ) / 6 * (c - b)

/-- Outer Napoleon vertices: `Gₖ` is the centroid of the outer equilateral triangle
    on the side opposite `zₖ`. -/
noncomputable def G₁ (z₁ z₂ z₃ : ℂ) : ℂ := napoleonCenter z₂ z₃
noncomputable def G₂ (z₁ z₂ z₃ : ℂ) : ℂ := napoleonCenter z₃ z₁
noncomputable def G₃ (z₁ z₂ z₃ : ℂ) : ℂ := napoleonCenter z₁ z₂

/-- The centroid of the **inner** equilateral triangle on side (b, c): the opposite
    displacement direction, `(b+c)/2 - i√3/6·(c-b)`. -/
noncomputable def innerNapoleonCenter (b c : ℂ) : ℂ :=
  (b + c) / 2 - I * (↑(Real.sqrt 3) : ℂ) / 6 * (c - b)

/-- Inner Napoleon vertices. -/
noncomputable def G₁' (z₁ z₂ z₃ : ℂ) : ℂ := innerNapoleonCenter z₂ z₃
noncomputable def G₂' (z₁ z₂ z₃ : ℂ) : ℂ := innerNapoleonCenter z₃ z₁
noncomputable def G₃' (z₁ z₂ z₃ : ℂ) : ℂ := innerNapoleonCenter z₁ z₂

-- ============================================================
-- PART 1: The displacement-square identity
-- ============================================================

/-- `√3` squared, lifted to ℂ. -/
theorem sqrt3_sq : (↑(Real.sqrt 3) : ℂ) ^ 2 = (3 : ℂ) := by
  have h : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [← Complex.ofReal_pow, h]
  norm_num

/-- The Napoleon displacement coefficient `a = i√3/6` squares to `-1/12`:
    `a² = i²·(√3)²/36 = (-1)(3)/36 = -1/12`.  This is the single non-ring fact
    behind every collapse below. -/
theorem disp_sq : (I * (↑(Real.sqrt 3) : ℂ) / 6) ^ 2 = -1 / 12 := by
  rw [div_pow, mul_pow, Complex.I_sq, sqrt3_sq]
  norm_num

-- ============================================================
-- PART 2: outer ∘ inner collapses every vertex to the centroid
-- ============================================================

/-- First outer-Napoleon vertex of the inner Napoleon triangle equals the centroid. -/
theorem outer_inner_G₁ (z₁ z₂ z₃ : ℂ) :
    G₁ (G₁' z₁ z₂ z₃) (G₂' z₁ z₂ z₃) (G₃' z₁ z₂ z₃) = (z₁ + z₂ + z₃) / 3 := by
  simp only [G₁, G₂', G₃', napoleonCenter, innerNapoleonCenter]
  linear_combination (2 * z₁ - z₂ - z₃) * disp_sq

/-- Second outer-Napoleon vertex of the inner Napoleon triangle equals the centroid. -/
theorem outer_inner_G₂ (z₁ z₂ z₃ : ℂ) :
    G₂ (G₁' z₁ z₂ z₃) (G₂' z₁ z₂ z₃) (G₃' z₁ z₂ z₃) = (z₁ + z₂ + z₃) / 3 := by
  simp only [G₂, G₁', G₃', napoleonCenter, innerNapoleonCenter]
  linear_combination (-z₁ + 2 * z₂ - z₃) * disp_sq

/-- Third outer-Napoleon vertex of the inner Napoleon triangle equals the centroid. -/
theorem outer_inner_G₃ (z₁ z₂ z₃ : ℂ) :
    G₃ (G₁' z₁ z₂ z₃) (G₂' z₁ z₂ z₃) (G₃' z₁ z₂ z₃) = (z₁ + z₂ + z₃) / 3 := by
  simp only [G₃, G₁', G₂', napoleonCenter, innerNapoleonCenter]
  linear_combination (-z₁ - z₂ + 2 * z₃) * disp_sq

-- ============================================================
-- PART 3: inner ∘ outer collapses every vertex to the centroid
-- ============================================================

/-- First inner-Napoleon vertex of the outer Napoleon triangle equals the centroid. -/
theorem inner_outer_G₁ (z₁ z₂ z₃ : ℂ) :
    G₁' (G₁ z₁ z₂ z₃) (G₂ z₁ z₂ z₃) (G₃ z₁ z₂ z₃) = (z₁ + z₂ + z₃) / 3 := by
  simp only [G₁', G₂, G₃, napoleonCenter, innerNapoleonCenter]
  linear_combination (2 * z₁ - z₂ - z₃) * disp_sq

/-- Second inner-Napoleon vertex of the outer Napoleon triangle equals the centroid. -/
theorem inner_outer_G₂ (z₁ z₂ z₃ : ℂ) :
    G₂' (G₁ z₁ z₂ z₃) (G₂ z₁ z₂ z₃) (G₃ z₁ z₂ z₃) = (z₁ + z₂ + z₃) / 3 := by
  simp only [G₂', G₃, G₁, napoleonCenter, innerNapoleonCenter]
  linear_combination (-z₁ + 2 * z₂ - z₃) * disp_sq

/-- Third inner-Napoleon vertex of the outer Napoleon triangle equals the centroid. -/
theorem inner_outer_G₃ (z₁ z₂ z₃ : ℂ) :
    G₃' (G₁ z₁ z₂ z₃) (G₂ z₁ z₂ z₃) (G₃ z₁ z₂ z₃) = (z₁ + z₂ + z₃) / 3 := by
  simp only [G₃', G₁, G₂, napoleonCenter, innerNapoleonCenter]
  linear_combination (-z₁ - z₂ + 2 * z₃) * disp_sq

-- ============================================================
-- PART 4: Capstone — shape annihilation in either order
-- ============================================================

/-- **Shape annihilation (outer ∘ inner).**  Applying the outer Napoleon
    construction to the inner Napoleon triangle of `z₁z₂z₃` collapses all three
    vertices onto the single point `(z₁+z₂+z₃)/3`, the centroid of the original
    triangle.  The composed "triangle" is degenerate: it has no shape left. -/
theorem outer_of_inner_collapses (z₁ z₂ z₃ : ℂ) :
    G₁ (G₁' z₁ z₂ z₃) (G₂' z₁ z₂ z₃) (G₃' z₁ z₂ z₃) = (z₁ + z₂ + z₃) / 3 ∧
    G₂ (G₁' z₁ z₂ z₃) (G₂' z₁ z₂ z₃) (G₃' z₁ z₂ z₃) = (z₁ + z₂ + z₃) / 3 ∧
    G₃ (G₁' z₁ z₂ z₃) (G₂' z₁ z₂ z₃) (G₃' z₁ z₂ z₃) = (z₁ + z₂ + z₃) / 3 :=
  ⟨outer_inner_G₁ z₁ z₂ z₃, outer_inner_G₂ z₁ z₂ z₃, outer_inner_G₃ z₁ z₂ z₃⟩

/-- **Shape annihilation (inner ∘ outer).**  The symmetric statement: applying the
    inner Napoleon construction to the outer Napoleon triangle also collapses all
    three vertices onto the original centroid. -/
theorem inner_of_outer_collapses (z₁ z₂ z₃ : ℂ) :
    G₁' (G₁ z₁ z₂ z₃) (G₂ z₁ z₂ z₃) (G₃ z₁ z₂ z₃) = (z₁ + z₂ + z₃) / 3 ∧
    G₂' (G₁ z₁ z₂ z₃) (G₂ z₁ z₂ z₃) (G₃ z₁ z₂ z₃) = (z₁ + z₂ + z₃) / 3 ∧
    G₃' (G₁ z₁ z₂ z₃) (G₂ z₁ z₂ z₃) (G₃ z₁ z₂ z₃) = (z₁ + z₂ + z₃) / 3 :=
  ⟨inner_outer_G₁ z₁ z₂ z₃, inner_outer_G₂ z₁ z₂ z₃, inner_outer_G₃ z₁ z₂ z₃⟩

/-- **The two constructions commute on shape: both orders give the same point.**
    Outer-of-inner and inner-of-outer land on the *same* degenerate triangle (the
    centroid), so the composed maps agree vertex-by-vertex. -/
theorem outer_inner_eq_inner_outer (z₁ z₂ z₃ : ℂ) :
    G₁ (G₁' z₁ z₂ z₃) (G₂' z₁ z₂ z₃) (G₃' z₁ z₂ z₃) =
      G₁' (G₁ z₁ z₂ z₃) (G₂ z₁ z₂ z₃) (G₃ z₁ z₂ z₃) ∧
    G₂ (G₁' z₁ z₂ z₃) (G₂' z₁ z₂ z₃) (G₃' z₁ z₂ z₃) =
      G₂' (G₁ z₁ z₂ z₃) (G₂ z₁ z₂ z₃) (G₃ z₁ z₂ z₃) ∧
    G₃ (G₁' z₁ z₂ z₃) (G₂' z₁ z₂ z₃) (G₃' z₁ z₂ z₃) =
      G₃' (G₁ z₁ z₂ z₃) (G₂ z₁ z₂ z₃) (G₃ z₁ z₂ z₃) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [outer_inner_G₁, inner_outer_G₁]
  · rw [outer_inner_G₂, inner_outer_G₂]
  · rw [outer_inner_G₃, inner_outer_G₃]

/-- **Degeneracy certificate.**  After the double construction the three vertices
    are pairwise equal — the strongest sense in which the shape is destroyed. -/
theorem outer_of_inner_degenerate (z₁ z₂ z₃ : ℂ) :
    G₁ (G₁' z₁ z₂ z₃) (G₂' z₁ z₂ z₃) (G₃' z₁ z₂ z₃) =
      G₂ (G₁' z₁ z₂ z₃) (G₂' z₁ z₂ z₃) (G₃' z₁ z₂ z₃) ∧
    G₂ (G₁' z₁ z₂ z₃) (G₂' z₁ z₂ z₃) (G₃' z₁ z₂ z₃) =
      G₃ (G₁' z₁ z₂ z₃) (G₂' z₁ z₂ z₃) (G₃' z₁ z₂ z₃) := by
  constructor
  · rw [outer_inner_G₁, outer_inner_G₂]
  · rw [outer_inner_G₂, outer_inner_G₃]

/-- Centroid of the outer Napoleon triangle equals the original centroid
    (reproduced here so this file is self-contained). -/
theorem napoleon_centroid_eq_original (z₁ z₂ z₃ : ℂ) :
    (G₁ z₁ z₂ z₃ + G₂ z₁ z₂ z₃ + G₃ z₁ z₂ z₃) / 3 = (z₁ + z₂ + z₃) / 3 := by
  simp only [G₁, G₂, G₃, napoleonCenter]
  ring

/-- **Centroid is the unique surviving invariant.**  The annihilated triangle sits
    exactly at the original centroid, recovering — and sharpening — centroid
    preservation: not merely the centroid is preserved, but *everything else is
    destroyed*. -/
theorem doubled_napoleon_is_centroid (z₁ z₂ z₃ : ℂ) :
    G₁ (G₁' z₁ z₂ z₃) (G₂' z₁ z₂ z₃) (G₃' z₁ z₂ z₃) =
      (G₁ z₁ z₂ z₃ + G₂ z₁ z₂ z₃ + G₃ z₁ z₂ z₃) / 3 := by
  rw [outer_inner_G₁, napoleon_centroid_eq_original]

end NapoleonsTheoremOQ03
