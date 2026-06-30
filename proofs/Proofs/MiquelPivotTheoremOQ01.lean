import Mathlib

/-
# Miquel's Pivot Theorem (complex-number / cross-ratio proof)

## Open Question: miquel-pivot-theorem-oq-01

**Miquel's pivot theorem.** Let `ABC` be a triangle and let `X`, `Y`, `Z` lie on
the lines `BC`, `CA`, `AB` respectively. Then the three circles

  `(A Y Z)`,  `(B Z X)`,  `(C X Y)`

pass through a common point — the *Miquel point* `M`.

## Proof idea (this file)

We work in `ℂ` and use the classical fact that four points `a, b, c, d` are
concyclic-or-collinear iff their **cross-ratio**

  `(a,b ; c,d) = (a-c)(b-d) / ((a-d)(b-c))`

is real, and three points `a, b, c` are collinear iff `(a-c)/(b-c)` is real.

Rather than *construct* the Miquel point (an intersection of two circles), we
state the theorem in its sharp conditional form: assuming a point `M` lies on
two of the circles, it lies on the third. The whole proof rests on one
algebraic miracle — the product of the three Miquel cross-ratios is
**independent of `M`**:

  `(M,A;Y,Z) · (M,B;Z,X) · (M,C;X,Y)`
    `= (A-Z)(B-X)(C-Y) / ((A-Y)(B-Z)(C-X))`
    `= [(A-Z)/(B-Z)] · [(B-X)/(C-X)] · [(C-Y)/(A-Y)]`.

The three right-hand factors are exactly the collinearity ratios for
`Z ∈ AB`, `X ∈ BC`, `Y ∈ CA`, hence the product is real. Given that the first
two cross-ratios are real (M on the first two circles) and nonzero, the third
is real as a quotient of reals — i.e. `M` lies on the third circle. ∎

This is **axiom-free and sorry-free**: the realness predicate is closed under
products and quotients, and the cross-ratio cancellation is a pure field
identity (no complex conjugation needed).
-/

namespace MiquelPivotTheoremOQ01

/-- A complex number is real. -/
def IsReal (z : ℂ) : Prop := ∃ r : ℝ, z = (r : ℂ)

theorem IsReal.mul {z w : ℂ} (hz : IsReal z) (hw : IsReal w) : IsReal (z * w) := by
  obtain ⟨a, ha⟩ := hz; obtain ⟨b, hb⟩ := hw
  exact ⟨a * b, by rw [ha, hb]; push_cast; ring⟩

theorem IsReal.div {z w : ℂ} (hz : IsReal z) (hw : IsReal w) : IsReal (z / w) := by
  obtain ⟨a, ha⟩ := hz; obtain ⟨b, hb⟩ := hw
  exact ⟨a / b, by rw [ha, hb]; push_cast; ring⟩

/-- Cross-ratio `(a,b ; c,d) = (a-c)(b-d) / ((a-d)(b-c))`. -/
noncomputable def crossRatio (a b c d : ℂ) : ℂ := (a - c) * (b - d) / ((a - d) * (b - c))

/-- `a, b, c, d` concyclic-or-collinear: the cross-ratio is real. -/
def Concyclic (a b c d : ℂ) : Prop := IsReal (crossRatio a b c d)

/-- `a, b, c` collinear: `(a-c)/(b-c)` is real. -/
def Collinear (a b c : ℂ) : Prop := IsReal ((a - c) / (b - c))

/-- **Miquel's pivot theorem.**
Triangle `A B C`; `Z ∈ AB`, `X ∈ BC`, `Y ∈ CA`. If `M` lies on circles
`(A Y Z)` and `(B Z X)`, then it lies on circle `(C X Y)`. -/
theorem miquel_pivot
    (A B C X Y Z M : ℂ)
    (hAY : A ≠ Y) (hAZ : A ≠ Z) (hBX : B ≠ X) (hBZ : B ≠ Z)
    (hCX : C ≠ X) (hMX : M ≠ X) (hMY : M ≠ Y) (hMZ : M ≠ Z)
    (hZ : Collinear A B Z) (hX : Collinear B C X) (hY : Collinear C A Y)
    (h1 : Concyclic M A Y Z) (h2 : Concyclic M B Z X) :
    Concyclic M C X Y := by
  -- nonzero differences needed to clear denominators
  have eAY : A - Y ≠ 0 := sub_ne_zero.mpr hAY
  have eAZ : A - Z ≠ 0 := sub_ne_zero.mpr hAZ
  have eBX : B - X ≠ 0 := sub_ne_zero.mpr hBX
  have eBZ : B - Z ≠ 0 := sub_ne_zero.mpr hBZ
  have eCX : C - X ≠ 0 := sub_ne_zero.mpr hCX
  have eMX : M - X ≠ 0 := sub_ne_zero.mpr hMX
  have eMY : M - Y ≠ 0 := sub_ne_zero.mpr hMY
  have eMZ : M - Z ≠ 0 := sub_ne_zero.mpr hMZ
  -- the M-free product identity
  have key : crossRatio M A Y Z * crossRatio M B Z X * crossRatio M C X Y
      = ((A - Z) / (B - Z)) * ((B - X) / (C - X)) * ((C - Y) / (A - Y)) := by
    simp only [crossRatio]
    field_simp
  -- the first two cross-ratios are nonzero
  have hr1 : crossRatio M A Y Z ≠ 0 := by
    simp only [crossRatio]
    exact div_ne_zero (mul_ne_zero eMY eAZ) (mul_ne_zero eMZ eAY)
  have hr2 : crossRatio M B Z X ≠ 0 := by
    simp only [crossRatio]
    exact div_ne_zero (mul_ne_zero eMZ eBX) (mul_ne_zero eMX eBZ)
  -- collinearity ⟹ the right-hand product is real
  unfold Collinear at hZ hX hY
  have hRHS : IsReal (((A - Z) / (B - Z)) * ((B - X) / (C - X)) * ((C - Y) / (A - Y))) :=
    (hZ.mul hX).mul hY
  -- hence the cross-ratio product is real
  have hprod : IsReal (crossRatio M A Y Z * crossRatio M B Z X * crossRatio M C X Y) := by
    rw [key]; exact hRHS
  -- conclude: M lies on the third circle
  unfold Concyclic at h1 h2 ⊢
  have h12 : IsReal (crossRatio M A Y Z * crossRatio M B Z X) := h1.mul h2
  have hsplit : crossRatio M C X Y
      = (crossRatio M A Y Z * crossRatio M B Z X * crossRatio M C X Y)
          / (crossRatio M A Y Z * crossRatio M B Z X) := by
    rw [eq_div_iff (mul_ne_zero hr1 hr2)]; ring
  rw [hsplit]
  exact hprod.div h12

end MiquelPivotTheoremOQ01
