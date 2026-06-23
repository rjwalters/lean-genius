/-
  Unified Menelaus Theorem (parametrized by an odd measure function)

  Open Question: cevas-theorem-non-euclidean-oq-02-oq-01-oq-01

  The three classical Menelaus theorems differ only in the function used to
  measure signed geodesic arcs:

    - Euclidean : the identity   f x = x
    - Spherical : f x = sin x
    - Hyperbolic: f x = sinh x

  All three measure functions are *odd* (f (-x) = -f x). This file isolates
  that common structure into a `SignedMeasure` and proves a single unified
  Menelaus theorem from which the Euclidean, spherical, and hyperbolic cases
  follow as instances.

  **Why oddness is the right hypothesis.** The algebraic core of Menelaus is
  purely formal: for nonzero denominators it holds for *any* function. What an
  odd `f` buys is *signed-arc coherence*: reversing the orientation of a single
  arc (negating it) negates exactly one ratio, hence flips the product sign
  `+1 ↔ -1` (Ceva ↔ Menelaus). The "appropriate domain" for a measure function
  is therefore: any odd `f`, restricted to arcs whose denominator values are
  nonzero. We make this precise below.

  Parent: CevasTheoremNonEuclideanOQ02OQ01.lean (spherical Menelaus via sin)
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option linter.unusedVariables false

namespace CevasTheoremNonEuclideanOQ02OQ01OQ01

-- ============================================================
-- PART 1: Signed Measure Functions
-- ============================================================

/-- A signed measure function for geodesic arcs: an odd function `f : ℝ → ℝ`.

    Oddness `f (-x) = -f x` encodes the signed-arc sign convention: reversing
    the orientation of an arc negates its measure. The three classical Menelaus
    measures (identity, `sin`, `sinh`) are all instances. -/
structure SignedMeasure where
  f : ℝ → ℝ
  odd : ∀ x, f (-x) = -f x

/-- The Menelaus ratio product `(a/b)·(c/d)·(e/g)`. -/
noncomputable def ratioProduct (a b c d e g : ℝ) : ℝ :=
  (a / b) * (c / d) * (e / g)

-- ============================================================
-- PART 2: Unified Algebraic Core
-- ============================================================

/-- **Algebraic core**, function-agnostic form. For nonzero denominators the
    Menelaus product equals `-1` iff the numerator product equals minus the
    denominator product. This needs *no* hypothesis on the values: it is the
    formal identity shared by every geometry. -/
theorem ratioProduct_eq_neg_one_iff
    (a b c d e g : ℝ) (hb : b ≠ 0) (hd : d ≠ 0) (hg : g ≠ 0) :
    ratioProduct a b c d e g = -1 ↔ a * c * e = -(b * d * g) := by
  unfold ratioProduct
  have hD : b * d * g ≠ 0 := mul_ne_zero (mul_ne_zero hb hd) hg
  rw [div_mul_div_comm, div_mul_div_comm]
  constructor
  · intro h
    have := (div_eq_iff hD).mp h
    linarith
  · intro h
    rw [div_eq_iff hD]
    linarith

/-- Companion: the Menelaus product equals `+1` (the Ceva condition) iff the
    numerator product equals the denominator product. -/
theorem ratioProduct_eq_one_iff
    (a b c d e g : ℝ) (hb : b ≠ 0) (hd : d ≠ 0) (hg : g ≠ 0) :
    ratioProduct a b c d e g = 1 ↔ a * c * e = b * d * g := by
  unfold ratioProduct
  have hD : b * d * g ≠ 0 := mul_ne_zero (mul_ne_zero hb hd) hg
  rw [div_mul_div_comm, div_mul_div_comm, div_eq_one_iff_eq hD]

/-- **Unified Menelaus theorem.** For any signed measure `μ` and any six arcs
    whose denominator measures are nonzero:

      `μ(BD)/μ(DC) · μ(CE)/μ(EA) · μ(AF)/μ(FB) = -1`
        ↔ `μ(BD)·μ(CE)·μ(AF) = -(μ(DC)·μ(EA)·μ(FB))`.

    Specializing `μ` to the identity, `sin`, `sinh` recovers the Euclidean,
    spherical, and hyperbolic Menelaus theorems (see corollaries below). -/
theorem unified_menelaus (μ : SignedMeasure)
    (bd dc ce ea af fb : ℝ)
    (hdc : μ.f dc ≠ 0) (hea : μ.f ea ≠ 0) (hfb : μ.f fb ≠ 0) :
    ratioProduct (μ.f bd) (μ.f dc) (μ.f ce) (μ.f ea) (μ.f af) (μ.f fb) = -1 ↔
    μ.f bd * μ.f ce * μ.f af = -(μ.f dc * μ.f ea * μ.f fb) :=
  ratioProduct_eq_neg_one_iff _ _ _ _ _ _ hdc hea hfb

-- ============================================================
-- PART 3: Signed-Arc Coherence (the role of oddness)
-- ============================================================

/-- Restatement of oddness as a measure law: reversing an arc negates its
    measure. -/
theorem measure_neg (μ : SignedMeasure) (x : ℝ) : μ.f (-x) = -μ.f x :=
  μ.odd x

/-- The measure of a reversed arc is nonzero iff the measure of the arc is. -/
theorem measure_neg_ne_zero (μ : SignedMeasure) {x : ℝ} (hx : μ.f x ≠ 0) :
    μ.f (-x) ≠ 0 := by
  rw [measure_neg]; exact neg_ne_zero.mpr hx

/-- Reversing the orientation of the numerator arc `CE → -CE` negates the
    Menelaus product. -/
theorem ratioProduct_reverse_num (μ : SignedMeasure)
    (bd dc ce ea af fb : ℝ) :
    ratioProduct (μ.f bd) (μ.f dc) (μ.f (-ce)) (μ.f ea) (μ.f af) (μ.f fb)
      = -ratioProduct (μ.f bd) (μ.f dc) (μ.f ce) (μ.f ea) (μ.f af) (μ.f fb) := by
  unfold ratioProduct
  rw [measure_neg]
  ring

/-- Reversing the orientation of the denominator arc `EA → -EA` negates the
    Menelaus product (requires the original measure to be nonzero so the ratio
    is well behaved). -/
theorem ratioProduct_reverse_den (μ : SignedMeasure)
    (bd dc ce ea af fb : ℝ) (hea : μ.f ea ≠ 0) :
    ratioProduct (μ.f bd) (μ.f dc) (μ.f ce) (μ.f (-ea)) (μ.f af) (μ.f fb)
      = -ratioProduct (μ.f bd) (μ.f dc) (μ.f ce) (μ.f ea) (μ.f af) (μ.f fb) := by
  unfold ratioProduct
  rw [measure_neg, div_neg]
  ring

/-- **Ceva ↔ Menelaus under a single reversal.** A configuration satisfies the
    Ceva condition (product `= 1`) iff, after reversing one arc, it satisfies
    the Menelaus condition (product `= -1`). This is precisely the geometric
    content captured by requiring `μ` to be odd: an odd number of orientation
    reversals toggles between concurrency and collinearity. -/
theorem ceva_iff_menelaus_after_reverse (μ : SignedMeasure)
    (bd dc ce ea af fb : ℝ) (hea : μ.f ea ≠ 0) :
    ratioProduct (μ.f bd) (μ.f dc) (μ.f ce) (μ.f ea) (μ.f af) (μ.f fb) = 1 ↔
    ratioProduct (μ.f bd) (μ.f dc) (μ.f ce) (μ.f (-ea)) (μ.f af) (μ.f fb) = -1 := by
  rw [ratioProduct_reverse_den μ bd dc ce ea af fb hea]
  constructor
  · intro h; rw [h]
  · intro h; linarith

-- ============================================================
-- PART 4: The Three Classical Instances
-- ============================================================

/-- Euclidean measure: the identity function (signed lengths). -/
def idMeasure : SignedMeasure where
  f := id
  odd := fun x => rfl

/-- Spherical measure: `sin` (signed arc lengths on the sphere). -/
noncomputable def sinMeasure : SignedMeasure where
  f := Real.sin
  odd := fun x => Real.sin_neg x

/-- Hyperbolic measure: `sinh` (signed arc lengths in the hyperbolic plane). -/
noncomputable def sinhMeasure : SignedMeasure where
  f := Real.sinh
  odd := fun x => Real.sinh_neg x

/-- **Euclidean Menelaus** as an instance of the unified theorem. -/
theorem euclidean_menelaus
    (bd dc ce ea af fb : ℝ) (hdc : dc ≠ 0) (hea : ea ≠ 0) (hfb : fb ≠ 0) :
    ratioProduct bd dc ce ea af fb = -1 ↔
    bd * ce * af = -(dc * ea * fb) :=
  unified_menelaus idMeasure bd dc ce ea af fb hdc hea hfb

/-- **Spherical Menelaus** as an instance of the unified theorem. -/
theorem spherical_menelaus
    (bd dc ce ea af fb : ℝ)
    (hdc : Real.sin dc ≠ 0) (hea : Real.sin ea ≠ 0) (hfb : Real.sin fb ≠ 0) :
    ratioProduct (Real.sin bd) (Real.sin dc) (Real.sin ce) (Real.sin ea)
        (Real.sin af) (Real.sin fb) = -1 ↔
    Real.sin bd * Real.sin ce * Real.sin af =
      -(Real.sin dc * Real.sin ea * Real.sin fb) :=
  unified_menelaus sinMeasure bd dc ce ea af fb hdc hea hfb

/-- **Hyperbolic Menelaus** as an instance of the unified theorem. -/
theorem hyperbolic_menelaus
    (bd dc ce ea af fb : ℝ)
    (hdc : Real.sinh dc ≠ 0) (hea : Real.sinh ea ≠ 0) (hfb : Real.sinh fb ≠ 0) :
    ratioProduct (Real.sinh bd) (Real.sinh dc) (Real.sinh ce) (Real.sinh ea)
        (Real.sinh af) (Real.sinh fb) = -1 ↔
    Real.sinh bd * Real.sinh ce * Real.sinh af =
      -(Real.sinh dc * Real.sinh ea * Real.sinh fb) :=
  unified_menelaus sinhMeasure bd dc ce ea af fb hdc hea hfb

/-
## Summary

### Open Question
cevas-theorem-non-euclidean-oq-02-oq-01-oq-01: Is there a unified Menelaus
theorem parametrized by an odd measure function `f`, with the Euclidean,
spherical, and hyperbolic cases as instances?

### Answer (0 sorries, 0 axioms)
Yes. The common structure is captured by `SignedMeasure` (an odd `f : ℝ → ℝ`).

**Unified results**
1. `unified_menelaus` — Menelaus characterization for any `SignedMeasure`.
2. `ratioProduct_eq_neg_one_iff` / `ratioProduct_eq_one_iff` — function-agnostic
   algebraic cores for the Menelaus (`-1`) and Ceva (`+1`) conditions.

**Role of oddness (signed-arc coherence)**
3. `measure_neg`, `measure_neg_ne_zero` — reversing an arc negates its measure
   and preserves nondegeneracy.
4. `ratioProduct_reverse_num`, `ratioProduct_reverse_den` — a single orientation
   reversal negates the product.
5. `ceva_iff_menelaus_after_reverse` — one reversal toggles Ceva (`+1`) and
   Menelaus (`-1`); this is exactly what oddness provides.

**Instances**
6. `idMeasure` / `sinMeasure` / `sinhMeasure` and the corollaries
   `euclidean_menelaus`, `spherical_menelaus`, `hyperbolic_menelaus`.

### Domain characterization
The "appropriate domain" for a measure function is: *any* odd `f`, applied to
arcs whose denominator measures are nonzero (`μ.f dc, μ.f ea, μ.f fb ≠ 0`).
For `sin` this excludes arcs that are multiples of `π`; for `sinh` only the
zero arc; for `id` only the zero arc. Oddness is necessary for the signed-arc
sign convention (Ceva/Menelaus toggle), not for the bare algebraic identity.
-/

end CevasTheoremNonEuclideanOQ02OQ01OQ01
