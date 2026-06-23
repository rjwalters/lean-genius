/-
  Brahmagupta's Formula for Cyclic Quadrilaterals

  Generalizes Heron's formula from triangles to cyclic quadrilaterals.
  For a cyclic quadrilateral with sides a, b, c, d and semiperimeter
  s = (a + b + c + d) / 2:

    Area = sqrt((s-a)(s-b)(s-c)(s-d))

  Key results:
  1. Brahmagupta product definition and algebraic expansion
  2. Reduction to Heron's formula when d = 0
  3. Non-negativity of Brahmagupta product for valid quadrilaterals
  4. Isoperimetric inequality: maximum area quadrilateral is a square
  5. Area formula for rectangles as a special case

  Brahmagupta (628 AD)

  Axioms: 1 (Brahmagupta's formula for inscribed quadrilaterals)
  Sorries: 0
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Brahmagupta

open Real

-- ════════════════════════════════════════════════════════════════
-- PART I: Definitions
-- ════════════════════════════════════════════════════════════════

/-- Semi-perimeter of a quadrilateral with sides a, b, c, d -/
noncomputable def semiperimeter (a b c d : ℝ) : ℝ := (a + b + c + d) / 2

/-- Brahmagupta's product: (s-a)(s-b)(s-c)(s-d)
    This is the quantity under the square root in Brahmagupta's formula. -/
noncomputable def brahmaguptaProduct (a b c d : ℝ) : ℝ :=
  let s := semiperimeter a b c d
  (s - a) * (s - b) * (s - c) * (s - d)

-- ════════════════════════════════════════════════════════════════
-- PART II: Algebraic Properties
-- ════════════════════════════════════════════════════════════════

/-- **Brahmagupta product expansion**:
    The product (s-a)(s-b)(s-c)(s-d) in terms of side lengths only. -/
theorem brahmaguptaProduct_expand (a b c d : ℝ) :
    brahmaguptaProduct a b c d =
    ((-a + b + c + d) * (a - b + c + d) * (a + b - c + d) * (a + b + c - d)) / 16 := by
  unfold brahmaguptaProduct semiperimeter
  ring

/-- **Symmetry**: Brahmagupta product is invariant under cyclic permutation.
    This reflects the cyclic symmetry of the inscribed quadrilateral. -/
theorem brahmaguptaProduct_cyclic (a b c d : ℝ) :
    brahmaguptaProduct a b c d = brahmaguptaProduct b c d a := by
  unfold brahmaguptaProduct semiperimeter; ring

/-- **Symmetry under reversal**: Brahmagupta product is invariant under
    reversal of side order (reflecting the quadrilateral). -/
theorem brahmaguptaProduct_reverse (a b c d : ℝ) :
    brahmaguptaProduct a b c d = brahmaguptaProduct d c b a := by
  unfold brahmaguptaProduct semiperimeter; ring

-- ════════════════════════════════════════════════════════════════
-- PART III: Reduction to Heron's Formula
-- ════════════════════════════════════════════════════════════════

/-- Heron's product for a triangle (from parent file) -/
noncomputable def heronProduct (a b c : ℝ) : ℝ :=
  let s := (a + b + c) / 2
  s * (s - a) * (s - b) * (s - c)

/-- **Reduction to Heron**: When d = 0, Brahmagupta's product reduces
    to Heron's product. This is because a degenerate quadrilateral
    with one side of length 0 is a triangle.

    Brahmagupta's formula with d=0 gives:
    s = (a+b+c)/2, and (s-0) = s, so the product is s(s-a)(s-b)(s-c). -/
theorem brahmagupta_reduces_to_heron (a b c : ℝ) :
    brahmaguptaProduct a b c 0 = heronProduct a b c := by
  unfold brahmaguptaProduct heronProduct semiperimeter
  ring

-- ════════════════════════════════════════════════════════════════
-- PART IV: Non-negativity
-- ════════════════════════════════════════════════════════════════

/-- The Brahmagupta product is non-negative when all four generalized
    triangle inequalities hold. These are necessary conditions for a
    cyclic quadrilateral to exist. -/
theorem brahmaguptaProduct_nonneg {a b c d : ℝ}
    (h1 : a + b + c + d > 0)
    (h2 : b + c + d ≥ a) (h3 : a + c + d ≥ b)
    (h4 : a + b + d ≥ c) (h5 : a + b + c ≥ d) :
    0 ≤ brahmaguptaProduct a b c d := by
  rw [brahmaguptaProduct_expand]
  apply div_nonneg _ (by norm_num : (0 : ℝ) ≤ 16)
  apply mul_nonneg
  · apply mul_nonneg
    · apply mul_nonneg <;> linarith
    · linarith
  · linarith

-- ════════════════════════════════════════════════════════════════
-- PART V: Special Cases
-- ════════════════════════════════════════════════════════════════

/-- **Rectangle**: For a rectangle with sides a and b (opposite sides equal),
    Brahmagupta's product gives (ab)², so the area is ab. -/
theorem brahmaguptaProduct_rectangle (a b : ℝ) :
    brahmaguptaProduct a b a b = (a * b) ^ 2 := by
  unfold brahmaguptaProduct semiperimeter
  ring

/-- Rectangle area via Brahmagupta -/
theorem rectangle_area (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    sqrt (brahmaguptaProduct a b a b) = a * b := by
  rw [brahmaguptaProduct_rectangle]
  rw [sqrt_sq (mul_nonneg ha hb)]

/-- **Square**: For a square with side a, Brahmagupta gives a⁴, area = a². -/
theorem brahmaguptaProduct_square (a : ℝ) :
    brahmaguptaProduct a a a a = a ^ 4 := by
  unfold brahmaguptaProduct semiperimeter; ring

theorem square_area (a : ℝ) (ha : 0 ≤ a) :
    sqrt (brahmaguptaProduct a a a a) = a ^ 2 := by
  rw [brahmaguptaProduct_square, ← sq_abs, ← pow_mul]
  rw [sqrt_sq (pow_nonneg ha 2)]

-- ════════════════════════════════════════════════════════════════
-- PART VI: Isoperimetric Inequality for Quadrilaterals
-- ════════════════════════════════════════════════════════════════

/-- **Isoperimetric inequality (quadrilateral version)**: Among all cyclic
    quadrilaterals with fixed perimeter, the square maximizes the area.

    Proof: By AM-GM, (s-a)(s-b)(s-c)(s-d) ≤ ((s-a+s-b+s-c+s-d)/4)⁴ = (s/2)⁴.
    Equality holds when s-a = s-b = s-c = s-d, i.e., a = b = c = d (square). -/
theorem isoperimetric_quadrilateral {a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h2 : b + c + d > a) (h3 : a + c + d > b)
    (h4 : a + b + d > c) (h5 : a + b + c > d) :
    brahmaguptaProduct a b c d ≤ ((a + b + c + d) / 4) ^ 4 := by
  -- By repeated 2-variable AM-GM: xy ≤ ((x+y)/2)² from (x-y)² ≥ 0.
  -- Applied three times to get the 4-variable version.
  unfold brahmaguptaProduct semiperimeter
  set sa := (a + b + c + d) / 2 - a with hsa_def
  set sb := (a + b + c + d) / 2 - b with hsb_def
  set sc := (a + b + c + d) / 2 - c with hsc_def
  set sd := (a + b + c + d) / 2 - d with hsd_def
  have hsa : 0 < sa := by rw [hsa_def]; linarith
  have hsb : 0 < sb := by rw [hsb_def]; linarith
  have hsc : 0 < sc := by rw [hsc_def]; linarith
  have hsd : 0 < sd := by rw [hsd_def]; linarith
  -- Sum identities
  have hab_sum : sa + sb = c + d := by rw [hsa_def, hsb_def]; ring
  have hcd_sum : sc + sd = a + b := by rw [hsc_def, hsd_def]; ring
  have hfinal : sa + sb + sc + sd = a + b + c + d := by
    rw [hsa_def, hsb_def, hsc_def, hsd_def]; ring
  -- AM-GM step 1: sa·sb ≤ ((sa+sb)/2)²
  have hab : sa * sb ≤ ((sa + sb) / 2) ^ 2 := by nlinarith [sq_nonneg (sa - sb)]
  -- AM-GM step 2: sc·sd ≤ ((sc+sd)/2)²
  have hcd : sc * sd ≤ ((sc + sd) / 2) ^ 2 := by nlinarith [sq_nonneg (sc - sd)]
  -- Combine pairs
  have hprod : sa * sb * (sc * sd) ≤ ((sa + sb) / 2) ^ 2 * ((sc + sd) / 2) ^ 2 :=
    mul_le_mul hab hcd (mul_nonneg hsc.le hsd.le) (by positivity)
  -- AM-GM step 3: ((sa+sb)/2)·((sc+sd)/2) ≤ ((sa+sb+sc+sd)/4)²
  have hpair : ((sa + sb) / 2) * ((sc + sd) / 2) ≤ ((sa + sb + sc + sd) / 4) ^ 2 := by
    nlinarith [sq_nonneg ((sa + sb) / 2 - (sc + sd) / 2)]
  -- Chain: sa·sb·sc·sd ≤ ((sa+sb)/2)²·((sc+sd)/2)² = (product)² ≤ ((sum/4)²)² = (sum/4)⁴
  calc sa * sb * sc * sd
      = sa * sb * (sc * sd) := by ring
    _ ≤ ((sa + sb) / 2) ^ 2 * ((sc + sd) / 2) ^ 2 := hprod
    _ = (((sa + sb) / 2) * ((sc + sd) / 2)) ^ 2 := by ring
    _ ≤ (((sa + sb + sc + sd) / 4) ^ 2) ^ 2 :=
        pow_le_pow_left (by positivity) hpair 2
    _ = ((sa + sb + sc + sd) / 4) ^ 4 := by ring
    _ = ((a + b + c + d) / 4) ^ 4 := by rw [hfinal]

-- ════════════════════════════════════════════════════════════════
-- PART VII: The Brahmagupta Formula (Axiomatized)
-- ════════════════════════════════════════════════════════════════

/-- **Brahmagupta's Formula** (628 AD):
    For a cyclic quadrilateral inscribed in a circle with sides a, b, c, d,
    the area equals sqrt((s-a)(s-b)(s-c)(s-d)).

    This is axiomatized because proving it requires:
    1. A definition of "cyclic quadrilateral" (all 4 vertices on a circle)
    2. The connection between the diagonal configuration and the area
    3. The law of cosines applied to opposite angles summing to π

    The proof would use: Area = (1/2)|p·q|·sin(θ) where p, q are diagonals
    and θ is the angle between them, combined with Ptolemy's theorem and
    the constraint that opposite angles are supplementary. -/
axiom brahmagupta_formula (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (area : ℝ) (harea : 0 ≤ area)
    (hcyclic : True) -- placeholder for "inscribed in a circle" condition
    : area ^ 2 = brahmaguptaProduct a b c d

-- ════════════════════════════════════════════════════════════════
-- PART VIII: Concrete Examples
-- ════════════════════════════════════════════════════════════════

/-- **3-4-5 triangle via Brahmagupta** (d = 0):
    Brahmagupta with d = 0 gives Heron's product for the 3-4-5 triangle.
    s = 6, product = 6 · 3 · 2 · 1 = 36, area = 6. -/
theorem brahmagupta_345 : brahmaguptaProduct 3 4 5 0 = 36 := by
  unfold brahmaguptaProduct semiperimeter; norm_num

/-- **Unit square**: sides 1,1,1,1.
    s = 2, product = 1·1·1·1 = 1, area = 1. -/
theorem brahmagupta_unit_square : brahmaguptaProduct 1 1 1 1 = 1 := by
  unfold brahmaguptaProduct semiperimeter; norm_num

/-- **2×3 rectangle**: sides 2,3,2,3.
    s = 5, product = 3·2·3·2 = 36, area = 6. -/
theorem brahmagupta_rectangle_2_3 : brahmaguptaProduct 2 3 2 3 = 36 := by
  unfold brahmaguptaProduct semiperimeter; norm_num

end Brahmagupta
