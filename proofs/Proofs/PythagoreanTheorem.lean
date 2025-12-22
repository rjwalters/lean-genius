import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# Pythagorean Theorem: a² + b² = c²

A formal proof of the Pythagorean theorem using inner product spaces.
In a right triangle, the square of the hypotenuse equals the sum of
the squares of the other two sides.

This proof uses the elegant connection between perpendicularity (zero inner
product) and the norm formula in inner product spaces.

Historical Note: While Pythagoras (c. 570-495 BCE) gets credit, the theorem
was known to Babylonians 1000 years earlier and has 300+ known proofs.
-/

set_option linter.unusedVariables false

open scoped RealInnerProductSpace

-- ============================================================
-- PART 1: Vector Space Structure
-- ============================================================

-- We work in ℝ², the Euclidean plane
abbrev Vec2 := EuclideanSpace ℝ (Fin 2)

-- ============================================================
-- PART 2: Inner Product and Norm
-- ============================================================

-- The inner product ⟨v, w⟩ = v₁w₁ + v₂w₂
#check @inner ℝ Vec2 _

-- The squared norm ‖v‖² = v₁² + v₂²
-- norm : Vec2 → ℝ

-- Key property: ‖v‖² = ⟨v, v⟩
theorem norm_sq_eq_inner (v : Vec2) : ‖v‖^2 = inner v v := by
  rw [sq, ← real_inner_self_eq_norm_mul_norm]

-- ============================================================
-- PART 3: Perpendicularity
-- ============================================================

/-- Two vectors are perpendicular if their inner product is zero -/
def perpendicular (v w : Vec2) : Prop := inner v w = (0 : ℝ)

notation v " ⊥ " w => perpendicular v w

-- Perpendicularity is symmetric
theorem perp_symm (v w : Vec2) (h : v ⊥ w) : w ⊥ v := by
  unfold perpendicular at *
  rw [real_inner_comm]
  exact h

-- ============================================================
-- PART 4: The Pythagorean Theorem
-- ============================================================

/-- **The Pythagorean Theorem** (inner product space version)

For perpendicular vectors v and w:
  ‖v + w‖² = ‖v‖² + ‖w‖²

This says: if two sides of a right triangle are represented by v and w
(with the right angle between them), then the hypotenuse (v + w) satisfies
the Pythagorean relation. -/
theorem pythagorean_theorem (v w : Vec2) (h : v ⊥ w) :
    ‖v + w‖^2 = ‖v‖^2 + ‖w‖^2 := by
  -- Expand using ‖x‖² = ⟨x, x⟩
  simp only [sq]
  rw [← real_inner_self_eq_norm_mul_norm, ← real_inner_self_eq_norm_mul_norm,
      ← real_inner_self_eq_norm_mul_norm]
  -- Expand ⟨v + w, v + w⟩
  rw [inner_add_left, inner_add_right, inner_add_right]
  -- Use perpendicularity: ⟨v, w⟩ = 0
  unfold perpendicular at h
  have hw : inner w v = (0 : ℝ) := by rw [real_inner_comm]; exact h
  rw [h, hw]
  -- Simplify
  ring

-- ============================================================
-- PART 5: Classical Formulation
-- ============================================================

/-- Right triangle with legs a, b and hypotenuse c -/
structure RightTriangle where
  a : ℝ  -- length of first leg
  b : ℝ  -- length of second leg
  c : ℝ  -- length of hypotenuse
  a_pos : 0 < a
  b_pos : 0 < b
  c_pos : 0 < c
  pythagorean : a^2 + b^2 = c^2  -- the defining relation

/-- Classic examples of Pythagorean triples -/

-- 3² + 4² = 5²
theorem pythagorean_3_4_5 : (3 : ℝ)^2 + 4^2 = 5^2 := by norm_num

-- 5² + 12² = 13²
theorem pythagorean_5_12_13 : (5 : ℝ)^2 + 12^2 = 13^2 := by norm_num

-- 8² + 15² = 17²
theorem pythagorean_8_15_17 : (8 : ℝ)^2 + 15^2 = 17^2 := by norm_num

-- ============================================================
-- PART 6: Converse (Characterization of Right Angles)
-- ============================================================

/-- Converse of Pythagorean theorem: if ‖v + w‖² = ‖v‖² + ‖w‖², then v ⊥ w -/
theorem pythagorean_converse (v w : Vec2) :
    ‖v + w‖^2 = ‖v‖^2 + ‖w‖^2 → v ⊥ w := by
  intro h
  unfold perpendicular
  -- Expand ‖v + w‖² = ⟨v + w, v + w⟩ = ⟨v, v⟩ + 2⟨v, w⟩ + ⟨w, w⟩
  simp only [sq] at h
  rw [← real_inner_self_eq_norm_mul_norm, ← real_inner_self_eq_norm_mul_norm,
      ← real_inner_self_eq_norm_mul_norm] at h
  rw [inner_add_left, inner_add_right, inner_add_right] at h
  -- Now h says: ⟨v, v⟩ + ⟨v, w⟩ + ⟨w, v⟩ + ⟨w, w⟩ = ⟨v, v⟩ + ⟨w, w⟩
  -- Using ⟨w, v⟩ = ⟨v, w⟩, we get 2⟨v, w⟩ = 0
  simp only [real_inner_comm w v] at h
  rw [real_inner_comm]
  linarith

-- ============================================================
-- PART 7: Applications
-- ============================================================

/-!
### Distance in the Plane

The Pythagorean theorem underlies the Euclidean distance formula:
  d((x₁, y₁), (x₂, y₂)) = √((x₂-x₁)² + (y₂-y₁)²)

### Higher Dimensions

In ℝⁿ, the theorem generalizes:
  ‖v₁ + v₂ + ... + vₖ‖² = ‖v₁‖² + ‖v₂‖² + ... + ‖vₖ‖²
when all pairs of vectors are perpendicular.
-/

/-- Generalized Pythagorean theorem for mutually perpendicular vectors -/
theorem pythagorean_sum {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → Vec2}
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner (v i) (v j) = (0 : ℝ)) :
    ‖∑ i ∈ s, v i‖^2 = ∑ i ∈ s, ‖v i‖^2 := by
  -- Induction on the finite set
  induction s using Finset.induction_on with
  | empty =>
    -- Base case: empty sum
    simp
  | insert ha ih =>
    -- Induction step: add one element (a is the new element, s✝ is the smaller set)
    rename_i a s'
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    -- The key: v a ⊥ (∑ i ∈ s', v i) because v a ⊥ v i for all i ∈ s'
    have perp : inner (v a) (∑ i ∈ s', v i) = (0 : ℝ) := by
      rw [inner_sum]
      apply Finset.sum_eq_zero
      intro i hi
      apply h a (Finset.mem_insert_self a s') i (Finset.mem_insert_of_mem hi)
      intro eq
      rw [eq] at ha
      exact ha hi
    -- Apply Pythagorean theorem for two vectors
    have pyth : ‖v a + ∑ i ∈ s', v i‖^2 = ‖v a‖^2 + ‖∑ i ∈ s', v i‖^2 := by
      simp only [sq]
      rw [← real_inner_self_eq_norm_mul_norm, ← real_inner_self_eq_norm_mul_norm,
          ← real_inner_self_eq_norm_mul_norm]
      rw [inner_add_left, inner_add_right, inner_add_right]
      have perp_symm : inner (∑ i ∈ s', v i) (v a) = (0 : ℝ) := by
        rw [real_inner_comm]; exact perp
      rw [perp, perp_symm]
      ring
    rw [pyth]
    -- Apply induction hypothesis
    have ih' : ‖∑ i ∈ s', v i‖^2 = ∑ i ∈ s', ‖v i‖^2 := by
      apply ih
      intro i hi j hj ne
      apply h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) ne
    rw [ih']

-- Export main results
#check @pythagorean_theorem
#check @pythagorean_converse
#check @pythagorean_3_4_5
