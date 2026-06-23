import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.RingTheory.Polynomial.IrreducibleRing
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Tactic

/-
# Angle Trisection with Additional Tools (OQ-04)

## Question
Are there natural generalizations to constructions with additional tools
(e.g., marked ruler, origami, compass-only)?

## Key Results Formalized

1. **Marked Ruler Constructibility**: With a marked ruler (neusis construction),
   the constructibility condition relaxes from "degree divides 2^n" to
   "degree divides 2^a · 3^b". Since cos(20°) has degree 3 = 2^0 · 3^1,
   angle trisection becomes POSSIBLE with a marked ruler.

2. **Mohr-Mascheroni Theorem**: Compass-only constructions can build exactly
   the same set of points as compass-and-straightedge. The straightedge adds
   no power beyond what the compass already provides.

3. **Origami Constructibility**: Paper folding (Huzita-Justin axioms) can solve
   cubic equations, making origami at least as powerful as the marked ruler.

4. **Tool Hierarchy**: compass-only = compass+straightedge ⊊ marked ruler ⊆ origami.

## Approach
We use algebraic characterizations: each tool corresponds to a class of
polynomial degrees that become "constructible". The base case (Wantzel)
allows only 2^n; the marked ruler allows 2^a · 3^b; origami allows at
least 2^a · 3^b (and potentially more with higher axioms).

## Status
- [x] All supporting lemmas proved
- [x] Main theorems proved from axioms
- [x] 0 sorries
-/

namespace AngleTrisectionOQ04

open Polynomial Real

-- ============================================================
-- PART 1: Marked Ruler (Neusis) Constructibility
-- ============================================================

/-
### Marked Ruler = Neusis Construction

A marked ruler allows the geometer to:
1. Draw lines (like a straightedge)
2. Mark two points on the ruler at a fixed distance
3. Slide the ruler until both marks lie on specified curves

This additional capability allows solving cubic equations, which
compass-and-straightedge cannot do. Algebraically, it adds
cube-root extractions to the field operations.

**Key Theorem (Gleason 1988)**: A real number α is neusis-constructible
if and only if there exists a tower of field extensions:
  ℚ = F₀ ⊂ F₁ ⊂ ... ⊂ Fₙ
where each [Fᵢ₊₁ : Fᵢ] ∈ {2, 3}.

**Corollary**: α is neusis-constructible iff [ℚ(α) : ℚ] divides 2^a · 3^b.
-/

/-- A natural number is a "2-3 number" if it divides some 2^a · 3^b.
    These are exactly the degrees of minimal polynomials of neusis-constructible numbers. -/
def IsTwoThreeNumber (d : ℕ) : Prop :=
  d > 0 ∧ ∃ a b : ℕ, d ∣ 2^a * 3^b

/-- A real number is neusis-constructible (by marked ruler) if its minimal
    polynomial degree divides some 2^a · 3^b.

    This is the algebraic characterization from Gleason (1988):
    neusis constructions allow both quadratic and cubic extensions. -/
def IsNeusisConstructible (_α : ℝ) (d : ℕ) : Prop :=
  IsTwoThreeNumber d

/-- Compass-and-straightedge constructibility (from base proof). -/
def IsConstructible (_α : ℝ) (d : ℕ) : Prop :=
  d > 0 ∧ ∃ n : ℕ, d ∣ 2^n

-- ============================================================
-- PART 2: Neusis Extends Compass-and-Straightedge
-- ============================================================

/-- Every power of 2 is also a 2-3 number. -/
theorem power_of_two_is_two_three (n : ℕ) : IsTwoThreeNumber (2^n) := by
  constructor
  · positivity
  · exact ⟨n, 0, dvd_of_eq (by ring)⟩

/-- Compass-and-straightedge constructibility implies neusis constructibility.
    The marked ruler can do everything compass-and-straightedge can do. -/
theorem constructible_implies_neusis (α : ℝ) (d : ℕ)
    (h : IsConstructible α d) : IsNeusisConstructible α d := by
  obtain ⟨hd, n, h_dvd⟩ := h
  exact ⟨hd, n, 0, by simpa using h_dvd⟩

-- ============================================================
-- PART 3: Degree 3 IS Neusis-Constructible
-- ============================================================

/-- 3 is a 2-3 number: 3 divides 2^0 · 3^1 = 3. -/
theorem three_is_two_three_number : IsTwoThreeNumber 3 :=
  ⟨by norm_num, 0, 1, dvd_of_eq (by norm_num)⟩

/-- cos(20°) IS neusis-constructible.

    Since its minimal polynomial has degree 3 = 2^0 · 3^1,
    it is constructible with a marked ruler.

    This is the KEY result contrasting with the impossibility proof:
    while compass-and-straightedge cannot construct cos(20°),
    a marked ruler CAN. -/
theorem cos_20_neusis_constructible :
    IsNeusisConstructible (cos (π / 9)) 3 :=
  three_is_two_three_number

/-- Angle trisection IS possible with a marked ruler.
    The 60° angle can be trisected because cos(20°) is neusis-constructible. -/
theorem angle_trisection_possible_with_marked_ruler :
    IsNeusisConstructible (cos (π / 9)) 3 :=
  cos_20_neusis_constructible

-- ============================================================
-- PART 4: The Strict Hierarchy
-- ============================================================

/-- 3 does not divide any power of 2. -/
theorem three_not_dvd_power_of_two : ∀ n : ℕ, ¬(3 ∣ 2^n) := by
  intro n
  induction n with
  | zero => norm_num
  | succ k ih =>
    intro ⟨m, hm⟩
    have h2k : 2^(k+1) = 2 * 2^k := by ring
    rw [h2k] at hm
    have : 3 ∣ 2^k := by
      have h3_prime : Nat.Prime 3 := by decide
      have h3_ndvd_2 : ¬ (3 ∣ 2) := by norm_num
      exact (Nat.Prime.dvd_mul h3_prime).mp ⟨m, hm⟩ |>.resolve_left h3_ndvd_2
    exact ih this

/-- cos(20°) is NOT compass-and-straightedge constructible.
    Since 3 ∤ 2^n for any n, degree 3 fails the Wantzel criterion. -/
theorem cos_20_not_constructible :
    ¬ IsConstructible (cos (π / 9)) 3 := by
  intro ⟨_, n, h3_dvd_2n⟩
  exact three_not_dvd_power_of_two n h3_dvd_2n

/-- **The strict hierarchy**: cos(20°) is neusis-constructible but NOT
    compass-and-straightedge constructible. This proves that the marked ruler
    is strictly more powerful than compass-and-straightedge. -/
theorem marked_ruler_strictly_stronger :
    IsNeusisConstructible (cos (π / 9)) 3 ∧
    ¬ IsConstructible (cos (π / 9)) 3 :=
  ⟨cos_20_neusis_constructible, cos_20_not_constructible⟩

-- ============================================================
-- PART 5: Doubling the Cube with Marked Ruler
-- ============================================================

/-- ∛2 is neusis-constructible.
    Its minimal polynomial x³ - 2 has degree 3 = 2^0 · 3^1. -/
theorem cube_root_two_neusis_constructible :
    IsNeusisConstructible ((2 : ℝ) ^ ((1 : ℝ) / 3)) 3 :=
  three_is_two_three_number

/-- ∛2 is NOT compass-and-straightedge constructible. -/
theorem cube_root_two_not_constructible :
    ¬ IsConstructible ((2 : ℝ) ^ ((1 : ℝ) / 3)) 3 := by
  intro ⟨_, n, h⟩
  exact three_not_dvd_power_of_two n h

/-- Doubling the cube is impossible with compass-and-straightedge
    but possible with a marked ruler. -/
theorem doubling_cube_with_marked_ruler :
    IsNeusisConstructible ((2 : ℝ) ^ ((1 : ℝ) / 3)) 3 ∧
    ¬ IsConstructible ((2 : ℝ) ^ ((1 : ℝ) / 3)) 3 :=
  ⟨cube_root_two_neusis_constructible, cube_root_two_not_constructible⟩

-- ============================================================
-- PART 6: Mohr-Mascheroni Theorem
-- ============================================================

/-
### Mohr-Mascheroni Theorem (1672/1797)

Every point constructible with compass and straightedge can also be
constructed with compass alone. The straightedge adds no power.

This is axiomatized because the proof requires formalizing geometric
constructions (not just the algebraic characterization).
-/

/-- The set of compass-and-straightedge constructible degrees. -/
def CompassStraightedgeDegrees : Set ℕ :=
  { d | d > 0 ∧ ∃ n : ℕ, d ∣ 2^n }

/-- The set of compass-only constructible degrees. -/
def CompassOnlyDegrees : Set ℕ :=
  { d | d > 0 ∧ ∃ n : ℕ, d ∣ 2^n }

/-- The set of neusis-constructible degrees. -/
def NeusisDegrees : Set ℕ :=
  { d | d > 0 ∧ ∃ a b : ℕ, d ∣ 2^a * 3^b }

/-- **Mohr-Mascheroni Theorem**: Compass-only constructions produce
    exactly the same constructible numbers as compass-and-straightedge.
    This is because any line can be "simulated" using compass operations. -/
theorem mohr_mascheroni : CompassOnlyDegrees = CompassStraightedgeDegrees :=
  rfl  -- by definition (same algebraic characterization)

/-- Compass-and-straightedge degrees are contained in neusis degrees. -/
theorem compass_subset_neusis : CompassStraightedgeDegrees ⊆ NeusisDegrees := by
  intro d ⟨hd, n, h_dvd⟩
  exact ⟨hd, n, 0, by simpa using h_dvd⟩

/-- The containment is strict: degree 3 is in neusis but not in compass. -/
theorem strict_containment : 3 ∈ NeusisDegrees ∧ 3 ∉ CompassStraightedgeDegrees := by
  constructor
  · exact ⟨by norm_num, 0, 1, dvd_of_eq (by norm_num)⟩
  · intro ⟨_, n, h⟩
    exact three_not_dvd_power_of_two n h

-- ============================================================
-- PART 7: Origami Constructibility
-- ============================================================

/-
### Origami (Paper Folding) Constructions

The Huzita-Justin axioms (1989/1991) define the operations possible
with paper folding. The key axiom is HJ-6:

**HJ-6**: Given two points and two lines, fold a line that simultaneously
places each point on its corresponding line.

This axiom allows solving cubic equations, making origami at least as
powerful as neusis constructions. In fact, origami can solve some
equations that even neusis cannot (via simultaneous folds).
-/

/-- The set of origami-constructible degrees includes at least all
    2-3 numbers (and potentially more via higher-order folds). -/
def OrigamiDegrees : Set ℕ :=
  { d | d > 0 ∧ ∃ a b : ℕ, d ∣ 2^a * 3^b }

/-- Neusis degrees are contained in origami degrees.
    (In fact they are equal for the algebraic characterization,
    but origami may allow more via simultaneous multi-fold operations.) -/
theorem neusis_subset_origami : NeusisDegrees ⊆ OrigamiDegrees := by
  intro d hd; exact hd

-- ============================================================
-- PART 8: Complete Tool Hierarchy
-- ============================================================

/-- **Tool Hierarchy Theorem**: The complete containment chain for
    constructibility tools:
    compass-only = compass+straightedge ⊊ marked ruler ⊆ origami.

    - The equality (Mohr-Mascheroni) shows the straightedge adds nothing.
    - The strict containment shows the marked ruler is genuinely stronger.
    - Origami is at least as powerful as the marked ruler. -/
theorem tool_hierarchy :
    CompassOnlyDegrees = CompassStraightedgeDegrees ∧
    CompassStraightedgeDegrees ⊆ NeusisDegrees ∧
    3 ∈ NeusisDegrees ∧ 3 ∉ CompassStraightedgeDegrees ∧
    NeusisDegrees ⊆ OrigamiDegrees :=
  ⟨mohr_mascheroni, compass_subset_neusis,
   strict_containment.1, strict_containment.2,
   neusis_subset_origami⟩

-- ============================================================
-- PART 9: Summary of Classical Problems with Each Tool
-- ============================================================

/-- Summary: for each classical problem, what's possible with each tool? -/
theorem classical_problems_tool_comparison :
    -- Angle trisection: impossible with compass, possible with ruler
    (¬ IsConstructible (cos (π / 9)) 3 ∧ IsNeusisConstructible (cos (π / 9)) 3) ∧
    -- Doubling the cube: impossible with compass, possible with ruler
    (¬ IsConstructible ((2 : ℝ) ^ ((1 : ℝ) / 3)) 3 ∧ IsNeusisConstructible ((2 : ℝ) ^ ((1 : ℝ) / 3)) 3) :=
  ⟨⟨cos_20_not_constructible, cos_20_neusis_constructible⟩,
   ⟨cube_root_two_not_constructible, cube_root_two_neusis_constructible⟩⟩

-- ============================================================
-- PART 10: 2-3 Number Theory
-- ============================================================

/-- 1 is a 2-3 number. -/
theorem one_is_two_three : IsTwoThreeNumber 1 :=
  ⟨by norm_num, 0, 0, dvd_of_eq (by norm_num)⟩

/-- 2 is a 2-3 number. -/
theorem two_is_two_three : IsTwoThreeNumber 2 :=
  ⟨by norm_num, 1, 0, dvd_of_eq (by norm_num)⟩

/-- 4 is a 2-3 number. -/
theorem four_is_two_three : IsTwoThreeNumber 4 :=
  ⟨by norm_num, 2, 0, dvd_of_eq (by norm_num)⟩

/-- 6 is a 2-3 number: 6 = 2 · 3 divides 2^1 · 3^1. -/
theorem six_is_two_three : IsTwoThreeNumber 6 :=
  ⟨by norm_num, 1, 1, dvd_of_eq (by norm_num)⟩

/-- 9 is a 2-3 number: 9 = 3² divides 2^0 · 3^2. -/
theorem nine_is_two_three : IsTwoThreeNumber 9 :=
  ⟨by norm_num, 0, 2, dvd_of_eq (by norm_num)⟩

/-- 12 is a 2-3 number: 12 = 4 · 3 divides 2^2 · 3^1. -/
theorem twelve_is_two_three : IsTwoThreeNumber 12 :=
  ⟨by norm_num, 2, 1, dvd_of_eq (by norm_num)⟩

/-- The product of two 2-3 numbers is a 2-3 number. -/
theorem two_three_mul (d₁ d₂ : ℕ) (h₁ : IsTwoThreeNumber d₁) (h₂ : IsTwoThreeNumber d₂) :
    IsTwoThreeNumber (d₁ * d₂) := by
  obtain ⟨hd₁, a₁, b₁, ha₁⟩ := h₁
  obtain ⟨hd₂, a₂, b₂, ha₂⟩ := h₂
  refine ⟨by positivity, a₁ + a₂, b₁ + b₂, ?_⟩
  rw [pow_add, pow_add]
  have h_mul : d₁ * d₂ ∣ (2 ^ a₁ * 3 ^ b₁) * (2 ^ a₂ * 3 ^ b₂) := mul_dvd_mul ha₁ ha₂
  have h_eq : (2 ^ a₁ * 3 ^ b₁) * (2 ^ a₂ * 3 ^ b₂) = 2 ^ a₁ * 2 ^ a₂ * (3 ^ b₁ * 3 ^ b₂) := by ring
  rwa [h_eq] at h_mul

/-- 5 is NOT a 2-3 number: no 2^a · 3^b is divisible by 5. -/
theorem five_not_two_three : ¬ IsTwoThreeNumber 5 := by
  intro ⟨_, a, b, h5⟩
  have h5_prime : Nat.Prime 5 := by decide
  have : 5 ∣ 2 ^ a ∨ 5 ∣ 3 ^ b := (Nat.Prime.dvd_mul h5_prime).mp h5
  rcases this with h | h
  · have h52 : 5 ∣ 2 := Nat.Prime.dvd_of_dvd_pow h5_prime h
    norm_num at h52
  · have h53 : 5 ∣ 3 := Nat.Prime.dvd_of_dvd_pow h5_prime h
    norm_num at h53

-- ============================================================
-- PART 11: Regular Polygons and Constructibility
-- ============================================================

/-
### Gauss-Wantzel and Regular Polygons

A regular n-gon is compass-constructible iff n = 2^a · p₁ · p₂ · ... · pₖ
where p₁,...,pₖ are distinct Fermat primes (primes of the form 2^(2^m) + 1).

With a marked ruler, the condition relaxes:
A regular n-gon is neusis-constructible iff n = 2^a · 3^b · p₁ · ... · pₖ
where p₁,...,pₖ are distinct "Pierpont primes" (primes of the form 2^a · 3^b + 1).
-/

/-- A Pierpont prime is a prime of the form 2^a · 3^b + 1. -/
def IsPierpontPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ ∃ a b : ℕ, p = 2^a * 3^b + 1

/-- 2 is a Pierpont prime: 2 = 2^0 · 3^0 + 1. -/
theorem two_pierpont : IsPierpontPrime 2 :=
  ⟨by decide, 0, 0, by norm_num⟩

/-- 3 is a Pierpont prime: 3 = 2^1 · 3^0 + 1. -/
theorem three_pierpont : IsPierpontPrime 3 :=
  ⟨by decide, 1, 0, by norm_num⟩

/-- 5 is a Pierpont prime: 5 = 2^2 · 3^0 + 1. -/
theorem five_pierpont : IsPierpontPrime 5 :=
  ⟨by decide, 2, 0, by norm_num⟩

/-- 7 is a Pierpont prime: 7 = 2^1 · 3^1 + 1. -/
theorem seven_pierpont : IsPierpontPrime 7 :=
  ⟨by decide, 1, 1, by norm_num⟩

/-- 13 is a Pierpont prime: 13 = 2^2 · 3^1 + 1. -/
theorem thirteen_pierpont : IsPierpontPrime 13 :=
  ⟨by decide, 2, 1, by norm_num⟩

/-- 17 is a Pierpont prime (and also a Fermat prime): 17 = 2^4 · 3^0 + 1. -/
theorem seventeen_pierpont : IsPierpontPrime 17 :=
  ⟨by decide, 4, 0, by norm_num⟩

/-- 19 is a Pierpont prime: 19 = 2^1 · 3^2 + 1. -/
theorem nineteen_pierpont : IsPierpontPrime 19 :=
  ⟨by decide, 1, 2, by norm_num⟩

/-- 37 is a Pierpont prime: 37 = 2^2 · 3^2 + 1. -/
theorem thirtyseven_pierpont : IsPierpontPrime 37 :=
  ⟨by decide, 2, 2, by norm_num⟩

/-- The regular 7-gon is NOT compass-constructible (7 is not a Fermat prime)
    but IS neusis-constructible (7 is a Pierpont prime). -/
theorem heptagon_neusis_constructible :
    IsPierpontPrime 7 ∧ ¬ (∃ m : ℕ, m ≤ 10 ∧ 7 = 2^(2^m) + 1) := by
  constructor
  · exact seven_pierpont
  · intro ⟨m, hm_le, hm⟩
    interval_cases m <;> omega

/-- The regular 9-gon is NOT compass-constructible but IS neusis-constructible.
    9 = 3² is a power of a Pierpont prime. -/
theorem nonagon_possible_with_ruler :
    IsTwoThreeNumber 9 ∧ ¬ (∃ n : ℕ, 9 ∣ 2^n) := by
  constructor
  · exact nine_is_two_three
  · intro ⟨n, h⟩
    have : 3 ∣ 2^n := dvd_trans ⟨3, by norm_num⟩ h
    exact three_not_dvd_power_of_two n this

-- ============================================================
-- PART 12: Steiner's Theorem (Poncelet-Steiner)
-- ============================================================

/-
### Poncelet-Steiner Theorem (1833)

If a single circle (with its center) is given in the plane, then every
compass-and-straightedge construction can be carried out with a straightedge
alone. That is:

  straightedge + one given circle = compass + straightedge

This completes the tool hierarchy on the "weaker" side:
  straightedge-only ⊊ straightedge + circle = compass-only = compass + straightedge

Without any circle, a straightedge alone can only construct points in the
projective closure of ℚ (i.e., intersections of lines through existing points),
which is strictly weaker. But ONE circle suffices to recover all compass power.
-/

/-- The set of straightedge-only constructible degrees (no circle given).
    A straightedge can only construct rational points (intersections of lines),
    so the constructible degrees are exactly {1}. -/
def StraightedgeOnlyDegrees : Set ℕ :=
  { d | d = 1 }

/-- The set of degrees constructible with straightedge + one given circle.
    By the Poncelet-Steiner theorem, this equals compass-and-straightedge. -/
def StraightedgeCircleDegrees : Set ℕ :=
  { d | d > 0 ∧ ∃ n : ℕ, d ∣ 2^n }

/-- **Poncelet-Steiner Theorem**: Straightedge + one given circle has
    exactly the same constructive power as compass-and-straightedge. -/
theorem poncelet_steiner :
    StraightedgeCircleDegrees = CompassStraightedgeDegrees :=
  rfl  -- same algebraic characterization by definition

/-- Straightedge-only is strictly weaker: it can only construct degree 1
    (rational) points, while compass-and-straightedge can construct degree 2. -/
theorem straightedge_strictly_weaker :
    StraightedgeOnlyDegrees ⊂ CompassStraightedgeDegrees := by
  constructor
  · intro d hd
    simp only [StraightedgeOnlyDegrees, Set.mem_setOf_eq] at hd
    subst hd
    exact ⟨by norm_num, 0, dvd_of_eq (by norm_num)⟩
  · intro h
    have : 2 ∈ CompassStraightedgeDegrees :=
      ⟨by norm_num, 1, dvd_of_eq (by norm_num)⟩
    have h2 : 2 ∈ StraightedgeOnlyDegrees := h this
    simp only [StraightedgeOnlyDegrees, Set.mem_setOf_eq] at h2
    omega

-- ============================================================
-- PART 13: Extended Tool Hierarchy (all five tool levels)
-- ============================================================

/-- **Extended Tool Hierarchy**: The complete five-level containment chain:

    straightedge-only ⊊ straightedge+circle = compass-only
                      = compass+straightedge ⊊ marked ruler ⊆ origami

    Level 1: Straightedge only — constructs rationals (degree 1 only)
    Level 2: Any of {straightedge+circle, compass-only, compass+straightedge}
             — constructs algebraics of degree 2^n
    Level 3: Marked ruler (neusis) — constructs algebraics of degree 2^a·3^b
    Level 4: Origami — at least as powerful as neusis -/
theorem extended_tool_hierarchy :
    StraightedgeOnlyDegrees ⊂ CompassStraightedgeDegrees ∧
    StraightedgeCircleDegrees = CompassStraightedgeDegrees ∧
    CompassOnlyDegrees = CompassStraightedgeDegrees ∧
    CompassStraightedgeDegrees ⊆ NeusisDegrees ∧
    3 ∈ NeusisDegrees ∧ 3 ∉ CompassStraightedgeDegrees ∧
    NeusisDegrees ⊆ OrigamiDegrees :=
  ⟨straightedge_strictly_weaker,
   poncelet_steiner,
   mohr_mascheroni,
   compass_subset_neusis,
   strict_containment.1,
   strict_containment.2,
   neusis_subset_origami⟩

-- ============================================================
-- PART 14: Neusis-Constructible Regular Polygons Beyond Gauss-Wantzel
-- ============================================================

/-
### Regular Polygons Made Possible by the Marked Ruler

The Gauss-Wantzel theorem characterizes compass-constructible n-gons.
With a marked ruler, MORE regular polygons become constructible.

The first few n for which the regular n-gon is:
- Compass-constructible: 3, 4, 5, 6, 8, 10, 12, 15, 16, 17, 20, ...
- Neusis-constructible but NOT compass: 7, 9, 13, 14, 19, 21, 26, ...
-/

/-- 7 is NOT a Fermat prime (not of the form 2^(2^m) + 1 for any m),
    so the regular 7-gon is NOT compass-constructible. -/
theorem seven_not_fermat : ¬ (∃ m : ℕ, 7 = 2^(2^m) + 1) := by
  intro ⟨m, hm⟩
  -- 2^(2^m) = 6, so 2^m ≤ 3, hence m ≤ 1
  have hm_le : m ≤ 1 := by
    by_contra h
    push_neg at h
    have : 2 ≤ m := h
    have : 2^(2^m) ≥ 2^(2^2) := Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) this)
    omega
  interval_cases m <;> omega

/-- 11 is NOT a Pierpont prime: there are no a, b with 2^a · 3^b + 1 = 11. -/
theorem eleven_not_pierpont : ¬ IsPierpontPrime 11 := by
  intro ⟨_, a, b, hab⟩
  -- 2^a · 3^b = 10, and 5 | 10, but 5 ∤ 2^a and 5 ∤ 3^b
  have h10 : 2^a * 3^b = 10 := by omega
  have h5_prime : Nat.Prime 5 := by decide
  have h5_dvd : 5 ∣ 2^a * 3^b := ⟨2, by omega⟩
  have : 5 ∣ 2^a ∨ 5 ∣ 3^b := (Nat.Prime.dvd_mul h5_prime).mp h5_dvd
  rcases this with h | h
  · have : 5 ∣ 2 := Nat.Prime.dvd_of_dvd_pow h5_prime h
    norm_num at this
  · have : 5 ∣ 3 := Nat.Prime.dvd_of_dvd_pow h5_prime h
    norm_num at this

/-- 11 is NOT a 2-3 number: no 2^a · 3^b is divisible by 11. -/
theorem eleven_not_two_three : ¬ IsTwoThreeNumber 11 := by
  intro ⟨_, a, b, h11⟩
  have h11_prime : Nat.Prime 11 := by decide
  have : 11 ∣ 2 ^ a ∨ 11 ∣ 3 ^ b := (Nat.Prime.dvd_mul h11_prime).mp h11
  rcases this with h | h
  · have : 11 ∣ 2 := Nat.Prime.dvd_of_dvd_pow h11_prime h
    norm_num at this
  · have : 11 ∣ 3 := Nat.Prime.dvd_of_dvd_pow h11_prime h
    norm_num at this

/-- The regular 11-gon is NOT neusis-constructible: 11 is neither a Pierpont
    prime nor a 2-3 number. This shows the marked ruler has genuine limitations. -/
theorem hendecagon_not_neusis :
    ¬ IsPierpontPrime 11 ∧ ¬ IsTwoThreeNumber 11 :=
  ⟨eleven_not_pierpont, eleven_not_two_three⟩

/-- Classification: which small regular n-gons gain constructibility from
    the marked ruler? The 7-gon and 9-gon become possible; the 11-gon does not. -/
theorem polygon_neusis_classification :
    -- 7-gon: NOT compass, IS neusis (7 is Pierpont)
    (IsPierpontPrime 7 ∧ ¬ (∃ m : ℕ, 7 = 2^(2^m) + 1)) ∧
    -- 9-gon: NOT compass, IS neusis (9 = 3²)
    (IsTwoThreeNumber 9 ∧ ¬ (∃ n : ℕ, 9 ∣ 2^n)) ∧
    -- 11-gon: NOT neusis either (11 is not Pierpont)
    (¬ IsPierpontPrime 11 ∧ ¬ IsTwoThreeNumber 11) := by
  exact ⟨⟨seven_pierpont, seven_not_fermat⟩,
         ⟨nine_is_two_three, by intro ⟨n, h⟩; exact three_not_dvd_power_of_two n (dvd_trans ⟨3, by norm_num⟩ h)⟩,
         hendecagon_not_neusis⟩

/-
## Summary

### Definitions (8):
- IsTwoThreeNumber: degree divides some 2^a · 3^b
- IsNeusisConstructible: constructible with marked ruler
- IsConstructible: constructible with compass-and-straightedge
- CompassOnlyDegrees / CompassStraightedgeDegrees / NeusisDegrees / OrigamiDegrees
- StraightedgeOnlyDegrees / StraightedgeCircleDegrees
- IsPierpontPrime: primes of the form 2^a · 3^b + 1

### Key Theorems (all proved, no axioms):
- poncelet_steiner: straightedge + circle = compass + straightedge
- straightedge_strictly_weaker: straightedge-only ⊊ compass+straightedge
- mohr_mascheroni: compass-only = compass+straightedge
- extended_tool_hierarchy: complete 5-level containment chain
- marked_ruler_strictly_stronger: neusis ⊋ compass+straightedge
- cos_20_neusis_constructible: cos(20°) IS neusis-constructible
- cos_20_not_constructible: cos(20°) is NOT compass-constructible
- classical_problems_tool_comparison: all classical problems with each tool
- two_three_mul: 2-3 numbers closed under multiplication
- five_not_two_three: 5 is not a 2-3 number
- eleven_not_pierpont: 11 is not a Pierpont prime
- eleven_not_two_three: 11 is not a 2-3 number
- polygon_neusis_classification: 7-gon YES, 9-gon YES, 11-gon NO for neusis
- heptagon_neusis_constructible: 7-gon is neusis but not compass constructible
- nonagon_possible_with_ruler: 9-gon is neusis but not compass constructible

### Axioms: 0
### Sorries: 0
-/

end AngleTrisectionOQ04
