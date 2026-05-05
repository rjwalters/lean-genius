import Proofs.MinkowskiFundamentalTheorem
import Mathlib.Analysis.Convex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Dirichlet's Approximation Theorem via Minkowski's Lattice Point Theorem

## What This Proves

**Dirichlet's Approximation Theorem**: For any real α and positive integer Q,
there exist integers p, q with 1 ≤ q ≤ Q and |qα − p| < 1/Q.

This proof derives Dirichlet's theorem as a direct corollary of Minkowski's
fundamental theorem (geometry of numbers), demonstrating the power of geometric
methods in number theory.

## Proof Strategy

1. **Construct the Dirichlet parallelogram**
   S = {(x, y) ∈ ℝ² : |x| < Q + 1, |αx − y| < 1/Q}
2. **S is centrally symmetric**: |−x| = |x| and |α(−x) − (−y)| = |αx − y|
3. **S is convex**: defined by linear constraints (intersection of halfspaces)
4. **Area(S) = 4(Q+1)/Q > 4 = 2²**: key volume inequality for Minkowski
5. **Apply Minkowski**: S contains a non-zero integer point (a, b) ∈ ℤ²
6. **a ≠ 0**: if a = 0, then |b| < 1/Q < 1, so b = 0, contradicting nonzero
7. **Conclusion**: q = |a| satisfies 1 ≤ q ≤ Q and |αq − p| < 1/Q

## Historical Context

This application of geometry of numbers to Diophantine approximation is one
of the founding examples of Minkowski's 1896 work. The argument shows that
a purely geometric fact (lattice points in parallelograms) immediately implies
the arithmetic theorem on rational approximations.

## Mathlib Foundation

Uses `MinkowskiProved.minkowski_integer_lattice_proved` from the companion file
`MinkowskiFundamentalTheorem.lean`. That theorem is fully proved (0 axioms) using
Mathlib's `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`.

## Axioms

Three axioms handle measure-theoretic steps in this file:
- `dirichletSet_convex`: the parallelogram is a convex set (linear halfplanes)
- `dirichletSet_measurable`: the parallelogram is Lebesgue measurable (open set)
- `dirichletSet_volume`: area = 4(Q+1)/Q, by Fubini or the shear-map argument

The integer-coordinate extraction step is proved from `Submodule.mem_span_range_iff_exists_fun`.
-/

open MeasureTheory Set Real

namespace DirichletFromMinkowski

-- ============================================================
-- PART 1: The Dirichlet Parallelogram
-- ============================================================

/-- The parallelogram for Dirichlet's theorem:
    S = {(x, y) ∈ ℝ² : |x| < Q+1 and |αx − y| < 1/Q}.

    This is centrally symmetric, convex, and has area 4(Q+1)/Q > 4. -/
def dirichletSet (α : ℝ) (Q : ℕ) : Set (Fin 2 → ℝ) :=
  {v | |v 0| < (Q : ℝ) + 1 ∧ |α * v 0 - v 1| < 1 / (Q : ℝ)}

-- ============================================================
-- PART 2: Central Symmetry (Proved)
-- ============================================================

/-- The Dirichlet parallelogram is centrally symmetric.
    (x, y) ∈ S ⟹ (−x, −y) ∈ S, since |−x| = |x| and |α(−x) − (−y)| = |αx − y|. -/
theorem dirichletSet_symmetric (α : ℝ) (Q : ℕ) :
    ∀ v ∈ dirichletSet α Q, -v ∈ dirichletSet α Q := by
  intro v ⟨hv0, hv1⟩
  constructor
  · -- |(-v) 0| = |-v 0| = |v 0|
    simp only [Pi.neg_apply, abs_neg]; exact hv0
  · -- |α * (-v 0) - (-v 1)| = |-(α * v 0 - v 1)| = |α * v 0 - v 1|
    simp only [Pi.neg_apply]
    rw [show α * -v 0 - -v 1 = -(α * v 0 - v 1) by ring, abs_neg]
    exact hv1

-- ============================================================
-- PART 3: Measurability, Convexity, Volume (Axioms)
-- ============================================================

/-!
### Measure-Theoretic Properties

The Dirichlet parallelogram S can be described as the preimage of the open
rectangle R = (−Q−1, Q+1) × (−1/Q, 1/Q) under the shear map T(x,y) = (x, αx−y).

**Convexity**: S is the intersection of two open halfplanes, each convex.

**Measurability**: S is open (preimage of open set under continuous map), hence measurable.

**Volume**: T has determinant det([[1,0],[α,−1]]) = −1, so |det(T)| = 1.
By the change-of-variables formula, vol(S) = vol(T⁻¹(R)) = vol(R) / |det(T)| = vol(R).
vol(R) = 2(Q+1) · (2/Q) = 4(Q+1)/Q.
-/

/-- The Dirichlet parallelogram is convex (intersection of two halfplanes).
    Triangle inequality: |a*x + b*y| ≤ a*|x| + b*|y| < a*c + b*c = c when a+b=1. -/
theorem dirichletSet_convex (α : ℝ) (Q : ℕ) :
    Convex ℝ (dirichletSet α Q) := by
  intro x hx y hy a b ha hb hab
  simp only [dirichletSet, Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  constructor
  · calc |a * x 0 + b * y 0|
        ≤ |a * x 0| + |b * y 0| := abs_add _ _
      _ = a * |x 0| + b * |y 0| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ < a * ((Q : ℝ) + 1) + b * ((Q : ℝ) + 1) :=
          add_lt_add (mul_lt_mul_of_nonneg_left hx0 ha) (mul_lt_mul_of_nonneg_left hy0 hb)
      _ = (Q : ℝ) + 1 := by rw [← add_mul, hab, one_mul]
  · calc |α * (a * x 0 + b * y 0) - (a * x 1 + b * y 1)|
        = |a * (α * x 0 - x 1) + b * (α * y 0 - y 1)| := by ring_nf
      _ ≤ |a * (α * x 0 - x 1)| + |b * (α * y 0 - y 1)| := abs_add _ _
      _ = a * |α * x 0 - x 1| + b * |α * y 0 - y 1| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ < a * (1 / (Q : ℝ)) + b * (1 / (Q : ℝ)) :=
          add_lt_add (mul_lt_mul_of_nonneg_left hx1 ha) (mul_lt_mul_of_nonneg_left hy1 hb)
      _ = 1 / (Q : ℝ) := by rw [← add_mul, hab, one_mul]

/-- The Dirichlet parallelogram is open (preimage of open set under continuous map),
    hence Lebesgue measurable. -/
theorem dirichletSet_measurable (α : ℝ) (Q : ℕ) :
    MeasurableSet (dirichletSet α Q) := by
  apply IsOpen.measurableSet
  unfold dirichletSet
  simp only [Set.setOf_and]
  apply IsOpen.inter
  · exact isOpen_lt (continuous_abs.comp (continuous_apply 0)) continuous_const
  · exact isOpen_lt
      (continuous_abs.comp ((continuous_const.mul (continuous_apply 0)).sub (continuous_apply 1)))
      continuous_const

/-- The Lebesgue measure of the Dirichlet parallelogram equals 4(Q+1)/Q.

    The shear T(x,y) = (x, αx−y) has determinant −1 and maps S to the rectangle
    (−Q−1, Q+1) × (−1/Q, 1/Q). Since |det(T)| = 1, vol(S) = vol(rectangle) = 4(Q+1)/Q. -/
axiom dirichletSet_volume (α : ℝ) (Q : ℕ) (hQ : 0 < Q) :
    MeasureTheory.volume (dirichletSet α Q) =
      ENNReal.ofReal (4 * ((Q : ℝ) + 1) / (Q : ℝ))

-- ============================================================
-- PART 4: Volume Exceeds the Minkowski Threshold 2² = 4
-- ============================================================

/-- The area 4(Q+1)/Q exceeds 4 = 2² when Q ≥ 1.
    Area = 4 + 4/Q > 4. -/
theorem dirichletSet_volume_gt_four (α : ℝ) (Q : ℕ) (hQ : 0 < Q) :
    (2 : ENNReal) ^ 2 < MeasureTheory.volume (dirichletSet α Q) := by
  rw [dirichletSet_volume α Q hQ]
  have hQpos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ
  have hlt : (4 : ℝ) < 4 * ((Q : ℝ) + 1) / (Q : ℝ) := by
    rw [lt_div_iff hQpos]; linarith
  calc (2 : ENNReal) ^ 2
      = ENNReal.ofReal 4 := by norm_num
    _ < ENNReal.ofReal (4 * ((Q : ℝ) + 1) / (Q : ℝ)) :=
        ENNReal.ofReal_lt_ofReal_of_nonneg (by norm_num) hlt

-- ============================================================
-- PART 5: Integer Coordinates from stdLattice 2
-- ============================================================

open MinkowskiProved in
/-- A point in the standard integer lattice `stdLattice 2 = ℤ²` has integer coordinates.

    This follows from `stdLattice 2 = Submodule.span ℤ {e₀, e₁}` where e₀ = (1,0), e₁ = (0,1).
    Any element is `c₀ • e₀ + c₁ • e₁ = (c₀, c₁)` for integers c₀, c₁. -/
lemma stdLattice2_coords (x : stdLattice 2) :
    ∃ (a b : ℤ), (x : Fin 2 → ℝ) 0 = (a : ℝ) ∧ (x : Fin 2 → ℝ) 1 = (b : ℝ) := by
  -- Membership in ℤ-span of standard basis
  have hmem : (x : Fin 2 → ℝ) ∈
      Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 2))) := x.2
  -- Decompose: ∃ c : Fin 2 → ℤ, x = ∑ i, c i • e_i
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  -- Convert ℤ-smul to ℝ-smul: x = ∑ i, (c i : ℝ) • e_i
  have hc_real : (x : Fin 2 → ℝ) = ∑ i : Fin 2, (c i : ℝ) • Pi.basisFun ℝ (Fin 2) i := by
    rw [hc]; simp_rw [zsmul_eq_smul_cast ℝ]
  -- Extract coordinates: (∑ i, (c i : ℝ) • e_i) j = c j
  refine ⟨c 0, c 1, ?_, ?_⟩
  · -- Coordinate 0
    rw [hc_real]
    simp [Pi.basisFun_apply, Fin.sum_univ_two, Pi.single_apply]
  · -- Coordinate 1
    rw [hc_real]
    simp [Pi.basisFun_apply, Fin.sum_univ_two, Pi.single_apply]

-- ============================================================
-- PART 6: Main Theorem — Dirichlet from Minkowski
-- ============================================================

/-- **Dirichlet's Approximation Theorem** derived from Minkowski's theorem.

For any real α and positive integer Q, there exist integers p, q with
1 ≤ q ≤ Q and |qα − p| < 1/Q.

**Proof**:
1. The parallelogram S = {|x| < Q+1, |αx−y| < 1/Q} has area 4(Q+1)/Q > 4 = 2².
2. By Minkowski's theorem, S contains a nonzero integer point (a, b).
3. If a = 0, then |b| < 1/Q < 1, forcing b = 0 (integer), contradicting nonzero.
4. So a ≠ 0, giving q = |a| with 1 ≤ |a| ≤ Q (since |a| < Q+1 and a ∈ ℤ).
5. Setting p = b (if a > 0) or p = -b (if a < 0), we get |qα − p| < 1/Q. -/
theorem dirichlet_approximation_from_minkowski (α : ℝ) (Q : ℕ) (hQ : 0 < Q) :
    ∃ (q p : ℤ), 1 ≤ q ∧ q ≤ Q ∧ |α * (q : ℝ) - (p : ℝ)| < 1 / (Q : ℝ) := by
  -- Step 1: Apply Minkowski to get a nonzero integer point in S
  obtain ⟨x, hx_ne, hx_S⟩ :=
    MinkowskiProved.minkowski_integer_lattice_proved 2 (dirichletSet α Q)
      (dirichletSet_symmetric α Q)
      (dirichletSet_convex α Q)
      (dirichletSet_volume_gt_four α Q hQ)
  -- Step 2: Extract integer coordinates (a, b) from x ∈ ℤ²
  obtain ⟨a, b, ha, hb⟩ := stdLattice2_coords x
  -- Step 3: Parse membership x ∈ S
  simp only [dirichletSet, Set.mem_setOf_eq] at hx_S
  obtain ⟨ha_bound, hab_approx⟩ := hx_S
  rw [ha] at ha_bound hab_approx
  rw [hb] at hab_approx
  -- Positivity facts
  have hQpos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ
  -- Step 4: Show a ≠ 0 (the first coordinate is nonzero)
  have ha_ne : a ≠ 0 := by
    intro ha0; subst ha0
    -- If a = 0: |α * 0 − b| = |b| < 1/Q < 1
    simp only [Int.cast_zero, mul_zero, zero_sub, abs_neg] at hab_approx
    -- |b| < 1/Q ≤ 1 since Q ≥ 1
    have hQge1 : (1 : ℝ) ≤ (Q : ℝ) :=
      by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hQ)
    have hb_lt1 : |(b : ℝ)| < 1 :=
      hab_approx.trans_le (div_le_one hQpos |>.mpr hQge1)
    -- |b| < 1 and b : ℤ → b = 0
    have hb0 : b = 0 := by
      have hlt : b < (1 : ℤ) := by exact_mod_cast (abs_lt.mp hb_lt1).2
      have hgt : -(1 : ℤ) < b := by exact_mod_cast (abs_lt.mp hb_lt1).1
      omega
    -- (a, b) = (0, 0) contradicts x ≠ 0
    apply hx_ne
    apply Subtype.ext
    funext i
    fin_cases i
    · -- Coordinate 0: x 0 = (0:ℤ):ℝ = 0
      simp only [Pi.zero_apply]; rw [ha]; simp
    · -- Coordinate 1: x 1 = (b:ℝ) = 0
      simp only [Pi.zero_apply]; rw [hb]; simp [hb0]
  -- Step 5: Set q = |a|, p = b if a > 0, -b if a < 0
  refine ⟨|a|, if 0 < a then b else -b, ?_, ?_, ?_⟩
  · -- 1 ≤ |a|: since a ≠ 0 is an integer
    exact Int.one_le_abs ha_ne
  · -- |a| ≤ Q: from |a| < Q+1 and a ∈ ℤ
    have hcast : |(a : ℝ)| < (Q : ℝ) + 1 := ha_bound
    rw [Int.cast_abs] at hcast
    have h : (|a| : ℝ) < (Q : ℝ) + 1 := hcast
    have h' : |a| < (Q : ℤ) + 1 := by exact_mod_cast h
    exact_mod_cast Int.lt_add_one_iff.mp h'
  · -- |α * |a| − p| < 1/Q
    split_ifs with hpos
    · -- a > 0: |a| = a
      rw [Int.abs_of_pos hpos]; exact hab_approx
    · -- a < 0: |a| = −a, and α·(−a) − (−b) = −(α·a − b)
      have hneg : a < 0 := lt_of_le_of_ne (le_of_not_lt hpos) ha_ne
      rw [Int.abs_of_neg hneg]
      push_cast
      rw [show α * -(a : ℝ) - -(b : ℝ) = -(α * (a : ℝ) - (b : ℝ)) by ring, abs_neg]
      exact hab_approx

-- ============================================================
-- PART 7: Corollary
-- ============================================================

/-- Dirichlet's theorem gives rational approximations of any precision.
    For any ε > 0, there exist integers p, q > 0 with |α − p/q| < ε/q. -/
theorem dirichlet_approximation_corollary (α : ℝ) (Q : ℕ) (hQ : 0 < Q) :
    ∃ (q p : ℤ), 1 ≤ q ∧ q ≤ (Q : ℤ) ∧
    |α - (p : ℝ) / (q : ℝ)| < 1 / ((Q : ℝ) * (q : ℝ)) := by
  obtain ⟨q, p, hq1, hqQ, happrox⟩ := dirichlet_approximation_from_minkowski α Q hQ
  refine ⟨q, p, hq1, hqQ, ?_⟩
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast Int.lt_of_lt_of_le Int.one_pos hq1
  have hQpos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ
  rw [show α - (p : ℝ) / (q : ℝ) = (α * (q : ℝ) - (p : ℝ)) / (q : ℝ) by field_simp; ring,
      abs_div, abs_of_pos hqpos, div_lt_div_iff hqpos (mul_pos hQpos hqpos)]
  -- Goal: |α*q - p| * (Q*q) < 1 * q = q
  -- From happrox: |α*q - p| < 1/Q, so |α*q - p| * Q < 1
  have key : |α * (q : ℝ) - (p : ℝ)| * (Q : ℝ) < 1 := by rwa [lt_div_iff hQpos] at happrox
  nlinarith

end DirichletFromMinkowski

-- ============================================================
-- PART 8: Gallery Export
-- ============================================================

/-- **Dirichlet's Approximation Theorem** — proved via Minkowski's geometry of numbers.

For any real α and positive integer Q, there exist integers p, q with
1 ≤ q ≤ Q and |αq − p| < 1/Q.

**Proof method**: Apply Minkowski's lattice point theorem to the parallelogram
S = {(x,y) ∈ ℝ² : |x| < Q+1, |αx−y| < 1/Q}. This set has area 4(Q+1)/Q > 4,
so it contains a nonzero integer lattice point (q,p) ∈ ℤ². The first coordinate
q is nonzero (else the second is also 0, contradicting nonzero), and
1 ≤ |q| ≤ Q and |αq−p| < 1/Q. -/
theorem dirichlet_from_minkowski (α : ℝ) (Q : ℕ) (hQ : 0 < Q) :
    ∃ (q p : ℤ), 1 ≤ q ∧ q ≤ Q ∧ |α * (q : ℝ) - (p : ℝ)| < 1 / (Q : ℝ) :=
  DirichletFromMinkowski.dirichlet_approximation_from_minkowski α Q hQ

#check dirichlet_from_minkowski
