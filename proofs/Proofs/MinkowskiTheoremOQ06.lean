import Proofs.MinkowskiFundamentalTheorem
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

/-
# Dirichlet's Approximation Theorem as a Corollary of Minkowski (OQ-06)

## What This Proves

Minkowski's convex body theorem for the integer lattice `ℤⁿ` (proved from Mathlib
in `Proofs.MinkowskiFundamentalTheorem` as `minkowski_integer_lattice_proved`)
specializes, in dimension `2`, to **Dirichlet's approximation theorem**:

> For every real number `α` and every integer `N ≥ 1` there exist integers
> `p, q` with `0 < q ≤ N` and `|q·α − p| ≤ 1/N`.

This is the parent entry `minkowski-theorem`'s listed open question
*"Can Dirichlet's approximation theorem be stated and proved as a direct corollary
of the integer lattice specialization?"*

## Why Minkowski (and not pigeonhole)

Mathlib already contains Dirichlet's theorem
(`Real.exists_nat_abs_mul_sub_round_le` and friends in
`Mathlib.NumberTheory.DiophantineApproximation.Basic`), but it is derived there via
the **pigeonhole principle**. The contribution here is the *geometry-of-numbers*
proof: we exhibit a centrally symmetric convex region of area `> 4` in `ℝ²` and read
off a nonzero integer lattice point inside it from Minkowski's theorem. The region is

```
R = { (x, y) : |x| ≤ N + 1/2,  |α·x − y| ≤ 1/N }
```

which is the image of the axis-aligned box `[−(N+½), N+½] × [−1/N, 1/N]` under the
area-preserving shear `(x, t) ↦ (x, α·x + t)`. Its area is `(2N+1)·(2/N) = 4 + 2/N > 4`,
so the **strict** form of Minkowski's theorem applies directly — no compactness or
boundary case is needed.

## Honesty Notes

* The bound obtained is `|q·α − p| ≤ 1/N`. This is the genuine Minkowski-route bound;
  the slightly sharper `≤ 1/(N+1)` available from pigeonhole is not claimed.
* `N = 1` is handled by the trivial rounding bound `|α − round α| ≤ 1/2 ≤ 1`.
* The proof is `sorry`-free and introduces no axioms beyond those used by the parent
  Minkowski development (which is `verified`, `0` axioms).
-/

set_option linter.unusedVariables false

open scoped BigOperators
open Set MeasureTheory MinkowskiFundamentalTheorem MinkowskiProved

namespace MinkowskiTheoremOQ06

/-! ## The area-preserving shear -/

/-- The `2 × 2` shear matrix `[[1,0],[α,1]]`. Its determinant is `1`. -/
noncomputable def shearMat (α : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; α, 1]

/-- The shear `(x, t) ↦ (x, α·x + t)` as a linear endomorphism of `ℝ²`. -/
noncomputable def shear (α : ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
  Matrix.toLin' (shearMat α)

@[simp] theorem shear_apply_zero (α : ℝ) (v : Fin 2 → ℝ) : (shear α v) 0 = v 0 := by
  simp [shear, shearMat, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Matrix.vecHead, Matrix.vecTail, Fin.succ_zero_eq_one]

@[simp] theorem shear_apply_one (α : ℝ) (v : Fin 2 → ℝ) :
    (shear α v) 1 = α * v 0 + v 1 := by
  simp [shear, shearMat, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Matrix.vecHead, Matrix.vecTail, Fin.succ_zero_eq_one]

/-- The shear is area preserving: `det = 1`. -/
theorem shear_det (α : ℝ) : LinearMap.det (shear α) = 1 := by
  rw [shear, LinearMap.det_toLin']
  simp [shearMat, Matrix.det_fin_two_of]

/-! ## The convex body (an inflated, sheared box) -/

/-- Half-lengths of the axis-aligned pre-image box: `N + 1/2` in the `x`-direction
and `1/N` in the `t`-direction. -/
noncomputable def boxR (N : ℝ) : Fin 2 → ℝ := ![N + 1 / 2, 1 / N]

/-- The axis-aligned box `[−(N+½), N+½] × [−1/N, 1/N]`. -/
noncomputable def box (N : ℝ) : Set (Fin 2 → ℝ) :=
  Set.univ.pi (fun i => Set.Icc (-(boxR N i)) (boxR N i))

theorem box_convex (N : ℝ) : Convex ℝ (box N) :=
  convex_pi (fun i _ => convex_Icc _ _)

theorem box_symmetric (N : ℝ) {v : Fin 2 → ℝ} (hv : v ∈ box N) : -v ∈ box N := by
  simp only [box, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc] at hv ⊢
  intro i
  obtain ⟨h1, h2⟩ := hv i
  simp only [Pi.neg_apply]
  constructor <;> linarith

/-- Volume of the box: `(2·(N+½)) · (2·(1/N))`. -/
theorem box_volume (N : ℝ) :
    volume (box N) = ENNReal.ofReal (2 * (N + 1 / 2)) * ENNReal.ofReal (2 * (1 / N)) := by
  rw [box, volume_pi_pi, Fin.prod_univ_two]
  simp only [boxR, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Real.volume_Icc]
  rw [show (N + 1 / 2) - -(N + 1 / 2) = 2 * (N + 1 / 2) by ring,
      show (1 / N) - -(1 / N) = 2 * (1 / N) by ring]

/-- The Minkowski region `R = shear '' box`. -/
noncomputable def region (α N : ℝ) : Set (Fin 2 → ℝ) := shear α '' box N

theorem region_convex (α N : ℝ) : Convex ℝ (region α N) :=
  (box_convex N).linear_image (shear α)

theorem region_symmetric (α N : ℝ) {x : Fin 2 → ℝ} (hx : x ∈ region α N) :
    -x ∈ region α N := by
  obtain ⟨v, hv, rfl⟩ := hx
  exact ⟨-v, box_symmetric N hv, by rw [map_neg]⟩

/-- The region has area `4 + 2/N`, which exceeds `4 = 2²` when `N > 0`. -/
theorem region_volume_gt (α : ℝ) {N : ℝ} (hN : 0 < N) :
    (2 : ENNReal) ^ 2 < volume (region α N) := by
  have hNne : N ≠ 0 := ne_of_gt hN
  rw [region, Measure.addHaar_image_linearMap, shear_det]
  simp only [abs_one, ENNReal.ofReal_one, one_mul]
  rw [box_volume, ← ENNReal.ofReal_mul (by linarith)]
  have hval : (2 * (N + 1 / 2)) * (2 * (1 / N)) = 4 + 2 / N := by field_simp; ring
  rw [hval]
  have h4 : (2 : ENNReal) ^ 2 = ENNReal.ofReal 4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_ofNat]
  rw [h4]
  have hpos : (0 : ℝ) < 4 + 2 / N := by
    have : (0 : ℝ) < 2 / N := div_pos (by norm_num) hN
    linarith
  rw [ENNReal.ofReal_lt_ofReal_iff hpos]
  have : (0 : ℝ) < 2 / N := div_pos (by norm_num) hN
  linarith

/-! ## Extracting integer coordinates from a lattice point -/

/-- A point of the standard integer lattice `ℤ²` has integer coordinates. -/
theorem stdLattice_coord_int {v : Fin 2 → ℝ}
    (hv : v ∈ stdLattice 2) (i : Fin 2) : ∃ k : ℤ, v i = (k : ℝ) := by
  have hb : v ∈ Submodule.span ℤ (Set.range (stdBasis 2)) := hv
  obtain ⟨k, hk⟩ := ((stdBasis 2).mem_span_iff_repr_mem ℤ v).mp hb i
  refine ⟨k, ?_⟩
  have hrepr : (stdBasis 2).repr v i = v i := by
    simp [stdBasis, Pi.basisFun_repr]
  rw [← hrepr, ← hk]
  simp

/-! ## Dirichlet's approximation theorem -/

/-- **Dirichlet's approximation theorem, via Minkowski.**
For every real `α` and integer `N ≥ 1` there are integers `p, q` with
`0 < q ≤ N` and `|q·α − p| ≤ 1/N`. -/
theorem dirichlet_approx (α : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    ∃ q p : ℤ, 0 < q ∧ q ≤ (N : ℤ) ∧ |(q : ℝ) * α - (p : ℝ)| ≤ 1 / (N : ℝ) := by
  -- The case `N = 1` is the trivial rounding bound.
  rcases Nat.lt_or_ge N 2 with hN1 | hN2
  · interval_cases N
    refine ⟨1, round α, by norm_num, by norm_num, ?_⟩
    have hround : |α - (round α : ℝ)| ≤ 1 / 2 := abs_sub_round α
    have : |(1 : ℝ) * α - (round α : ℝ)| ≤ 1 / 2 := by rwa [one_mul]
    push_cast
    calc |(1 : ℝ) * α - (round α : ℝ)| ≤ 1 / 2 := this
      _ ≤ 1 / (1 : ℝ) := by norm_num
  -- Main case `N ≥ 2`.
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  -- Apply Minkowski's theorem to the inflated sheared box.
  obtain ⟨x, hx0, hxmem⟩ :=
    minkowski_integer_lattice_proved 2 (region α (N : ℝ))
      (fun y hy => region_symmetric α (N : ℝ) hy)
      (region_convex α (N : ℝ))
      (region_volume_gt α hNpos)
  -- Unpack the lattice point as a sheared box point.
  obtain ⟨v, hv, hxv⟩ := hxmem
  set xv : Fin 2 → ℝ := (x : Fin 2 → ℝ) with hxv_def
  -- Coordinate bounds from membership in the box.
  have hv0 : |v 0| ≤ (N : ℝ) + 1 / 2 := by
    have hmem := hv 0 (Set.mem_univ 0)
    rw [abs_le]
    simpa [boxR, Set.mem_Icc, Matrix.cons_val_zero] using hmem
  have hv1 : |v 1| ≤ 1 / (N : ℝ) := by
    have hmem := hv 1 (Set.mem_univ 1)
    rw [abs_le]
    simpa [boxR, Set.mem_Icc, Matrix.cons_val_one, Matrix.head_cons] using hmem
  -- Translate to the coordinates of the lattice point `xv`.
  have hx0eq : xv 0 = v 0 := by rw [← hxv, shear_apply_zero]
  have hx1eq : α * xv 0 - xv 1 = - v 1 := by
    rw [← hxv, shear_apply_zero, shear_apply_one]; ring
  have hbound_x0 : |xv 0| ≤ (N : ℝ) + 1 / 2 := by rw [hx0eq]; exact hv0
  have hbound_diff : |α * xv 0 - xv 1| ≤ 1 / (N : ℝ) := by
    rw [hx1eq, abs_neg]; exact hv1
  -- The coordinates are integers.
  have hxmemL : xv ∈ stdLattice 2 := x.2
  obtain ⟨q0, hq0⟩ := stdLattice_coord_int hxmemL 0
  obtain ⟨p0, hp0⟩ := stdLattice_coord_int hxmemL 1
  -- `|q0| ≤ N` since `q0` is an integer and `|q0| ≤ N + 1/2 < N + 1`.
  have hq0_le : |q0| ≤ (N : ℤ) := by
    have h1 : |(q0 : ℝ)| ≤ (N : ℝ) + 1 / 2 := by rw [← hq0]; exact hbound_x0
    have h3 : |(q0 : ℝ)| < (N : ℝ) + 1 := by linarith
    have h4 : |q0| < (N : ℤ) + 1 := by exact_mod_cast h3
    exact Int.lt_add_one_iff.mp h4
  -- `q0 ≠ 0`: otherwise `|p0| ≤ 1/N < 1` forces `p0 = 0`, contradicting `x ≠ 0`.
  have hq0_ne : q0 ≠ 0 := by
    intro h
    have hxv0 : xv 0 = 0 := by rw [hq0, h]; simp
    have hp_bound : |(p0 : ℝ)| ≤ 1 / (N : ℝ) := by
      have hbd := hbound_diff
      rw [hxv0] at hbd
      simp only [mul_zero, zero_sub, abs_neg] at hbd
      rw [← hp0]; exact hbd
    have hlt1 : 1 / (N : ℝ) < 1 := by rw [div_lt_one hNpos]; linarith
    have hp0_lt : |(p0 : ℝ)| < 1 := lt_of_le_of_lt hp_bound hlt1
    have hp0z : p0 = 0 := by
      have hp0i : |p0| < 1 := by exact_mod_cast hp0_lt
      rw [abs_lt] at hp0i
      omega
    have hxvzero : xv = 0 := by
      funext i; fin_cases i
      · simpa using hxv0
      · simp [hp0, hp0z]
    exact hx0 (ZeroMemClass.coe_eq_zero.mp hxvzero)
  -- Bound on `|α q0 − p0|`.
  have hbq : |α * (q0 : ℝ) - (p0 : ℝ)| ≤ 1 / (N : ℝ) := by
    have hbd := hbound_diff; rw [hq0, hp0] at hbd; exact hbd
  -- Conclude, choosing signs so that `q > 0`.
  rcases lt_or_gt_of_ne hq0_ne with hneg | hpos
  · -- `q0 < 0`: use `q = -q0`, `p = -p0`.
    have habs : |q0| = -q0 := abs_of_neg hneg
    refine ⟨-q0, -p0, by omega, by rw [habs] at hq0_le; omega, ?_⟩
    have heq : |((-q0 : ℤ) : ℝ) * α - ((-p0 : ℤ) : ℝ)| = |α * (q0 : ℝ) - (p0 : ℝ)| := by
      push_cast
      rw [show (-(q0 : ℝ)) * α - (-(p0 : ℝ)) = -(α * (q0 : ℝ) - (p0 : ℝ)) by ring, abs_neg]
    rw [heq]; exact hbq
  · -- `q0 > 0`: use `q = q0`, `p = p0`.
    have habs : |q0| = q0 := abs_of_pos hpos
    refine ⟨q0, p0, hpos, by rw [habs] at hq0_le; omega, ?_⟩
    have heq : |((q0 : ℤ) : ℝ) * α - ((p0 : ℤ) : ℝ)| = |α * (q0 : ℝ) - (p0 : ℝ)| := by
      push_cast
      rw [show (q0 : ℝ) * α = α * (q0 : ℝ) from mul_comm _ _]
    rw [heq]; exact hbq

/-- **Corollary: the `1/q²` bound.** For `α` real and `N ≥ 1` there is a
rational `p/q` with `0 < q ≤ N` and `|α − p/q| ≤ 1/(q·N) ≤ 1/q²`. -/
theorem dirichlet_sq_bound (α : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    ∃ q p : ℤ, 0 < q ∧ q ≤ (N : ℤ) ∧
      |α - (p : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) * (q : ℝ)) := by
  obtain ⟨q, p, hq_pos, hq_le, hbound⟩ := dirichlet_approx α hN
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos
  have hqleN : (q : ℝ) ≤ (N : ℝ) := by exact_mod_cast hq_le
  refine ⟨q, p, hq_pos, hq_le, ?_⟩
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqR
  have key : α - (p : ℝ) / (q : ℝ) = ((q : ℝ) * α - (p : ℝ)) / (q : ℝ) := by
    rw [eq_comm, sub_div, mul_comm (q : ℝ) α, mul_div_assoc, div_self hqne, mul_one]
  have hstep : |α - (p : ℝ) / (q : ℝ)| ≤ (1 / (N : ℝ)) / (q : ℝ) := by
    rw [key, abs_div, abs_of_pos hqR]
    gcongr
  have hqN : 1 / ((N : ℝ) * (q : ℝ)) ≤ 1 / ((q : ℝ) * (q : ℝ)) :=
    one_div_le_one_div_of_le (by positivity)
      (by nlinarith [mul_nonneg (sub_nonneg.mpr hqleN) (le_of_lt hqR)])
  calc |α - (p : ℝ) / (q : ℝ)| ≤ (1 / (N : ℝ)) / (q : ℝ) := hstep
    _ = 1 / ((N : ℝ) * (q : ℝ)) := by rw [div_div]
    _ ≤ 1 / ((q : ℝ) * (q : ℝ)) := hqN

end MinkowskiTheoremOQ06

