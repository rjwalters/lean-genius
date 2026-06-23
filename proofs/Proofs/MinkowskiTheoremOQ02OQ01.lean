/-
# Dirichlet's Approximation Theorem via Minkowski: Axiom-Free Proof (OQ-01)

## What This Proves

The proof `MinkowskiTheoremOQ02.lean` formalizes Dirichlet's Approximation Theorem via
Minkowski's Lattice Point Theorem, but relies on three axioms about the Dirichlet parallelogram:

1. **`dirichletSet_convex`**: The parallelogram `{|x| < Q+1, |αx−y| < 1/Q}` is convex.
2. **`dirichletSet_measurable`**: The parallelogram is Lebesgue measurable.
3. **`dirichletSet_volume`**: Area = 4(Q+1)/Q.

This file eliminates all three axioms, making the proof fully axiom-free.

## Key Techniques

- **Measurability**: The set is open — preimage of `Ioo × Ioo` under continuous maps.
- **Convexity**: Each condition is the preimage of an `Ioo` interval under a linear functional.
- **Volume**: The shear map T(x,y) = (x, αx−y) has |det| = 1 and maps S to the rectangle
  `(−Q−1,Q+1)×(−1/Q,1/Q)`, which has area 4(Q+1)/Q.
- **Minkowski**: Applied directly via Mathlib's geometry of numbers.
-/

import Mathlib.Analysis.Convex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open MeasureTheory Set Real

namespace DirichletMinkowskiAxiomFree

-- ============================================================
-- PART 1: The Dirichlet Parallelogram
-- ============================================================

/-- The parallelogram S = {(x,y) : |x| < Q+1 ∧ |αx−y| < 1/Q}. -/
def dirichletSet (α : ℝ) (Q : ℕ) : Set (Fin 2 → ℝ) :=
  {v | |v 0| < (Q : ℝ) + 1 ∧ |α * v 0 - v 1| < 1 / (Q : ℝ)}

-- ============================================================
-- PART 2: Central Symmetry
-- ============================================================

theorem dirichletSet_symmetric (α : ℝ) (Q : ℕ) :
    ∀ v ∈ dirichletSet α Q, -v ∈ dirichletSet α Q := by
  intro v ⟨hv0, hv1⟩
  constructor
  · simp only [Pi.neg_apply, abs_neg]; exact hv0
  · simp only [Pi.neg_apply]
    rw [show α * -v 0 - -v 1 = -(α * v 0 - v 1) by ring, abs_neg]; exact hv1

-- ============================================================
-- PART 3: Measurability
-- ============================================================

theorem dirichletSet_measurable (α : ℝ) (Q : ℕ) :
    MeasurableSet (dirichletSet α Q) := by
  apply IsOpen.measurableSet
  have heq : dirichletSet α Q =
      (fun v : Fin 2 → ℝ => v 0) ⁻¹' Set.Ioo (-((Q : ℝ) + 1)) ((Q : ℝ) + 1) ∩
      (fun v : Fin 2 → ℝ => α * v 0 - v 1) ⁻¹' Set.Ioo (-(1 / (Q : ℝ))) (1 / (Q : ℝ)) := by
    ext v; simp [dirichletSet, Set.mem_Ioo, abs_lt]
  rw [heq]
  exact (isOpen_Ioo.preimage (continuous_apply 0)).inter
    (isOpen_Ioo.preimage ((continuous_const.mul (continuous_apply 0)).sub (continuous_apply 1)))

-- ============================================================
-- PART 4: Convexity
-- ============================================================

theorem dirichletSet_convex (α : ℝ) (Q : ℕ) :
    Convex ℝ (dirichletSet α Q) := by
  have heq : dirichletSet α Q =
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0) ⁻¹'
      Set.Ioo (-((Q : ℝ) + 1)) ((Q : ℝ) + 1) ∩
      (α • (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0) -
       LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1) ⁻¹'
      Set.Ioo (-(1 / (Q : ℝ))) (1 / (Q : ℝ)) := by
    ext v; simp [dirichletSet, Set.mem_Ioo, abs_lt, LinearMap.proj_apply]
  rw [heq]
  exact ((convex_Ioo _ _).linear_preimage _).inter ((convex_Ioo _ _).linear_preimage _)

-- ============================================================
-- PART 5: Volume via Shear Map
-- ============================================================

/-- The shear map T(x,y) = (x, αx−y) has determinant −1. -/
private theorem shearMap_det (α : ℝ) :
    (Matrix.det (!![1, 0; α, -1] : Matrix (Fin 2) (Fin 2) ℝ)) = -1 := by
  simp [Matrix.det_fin_two]

theorem dirichletSet_volume (α : ℝ) (Q : ℕ) (hQ : 0 < Q) :
    MeasureTheory.volume (dirichletSet α Q) =
      ENNReal.ofReal (4 * ((Q : ℝ) + 1) / (Q : ℝ)) := by
  have hQpos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ
  -- Define the shear matrix and linear map
  let M : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; α, -1]
  let T : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) := M.toLin'
  have hdet : M.det = -1 := shearMap_det α
  have hdet_ne : M.det ≠ 0 := by simp [hdet]
  -- T(v) = (v 0, αv0 − v1)
  have Tv0 : ∀ v : Fin 2 → ℝ, T v 0 = v 0 := fun v => by
    simp [T, M, Matrix.toLin'_apply, Matrix.mulVec, Fin.sum_univ_two, dotProduct]
  have Tv1 : ∀ v : Fin 2 → ℝ, T v 1 = α * v 0 - v 1 := fun v => by
    simp [T, M, Matrix.toLin'_apply, Matrix.mulVec, Fin.sum_univ_two, dotProduct]
    ring
  -- The image rectangle
  let rect := Set.pi Set.univ (fun i : Fin 2 =>
    Set.Ioo (![-((Q : ℝ) + 1), -(1 / (Q : ℝ))] i) (![(Q : ℝ) + 1, 1 / (Q : ℝ)] i))
  -- S = T⁻¹(rect)
  have h_eq : dirichletSet α Q = T ⁻¹' rect := by
    ext v
    simp only [dirichletSet, Set.mem_setOf_eq, Set.mem_preimage, rect, Set.mem_pi,
               Set.mem_univ, forall_true_left, Fin.forall_fin_two, Set.mem_Ioo,
               Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [Tv0 v, Tv1 v]
    constructor
    · rintro ⟨h0, h1⟩; exact ⟨abs_lt.mp h0, abs_lt.mp h1⟩
    · rintro ⟨h0, h1⟩; exact ⟨abs_lt.mpr h0, abs_lt.mpr h1⟩
  -- T preserves volume (|det| = 1)
  have h_meas_T : Measurable T :=
    Continuous.measurable (LinearMap.continuous_on_pi T)
  have h_meas_rect : MeasurableSet rect :=
    MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)
  have h_map : Measure.map T volume = volume := by
    rw [map_matrix_volume_pi_eq_smul_volume_pi hdet_ne, hdet]
    norm_num
  -- vol(S) = vol(T⁻¹(rect)) = vol(rect)
  rw [h_eq, ← Measure.map_apply h_meas_T h_meas_rect, h_map]
  -- Compute vol(rect) = 2(Q+1)·(2/Q)
  rw [volume_pi_Ioo, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show (Q : ℝ) + 1 - (-((Q : ℝ) + 1)) = 2 * ((Q : ℝ) + 1) from by ring,
      show 1 / (Q : ℝ) - (-(1 / (Q : ℝ))) = 2 / (Q : ℝ) from by ring,
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * ((Q : ℝ) + 1))]
  congr 1; field_simp; ring

-- ============================================================
-- PART 6: Volume > 4
-- ============================================================

theorem dirichletSet_volume_gt_four (α : ℝ) (Q : ℕ) (hQ : 0 < Q) :
    (2 : ENNReal) ^ 2 < MeasureTheory.volume (dirichletSet α Q) := by
  rw [dirichletSet_volume α Q hQ]
  have hQpos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ
  have hlt : (4 : ℝ) < 4 * ((Q : ℝ) + 1) / (Q : ℝ) := by
    rw [lt_div_iff₀ hQpos]; linarith
  calc (2 : ENNReal) ^ 2
      = ENNReal.ofReal 4 := by norm_num
    _ < ENNReal.ofReal (4 * ((Q : ℝ) + 1) / (Q : ℝ)) :=
        (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hlt

-- ============================================================
-- PART 7: Main Theorem
-- ============================================================

theorem dirichlet_approximation (α : ℝ) (Q : ℕ) (hQ : 0 < Q) :
    ∃ (q p : ℤ), 1 ≤ q ∧ q ≤ Q ∧ |α * (q : ℝ) - (p : ℝ)| < 1 / (Q : ℝ) := by
  have hQpos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ
  -- Standard ℤ² lattice
  let b := Pi.basisFun ℝ (Fin 2)
  have h_fund := ZSpan.isAddFundamentalDomain' b volume
  have h_count : Countable (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
    change Countable (Submodule.span ℤ (Set.range b)); infer_instance
  -- Volume of fundamental domain [0,1)² is 1
  have h_vol_fund : MeasureTheory.volume (ZSpan.fundamentalDomain b) = 1 := by
    have hmat : (Matrix.of b).det = 1 := by
      have hbeq : Matrix.of b = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
        ext i j
        -- b is definitionally Pi.basisFun ℝ (Fin 2), so b i j = Pi.single i 1 j
        change (Matrix.of (Pi.basisFun ℝ (Fin 2))) i j = (1 : Matrix (Fin 2) (Fin 2) ℝ) i j
        simp [Matrix.of_apply, Pi.basisFun_apply, Pi.single_apply, Matrix.one_apply, eq_comm]
      simp [hbeq]
    rw [ZSpan.volume_fundamentalDomain, hmat, abs_one, ENNReal.ofReal_one]
  -- Apply Minkowski's theorem
  have h_vol_cond :
      MeasureTheory.volume (ZSpan.fundamentalDomain b) * 2 ^ Module.finrank ℝ (Fin 2 → ℝ) <
      MeasureTheory.volume (dirichletSet α Q) := by
    rw [h_vol_fund, one_mul, Module.finrank_fin_fun]
    exact dirichletSet_volume_gt_four α Q hQ
  obtain ⟨⟨x_val, hx_mem⟩, hx_ne, hx_S⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      h_fund (dirichletSet_symmetric α Q) (dirichletSet_convex α Q) h_vol_cond
  -- Extract integer coordinates from x_val ∈ span ℤ (range b)
  rw [Submodule.mem_toAddSubgroup] at hx_mem
  rw [Submodule.mem_span_range_iff_exists_fun] at hx_mem
  obtain ⟨c, hc⟩ := hx_mem
  -- Compute x_val 0 = c 0 and x_val 1 = c 1
  -- b is definitionally Pi.basisFun ℝ (Fin 2), so b i = Pi.single i 1
  have hb00 : b 0 0 = 1 := by
    change Pi.basisFun ℝ (Fin 2) 0 0 = 1; simp [Pi.basisFun_apply]
  have hb10 : b 1 0 = 0 := by
    change Pi.basisFun ℝ (Fin 2) 1 0 = 0; simp [Pi.basisFun_apply]
  have hb01 : b 0 1 = 0 := by
    change Pi.basisFun ℝ (Fin 2) 0 1 = 0; simp [Pi.basisFun_apply]
  have hb11 : b 1 1 = 1 := by
    change Pi.basisFun ℝ (Fin 2) 1 1 = 1; simp [Pi.basisFun_apply]
  have ha : x_val 0 = (c 0 : ℝ) := by
    have h0 := congr_fun hc 0
    rw [Fin.sum_univ_two] at h0
    simp only [Pi.add_apply, Pi.smul_apply] at h0
    rw [hb00, hb10] at h0
    simp only [zsmul_one, smul_zero, add_zero] at h0
    exact h0.symm
  have hb' : x_val 1 = (c 1 : ℝ) := by
    have h1 := congr_fun hc 1
    rw [Fin.sum_univ_two] at h1
    simp only [Pi.add_apply, Pi.smul_apply] at h1
    rw [hb01, hb11] at h1
    simp only [smul_zero, zsmul_one, zero_add] at h1
    exact h1.symm
  -- Unpack membership in dirichletSet
  simp only [dirichletSet, Set.mem_setOf_eq] at hx_S
  obtain ⟨ha_bound, hab_approx⟩ := hx_S
  rw [ha] at ha_bound hab_approx
  rw [hb'] at hab_approx
  -- c 0 ≠ 0 (otherwise x_val = 0, contradicting nonzero)
  have ha_ne : c 0 ≠ 0 := by
    intro ha0
    have ha0r : (c 0 : ℝ) = 0 := by exact_mod_cast ha0
    rw [ha0r, mul_zero, zero_sub, abs_neg] at hab_approx
    have hQge1 : (1 : ℝ) ≤ (Q : ℝ) :=
      by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hQ)
    have hb_lt1 : |(c 1 : ℝ)| < 1 :=
      hab_approx.trans_le (div_le_one hQpos |>.mpr hQge1)
    have hb0 : c 1 = 0 := by
      have hlt : c 1 < (1 : ℤ) := by exact_mod_cast (abs_lt.mp hb_lt1).2
      have hgt : -(1 : ℤ) < c 1 := by exact_mod_cast (abs_lt.mp hb_lt1).1
      omega
    apply hx_ne; apply Subtype.ext; funext i; fin_cases i
    · show x_val 0 = 0; rw [ha, ha0r]
    · show x_val 1 = 0; rw [hb']; exact_mod_cast hb0
  -- Choose q = |c 0|, p = sign(c 0) · c 1
  refine ⟨|c 0|, if 0 < c 0 then c 1 else -(c 1), Int.one_le_abs ha_ne, ?_, ?_⟩
  · -- |c 0| ≤ Q
    have h_real : (|c 0| : ℝ) < (Q : ℝ) + 1 := by exact_mod_cast ha_bound
    have h_int : (|c 0| : ℤ) < (Q : ℤ) + 1 := by exact_mod_cast h_real
    omega
  · -- approximation bound
    split_ifs with hpos
    · rw [abs_of_pos hpos]; exact hab_approx
    · have hneg : c 0 < 0 := lt_of_le_of_ne (le_of_not_gt hpos) ha_ne
      rw [abs_of_neg hneg]; push_cast
      rw [show α * -(c 0 : ℝ) - -(c 1 : ℝ) = -(α * (c 0 : ℝ) - (c 1 : ℝ)) by ring, abs_neg]
      exact hab_approx

end DirichletMinkowskiAxiomFree

-- ============================================================
-- Gallery Export
-- ============================================================

/-- **Dirichlet's Approximation Theorem** — fully axiom-free via Minkowski.

For any real α and positive integer Q, there exist integers p, q with
1 ≤ q ≤ Q and |αq − p| < 1/Q.

Proved from Mathlib with 0 axioms and 0 sorries. -/
theorem dirichlet_from_minkowski_axiom_free (α : ℝ) (Q : ℕ) (hQ : 0 < Q) :
    ∃ (q p : ℤ), 1 ≤ q ∧ q ≤ Q ∧ |α * (q : ℝ) - (p : ℝ)| < 1 / (Q : ℝ) :=
  DirichletMinkowskiAxiomFree.dirichlet_approximation α Q hQ

#check dirichlet_from_minkowski_axiom_free
