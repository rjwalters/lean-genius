/-
Spherical Law of Sines

For a spherical triangle with unit vector vertices A, B, C ∈ ℝ³
and arc-length sides a = arcLen(B,C), b = arcLen(A,C), c = arcLen(A,B):

  sin(a)/sin(α) = sin(b)/sin(β) = sin(c)/sin(γ)

where α, β, γ are the dihedral angles at A, B, C respectively.

## Proof outline

Key identity: projPerp(B,A) × projPerp(C,A) = det[A,B,C] · A

This holds because both projections are ⊥ to unit vector A. Algebraically:
  LHS_component_i - det[A,B,C] · A_i = (1 - |A|²) · (B×C)_i  →  0  when |A|=1

Consequences:
  |projPerp(B,A) × projPerp(C,A)|² = det²
  sin²(α) = det² / (sin²(c) · sin²(b))
  sin²(a)/sin²(α) = sin²(a)·sin²(b)·sin²(c)/det²  [symmetric → law of sines]
-/

import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

open Real

set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace SphericalLawOfSines

local notation a " ×₃ " b => crossProduct a b

/-! ### Setup: vectors in Fin 3 → ℝ -/

noncomputable def dot (u v : Fin 3 → ℝ) : ℝ := ∑ i, u i * v i

noncomputable def normSq (u : Fin 3 → ℝ) : ℝ := dot u u

def IsUnit3 (u : Fin 3 → ℝ) : Prop := normSq u = 1

noncomputable def arcLen (u v : Fin 3 → ℝ) : ℝ := Real.arccos (dot u v)

noncomputable def tripleProduct (a b c : Fin 3 → ℝ) : ℝ := dot a (b ×₃ c)

noncomputable def projPerp (u w : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => u i - dot u w * w i

/-! ### Basic lemmas -/

theorem dot_comm (u v : Fin 3 → ℝ) : dot u v = dot v u := by
  simp [dot, mul_comm]

theorem arcLen_comm (u v : Fin 3 → ℝ) : arcLen u v = arcLen v u := by
  simp [arcLen, dot_comm]

theorem normSq_nonneg (u : Fin 3 → ℝ) : 0 ≤ normSq u := by
  unfold normSq dot
  apply Finset.sum_nonneg
  intro i _
  exact mul_self_nonneg _

theorem normSq_cross_nonneg (u v : Fin 3 → ℝ) : 0 ≤ normSq (u ×₃ v) :=
  normSq_nonneg _

/-- Unit vector constraint as a sum -/
theorem unit_sum (A : Fin 3 → ℝ) (hA : IsUnit3 A) :
    A 0 * A 0 + A 1 * A 1 + A 2 * A 2 = 1 := by
  have := hA
  simp only [IsUnit3, normSq, dot, Fin.sum_univ_three] at this
  linarith

/-- Lagrange's identity: |u × v|² = |u|²|v|² - (u·v)² -/
theorem lagrange_identity (u v : Fin 3 → ℝ) :
    normSq (u ×₃ v) = normSq u * normSq v - (dot u v) ^ 2 := by
  simp [normSq, dot, crossProduct, Fin.sum_univ_three]
  ring

theorem tripleProduct_swap_12 (a b c : Fin 3 → ℝ) :
    tripleProduct b a c = -tripleProduct a b c := by
  simp [tripleProduct, dot, crossProduct, Fin.sum_univ_three]; ring

theorem tripleProduct_sq_swap (a b c : Fin 3 → ℝ) :
    tripleProduct a b c ^ 2 = tripleProduct b a c ^ 2 := by
  rw [tripleProduct_swap_12]; ring

theorem tripleProduct_cyclic (a b c : Fin 3 → ℝ) :
    tripleProduct b c a = tripleProduct a b c := by
  simp [tripleProduct, dot, crossProduct, Fin.sum_univ_three]; ring

/-! ### Perpendicular projections -/

/-- projPerp u w · w = 0 when w is unit -/
theorem projPerp_dot_zero (u w : Fin 3 → ℝ) (hw : IsUnit3 w) :
    dot (projPerp u w) w = 0 := by
  have h : w 0 * w 0 + w 1 * w 1 + w 2 * w 2 = 1 := unit_sum w hw
  simp only [projPerp, dot, Fin.sum_univ_three]
  linear_combination -(u 0 * w 0 + u 1 * w 1 + u 2 * w 2) * h

/-- For unit w: |projPerp u w|² = |u|² - (u·w)² -/
theorem normSq_projPerp (u w : Fin 3 → ℝ) (hw : IsUnit3 w) :
    normSq (projPerp u w) = normSq u - (dot u w) ^ 2 := by
  have h : w 0 * w 0 + w 1 * w 1 + w 2 * w 2 = 1 := unit_sum w hw
  simp only [normSq, dot, projPerp, Fin.sum_univ_three]
  linear_combination (u 0 * w 0 + u 1 * w 1 + u 2 * w 2) *
    (u 0 * w 0 + u 1 * w 1 + u 2 * w 2) * h

/-- For unit u, w: |projPerp u w|² = sin²(arcLen u w) -/
theorem normSq_projPerp_unit (u w : Fin 3 → ℝ) (hu : IsUnit3 u) (hw : IsUnit3 w) :
    normSq (projPerp u w) = Real.sin (arcLen u w) ^ 2 := by
  -- Key: sin(arccos x) = sqrt(1 - x²), and sqrt(x)² = x for x ≥ 0
  -- Need: 0 ≤ 1 - (dot u w)²
  have h_nn2 : 0 ≤ 1 - (dot u w) ^ 2 := by
    have h_lag := lagrange_identity u w
    have h_nn := normSq_cross_nonneg u w
    have : normSq (u ×₃ w) = 1 - (dot u w) ^ 2 := by
      rw [h_lag, hu, hw]; ring
    linarith
  rw [normSq_projPerp u w hw, hu, arcLen, Real.sin_arccos, Real.sq_sqrt h_nn2]

/-! ### Key cross product identity -/

/-- **Key identity**: projPerp(B,A) × projPerp(C,A) = det[A,B,C] · A

For unit vector A, both projections lie in the plane ⊥ A, so their cross product
lies along A. The coefficient is the scalar triple product det[A,B,C].

Algebraically, component i of LHS − RHS = (1 − |A|²) · (B×C)ᵢ, which is 0 for unit A.
-/
theorem projPerp_cross_eq (A B C : Fin 3 → ℝ) (hA : IsUnit3 A) :
    (projPerp B A ×₃ projPerp C A) = tripleProduct A B C • A := by
  have h : A 0 * A 0 + A 1 * A 1 + A 2 * A 2 = 1 := unit_sum A hA
  funext i; fin_cases i
  · -- Component 0: LHS − RHS = (1−|A|²)(B₁C₂−B₂C₁)
    simp [projPerp, tripleProduct, dot, crossProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
    linear_combination -(B 1 * C 2 - B 2 * C 1) * h
  · -- Component 1: LHS − RHS = (1−|A|²)(B₂C₀−B₀C₂)
    simp [projPerp, tripleProduct, dot, crossProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
    linear_combination -(B 2 * C 0 - B 0 * C 2) * h
  · -- Component 2: LHS − RHS = (1−|A|²)(B₀C₁−B₁C₀)
    simp [projPerp, tripleProduct, dot, crossProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
    linear_combination -(B 0 * C 1 - B 1 * C 0) * h

/-- The cross product of projections has norm squared = det² -/
theorem normSq_projPerp_cross (A B C : Fin 3 → ℝ) (hA : IsUnit3 A) :
    normSq (projPerp B A ×₃ projPerp C A) = tripleProduct A B C ^ 2 := by
  rw [projPerp_cross_eq A B C hA]
  have h : A 0 * A 0 + A 1 * A 1 + A 2 * A 2 = 1 := unit_sum A hA
  simp only [normSq, dot, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  linear_combination tripleProduct A B C ^ 2 * h

/-! ### Dihedral angle -/

/-- The dihedral angle at vertex A: angle between the projections of B and C. -/
noncomputable def dihedralAngle (A B C : Fin 3 → ℝ) : ℝ :=
  let pB := projPerp B A
  let pC := projPerp C A
  if Real.sqrt (normSq pB) = 0 ∨ Real.sqrt (normSq pC) = 0 then 0
  else Real.arccos (dot pB pC / (Real.sqrt (normSq pB) * Real.sqrt (normSq pC)))

/-- Dihedral angle is symmetric in last two args (angle at vertex is undirected) -/
theorem dihedralAngle_comm_last (A B C : Fin 3 → ℝ) :
    dihedralAngle A B C = dihedralAngle A C B := by
  simp only [dihedralAngle, dot_comm (projPerp B A) (projPerp C A),
             mul_comm (Real.sqrt (normSq (projPerp B A))) (Real.sqrt (normSq (projPerp C A))),
             or_comm]

/-- sin²(α) = det² / (sin²(c) · sin²(b)) in the non-degenerate case -/
theorem sin_sq_dihedralAngle (A B C : Fin 3 → ℝ) (hA : IsUnit3 A)
    (hpB : normSq (projPerp B A) ≠ 0)
    (hpC : normSq (projPerp C A) ≠ 0) :
    Real.sin (dihedralAngle A B C) ^ 2 =
      tripleProduct A B C ^ 2 /
        (normSq (projPerp B A) * normSq (projPerp C A)) := by
  have hpB_pos : 0 < normSq (projPerp B A) :=
    lt_of_le_of_ne (normSq_nonneg _) (Ne.symm hpB)
  have hpC_pos : 0 < normSq (projPerp C A) :=
    lt_of_le_of_ne (normSq_nonneg _) (Ne.symm hpC)
  have hsBpos : 0 < Real.sqrt (normSq (projPerp B A)) := Real.sqrt_pos.mpr hpB_pos
  have hsCpos : 0 < Real.sqrt (normSq (projPerp C A)) := Real.sqrt_pos.mpr hpC_pos
  simp only [dihedralAngle]
  rw [if_neg (by push_neg; exact ⟨hsBpos.ne', hsCpos.ne'⟩)]
  -- sin(arccos(x)) = sqrt(1 - x²) for all x (Mathlib lemma, no bounds needed)
  rw [Real.sin_arccos]
  -- Set shorthands
  set pB := projPerp B A
  set pC := projPerp C A
  set nB := Real.sqrt (normSq pB)
  set nC := Real.sqrt (normSq pC)
  have hnB_sq : nB ^ 2 = normSq pB := Real.sq_sqrt (normSq_nonneg pB)
  have hnC_sq : nC ^ 2 = normSq pC := Real.sq_sqrt (normSq_nonneg pC)
  -- Cauchy-Schwarz: (dot pB pC)² ≤ (nB * nC)²
  have h_lag := lagrange_identity pB pC
  have h_key := normSq_projPerp_cross A B C hA
  have h_prod_pos : 0 < nB * nC := mul_pos hsBpos hsCpos
  have h_cs : (dot pB pC) ^ 2 ≤ (nB * nC) ^ 2 := by
    rw [mul_pow, hnB_sq, hnC_sq]
    linarith [normSq_cross_nonneg pB pC]
  -- 0 ≤ 1 - (dot pB pC / (nB * nC))²
  have h_nn : 0 ≤ 1 - (dot pB pC / (nB * nC)) ^ 2 := by
    rw [sub_nonneg, div_pow, div_le_one (by positivity)]
    exact h_cs
  -- Goal: sqrt(1 - (dot pB pC / (nB*nC))²)² = det² / (normSq pB * normSq pC)
  rw [Real.sq_sqrt h_nn]
  -- Goal: 1 - (dot pB pC / (nB*nC))² = det² / (normSq pB * normSq pC)
  have h_denom : nB ^ 2 * nC ^ 2 = normSq pB * normSq pC := by
    rw [hnB_sq, hnC_sq]
  have h_prod_ne : normSq pB * normSq pC ≠ 0 := mul_ne_zero hpB hpC
  rw [div_pow, show (nB * nC) ^ 2 = normSq pB * normSq pC from by rw [mul_pow, hnB_sq, hnC_sq]]
  -- Goal: 1 - dot pB pC ^ 2 / (nB*nC)^2 = det² / (nB*nC)^2
  field_simp [h_prod_ne]
  linarith [h_lag, h_key]

/-! ### The Spherical Law of Sines -/

/-- sin²(arcLen u w) = normSq(projPerp w u) for unit u, w -/
theorem sin_sq_arcLen (u w : Fin 3 → ℝ) (hu : IsUnit3 u) (hw : IsUnit3 w) :
    Real.sin (arcLen u w) ^ 2 = normSq (projPerp w u) := by
  rw [normSq_projPerp_unit w u hw hu, arcLen_comm]

/-- **Spherical Law of Sines** (squared, two-ratio form)

  sin²(a)/sin²(α) = sin²(b)/sin²(β)

Both equal sin²(a)·sin²(b)·sin²(c) / det[A,B,C]².
-/
theorem spherical_law_of_sines_sq (A B C : Fin 3 → ℝ)
    (hA : IsUnit3 A) (hB : IsUnit3 B) (hC : IsUnit3 C)
    (hpBA : normSq (projPerp B A) ≠ 0)  -- sin(c) ≠ 0
    (hpCA : normSq (projPerp C A) ≠ 0)  -- sin(b) ≠ 0
    (hpAB : normSq (projPerp A B) ≠ 0)  -- sin(c) from B's perspective
    (hpCB : normSq (projPerp C B) ≠ 0)  -- sin(a) ≠ 0
    (hT : tripleProduct A B C ≠ 0) :
    Real.sin (arcLen B C) ^ 2 / Real.sin (dihedralAngle A B C) ^ 2 =
    Real.sin (arcLen A C) ^ 2 / Real.sin (dihedralAngle B A C) ^ 2 := by
  -- Side lengths as normSq of projections
  have ha : Real.sin (arcLen B C) ^ 2 = normSq (projPerp C B) := sin_sq_arcLen B C hB hC
  have hb : Real.sin (arcLen A C) ^ 2 = normSq (projPerp C A) := sin_sq_arcLen A C hA hC
  -- Dihedral angles from the key formula
  have hα := sin_sq_dihedralAngle A B C hA hpBA hpCA
  -- For β: tripleProduct B A C = -tripleProduct A B C, so squares match
  have hT_BA_sq : tripleProduct B A C ^ 2 = tripleProduct A B C ^ 2 := by
    rw [tripleProduct_swap_12]; ring
  -- normSq(projPerp B A) = normSq(projPerp A B): both equal sin²(arcLen A B)
  have h_sym_c : normSq (projPerp B A) = normSq (projPerp A B) := by
    rw [normSq_projPerp_unit B A hB hA, normSq_projPerp_unit A B hA hB, arcLen_comm]
  have hβ : Real.sin (dihedralAngle B A C) ^ 2 =
      tripleProduct A B C ^ 2 / (normSq (projPerp A B) * normSq (projPerp C B)) := by
    rw [← hT_BA_sq]
    exact sin_sq_dihedralAngle B A C hB hpAB hpCB
  rw [ha, hb, hα, hβ, h_sym_c]
  -- Both sides: normSq(CB) / (det²/(normSq(AB)*normSq(CA))) =
  --             normSq(CA) / (det²/(normSq(AB)*normSq(CB)))
  -- Simplify using field arithmetic
  field_simp

/-- Dihedral angle at B: B A C = B C A (symmetric in last two args) -/
theorem dihedralAngle_B_comm (A B C : Fin 3 → ℝ) :
    dihedralAngle B A C = dihedralAngle B C A :=
  dihedralAngle_comm_last B A C

/-- Dihedral angle at C: C A B = C B A (symmetric in last two args) -/
theorem dihedralAngle_C_comm (A B C : Fin 3 → ℝ) :
    dihedralAngle C A B = dihedralAngle C B A :=
  dihedralAngle_comm_last C A B

/-- **Spherical Law of Sines** (all three ratios equal, squared form) -/
theorem spherical_law_of_sines_all_sq (A B C : Fin 3 → ℝ)
    (hA : IsUnit3 A) (hB : IsUnit3 B) (hC : IsUnit3 C)
    (hpBA : normSq (projPerp B A) ≠ 0) (hpCA : normSq (projPerp C A) ≠ 0)
    (hpAB : normSq (projPerp A B) ≠ 0) (hpCB : normSq (projPerp C B) ≠ 0)
    (hpAC : normSq (projPerp A C) ≠ 0) (hpBC : normSq (projPerp B C) ≠ 0)
    (hT : tripleProduct A B C ≠ 0) :
    Real.sin (arcLen B C) ^ 2 / Real.sin (dihedralAngle A B C) ^ 2 =
    Real.sin (arcLen A C) ^ 2 / Real.sin (dihedralAngle B A C) ^ 2 ∧
    Real.sin (arcLen A C) ^ 2 / Real.sin (dihedralAngle B A C) ^ 2 =
    Real.sin (arcLen A B) ^ 2 / Real.sin (dihedralAngle C A B) ^ 2 := by
  have hT_BCA : tripleProduct B C A ≠ 0 := by rw [tripleProduct_cyclic]; exact hT
  -- normSq symmetries
  have h_sym_b : normSq (projPerp C A) = normSq (projPerp A C) := by
    rw [normSq_projPerp_unit C A hC hA, normSq_projPerp_unit A C hA hC, arcLen_comm]
  have h_sym_a : normSq (projPerp C B) = normSq (projPerp B C) := by
    rw [normSq_projPerp_unit C B hC hB, normSq_projPerp_unit B C hB hC, arcLen_comm]
  constructor
  · -- sin²(a)/sin²(α) = sin²(b)/sin²(β)
    exact spherical_law_of_sines_sq A B C hA hB hC hpBA hpCA hpAB hpCB hT
  · -- sin²(b)/sin²(β) = sin²(c)/sin²(γ)
    -- Apply law of sines to (B, C, A): gives sin²(arcLen CA)/sin²(dih B C A) = sin²(arcLen BA)/sin²(dih C B A)
    -- Note: dih B C A = dih B A C (= β) and dih C B A = dih C A B (= γ) by symmetry
    have hpCB' : normSq (projPerp C B) ≠ 0 := hpCB
    have hpAB' : normSq (projPerp A B) ≠ 0 := hpAB
    have hpBC' : normSq (projPerp B C) ≠ 0 := by rwa [← h_sym_a]
    have hpAC' : normSq (projPerp A C) ≠ 0 := by rwa [← h_sym_b]
    have h_eq := spherical_law_of_sines_sq B C A hB hC hA hpCB hpAB hpBC' hpAC' hT_BCA
    -- h_eq: sin²(arcLen CA)/sin²(dih B C A) = sin²(arcLen BA)/sin²(dih C B A)
    -- Use explicit instantiation to avoid ambiguous pattern matching
    rw [(dihedralAngle_B_comm A B C).symm, (dihedralAngle_C_comm A B C).symm] at h_eq
    -- h_eq: sin²(arcLen CA)/sin²(dih B A C) = sin²(arcLen BA)/sin²(dih C A B)
    rw [show arcLen C A = arcLen A C from arcLen_comm C A] at h_eq
    rw [show arcLen B A = arcLen A B from arcLen_comm B A] at h_eq
    exact h_eq

/-! ### Summary

| Result                                                           | Status |
|------------------------------------------------------------------|--------|
| Lagrange's identity: |u×v|² = |u|²|v|² − (u·v)²               | PROVED |
| Cauchy-Schwarz: (dot u w)² ≤ 1 for unit vectors                 | PROVED |
| |projPerp u w|² = sin²(arcLen u w) for unit u, w               | PROVED |
| Key identity: projPerp(B,A)×projPerp(C,A) = det[A,B,C]·A       | PROVED |
| |cross of projections|² = det²                                   | PROVED |
| sin²(dihedral angle) = det² / (sin²(b)·sin²(c))                | PROVED |
| sin²(a)/sin²(α) = sin²(b)/sin²(β)                              | PROVED |
| All three ratios equal                                            | PROVED |

Sorries: 0
Axioms: 0
-/

end SphericalLawOfSines
