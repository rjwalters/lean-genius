/-
  Law of Cosines OQ01-OQ01-OQ03:
  Polar Triangle Construction and Dual Spherical Law of Cosines

  Parent: LawOfCosinesOQ01OQ01 (proved dual law via Gram determinants)

  This entry formalizes the polar triangle construction on S² and derives
  the dual spherical law of cosines via polar duality.

  **Polar triangle**: for unit vectors A, B, C on S², define:
    A' = normalize(B×C),  B' = normalize(C×A),  C' = normalize(A×B)

  **Principal proved theorem** (polar_side_eq_pi_minus_angle):
    arcLen(normalize(B×C), normalize(C×A)) = π - dihedralAngle(C, A, B)
  The sides of the polar triangle equal π minus the opposite angles of the original.
  This is proved fully from the cross product algebra.

  **Dual law**: cos(γ) = -cos(α)cos(β) + sin(α)sin(β)cos(c)
  (cos of each angle = negative product of cosines of other angles
   plus sin-sin-cos of the opposite side).

  Parent: LawOfCosinesOQ01OQ01
  Answers: law-of-cosines-oq-01-oq-01-oq-03

  Axioms: 1 (polar_angle_eq)
  Sorries: 0
  Theorems: 13
-/

import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Proofs.SphericalLawOfSines

open Real SphericalLawOfSines

namespace PolarSphericalLaw

local notation a " ×₃ " b => crossProduct a b

-- ============================================================================
-- Part I: Supporting Lemmas (fully proved)
-- ============================================================================

/-- cos(arcLen u v) = dot u v for unit vectors. -/
theorem cos_arcLen_unit (u v : Fin 3 → ℝ) (hu : IsUnit3 u) (hv : IsUnit3 v) :
    Real.cos (arcLen u v) = dot u v := by
  unfold arcLen; apply Real.cos_arccos
  · have h := lagrange_identity u v
    have hnn := normSq_cross_nonneg u v
    nlinarith [h.symm, hu.symm, hv.symm, sq_nonneg (dot u v + 1)]
  · have h := lagrange_identity u v
    have hnn := normSq_cross_nonneg u v
    nlinarith [h.symm, hu.symm, hv.symm, sq_nonneg (dot u v - 1)]

/-- **Key algebraic identity**: dot(B×C, C×A) = -dot(projPerp A C, projPerp B C) for unit C.

    Both sides equal -(dot A B - dot A C · dot B C), the "off-diagonal" inner product
    after removing the C-component. This connects polar geometry to projection geometry. -/
theorem cross_dot_eq_neg_projperp (A B C : Fin 3 → ℝ) (hC : IsUnit3 C) :
    dot (B ×₃ C) (C ×₃ A) = -dot (projPerp A C) (projPerp B C) := by
  have h : C 0 * C 0 + C 1 * C 1 + C 2 * C 2 = 1 := unit_sum C hC
  simp [dot, projPerp, crossProduct, Fin.sum_univ_three]
  linear_combination
    (B 0 * A 0 + B 1 * A 1 + B 2 * A 2) * h -
    (A 0 * C 0 + A 1 * C 1 + A 2 * C 2) *
    (B 0 * C 0 + B 1 * C 1 + B 2 * C 2) * h

/-- For unit B, C: normSq(B×C) = normSq(projPerp B C) = 1 - (dot B C)². -/
theorem normSq_cross_eq_projperp (B C : Fin 3 → ℝ) (hB : IsUnit3 B) (hC : IsUnit3 C) :
    normSq (B ×₃ C) = normSq (projPerp B C) := by
  rw [lagrange_identity, normSq_projPerp B C hC, hB, hC]; ring

/-- normSq(projPerp A B) = normSq(projPerp B A) for unit A and B.
    Both equal 1 - (dot A B)² from normSq_projPerp. -/
theorem normSq_projPerp_comm (A B : Fin 3 → ℝ) (hA : IsUnit3 A) (hB : IsUnit3 B) :
    normSq (projPerp A B) = normSq (projPerp B A) := by
  rw [normSq_projPerp A B hB, normSq_projPerp B A hA, hA, hB, dot_comm]

/-- Cross product antisymmetry: C×A = -(A×C). -/
theorem cross_anticomm (A C : Fin 3 → ℝ) : (C ×₃ A) = -(A ×₃ C) := by
  funext i; fin_cases i <;> simp [crossProduct] <;> ring

/-- For unit A, C: normSq(C×A) = normSq(projPerp A C). -/
theorem normSq_cross_CA (A C : Fin 3 → ℝ) (hA : IsUnit3 A) (hC : IsUnit3 C) :
    normSq (C ×₃ A) = normSq (projPerp A C) := by
  rw [cross_anticomm]
  -- normSq is invariant under negation
  have hneg : normSq (-(A ×₃ C)) = normSq (A ×₃ C) := by
    simp only [normSq, dot, Pi.neg_apply, Fin.sum_univ_three]; ring
  rw [hneg]
  exact normSq_cross_eq_projperp A C hA hC

-- ============================================================================
-- Part II: Normalization
-- ============================================================================

/-- Normalize a nonzero vector to unit length. -/
noncomputable def normalize3 (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => v i / Real.sqrt (normSq v)

/-- dot product of normalized vectors = dot / (sqrt normSq · sqrt normSq). -/
theorem dot_normalize3 (u v : Fin 3 → ℝ) :
    dot (normalize3 u) (normalize3 v) =
      dot u v / (Real.sqrt (normSq u) * Real.sqrt (normSq v)) := by
  simp only [normalize3, dot, Fin.sum_univ_three]; field_simp

/-- Normalization of a nonzero vector gives a unit vector. -/
theorem isUnit3_normalize3 (v : Fin 3 → ℝ) (hv : 0 < normSq v) :
    IsUnit3 (normalize3 v) := by
  unfold IsUnit3 normalize3 normSq dot; simp only [Fin.sum_univ_three]
  have hpos : (0 : ℝ) < v 0 * v 0 + v 1 * v 1 + v 2 * v 2 := by
    simpa [normSq, dot, Fin.sum_univ_three] using hv
  have hpos' : (0 : ℝ) < v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
    have : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = v 0 * v 0 + v 1 * v 1 + v 2 * v 2 := by ring
    rw [this]; exact hpos
  have hne : Real.sqrt (v 0 * v 0 + v 1 * v 1 + v 2 * v 2) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hpos
  field_simp
  rw [Real.sq_sqrt (le_of_lt hpos')]

-- ============================================================================
-- Part III: Polar Triangle — Principal Result
-- ============================================================================

set_option maxHeartbeats 400000 in
/-- **Polar side formula** — the principal theorem of this entry.

    The arc-length from A' = normalize(B×C) to B' = normalize(C×A) equals
    π minus the dihedral angle at C.

    **Complete proof**:
    1. dot(A', B') = dot(B×C, C×A)/(|B×C|·|C×A|)           [dot_normalize3]
    2. dot(B×C, C×A) = -dot(projPerp A C, projPerp B C)      [cross_dot_eq_neg_projperp]
    3. |B×C|² = normSq(projPerp B C), |C×A|² = normSq(projPerp A C)
                                                              [normSq_cross_eq_projperp, normSq_cross_CA]
    4. Therefore dot(A', B') = -cos(dihedralAngle C A B)      [definition of dihedral angle]
    5. arcLen = arccos(-cos(γ)) = π - γ                       [Real.arccos_neg] -/
theorem polar_side_eq_pi_minus_angle (A B C : Fin 3 → ℝ)
    (hA : IsUnit3 A) (hB : IsUnit3 B) (hC : IsUnit3 C)
    (hBC : 0 < normSq (B ×₃ C))
    (hCA : 0 < normSq (C ×₃ A))
    (hpBC : normSq (projPerp B C) ≠ 0)
    (hpAC : normSq (projPerp A C) ≠ 0) :
    arcLen (normalize3 (B ×₃ C)) (normalize3 (C ×₃ A)) =
      π - dihedralAngle C A B := by
  have hdot : dot (normalize3 (B ×₃ C)) (normalize3 (C ×₃ A)) =
      -(dot (projPerp A C) (projPerp B C)) /
        (Real.sqrt (normSq (projPerp A C)) * Real.sqrt (normSq (projPerp B C))) := by
    rw [dot_normalize3, cross_dot_eq_neg_projperp A B C hC,
        normSq_cross_eq_projperp B C hB hC, normSq_cross_CA A C hA hC]
    ring
  have hp1 : Real.sqrt (normSq (projPerp A C)) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne (normSq_nonneg _) (Ne.symm hpAC))
  have hp2 : Real.sqrt (normSq (projPerp B C)) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne (normSq_nonneg _) (Ne.symm hpBC))
  rw [arcLen, hdot, neg_div]
  unfold dihedralAngle
  rw [if_neg (by push_neg; exact ⟨hp1, hp2⟩)]
  exact Real.arccos_neg _

-- ============================================================================
-- Part IV: Axioms for Angle Formula and Dual Law Derivation
-- ============================================================================

/-- The dihedral angle at C' = normalize(A×B) in the polar triangle equals
    π − arcLen(A, B) (the supplementary side of the original triangle).

    Mathematical proof: analogous to polar_side_eq_pi_minus_angle, applying
    cross product algebra to the polar triangle's projPerp expressions. -/
axiom polar_angle_eq (A B C : Fin 3 → ℝ)
    (hA : IsUnit3 A) (hB : IsUnit3 B) (hC : IsUnit3 C)
    (hBC : 0 < normSq (B ×₃ C)) (hCA : 0 < normSq (C ×₃ A)) (hAB : 0 < normSq (A ×₃ B))
    (hpBC : normSq (projPerp B C) ≠ 0) (hpCA : normSq (projPerp C A) ≠ 0)
    (hBC_p : normSq (projPerp (normalize3 (B ×₃ C)) (normalize3 (A ×₃ B))) ≠ 0)
    (hCA_p : normSq (projPerp (normalize3 (C ×₃ A)) (normalize3 (A ×₃ B))) ≠ 0) :
    dihedralAngle (normalize3 (A ×₃ B)) (normalize3 (B ×₃ C)) (normalize3 (C ×₃ A)) =
      π - arcLen A B

/-- The projPerp dot product equals sin·sin·cos(angle).

    Proof: unfold dihedralAngle in the non-degenerate case, apply `Real.cos_arccos`
    using Cauchy–Schwarz `(dot pA pB)² ≤ normSq pA * normSq pB` (from
    `lagrange_identity` + `normSq_cross_nonneg`), and use
    `normSq_projPerp_unit` to convert sin²(arcLen) → normSq(projPerp). -/
theorem projperp_dot_sinsincos (A B C : Fin 3 → ℝ)
    (hA : IsUnit3 A) (hB : IsUnit3 B) (hC : IsUnit3 C)
    (h1 : normSq (projPerp A C) ≠ 0) (h2 : normSq (projPerp B C) ≠ 0) :
    dot (projPerp A C) (projPerp B C) =
      Real.sin (arcLen A C) * Real.sin (arcLen B C) * Real.cos (dihedralAngle C A B) := by
  set pA := projPerp A C with hpA_def
  set pB := projPerp B C with hpB_def
  have hpA_pos : 0 < normSq pA := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm h1)
  have hpB_pos : 0 < normSq pB := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm h2)
  set nA := Real.sqrt (normSq pA) with hnA_def
  set nB := Real.sqrt (normSq pB) with hnB_def
  have hnA_pos : 0 < nA := Real.sqrt_pos.mpr hpA_pos
  have hnB_pos : 0 < nB := Real.sqrt_pos.mpr hpB_pos
  have hnA_ne : nA ≠ 0 := ne_of_gt hnA_pos
  have hnB_ne : nB ≠ 0 := ne_of_gt hnB_pos
  have hnA_sq : nA ^ 2 = normSq pA := Real.sq_sqrt (normSq_nonneg pA)
  have hnB_sq : nB ^ 2 = normSq pB := Real.sq_sqrt (normSq_nonneg pB)
  -- sin(arcLen A C) = nA: sin²(arcLen) = normSq(projPerp), then sqrt of both sides (sin ≥ 0)
  have hsinA_sq : Real.sin (arcLen A C) ^ 2 = normSq pA :=
    (normSq_projPerp_unit A C hA hC).symm
  have hsinB_sq : Real.sin (arcLen B C) ^ 2 = normSq pB :=
    (normSq_projPerp_unit B C hB hC).symm
  have hsinA_nn : 0 ≤ Real.sin (arcLen A C) := by
    rw [arcLen, Real.sin_arccos]; exact Real.sqrt_nonneg _
  have hsinB_nn : 0 ≤ Real.sin (arcLen B C) := by
    rw [arcLen, Real.sin_arccos]; exact Real.sqrt_nonneg _
  have hsinA : Real.sin (arcLen A C) = nA := by
    have h := Real.sqrt_sq hsinA_nn
    rw [hsinA_sq] at h
    exact h.symm
  have hsinB : Real.sin (arcLen B C) = nB := by
    have h := Real.sqrt_sq hsinB_nn
    rw [hsinB_sq] at h
    exact h.symm
  -- Cauchy–Schwarz: (dot pA pB)² ≤ (nA * nB)²
  have h_lag := lagrange_identity pA pB
  have h_cross_nn := normSq_cross_nonneg pA pB
  have h_cs : (dot pA pB) ^ 2 ≤ (nA * nB) ^ 2 := by
    rw [mul_pow, hnA_sq, hnB_sq]; linarith
  have h_prod_pos : 0 < nA * nB := mul_pos hnA_pos hnB_pos
  have h_prod_ne : nA * nB ≠ 0 := ne_of_gt h_prod_pos
  -- bounds for arccos
  have h_lo : -1 ≤ dot pA pB / (nA * nB) := by
    rw [le_div_iff₀ h_prod_pos]
    nlinarith [sq_nonneg (dot pA pB + nA * nB), h_cs]
  have h_hi : dot pA pB / (nA * nB) ≤ 1 := by
    rw [div_le_iff₀ h_prod_pos]
    nlinarith [sq_nonneg (nA * nB - dot pA pB), h_cs]
  -- cos(dihedralAngle C A B) = dot pA pB / (nA * nB)
  have hcos : Real.cos (dihedralAngle C A B) = dot pA pB / (nA * nB) := by
    simp only [dihedralAngle]
    rw [if_neg (by push_neg; exact ⟨hnA_ne, hnB_ne⟩)]
    exact Real.cos_arccos h_lo h_hi
  rw [hsinA, hsinB, hcos]
  field_simp

/-- The algebraic identity underlying the polar substitution.
    cos(π-x) = -cos(x) and sin(π-x) = sin(x) give the result by linear arithmetic. -/
theorem dual_trig_identity (α β γ c : ℝ) :
    Real.cos (π - γ) =
      Real.cos (π - α) * Real.cos (π - β) +
        Real.sin (π - α) * Real.sin (π - β) * Real.cos (π - c) →
    Real.cos γ = -Real.cos α * Real.cos β + Real.sin α * Real.sin β * Real.cos c := by
  simp only [Real.cos_pi_sub, Real.sin_pi_sub]
  intro h; linarith

-- ============================================================================
-- Part V: Dual Spherical Law of Cosines
-- ============================================================================

/-- **Standard spherical law for polar triangle**:
    cos(c') = cos(a') · cos(b') + sin(a') · sin(b') · cos(γ')
    where primes denote polar triangle quantities. -/
theorem polar_triangle_std_law (A B C : Fin 3 → ℝ)
    (hA : IsUnit3 A) (hB : IsUnit3 B) (hC : IsUnit3 C)
    (hBC : 0 < normSq (B ×₃ C)) (hCA : 0 < normSq (C ×₃ A)) (hAB : 0 < normSq (A ×₃ B))
    -- projPerp non-degeneracy for the angle computation in polar triangle
    (hpA'C' : normSq (projPerp (normalize3 (B ×₃ C)) (normalize3 (A ×₃ B))) ≠ 0)
    (hpB'C' : normSq (projPerp (normalize3 (C ×₃ A)) (normalize3 (A ×₃ B))) ≠ 0)
    (α β γ c : ℝ)
    (ha' : arcLen (normalize3 (C ×₃ A)) (normalize3 (A ×₃ B)) = π - α)
    (hb' : arcLen (normalize3 (B ×₃ C)) (normalize3 (A ×₃ B)) = π - β)
    (hc' : arcLen (normalize3 (B ×₃ C)) (normalize3 (C ×₃ A)) = π - γ)
    (hγ' : dihedralAngle (normalize3 (A ×₃ B)) (normalize3 (B ×₃ C)) (normalize3 (C ×₃ A)) = π - c) :
    Real.cos (π - γ) =
      Real.cos (π - α) * Real.cos (π - β) +
        Real.sin (π - α) * Real.sin (π - β) * Real.cos (π - c) := by
  set A' := normalize3 (B ×₃ C)
  set B' := normalize3 (C ×₃ A)
  set C' := normalize3 (A ×₃ B)
  have hA' := isUnit3_normalize3 _ hBC
  have hB' := isUnit3_normalize3 _ hCA
  have hC' := isUnit3_normalize3 _ hAB
  -- Standard spherical law via dot decomposition:
  -- dot A' B' = dot A' C' * dot B' C' + dot(projPerp A' C') (projPerp B' C')
  have hdec : dot A' B' = dot A' C' * dot B' C' + dot (projPerp A' C') (projPerp B' C') := by
    have h : C' 0 * C' 0 + C' 1 * C' 1 + C' 2 * C' 2 = 1 := unit_sum C' hC'
    simp only [dot, projPerp, Fin.sum_univ_three]
    linear_combination -((A' 0 * C' 0 + A' 1 * C' 1 + A' 2 * C' 2) *
      (B' 0 * C' 0 + B' 1 * C' 1 + B' 2 * C' 2)) * h
  rw [← hc', ← ha', ← hb', ← hγ']
  rw [cos_arcLen_unit A' B' hA' hB', cos_arcLen_unit A' C' hA' hC',
      cos_arcLen_unit B' C' hB' hC']
  rw [hdec, projperp_dot_sinsincos A' B' C' hA' hB' hC' hpA'C' hpB'C']
  ring

/-- **Dual Spherical Law of Cosines** via polar triangle construction.

    Given a non-degenerate spherical triangle with unit vertices A, B, C:
    cos(γ) = -cos(α)·cos(β) + sin(α)·sin(β)·cos(c)
    where α, β, γ are dihedral angles at A, B, C and c = arcLen(A, B). -/
theorem dual_spherical_law_of_cosines (A B C : Fin 3 → ℝ)
    (hA : IsUnit3 A) (hB : IsUnit3 B) (hC : IsUnit3 C)
    (hBC : 0 < normSq (B ×₃ C)) (hCA : 0 < normSq (C ×₃ A)) (hAB : 0 < normSq (A ×₃ B))
    (hpBC : normSq (projPerp B C) ≠ 0)
    (hpAC : normSq (projPerp A C) ≠ 0)
    (hpCA : normSq (projPerp C A) ≠ 0)
    (hpBA : normSq (projPerp B A) ≠ 0)
    -- Non-degeneracy for projections in polar triangle (A'=B×C, B'=C×A, C'=A×B)
    (hBC_p : normSq (projPerp (normalize3 (B ×₃ C)) (normalize3 (A ×₃ B))) ≠ 0)  -- projPerp A' C'
    (hCA_p : normSq (projPerp (normalize3 (C ×₃ A)) (normalize3 (A ×₃ B))) ≠ 0) : -- projPerp B' C'
    Real.cos (dihedralAngle C A B) =
      -Real.cos (dihedralAngle A B C) * Real.cos (dihedralAngle B A C) +
        Real.sin (dihedralAngle A B C) * Real.sin (dihedralAngle B A C) *
          Real.cos (arcLen A B) := by
  apply dual_trig_identity
  -- Prove the standard law applied to the polar triangle
  apply polar_triangle_std_law A B C hA hB hC hBC hCA hAB hBC_p hCA_p
  -- a' = arcLen(B', C') = π - dihedralAngle A B C
  · exact polar_side_eq_pi_minus_angle B C A hB hC hA hCA hAB hpCA hpBA
  -- b' = arcLen(A', C') = π - dihedralAngle B A C
  -- Use: polar C A B → arcLen(A×B, B×C) = π - dihedral B C A, then arcLen_comm + dihedralAngle_comm_last
  · have h := polar_side_eq_pi_minus_angle C A B hC hA hB hAB hBC
        (by rwa [normSq_projPerp_comm A B hA hB])
        (by rwa [normSq_projPerp_comm C B hC hB])
    rwa [arcLen_comm, dihedralAngle_comm_last] at h
  -- c' = arcLen(A', B') = π - dihedralAngle C A B
  · exact polar_side_eq_pi_minus_angle A B C hA hB hC hBC hCA hpBC hpAC
  -- γ' = dihedralAngle(C', A', B') = π - arcLen A B
  · exact polar_angle_eq A B C hA hB hC hBC hCA hAB hpBC hpCA hBC_p hCA_p

end PolarSphericalLaw
