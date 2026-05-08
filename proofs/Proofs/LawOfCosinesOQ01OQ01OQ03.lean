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

  Axioms: 0 (was 1; polar_angle_eq proved 2026-05-08, Session 4)
  Sorries: 0
  Theorems: 16
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

/-- **Cross-of-crosses identity**: `(C ×₃ A) ×₃ (A ×₃ B) = tripleProduct A B C • A`.

    A specialization of the BAC-CAB rule `u × (v × w) = (u·w)v - (u·v)w` with
    `u = C×A`, `v = A`, `w = B`: `(C×A)·B = tripleProduct A B C` (cyclic) and
    `(C×A)·A = 0` (cross is perpendicular to A). No unit hypothesis needed. -/
theorem cross_CA_cross_AB (A B C : Fin 3 → ℝ) :
    (C ×₃ A) ×₃ (A ×₃ B) = tripleProduct A B C • A := by
  funext i; fin_cases i <;>
    simp [tripleProduct, dot, crossProduct, Fin.sum_univ_three,
          Pi.smul_apply, smul_eq_mul] <;>
    ring

/-- **Cross-of-crosses identity**: `(A ×₃ B) ×₃ (B ×₃ C) = tripleProduct A B C • B`.

    Specialization of BAC-CAB with `u = A×B`, `v = B`, `w = C`:
    `(A×B)·C = tripleProduct A B C` (cyclic) and `(A×B)·B = 0`. -/
theorem cross_AB_cross_BC (A B C : Fin 3 → ℝ) :
    (A ×₃ B) ×₃ (B ×₃ C) = tripleProduct A B C • B := by
  funext i; fin_cases i <;>
    simp [tripleProduct, dot, crossProduct, Fin.sum_univ_three,
          Pi.smul_apply, smul_eq_mul] <;>
    ring

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
-- Part IV: Polar Angle Formula and Dihedral Identity (axiom-free)
-- ============================================================================

set_option maxHeartbeats 800000 in
/-- **[PROVED]** The dihedral angle at `C' = normalize(A×B)` in the polar triangle
    equals `π − arcLen(A, B)` — the supplementary side of the original triangle.

    **Proof strategy** (the polar of the polar is the original, up to sign):

    1. Apply `polar_side_eq_pi_minus_angle` to the polar triangle's vertices
       `A' = normalize(B×C), B' = normalize(C×A), C' = normalize(A×B)`. This yields
       `arcLen(normalize(B' × C'), normalize(C' × A')) = π - dihedralAngle(C', A', B')`.

    2. Compute `B' × C' = (t/(nCA·nAB)) • A` and `C' × A' = (t/(nAB·nBC)) • B`,
       where `t = tripleProduct A B C` and `n_uv = sqrt(normSq(u×v))`. This uses the
       BAC-CAB-style cross-of-crosses identities `cross_CA_cross_AB`, `cross_AB_cross_BC`.

    3. The non-degeneracy hypothesis `hBC_p` forces `t ≠ 0` (since
       `normSq(projPerp B' C') = normSq(B' × C') = (t/(nCA·nAB))² > 0`).

    4. Compute `dot(normalize(B' × C'), normalize(C' × A')) = dot A B` directly:
       both vectors are positive scalar multiples of `±A` and `±B` respectively, with
       matching signs (both `sign(t)`), so `sign² = 1` cancels and the dot product
       reduces to `dot A B`.

    5. Hence `arcLen(normalize(B' × C'), normalize(C' × A')) = arccos(dot A B) =
       arcLen A B`, and step 1 gives `arcLen A B = π - dihedralAngle(C', A', B')`. -/
theorem polar_angle_eq (A B C : Fin 3 → ℝ)
    (hA : IsUnit3 A) (hB : IsUnit3 B) (hC : IsUnit3 C)
    (hBC : 0 < normSq (B ×₃ C)) (hCA : 0 < normSq (C ×₃ A)) (hAB : 0 < normSq (A ×₃ B))
    (hpBC : normSq (projPerp B C) ≠ 0) (hpCA : normSq (projPerp C A) ≠ 0)
    (hBC_p : normSq (projPerp (normalize3 (B ×₃ C)) (normalize3 (A ×₃ B))) ≠ 0)
    (hCA_p : normSq (projPerp (normalize3 (C ×₃ A)) (normalize3 (A ×₃ B))) ≠ 0) :
    dihedralAngle (normalize3 (A ×₃ B)) (normalize3 (B ×₃ C)) (normalize3 (C ×₃ A)) =
      π - arcLen A B := by
  set A' := normalize3 (B ×₃ C) with hA'_def
  set B' := normalize3 (C ×₃ A) with hB'_def
  set C' := normalize3 (A ×₃ B) with hC'_def
  have hA'_unit : IsUnit3 A' := isUnit3_normalize3 _ hBC
  have hB'_unit : IsUnit3 B' := isUnit3_normalize3 _ hCA
  have hC'_unit : IsUnit3 C' := isUnit3_normalize3 _ hAB
  -- Step 1: Apply polar_side_eq_pi_minus_angle to the polar triangle (A', B', C')
  have h_cross_BC' : 0 < normSq (B' ×₃ C') := by
    rw [normSq_cross_eq_projperp B' C' hB'_unit hC'_unit]
    exact lt_of_le_of_ne (normSq_nonneg _) (Ne.symm hBC_p)
  have h_cross_CA' : 0 < normSq (C' ×₃ A') := by
    rw [normSq_cross_CA A' C' hA'_unit hC'_unit]
    exact lt_of_le_of_ne (normSq_nonneg _) (Ne.symm hCA_p)
  have h_polar_polar :
      arcLen (normalize3 (B' ×₃ C')) (normalize3 (C' ×₃ A')) =
        π - dihedralAngle C' A' B' :=
    polar_side_eq_pi_minus_angle A' B' C' hA'_unit hB'_unit hC'_unit
      h_cross_BC' h_cross_CA' hBC_p hCA_p
  -- Step 2: Express B' × C' and C' × A' via the cross-cross identities
  set nBC := Real.sqrt (normSq (B ×₃ C)) with hnBC_def
  set nCA := Real.sqrt (normSq (C ×₃ A)) with hnCA_def
  set nAB := Real.sqrt (normSq (A ×₃ B)) with hnAB_def
  have hnBC_pos : 0 < nBC := Real.sqrt_pos.mpr hBC
  have hnCA_pos : 0 < nCA := Real.sqrt_pos.mpr hCA
  have hnAB_pos : 0 < nAB := Real.sqrt_pos.mpr hAB
  have hnBC_ne : nBC ≠ 0 := ne_of_gt hnBC_pos
  have hnCA_ne : nCA ≠ 0 := ne_of_gt hnCA_pos
  have hnAB_ne : nAB ≠ 0 := ne_of_gt hnAB_pos
  set t := tripleProduct A B C with ht_def
  -- B' = (1/nCA) • (C ×₃ A), C' = (1/nAB) • (A ×₃ B), so B' ×₃ C' = (1/(nCA·nAB)) • ((C×A)×(A×B)) = (t/(nCA·nAB)) • A
  have hBxC : B' ×₃ C' = (t / (nCA * nAB)) • A := by
    have h_id : (C ×₃ A) ×₃ (A ×₃ B) = t • A := cross_CA_cross_AB A B C
    funext i
    have h_id_i : ((C ×₃ A) ×₃ (A ×₃ B)) i = t * A i := by
      rw [h_id]; simp [Pi.smul_apply, smul_eq_mul]
    have hB'_i : ∀ j, B' j = (C ×₃ A) j / nCA := by
      intro j; simp only [hB'_def, normalize3]
    have hC'_i : ∀ j, C' j = (A ×₃ B) j / nAB := by
      intro j; simp only [hC'_def, normalize3]
    show (B' ×₃ C') i = (t / (nCA * nAB)) * A i
    fin_cases i <;> (
      simp only [crossProduct, LinearMap.mk₂_apply, Matrix.cons_val_zero,
                 Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one] at h_id_i ⊢
      rw [hB'_i, hB'_i, hC'_i, hC'_i]
      field_simp
      linarith [h_id_i])
  -- Similarly C' ×₃ A' = (t/(nAB·nBC)) • B
  have hCxA : C' ×₃ A' = (t / (nAB * nBC)) • B := by
    have h_id : (A ×₃ B) ×₃ (B ×₃ C) = t • B := cross_AB_cross_BC A B C
    funext i
    have h_id_i : ((A ×₃ B) ×₃ (B ×₃ C)) i = t * B i := by
      rw [h_id]; simp [Pi.smul_apply, smul_eq_mul]
    have hA'_i : ∀ j, A' j = (B ×₃ C) j / nBC := by
      intro j; simp only [hA'_def, normalize3]
    have hC'_i : ∀ j, C' j = (A ×₃ B) j / nAB := by
      intro j; simp only [hC'_def, normalize3]
    show (C' ×₃ A') i = (t / (nAB * nBC)) * B i
    fin_cases i <;> (
      simp only [crossProduct, LinearMap.mk₂_apply, Matrix.cons_val_zero,
                 Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one] at h_id_i ⊢
      rw [hA'_i, hA'_i, hC'_i, hC'_i]
      field_simp
      linarith [h_id_i])
  -- Step 3: t ≠ 0 from non-degeneracy
  have ht_sq_pos : 0 < t ^ 2 := by
    have h1 : 0 < normSq (projPerp B' C') :=
      lt_of_le_of_ne (normSq_nonneg _) (Ne.symm hBC_p)
    rw [normSq_cross_eq_projperp B' C' hB'_unit hC'_unit] at h1
    -- normSq (B' ×₃ C') = (t/(nCA·nAB))² · normSq A = (t/(nCA·nAB))² (unit A)
    rw [hBxC] at h1
    have hnsA : normSq ((t / (nCA * nAB)) • A) = (t / (nCA * nAB)) ^ 2 := by
      simp [normSq, dot, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
      have hA_sum : A 0 * A 0 + A 1 * A 1 + A 2 * A 2 = 1 := unit_sum A hA
      nlinarith [hA_sum]
    rw [hnsA] at h1
    have h_pos_denom : 0 < nCA * nAB := mul_pos hnCA_pos hnAB_pos
    have h_pos_denom_ne : nCA * nAB ≠ 0 := ne_of_gt h_pos_denom
    have h_div_sq : (t / (nCA * nAB)) ^ 2 = t ^ 2 / (nCA * nAB) ^ 2 := by ring
    rw [h_div_sq] at h1
    nlinarith [sq_nonneg (nCA * nAB)]
  have ht_ne : t ≠ 0 := by
    intro hcontra; rw [hcontra] at ht_sq_pos; norm_num at ht_sq_pos
  -- Step 4: Compute dot(normalize3(B'×C'), normalize3(C'×A')) = dot A B
  -- normalize3(k • A) for unit A and k ≠ 0 = (k/|k|) • A; product of signs = +1 since both same sign as t
  have h_normalize_smul_A :
      normalize3 (B' ×₃ C') = ((t / (nCA * nAB)) / |t / (nCA * nAB)|) • A := by
    rw [hBxC]
    funext i
    show (((t / (nCA * nAB)) • A) i) / Real.sqrt (normSq ((t / (nCA * nAB)) • A))
        = (t / (nCA * nAB)) / |t / (nCA * nAB)| * A i
    have hns : normSq ((t / (nCA * nAB)) • A) = (t / (nCA * nAB)) ^ 2 := by
      simp [normSq, dot, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
      have hA_sum : A 0 * A 0 + A 1 * A 1 + A 2 * A 2 = 1 := unit_sum A hA
      nlinarith [hA_sum]
    rw [normalize3, hns, Real.sqrt_sq_eq_abs]
    simp [Pi.smul_apply, smul_eq_mul]
    field_simp
  have h_normalize_smul_B :
      normalize3 (C' ×₃ A') = ((t / (nAB * nBC)) / |t / (nAB * nBC)|) • B := by
    rw [hCxA]
    funext i
    show (((t / (nAB * nBC)) • B) i) / Real.sqrt (normSq ((t / (nAB * nBC)) • B))
        = (t / (nAB * nBC)) / |t / (nAB * nBC)| * B i
    have hns : normSq ((t / (nAB * nBC)) • B) = (t / (nAB * nBC)) ^ 2 := by
      simp [normSq, dot, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
      have hB_sum : B 0 * B 0 + B 1 * B 1 + B 2 * B 2 = 1 := unit_sum B hB
      nlinarith [hB_sum]
    rw [normalize3, hns, Real.sqrt_sq_eq_abs]
    simp [Pi.smul_apply, smul_eq_mul]
    field_simp
  -- Both signs equal sign(t), so the product is +1
  have h_sign_A : (t / (nCA * nAB)) / |t / (nCA * nAB)| =
      if 0 < t then 1 else -1 := by
    have h_denom_pos : 0 < nCA * nAB := mul_pos hnCA_pos hnAB_pos
    by_cases ht_pos : 0 < t
    · simp [ht_pos]
      have h_pos : 0 < t / (nCA * nAB) := div_pos ht_pos h_denom_pos
      rw [abs_of_pos h_pos]; field_simp
    · push_neg at ht_pos
      have h_neg : t < 0 := lt_of_le_of_ne ht_pos ht_ne
      have h_div_neg : t / (nCA * nAB) < 0 := div_neg_of_neg_of_pos h_neg h_denom_pos
      simp [not_lt.mpr (le_of_lt h_neg), h_neg]
      rw [abs_of_neg h_div_neg]; field_simp
  have h_sign_B : (t / (nAB * nBC)) / |t / (nAB * nBC)| =
      if 0 < t then 1 else -1 := by
    have h_denom_pos : 0 < nAB * nBC := mul_pos hnAB_pos hnBC_pos
    by_cases ht_pos : 0 < t
    · simp [ht_pos]
      have h_pos : 0 < t / (nAB * nBC) := div_pos ht_pos h_denom_pos
      rw [abs_of_pos h_pos]; field_simp
    · push_neg at ht_pos
      have h_neg : t < 0 := lt_of_le_of_ne ht_pos ht_ne
      have h_div_neg : t / (nAB * nBC) < 0 := div_neg_of_neg_of_pos h_neg h_denom_pos
      simp [not_lt.mpr (le_of_lt h_neg), h_neg]
      rw [abs_of_neg h_div_neg]; field_simp
  -- Compute dot product
  have h_dot_eq : dot (normalize3 (B' ×₃ C')) (normalize3 (C' ×₃ A')) = dot A B := by
    rw [h_normalize_smul_A, h_normalize_smul_B, h_sign_A, h_sign_B]
    by_cases ht_pos : 0 < t
    · simp [ht_pos, dot, Pi.smul_apply, smul_eq_mul]
    · simp [ht_pos, dot, Pi.smul_apply, smul_eq_mul]
      ring
  -- Step 5: Combine — arcLen(normalize3(B' × C'), normalize3(C' × A')) = arcLen A B
  have h_arclen_eq : arcLen (normalize3 (B' ×₃ C')) (normalize3 (C' ×₃ A')) = arcLen A B := by
    rw [arcLen, arcLen, h_dot_eq]
  rw [h_arclen_eq] at h_polar_polar
  linarith

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
