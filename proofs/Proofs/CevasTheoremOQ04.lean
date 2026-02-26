import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-
# Ceva's Theorem via Mass Point Geometry (OQ-04)

## Research Question

Can we formalize Ceva's theorem using the **mass point geometry** approach,
providing an algebraic certificate for concurrent cevians via mass assignments?

## Answer: YES

Mass point geometry assigns positive real "masses" mA, mB, mC to triangle vertices.
Each mass assignment induces cevian division points:

  D on BC:  D = (1-d)·B + d·C,  where d = mC/(mB+mC)
  E on CA:  E = (1-e)·C + e·A,  where e = mA/(mC+mA)
  F on AB:  F = (1-f)·A + f·B,  where f = mB/(mA+mB)

**Key algebraic miracle**: rD·rE·rF = (1-rD)·(1-rE)·(1-rF) for ANY mass assignment,
because both sides equal mA·mB·mC / ((mB+mC)(mC+mA)(mA+mB)).

The converse (Ceva condition → mass assignment exists) is constructive:
given d·e·f = (1-d)·(1-e)·(1-f), set mA = 1, mC = (1-e)/e, mB = (1-e)(1-d)/(ed).

## Mathematical Significance

Mass point geometry is often taught in olympiad mathematics as an elementary
alternative to coordinate or trigonometric Ceva proofs. This formalization:
1. Shows mass points are just a bookkeeping device for ratio arithmetic
2. Provides an explicit constructive certificate (the mass assignment)
3. Connects to the physics interpretation (center of mass / lever arm balance)
-/

namespace MassPointCeva

/-- A mass point assignment for a triangle: positive masses at vertices A, B, C. -/
structure MassPoint where
  mA : ℝ
  mB : ℝ
  mC : ℝ
  hA : 0 < mA
  hB : 0 < mB
  hC : 0 < mC

-- Useful derived positivity facts
lemma MassPoint.hBC (mp : MassPoint) : 0 < mp.mB + mp.mC := add_pos mp.hB mp.hC
lemma MassPoint.hCA (mp : MassPoint) : 0 < mp.mC + mp.mA := add_pos mp.hC mp.hA
lemma MassPoint.hAB (mp : MassPoint) : 0 < mp.mA + mp.mB := add_pos mp.hA mp.hB

/-- D divides BC with parameter d = mC/(mB+mC). -/
noncomputable def rD (mp : MassPoint) : ℝ := mp.mC / (mp.mB + mp.mC)

/-- E divides CA with parameter e = mA/(mC+mA). -/
noncomputable def rE (mp : MassPoint) : ℝ := mp.mA / (mp.mC + mp.mA)

/-- F divides AB with parameter f = mB/(mA+mB). -/
noncomputable def rF (mp : MassPoint) : ℝ := mp.mB / (mp.mA + mp.mB)

/- ## Basic Positivity and Bounds -/

lemma rD_pos (mp : MassPoint) : 0 < rD mp :=
  div_pos mp.hC mp.hBC

lemma rE_pos (mp : MassPoint) : 0 < rE mp :=
  div_pos mp.hA mp.hCA

lemma rF_pos (mp : MassPoint) : 0 < rF mp :=
  div_pos mp.hB mp.hAB

lemma rD_lt_one (mp : MassPoint) : rD mp < 1 := by
  rw [rD, div_lt_one mp.hBC]
  linarith [mp.hB]

lemma rE_lt_one (mp : MassPoint) : rE mp < 1 := by
  rw [rE, div_lt_one mp.hCA]
  linarith [mp.hC]

lemma rF_lt_one (mp : MassPoint) : rF mp < 1 := by
  rw [rF, div_lt_one mp.hAB]
  linarith [mp.hA]

/-- 1 - rD = mB/(mB+mC). -/
lemma one_sub_rD (mp : MassPoint) : 1 - rD mp = mp.mB / (mp.mB + mp.mC) := by
  have h := mp.hBC.ne'
  simp only [rD]
  field_simp
  ring

lemma one_sub_rE (mp : MassPoint) : 1 - rE mp = mp.mC / (mp.mC + mp.mA) := by
  have h := mp.hCA.ne'
  simp only [rE]
  field_simp
  ring

lemma one_sub_rF (mp : MassPoint) : 1 - rF mp = mp.mA / (mp.mA + mp.mB) := by
  have h := mp.hAB.ne'
  simp only [rF]
  field_simp
  ring

/- ## Main Algebraic Identity -/

/-- **Mass Point Ceva Identity**: For any mass assignment, rD·rE·rF = (1-rD)·(1-rE)·(1-rF).
    Both sides equal mA·mB·mC / ((mB+mC)·(mC+mA)·(mA+mB)). -/
theorem ceva_identity (mp : MassPoint) :
    rD mp * rE mp * rF mp = (1 - rD mp) * (1 - rE mp) * (1 - rF mp) := by
  rw [one_sub_rD, one_sub_rE, one_sub_rF]
  simp only [rD, rE, rF]
  have hBC := mp.hBC.ne'
  have hCA := mp.hCA.ne'
  have hAB := mp.hAB.ne'
  field_simp

/- ## Converse: Mass Assignment from Ceva Condition -/

/-- **Existence of mass assignment**: Given d·e·f = (1-d)·(1-e)·(1-f) with all
    parameters in (0,1), an explicit mass assignment realizes these ratios. -/
theorem masses_from_ceva (d e f : ℝ)
    (hd : 0 < d) (hd' : d < 1)
    (he : 0 < e) (he' : e < 1)
    (hf : 0 < f) (_hf' : f < 1)
    (hceva : d * e * f = (1 - d) * (1 - e) * (1 - f)) :
    ∃ mp : MassPoint, rD mp = d ∧ rE mp = e ∧ rF mp = f := by
  have h1e : 0 < 1 - e := by linarith
  have h1d : 0 < 1 - d := by linarith
  have hde_pos : 0 < e * d := mul_pos he hd
  let mA : ℝ := 1
  let mC : ℝ := (1 - e) / e
  let mB : ℝ := (1 - e) * (1 - d) / (e * d)
  have hmA : 0 < mA := one_pos
  have hmC : 0 < mC := div_pos h1e he
  have hmB : 0 < mB := div_pos (mul_pos h1e h1d) hde_pos
  refine ⟨⟨mA, mB, mC, hmA, hmB, hmC⟩, ?_, ?_, ?_⟩
  · -- rD = d: mC/(mB+mC) = ((1-e)/e) / (((1-e)(1-d)/(ed)) + (1-e)/e) = d
    show mC / (mB + mC) = d
    show (1 - e) / e / ((1 - e) * (1 - d) / (e * d) + (1 - e) / e) = d
    have he_ne : e ≠ 0 := he.ne'
    have hd_ne : d ≠ 0 := hd.ne'
    field_simp
    ring
  · -- rE = e: mA/(mC+mA) = 1/((1-e)/e + 1) = e
    show mA / (mC + mA) = e
    show 1 / ((1 - e) / e + 1) = e
    have he_ne : e ≠ 0 := he.ne'
    field_simp
    ring
  · -- rF = f: uses the Ceva condition
    show mB / (mA + mB) = f
    show (1 - e) * (1 - d) / (e * d) / (1 + (1 - e) * (1 - d) / (e * d)) = f
    have he_ne : e ≠ 0 := he.ne'
    have hd_ne : d ≠ 0 := hd.ne'
    field_simp
    nlinarith [mul_pos h1e h1d, mul_pos he hd, mul_pos hf (mul_pos h1d h1e)]

/- ## Biconditional -/

/-- **Mass Point Ceva Theorem** (biconditional):
    Parameters d, e, f ∈ (0,1) satisfy the Ceva condition
    if and only if there exists a mass assignment realizing these ratios. -/
theorem mass_point_iff (d e f : ℝ)
    (hd : 0 < d) (hd' : d < 1)
    (he : 0 < e) (he' : e < 1)
    (hf : 0 < f) (hf' : f < 1) :
    d * e * f = (1 - d) * (1 - e) * (1 - f) ↔
    ∃ mp : MassPoint, rD mp = d ∧ rE mp = e ∧ rF mp = f := by
  constructor
  · exact masses_from_ceva d e f hd hd' he he' hf hf'
  · rintro ⟨mp, hd_eq, he_eq, hf_eq⟩
    rw [← hd_eq, ← he_eq, ← hf_eq]
    exact ceva_identity mp

/- ## Ratio Balance Lemmas -/

/-- **Lever arm balance**: BD/DC = mC/mB. -/
theorem ratio_balance (mp : MassPoint) :
    rD mp / (1 - rD mp) = mp.mC / mp.mB := by
  rw [one_sub_rD]
  simp only [rD]
  have hBC := mp.hBC.ne'
  have hB := mp.hB.ne'
  field_simp

theorem ratio_balance_E (mp : MassPoint) :
    rE mp / (1 - rE mp) = mp.mA / mp.mC := by
  rw [one_sub_rE]
  simp only [rE]
  have hCA := mp.hCA.ne'
  have hC := mp.hC.ne'
  field_simp

theorem ratio_balance_F (mp : MassPoint) :
    rF mp / (1 - rF mp) = mp.mB / mp.mA := by
  rw [one_sub_rF]
  simp only [rF]
  have hAB := mp.hAB.ne'
  have hA := mp.hA.ne'
  field_simp

/- ## Ceva Product in Ratio Form -/

/-- **Ceva product = 1**: (BD/DC)·(CE/EA)·(AF/FB) = (mC/mB)·(mA/mC)·(mB/mA) = 1. -/
theorem ceva_ratio_product_one (mp : MassPoint) :
    (rD mp / (1 - rD mp)) * (rE mp / (1 - rE mp)) * (rF mp / (1 - rF mp)) = 1 := by
  rw [ratio_balance, ratio_balance_E, ratio_balance_F]
  have hA := mp.hA.ne'
  have hB := mp.hB.ne'
  have hC := mp.hC.ne'
  field_simp

/- ## Concrete Example: Centroid via Equal Masses -/

/-- The centroid corresponds to equal masses: d = e = f = 1/2. -/
theorem centroid_example : ∃ mp : MassPoint, rD mp = 1/2 ∧ rE mp = 1/2 ∧ rF mp = 1/2 :=
  ⟨⟨1, 1, 1, one_pos, one_pos, one_pos⟩,
   by norm_num [rD], by norm_num [rE], by norm_num [rF]⟩

/-- Centroid satisfies the Ceva condition: (1/2)³ = (1/2)³. -/
theorem centroid_ceva : (1/2 : ℝ) * (1/2) * (1/2) = (1 - 1/2) * (1 - 1/2) * (1 - 1/2) := by
  norm_num

/- ## Summary -/

/-- **Mass Point Ceva Theorem Summary**:
    (1) Ceva condition ↔ mass assignment exists
    (2) Any mass assignment satisfies the Ceva identity
    (3) The ratio product = 1 for any mass assignment -/
theorem ceva_mass_point_summary (d e f : ℝ)
    (hd : 0 < d) (hd' : d < 1)
    (he : 0 < e) (he' : e < 1)
    (hf : 0 < f) (hf' : f < 1) :
    (d * e * f = (1 - d) * (1 - e) * (1 - f) ↔
     ∃ mp : MassPoint, rD mp = d ∧ rE mp = e ∧ rF mp = f) ∧
    (∀ mp : MassPoint, rD mp * rE mp * rF mp = (1 - rD mp) * (1 - rE mp) * (1 - rF mp)) ∧
    (∀ mp : MassPoint,
      (rD mp / (1 - rD mp)) * (rE mp / (1 - rE mp)) * (rF mp / (1 - rF mp)) = 1) :=
  ⟨mass_point_iff d e f hd hd' he he' hf hf',
   ceva_identity,
   ceva_ratio_product_one⟩

end MassPointCeva
