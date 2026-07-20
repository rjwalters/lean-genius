import Mathlib

open Finset

namespace ScratchMRCEq

/-- Lagrange / Binet–Cauchy identity for finite sums of reals. -/
theorem lagrange_sum_identity {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    ∑ i ∈ s, ∑ j ∈ s, (f i * g j - f j * g i) ^ 2
      = 2 * ((∑ i ∈ s, f i ^ 2) * (∑ j ∈ s, g j ^ 2) - (∑ i ∈ s, f i * g i) ^ 2) := by
  have hP1 : ∑ i ∈ s, ∑ j ∈ s, f i ^ 2 * g j ^ 2
      = (∑ i ∈ s, f i ^ 2) * (∑ j ∈ s, g j ^ 2) := (Finset.sum_mul_sum s s _ _).symm
  have hP2 : ∑ i ∈ s, ∑ j ∈ s, f j ^ 2 * g i ^ 2
      = (∑ i ∈ s, f i ^ 2) * (∑ j ∈ s, g j ^ 2) := by
    rw [Finset.sum_comm, ← Finset.sum_mul_sum]
  have hP3 : ∑ i ∈ s, ∑ j ∈ s, (f i * g i) * (f j * g j)
      = (∑ i ∈ s, f i * g i) ^ 2 := by
    rw [← Finset.sum_mul_sum, ← pow_two]
  calc ∑ i ∈ s, ∑ j ∈ s, (f i * g j - f j * g i) ^ 2
      = ∑ i ∈ s, ∑ j ∈ s,
          (f i ^ 2 * g j ^ 2 + f j ^ 2 * g i ^ 2 - 2 * ((f i * g i) * (f j * g j))) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = (∑ i ∈ s, ∑ j ∈ s, f i ^ 2 * g j ^ 2)
          + (∑ i ∈ s, ∑ j ∈ s, f j ^ 2 * g i ^ 2)
          - 2 * (∑ i ∈ s, ∑ j ∈ s, (f i * g i) * (f j * g j)) := by
        simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ = 2 * ((∑ i ∈ s, f i ^ 2) * (∑ j ∈ s, g j ^ 2) - (∑ i ∈ s, f i * g i) ^ 2) := by
        rw [hP1, hP2, hP3]; ring

/-- **Cauchy–Schwarz equality characterization (finite sums).**  For real sequences `f, g`
on a finite index set, the Cauchy–Schwarz inequality holds with *equality*,
`(∑ᵢ fᵢgᵢ)² = (∑ᵢ fᵢ²)(∑ⱼ gⱼ²)`, if and only if every 2×2 minor vanishes,
`fᵢgⱼ = fⱼgᵢ` for all `i, j` — i.e. the vectors `f` and `g` are proportional. -/
theorem cauchy_schwarz_eq_iff {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    (∑ i ∈ s, f i * g i) ^ 2 = (∑ i ∈ s, f i ^ 2) * (∑ j ∈ s, g j ^ 2) ↔
      ∀ i ∈ s, ∀ j ∈ s, f i * g j = f j * g i := by
  have hL := lagrange_sum_identity s f g
  constructor
  · intro heq
    have hzero : ∑ i ∈ s, ∑ j ∈ s, (f i * g j - f j * g i) ^ 2 = 0 := by
      rw [hL, heq]; ring
    have hnonneg : ∀ i ∈ s, 0 ≤ ∑ j ∈ s, (f i * g j - f j * g i) ^ 2 :=
      fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    have houter := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero
    intro i hi j hj
    have hinner := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => sq_nonneg (f i * g j - f j * g i))).mp (houter i hi)
    have hterm : f i * g j - f j * g i = 0 := sq_eq_zero_iff.mp (hinner j hj)
    linarith [hterm]
  · intro h
    have hzero : ∑ i ∈ s, ∑ j ∈ s, (f i * g j - f j * g i) ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
      rw [h i hi j hj]; ring
    rw [hzero] at hL
    linarith [hL]

/-- **Sharp Cauchy–Schwarz equality case of the MRC signal bound.**  For deterministic gains
`a`, signal amplitudes `sig`, and strictly positive branch noise variances `v`, the
maximal-ratio-combining bound `mrc_signal_sq_le` holds with *equality*,

    (∑ᵢ aᵢ·sigᵢ)² = (∑ᵢ aᵢ²·vᵢ) · (∑ᵢ sigᵢ²/vᵢ),

*if and only if* the gain vector is proportional to the matched-filter vector `sigᵢ/vᵢ`,
expressed cross-multiplied as `aᵢ·vᵢ·sigⱼ = aⱼ·vⱼ·sigᵢ` for all `i, j ∈ s`.  This identifies
the MRC optimum as exactly the *matched ray* `{a : aᵢ ∝ sigᵢ/vᵢ}`, sharpening `mrc_snr_le`
(a bare inequality) and generalizing `mrc_snr_matched` (the single point `aᵢ = sigᵢ/vᵢ`).
The engine is the Lagrange/Binet–Cauchy identity `lagrange_sum_identity` applied to the
Cauchy–Schwarz split `aᵢsigᵢ = (aᵢ√vᵢ)·(sigᵢ/√vᵢ)`. -/
theorem mrc_signal_sq_eq_iff {ι : Type*} (s : Finset ι) (a sig v : ι → ℝ)
    (hv : ∀ i ∈ s, 0 < v i) :
    (∑ i ∈ s, a i * sig i) ^ 2 = (∑ i ∈ s, a i ^ 2 * v i) * (∑ i ∈ s, sig i ^ 2 / v i) ↔
      ∀ i ∈ s, ∀ j ∈ s, a i * v i * sig j = a j * v j * sig i := by
  have e1 : ∀ i ∈ s, (a i * Real.sqrt (v i)) * (sig i / Real.sqrt (v i)) = a i * sig i := by
    intro i hi
    have hne : Real.sqrt (v i) ≠ 0 := Real.sqrt_ne_zero'.mpr (hv i hi)
    field_simp
  have e2 : ∀ i ∈ s, (a i * Real.sqrt (v i)) ^ 2 = a i ^ 2 * v i := by
    intro i hi; rw [mul_pow, Real.sq_sqrt (hv i hi).le]
  have e3 : ∀ i ∈ s, (sig i / Real.sqrt (v i)) ^ 2 = sig i ^ 2 / v i := by
    intro i hi; rw [div_pow, Real.sq_sqrt (hv i hi).le]
  rw [show (∑ i ∈ s, a i * sig i)
        = ∑ i ∈ s, (a i * Real.sqrt (v i)) * (sig i / Real.sqrt (v i))
        from (Finset.sum_congr rfl e1).symm,
      show (∑ i ∈ s, a i ^ 2 * v i) = ∑ i ∈ s, (a i * Real.sqrt (v i)) ^ 2
        from (Finset.sum_congr rfl e2).symm,
      show (∑ i ∈ s, sig i ^ 2 / v i) = ∑ j ∈ s, (sig j / Real.sqrt (v j)) ^ 2
        from (Finset.sum_congr rfl e3).symm,
      cauchy_schwarz_eq_iff s (fun i => a i * Real.sqrt (v i))
        (fun i => sig i / Real.sqrt (v i))]
  dsimp only
  refine forall_congr' fun i => imp_congr_right fun hi => forall_congr' fun j =>
    imp_congr_right fun hj => ?_
  have hxx : Real.sqrt (v i) * Real.sqrt (v i) = v i := Real.mul_self_sqrt (hv i hi).le
  have hyy : Real.sqrt (v j) * Real.sqrt (v j) = v j := Real.mul_self_sqrt (hv j hj).le
  have hxne : Real.sqrt (v i) ≠ 0 := Real.sqrt_ne_zero'.mpr (hv i hi)
  have hyne : Real.sqrt (v j) ≠ 0 := Real.sqrt_ne_zero'.mpr (hv j hj)
  constructor
  · intro h
    rw [← mul_div_assoc, ← mul_div_assoc, div_eq_div_iff hyne hxne] at h
    linear_combination h - (a i * sig j) * hxx + (a j * sig i) * hyy
  · intro h
    rw [← mul_div_assoc, ← mul_div_assoc, div_eq_div_iff hyne hxne]
    linear_combination h + (a i * sig j) * hxx - (a j * sig i) * hyy

/-- **MRC matched-ray achievability.**  Every gain vector on the matched ray, `aᵢ = c·sigᵢ/vᵢ`
for a scalar `c`, attains the Cauchy–Schwarz equality in the MRC signal bound.  Combined with
`mrc_signal_sq_eq_iff` this shows the optimum is achieved on the *entire* ray through the
matched-filter vector, not just at `c = 1` (`mrc_snr_matched`). -/
theorem mrc_matched_ray_eq {ι : Type*} (s : Finset ι) (c : ℝ) (sig v : ι → ℝ)
    (hv : ∀ i ∈ s, 0 < v i) :
    (∑ i ∈ s, (c * (sig i / v i)) * sig i) ^ 2
      = (∑ i ∈ s, (c * (sig i / v i)) ^ 2 * v i) * (∑ i ∈ s, sig i ^ 2 / v i) := by
  rw [mrc_signal_sq_eq_iff s (fun i => c * (sig i / v i)) sig v hv]
  intro i hi j hj
  have hvi : v i ≠ 0 := (hv i hi).ne'
  have hvj : v j ≠ 0 := (hv j hj).ne'
  field_simp
  ring

end ScratchMRCEq
