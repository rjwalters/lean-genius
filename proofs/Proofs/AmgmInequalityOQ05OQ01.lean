/-
  The equality case of Hölder's inequality for finite sums.

  For Hölder-conjugate exponents `p, q > 1` (`p⁻¹ + q⁻¹ = 1`) and nonnegative
  functions `f, g` on a finite index set `s`, Hölder's inequality states

      ∑ i, f i * g i ≤ (∑ i, f i ^ p) ^ (1/p) * (∑ i, g i ^ q) ^ (1/q).

  Mathlib provides this inequality (`Real.inner_le_Lp_mul_Lq_of_nonneg`) but does
  **not** characterise when equality holds.  This file fills that gap.  Writing
  `F = ∑ f i ^ p` and `G = ∑ g i ^ q`, the headline result is

      ∑ i, f i * g i = F ^ (1/p) * G ^ (1/q)
        ↔  ∀ i ∈ s,  G * f i ^ p = F * g i ^ q,

  i.e. equality holds **iff the vectors `(f i ^ p)` and `(g i ^ q)` are
  proportional** (the cross-multiplied form `G·fᵢᵖ = F·gᵢᵍ` is the proportionality
  condition, stated so that it degenerates gracefully when `F = 0` or `G = 0`).

  The proof rests on the *equality case of Young's inequality*
  `a*b = aᵖ/p + bᵍ/q ↔ aᵖ = bᵍ` (proved for `a, b > 0` in the parent entry
  `AmgmInequalityOQ05`; here extended to `a, b ≥ 0`).  Summing Young pointwise on
  unit-normalised vectors turns the slack `∑ (aᵖ/p + bᵍ/q − a·b)` into a sum of
  nonnegative terms which vanishes iff each term does — that is the equality case.

  All exponents are real, so `^` denotes `Real.rpow` throughout.

  Verified: 0 sorries, 0 axioms.
-/
import Mathlib
import Proofs.AmgmInequalityOQ05

open Real

namespace AmgmInequalityOQ05OQ01

/-- **Equality case of Young's inequality (nonnegative form).**  For
Hölder-conjugate exponents `p, q` and `a, b ≥ 0`,
`a * b = a ^ p / p + b ^ q / q ↔ a ^ p = b ^ q`.  This extends the parent entry's
`young_inequality_eq_iff` (stated for `a, b > 0`) to cover the boundary `a = 0`
or `b = 0`, where both sides reduce to "the other variable is `0`". -/
theorem young_eq_iff_nonneg {a b p q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hpq : p.HolderConjugate q) :
    a * b = a ^ p / p + b ^ q / q ↔ a ^ p = b ^ q := by
  have hp : (0 : ℝ) < p := hpq.pos
  have hq : (0 : ℝ) < q := hpq.symm.pos
  rcases ha.lt_or_eq with ha' | ha0
  · rcases hb.lt_or_eq with hb' | hb0
    · -- both positive: parent result
      exact AmgmInequalityOQ05.young_inequality_eq_iff ha' hb' hpq
    · -- b = 0
      subst hb0
      rw [mul_zero, Real.zero_rpow hq.ne', zero_div, add_zero, eq_comm, div_eq_zero_iff]
      simp [hp.ne']
  · -- a = 0
    subst ha0
    rw [zero_mul, Real.zero_rpow hp.ne', zero_div, zero_add, eq_comm, div_eq_zero_iff]
    simp [hq.ne', eq_comm]

/-- **Hölder's inequality for finite sums** (Mathlib re-export, ℝ-valued
nonnegative version), recorded here so the entry is self-contained. -/
theorem holder_sum_le {ι : Type*} (s : Finset ι) (f g : ι → ℝ) {p q : ℝ}
    (hpq : p.HolderConjugate q) (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) :
    ∑ i ∈ s, f i * g i ≤ (∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q) :=
  Real.inner_le_Lp_mul_Lq_of_nonneg s hpq hf hg

/-- **Equality case of Hölder's inequality — normalised form.**  When the
`Lᵖ`/`Lᵍ` norms are both `1` (`∑ f i ^ p = 1`, `∑ g i ^ q = 1`), equality in
Hölder `∑ f i * g i = 1` holds **iff** `f i ^ p = g i ^ q` for every `i ∈ s`.
This is the heart of the equality case: summing the pointwise Young inequality,
the slack is a sum of nonnegative terms, so it vanishes iff each Young inequality
is itself an equality. -/
theorem holder_sum_eq_iff_of_normalized {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i)
    (hfp : ∑ i ∈ s, f i ^ p = 1) (hgq : ∑ i ∈ s, g i ^ q = 1) :
    ∑ i ∈ s, f i * g i = 1 ↔ ∀ i ∈ s, f i ^ p = g i ^ q := by
  have hp : (0 : ℝ) < p := hpq.pos
  have hq : (0 : ℝ) < q := hpq.symm.pos
  -- slack of Young at each index
  set d : ι → ℝ := fun i => (f i ^ p / p + g i ^ q / q) - f i * g i with hd
  have hd_nonneg : ∀ i ∈ s, 0 ≤ d i := by
    intro i hi
    have := Real.young_inequality_of_nonneg (hf i hi) (hg i hi) hpq
    simp only [hd]; linarith
  have hsum_rhs : ∑ i ∈ s, (f i ^ p / p + g i ^ q / q) = 1 := by
    rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div, hfp, hgq, one_div, one_div,
      hpq.inv_add_inv_eq_one]
  have hsum_d : ∑ i ∈ s, d i = 1 - ∑ i ∈ s, f i * g i := by
    simp only [hd, Finset.sum_sub_distrib, hsum_rhs]
  constructor
  · intro h
    have hd0 : ∑ i ∈ s, d i = 0 := by rw [hsum_d, h]; ring
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hd_nonneg).mp hd0
    intro i hi
    have heq : f i * g i = f i ^ p / p + g i ^ q / q := by
      have := hall i hi; simp only [hd] at this; linarith
    exact (young_eq_iff_nonneg (hf i hi) (hg i hi) hpq).mp heq
  · intro h
    have hd0 : ∑ i ∈ s, d i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have heq : f i * g i = f i ^ p / p + g i ^ q / q :=
        (young_eq_iff_nonneg (hf i hi) (hg i hi) hpq).mpr (h i hi)
      simp only [hd]; linarith
    rw [hsum_d] at hd0; linarith

/-- **Equality case of Hölder's inequality for finite sums (general form).**
For Hölder-conjugate `p, q` and nonnegative `f, g` on a finite set `s`, equality

    ∑ i, f i * g i = (∑ i, f i ^ p) ^ (1/p) * (∑ i, g i ^ q) ^ (1/q)

holds **iff** the vectors `(f i ^ p)` and `(g i ^ q)` are proportional:

    ∀ i ∈ s,  (∑ j, g j ^ q) * f i ^ p = (∑ j, f j ^ p) * g i ^ q.

The cross-multiplied statement degenerates correctly when one of the sums is `0`
(then every `f i = 0`, resp. `g i = 0`, and both sides hold trivially). -/
theorem holder_sum_eq_iff {ι : Type*} (s : Finset ι) (f g : ι → ℝ) {p q : ℝ}
    (hpq : p.HolderConjugate q) (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) :
    ∑ i ∈ s, f i * g i = (∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q)
      ↔ ∀ i ∈ s, (∑ j ∈ s, g j ^ q) * f i ^ p = (∑ j ∈ s, f j ^ p) * g i ^ q := by
  have hp : (0 : ℝ) < p := hpq.pos
  have hq : (0 : ℝ) < q := hpq.symm.pos
  have hF : 0 ≤ ∑ i ∈ s, f i ^ p := Finset.sum_nonneg (fun i hi => Real.rpow_nonneg (hf i hi) p)
  have hG : 0 ≤ ∑ i ∈ s, g i ^ q := Finset.sum_nonneg (fun i hi => Real.rpow_nonneg (hg i hi) q)
  rcases eq_or_lt_of_le hF with hF0 | hFpos
  · -- F = 0
    have hfp0 : ∀ i ∈ s, f i ^ p = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i hi => Real.rpow_nonneg (hf i hi) p)).mp hF0.symm
    have hlhs : ∑ i ∈ s, f i * g i = 0 := by
      apply Finset.sum_eq_zero; intro i hi
      have hfi : f i = 0 := by
        by_contra hne
        exact (Real.rpow_pos_of_pos (lt_of_le_of_ne (hf i hi) (Ne.symm hne)) p).ne' (hfp0 i hi)
      rw [hfi, zero_mul]
    have hrhs : (∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q) = 0 := by
      rw [← hF0, Real.zero_rpow (one_div_ne_zero hp.ne'), zero_mul]
    constructor
    · intro _ i hi; rw [hfp0 i hi, ← hF0]; ring
    · intro _; rw [hlhs, hrhs]
  · rcases eq_or_lt_of_le hG with hG0 | hGpos
    · -- G = 0
      have hgq0 : ∀ i ∈ s, g i ^ q = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun i hi => Real.rpow_nonneg (hg i hi) q)).mp hG0.symm
      have hlhs : ∑ i ∈ s, f i * g i = 0 := by
        apply Finset.sum_eq_zero; intro i hi
        have hgi : g i = 0 := by
          by_contra hne
          exact (Real.rpow_pos_of_pos (lt_of_le_of_ne (hg i hi) (Ne.symm hne)) q).ne' (hgq0 i hi)
        rw [hgi, mul_zero]
      have hrhs : (∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q) = 0 := by
        rw [← hG0, Real.zero_rpow (one_div_ne_zero hq.ne'), mul_zero]
      constructor
      · intro _ i hi; rw [hgq0 i hi, ← hG0]; ring
      · intro _; rw [hlhs, hrhs]
    · -- F > 0 and G > 0: rescale to the normalised case
      set cF := (∑ i ∈ s, f i ^ p) ^ (1 / p) with hcF
      set cG := (∑ i ∈ s, g i ^ q) ^ (1 / q) with hcG
      have hcFpos : 0 < cF := Real.rpow_pos_of_pos hFpos _
      have hcGpos : 0 < cG := Real.rpow_pos_of_pos hGpos _
      have hcFp : cF ^ p = ∑ i ∈ s, f i ^ p := by
        rw [hcF, ← Real.rpow_mul hF, one_div, inv_mul_cancel₀ hp.ne', Real.rpow_one]
      have hcGq : cG ^ q = ∑ i ∈ s, g i ^ q := by
        rw [hcG, ← Real.rpow_mul hG, one_div, inv_mul_cancel₀ hq.ne', Real.rpow_one]
      have hf' : ∀ i ∈ s, 0 ≤ f i / cF := fun i hi => div_nonneg (hf i hi) hcFpos.le
      have hg' : ∀ i ∈ s, 0 ≤ g i / cG := fun i hi => div_nonneg (hg i hi) hcGpos.le
      have hfp' : ∑ i ∈ s, (f i / cF) ^ p = 1 := by
        have hpt : ∀ i ∈ s, (f i / cF) ^ p = f i ^ p / cF ^ p :=
          fun i hi => Real.div_rpow (hf i hi) hcFpos.le p
        rw [Finset.sum_congr rfl hpt, ← Finset.sum_div, hcFp, div_self hFpos.ne']
      have hgq' : ∑ i ∈ s, (g i / cG) ^ q = 1 := by
        have hpt : ∀ i ∈ s, (g i / cG) ^ q = g i ^ q / cG ^ q :=
          fun i hi => Real.div_rpow (hg i hi) hcGpos.le q
        rw [Finset.sum_congr rfl hpt, ← Finset.sum_div, hcGq, div_self hGpos.ne']
      have hnorm := holder_sum_eq_iff_of_normalized s (fun i => f i / cF) (fun i => g i / cG)
        hpq hf' hg' hfp' hgq'
      have hsum' : ∑ i ∈ s, (f i / cF) * (g i / cG) = (∑ i ∈ s, f i * g i) / (cF * cG) := by
        rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro i hi; rw [div_mul_div_comm]
      have hcFcG : cF * cG ≠ 0 := (mul_pos hcFpos hcGpos).ne'
      constructor
      · intro heq i hi
        have h1 : ∑ i ∈ s, (f i / cF) * (g i / cG) = 1 := by
          rw [hsum', heq, div_self hcFcG]
        have h2 := hnorm.mp h1 i hi
        dsimp only at h2
        rw [Real.div_rpow (hf i hi) hcFpos.le p, Real.div_rpow (hg i hi) hcGpos.le q,
          hcFp, hcGq, div_eq_div_iff hFpos.ne' hGpos.ne'] at h2
        linear_combination h2
      · intro hcond
        have h2 : ∀ i ∈ s, (f i / cF) ^ p = (g i / cG) ^ q := by
          intro i hi
          rw [Real.div_rpow (hf i hi) hcFpos.le p, Real.div_rpow (hg i hi) hcGpos.le q,
            hcFp, hcGq, div_eq_div_iff hFpos.ne' hGpos.ne']
          linear_combination hcond i hi
        have h1 := hnorm.mpr h2
        rw [hsum', div_eq_one_iff_eq hcFcG] at h1
        exact h1

end AmgmInequalityOQ05OQ01
