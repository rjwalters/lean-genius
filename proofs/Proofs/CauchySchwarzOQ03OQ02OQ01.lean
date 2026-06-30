/-
  Reverse Minkowski Inequality for 0 < p < 1 (from Reverse Hölder)
  Open Question: cauchy-schwarz-oq-03-oq-02-oq-01

  This file answers the open question raised by the parent
  `CauchySchwarzOQ03OQ02.lean` ("Minkowski from Hölder", forward case `p ≥ 1`):

    "For 0 < p < 1 the p-functional ‖v‖_p = (∑ vᵢ^p)^(1/p) is only a quasi-norm
     and the triangle inequality REVERSES. Can that reversed inequality be
     formalized in the same Hölder-based style?"

  Answer: YES. For nonnegative `a, b` and `0 < p < 1`,

    (∑ (aᵢ+bᵢ)^p)^(1/p)  ≥  (∑ aᵢ^p)^(1/p) + (∑ bᵢ^p)^(1/p)          (RM)

  the opposite of forward Minkowski (`p ≥ 1`). The functional `‖·‖_p` is a genuine
  norm only for `p ≥ 1`; for `0 < p < 1` it is a positively-homogeneous *concave*
  quasi-norm, hence **super**additive — which is exactly (RM).

  Engine: the **reverse Hölder inequality** for `0 < p < 1`. With the conjugate
  exponent `q = p/(p-1) < 0` (so `1/p + 1/q = 1`) and `v > 0`,

    (∑ uᵢ^p)^(1/p) · (∑ vᵢ^q)^(1/q)  ≤  ∑ uᵢ vᵢ                       (RH)

  again the reverse of forward Hölder. Mathlib has **no** `0 < p < 1` Hölder or
  Minkowski lemma — every Hölder statement is gated on `Real.HolderConjugate p q`,
  whose fields force `p, q > 1`. So (RM)/(RH) cannot be obtained by instantiating
  an existing Mathlib lemma; the reverse direction is built here.

  Proof of (RH): apply *forward* Hölder
  `NNReal.inner_le_Lp_mul_Lq` with the conjugate pair `P = 1/p > 1`,
  `P' = 1/(1-p) > 1` to the functions `fᵢ = (uᵢvᵢ)^p`, `gᵢ = vᵢ^(-p)`.
  Unwinding `fᵢ gᵢ = uᵢ^p`, `fᵢ^P = uᵢvᵢ`, `gᵢ^{P'} = vᵢ^q` yields
  `∑ uᵢ^p ≤ (∑ uᵢvᵢ)^p · (∑ vᵢ^q)^{1-p}`, and raising to the power `1/p` and
  reorganising gives (RH).

  Proof of (RM): the classical Riesz argument, run with (RH) in place of forward
  Hölder. Split `∑(a+b)^p = ∑ a·(a+b)^{p-1} + ∑ b·(a+b)^{p-1}`, apply (RH) to each
  summand with weight `v = (a+b)^{p-1}` (note `vᵢ^q = (aᵢ+bᵢ)^p`), add, and divide
  by the common factor `(∑(a+b)^p)^{1/q}`.

  Key Results:
  1. `reverse_holder`       — reverse Hölder (RH), `0 < p < 1`, `v > 0`.
  2. `reverse_minkowski`    — reverse Minkowski (RM), `0 < p < 1`, `a+b > 0`.
  3. `reverse_minkowski_half` — the `p = 1/2` instance `(∑√a)²+(∑√b)² ≤ (∑√(a+b))²`.

  All three are `0` sorries / `0` axioms (the ordinary `propext`/`Classical.choice`/
  `Quot.sound` only).

  Numerical certification (durable): `verify_reverse_minkowski.py` checks (RM),
  the equality locus (proportional vectors), and the (RH) engine over 70 000
  random trials with 0 violations.

  References:
  - Hardy–Littlewood–Pólya, "Inequalities" (1934), §2.8 (reverse Hölder /
    Minkowski for `0 < p < 1`).
  - F. Riesz (1910): the Hölder ⇒ Minkowski deduction (here run in reverse).
-/

import Mathlib

open Finset NNReal

namespace ReverseMinkowski

/-- **Reverse Hölder inequality** for `0 < p < 1`.

For nonnegative `u` and strictly positive `v`, with conjugate exponent
`q = p/(p-1) < 0` (so `1/p + 1/q = 1`),

  `(∑ uᵢ^p)^(1/p) · (∑ vᵢ^q)^(1/q) ≤ ∑ uᵢ vᵢ`.

The inequality is the reverse of forward Hölder and is proved *from* forward
Hölder (`NNReal.inner_le_Lp_mul_Lq`) by the exponent substitution
`P = 1/p`, `P' = 1/(1-p)`, `fᵢ = (uᵢvᵢ)^p`, `gᵢ = vᵢ^(-p)`. -/
theorem reverse_holder {ι : Type*} (s : Finset ι) (u v : ι → ℝ≥0)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hs : s.Nonempty) (hv : ∀ i ∈ s, 0 < v i) :
    (∑ i ∈ s, u i ^ p) ^ (1 / p) * (∑ i ∈ s, v i ^ (p / (p - 1))) ^ (1 / (p / (p - 1)))
      ≤ ∑ i ∈ s, u i * v i := by
  have hp0' : p ≠ 0 := hp0.ne'
  have hpm1 : p - 1 ≠ 0 := by linarith
  have h1p : (0:ℝ) < 1 - p := by linarith
  -- conjugate pair `P = 1/p`, `P' = 1/(1-p)`, both `> 1`
  have hconj : (p⁻¹).HolderConjugate ((1 - p)⁻¹) :=
    Real.HolderConjugate.inv_one_sub_inv hp0 hp1
  -- forward Hölder applied to `f = (u·v)^p`, `g = v^(-p)`
  have hf := NNReal.inner_le_Lp_mul_Lq s (fun i => (u i * v i) ^ p) (fun i => v i ^ (-p)) hconj
  simp only at hf
  -- the inner product collapses to `∑ u^p`
  have hLHS : ∑ i ∈ s, (u i * v i) ^ p * v i ^ (-p) = ∑ i ∈ s, u i ^ p := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [NNReal.mul_rpow, mul_assoc, ← NNReal.rpow_add (hv i hi).ne', add_neg_cancel,
      NNReal.rpow_zero, mul_one]
  -- first L^P factor reduces to `(∑ u v)^p`
  have hR1 : (∑ i ∈ s, ((u i * v i) ^ p) ^ p⁻¹) ^ (1 / p⁻¹) = (∑ i ∈ s, u i * v i) ^ p := by
    have he : (1:ℝ) / p⁻¹ = p := by rw [one_div, inv_inv]
    rw [he]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [← NNReal.rpow_mul, mul_inv_cancel₀ hp0', NNReal.rpow_one]
  -- second L^{P'} factor reduces to `(∑ v^q)^(1-p)`
  have hR2 : (∑ i ∈ s, (v i ^ (-p)) ^ (1 - p)⁻¹) ^ (1 / (1 - p)⁻¹)
      = (∑ i ∈ s, v i ^ (p / (p - 1))) ^ (1 - p) := by
    have he : (1:ℝ) / (1 - p)⁻¹ = 1 - p := by rw [one_div, inv_inv]
    have hexp : (-p) * (1 - p)⁻¹ = p / (p - 1) := by
      rw [mul_inv_eq_iff_eq_mul₀ h1p.ne', div_mul_eq_mul_div, eq_div_iff hpm1]; ring
    rw [he]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [← NNReal.rpow_mul, hexp]
  rw [hLHS, hR1, hR2] at hf
  -- hf : ∑ u^p ≤ (∑ u v)^p * (∑ v^(p/(p-1)))^(1-p)
  set A := ∑ i ∈ s, u i ^ p with hA
  set B := ∑ i ∈ s, u i * v i with hB
  set C := ∑ i ∈ s, v i ^ (p / (p - 1)) with hC
  have hCpos : 0 < C := by
    rw [hC]; exact Finset.sum_pos (fun i hi => NNReal.rpow_pos (hv i hi)) hs
  have hCne : C ≠ 0 := hCpos.ne'
  -- raise the goal to the power `p` and reduce both sides
  rw [← NNReal.rpow_le_rpow_iff hp0, NNReal.mul_rpow, ← NNReal.rpow_mul, ← NNReal.rpow_mul]
  have e1 : (1 / p) * p = 1 := by field_simp
  have e2 : (1 / (p / (p - 1))) * p = p - 1 := by field_simp
  rw [e1, e2, NNReal.rpow_one]
  calc A * C ^ (p - 1) ≤ (B ^ p * C ^ (1 - p)) * C ^ (p - 1) := by gcongr
    _ = B ^ p := by
        rw [mul_assoc, ← NNReal.rpow_add hCne]
        have : (1 - p) + (p - 1) = 0 := by ring
        rw [this, NNReal.rpow_zero, mul_one]

/-- **Reverse Minkowski inequality** for `0 < p < 1`.

For nonnegative `a, b` with `aᵢ + bᵢ > 0`,

  `(∑ aᵢ^p)^(1/p) + (∑ bᵢ^p)^(1/p) ≤ (∑ (aᵢ+bᵢ)^p)^(1/p)`.

This reverses the forward triangle inequality `p ≥ 1` proved in the parent: for
`0 < p < 1` the `p`-quasi-norm is superadditive. Proved by the Riesz argument run
with `reverse_holder` in place of forward Hölder. -/
theorem reverse_minkowski {ι : Type*} (s : Finset ι) (a b : ι → ℝ≥0)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hs : s.Nonempty)
    (hab : ∀ i ∈ s, 0 < a i + b i) :
    (∑ i ∈ s, a i ^ p) ^ (1 / p) + (∑ i ∈ s, b i ^ p) ^ (1 / p)
      ≤ (∑ i ∈ s, (a i + b i) ^ p) ^ (1 / p) := by
  have hp0' : p ≠ 0 := hp0.ne'
  have hpm1 : p - 1 ≠ 0 := by linarith
  set q := p / (p - 1) with hq
  -- weight `w i = (a i + b i)^(p-1) > 0`
  set w : ι → ℝ≥0 := fun i => (a i + b i) ^ (p - 1) with hw
  have hwpos : ∀ i ∈ s, 0 < w i := fun i hi => NNReal.rpow_pos (hab i hi)
  set S := ∑ i ∈ s, (a i + b i) ^ p with hS
  have hSpos : 0 < S := by
    rw [hS]; exact Finset.sum_pos (fun i hi => NNReal.rpow_pos (hab i hi)) hs
  have hSne : S ≠ 0 := hSpos.ne'
  -- `∑ wᵢ^q = ∑ (a+b)^p = S`
  have hwq : ∑ i ∈ s, w i ^ q = S := by
    rw [hS]; apply Finset.sum_congr rfl; intro i hi
    rw [hw, ← NNReal.rpow_mul]
    congr 1
    rw [hq]; field_simp
  -- reverse Hölder applied to `(a, w)` and `(b, w)`
  have ha := reverse_holder s a w hp0 hp1 hs hwpos
  have hb := reverse_holder s b w hp0 hp1 hs hwpos
  rw [hwq, ← hq] at ha hb
  -- the two right-hand sides reassemble to `S`
  have hsplit : (∑ i ∈ s, a i * w i) + (∑ i ∈ s, b i * w i) = S := by
    rw [← Finset.sum_add_distrib, hS]
    apply Finset.sum_congr rfl; intro i hi
    have hexp : (a i + b i) ^ p = (a i + b i) ^ (1 : ℝ) * (a i + b i) ^ (p - 1) := by
      rw [← NNReal.rpow_add (hab i hi).ne']; congr 1; ring
    rw [hw, ← add_mul, hexp, NNReal.rpow_one]
  have hkey : ((∑ i ∈ s, a i ^ p) ^ (1 / p) + (∑ i ∈ s, b i ^ p) ^ (1 / p)) * S ^ (1 / q) ≤ S := by
    rw [add_mul]
    calc (∑ i ∈ s, a i ^ p) ^ (1 / p) * S ^ (1 / q)
          + (∑ i ∈ s, b i ^ p) ^ (1 / p) * S ^ (1 / q)
        ≤ (∑ i ∈ s, a i * w i) + (∑ i ∈ s, b i * w i) := add_le_add ha hb
      _ = S := hsplit
  -- divide by the positive factor `S^(1/q)`; `1/p + 1/q = 1`
  apply le_of_mul_le_mul_right _ (NNReal.rpow_pos hSpos (p := 1 / q))
  calc ((∑ i ∈ s, a i ^ p) ^ (1 / p) + (∑ i ∈ s, b i ^ p) ^ (1 / p)) * S ^ (1 / q)
      ≤ S := hkey
    _ = (∑ i ∈ s, (a i + b i) ^ p) ^ (1 / p) * S ^ (1 / q) := by
        rw [← hS, ← NNReal.rpow_add hSne]
        have : (1 / p) + (1 / q) = 1 := by rw [hq]; field_simp; ring
        rw [this, NNReal.rpow_one]

/-- Reverse Minkowski at the representative exponent `p = 1/2`:
    `(∑ √aᵢ)² + (∑ √bᵢ)² ≤ (∑ √(aᵢ+bᵢ))²`. -/
theorem reverse_minkowski_half {ι : Type*} (s : Finset ι) (a b : ι → ℝ≥0)
    (hs : s.Nonempty) (hab : ∀ i ∈ s, 0 < a i + b i) :
    (∑ i ∈ s, a i ^ (1/2 : ℝ)) ^ (2 : ℝ) + (∑ i ∈ s, b i ^ (1/2 : ℝ)) ^ (2 : ℝ)
      ≤ (∑ i ∈ s, (a i + b i) ^ (1/2 : ℝ)) ^ (2 : ℝ) := by
  have h := reverse_minkowski s a b (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) < 1) hs hab
  have e : (1 : ℝ) / (1/2) = 2 := by norm_num
  rwa [e] at h

end ReverseMinkowski
