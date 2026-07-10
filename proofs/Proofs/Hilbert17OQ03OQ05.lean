/-
  Hilbert's 17th problem — the sharp PSD threshold of the Motzkin family, and
  the SOS failure across that whole family.

  The Motzkin polynomial `M(x, y) = x⁴y² + x²y⁴ + 1 − 3 x²y²` is the canonical
  example of a positive-semidefinite (PSD) polynomial that is *not* a sum of
  squares of polynomials.  Its parent entry establishes both facts; the
  non-SOS side is the deep content (it underlies the parent open question on the
  computational complexity of *deciding* whether a PSD polynomial is SOS, and on
  *quantifying* the PSD/SOS gap).

  This file studies the one-parameter family

      Mₐ(x, y) = x⁴y² + x²y⁴ + 1 − c·x²y²,   c ∈ ℝ.

  ## Sharp PSD threshold

  We prove the exact threshold

      Mₐ is PSD on ℝ²   ⟺   c ≤ 3,

  so the Motzkin polynomial (`c = 3`) sits exactly on the boundary of the PSD
  cone for this family.  This pins down *why* `3` is the canonical coefficient:
  it is the largest constant for which non-negativity survives.

    * `c ≤ 3 ⟹ PSD`: the AM–GM step `x⁴y² + x²y⁴ + 1 ≥ 3 x²y²` (an honest
      sum-of-squares certificate, found by `nlinarith`) dominates the deficit
      `(3 − c)·x²y² ≥ 0`.
    * `c > 3 ⟹ not PSD`: evaluate at `(1, 1)`, where `Mₐ(1,1) = 3 − c < 0`.

  ## SOS failure across the family

  The threshold locates the family inside the PSD cone.  The complementary,
  deeper fact is membership in the *SOS* cone.  We prove `motzkinPoly_not_sos`:
  **every** member with `c > 0` fails to be a sum of squares of polynomials —
  not just the boundary case `c = 3` (that case is the parent entry's
  `Hilbert17MotzkinNotSOS.motzkin_not_sos`).  Combined with the threshold this
  yields a genuine one-parameter family of PSD-but-not-SOS polynomials
  (`0 < c ≤ 3`, `motzkinPoly_psd_not_sos`), with the Motzkin polynomial at the
  extreme, PSD-boundary corner.

  The non-SOS proof reuses the elementary coefficient machinery of the parent
  non-SOS entry: in any SOS decomposition the coefficient `[x²y²]` is a sum of
  real squares, hence `≥ 0`, whereas for `motzkinPoly c` it equals `-c < 0`.
  Only the `x²y²` coefficient carries `c`; every pure-axis coefficient is
  `c`-independent and vanishes exactly as in the `c = 3` case, so the whole
  degree-bound and pure-axis-vanishing argument transfers verbatim.

  Everything is `0`-axiom, over `ℝ` and `MvPolynomial (Fin 2) ℝ`.
-/
import Mathlib
import Proofs.Hilbert17MotzkinNotSOS

namespace Hilbert17OQ03OQ05

open MvPolynomial
open Hilbert17MotzkinNotSOS

/-! ## The family as a real two-variable function -/

/-- The Motzkin family evaluated at real arguments:
    `Mₐ(x, y) = x⁴y² + x²y⁴ + 1 − c·x²y²`. -/
def motzkinFun (c x y : ℝ) : ℝ :=
  x ^ 4 * y ^ 2 + x ^ 2 * y ^ 4 + 1 - c * (x ^ 2 * y ^ 2)

/-- **AM–GM core.**  `x⁴y² + x²y⁴ + 1 ≥ 3 x²y²` for all real `x, y`.  This is a
    genuine sum-of-squares certificate (the affine Motzkin form has one, even
    though the homogeneous Motzkin polynomial does not). -/
theorem motzkin_amgm (x y : ℝ) :
    3 * (x ^ 2 * y ^ 2) ≤ x ^ 4 * y ^ 2 + x ^ 2 * y ^ 4 + 1 := by
  nlinarith [sq_nonneg (x * y - 1), sq_nonneg (x ^ 2 * y - y),
    sq_nonneg (x * y ^ 2 - x), sq_nonneg (x * y),
    mul_nonneg (sq_nonneg x) (sq_nonneg y), sq_nonneg (x ^ 2 * y ^ 2 - 1)]

/-- **Non-negativity for `c ≤ 3`.**  For every coefficient `c ≤ 3` the family
    `Mₐ` is non-negative everywhere. -/
theorem motzkinFun_nonneg {c : ℝ} (hc : c ≤ 3) (x y : ℝ) :
    0 ≤ motzkinFun c x y := by
  have hsq : (0 : ℝ) ≤ x ^ 2 * y ^ 2 :=
    mul_nonneg (sq_nonneg x) (sq_nonneg y)
  have hdef : c * (x ^ 2 * y ^ 2) ≤ 3 * (x ^ 2 * y ^ 2) := by
    exact mul_le_mul_of_nonneg_right hc hsq
  have hamgm := motzkin_amgm x y
  unfold motzkinFun
  linarith

/-- **Failure for `c > 3`.**  At `(x, y) = (1, 1)` the value is `3 − c < 0`,
    so the family is not PSD once `c` exceeds `3`. -/
theorem motzkinFun_neg_of_gt {c : ℝ} (hc : 3 < c) :
    motzkinFun c 1 1 < 0 := by
  unfold motzkinFun
  nlinarith [hc]

/-- **Sharp PSD threshold (real form).**  The family `Mₐ` is non-negative on all
    of `ℝ²` if and only if `c ≤ 3`.  Thus `c = 3` (the Motzkin polynomial) is the
    extremal PSD member of the family. -/
theorem motzkinFun_psd_iff (c : ℝ) :
    (∀ x y : ℝ, 0 ≤ motzkinFun c x y) ↔ c ≤ 3 := by
  constructor
  · intro h
    have h11 := h 1 1
    unfold motzkinFun at h11
    norm_num at h11
    linarith
  · intro hc x y
    exact motzkinFun_nonneg hc x y

/-- The Motzkin polynomial itself (`c = 3`) is PSD — the boundary case of the
    threshold. -/
theorem motzkin_nonneg (x y : ℝ) : 0 ≤ motzkinFun 3 x y :=
  motzkinFun_nonneg (le_refl 3) x y

/-- `3` is the **largest** coefficient for which the family is PSD: any strictly
    larger `c` fails non-negativity (witnessed at `(1,1)`). -/
theorem three_is_sharp {c : ℝ} (hPSD : ∀ x y : ℝ, 0 ≤ motzkinFun c x y) :
    c ≤ 3 := (motzkinFun_psd_iff c).1 hPSD

/-! ## The family as a genuine `MvPolynomial (Fin 2) ℝ`

We repackage the same threshold for the polynomial object, matching the parent
entry's `IsPositiveSemidefiniteMv` formulation. -/

/-- The Motzkin family as a bivariate polynomial:
    `X₀⁴ X₁² + X₀² X₁⁴ + 1 − c·X₀² X₁²`. -/
noncomputable def motzkinPoly (c : ℝ) : MvPolynomial (Fin 2) ℝ :=
  X 0 ^ 4 * X 1 ^ 2 + X 0 ^ 2 * X 1 ^ 4 + 1 - C c * (X 0 ^ 2 * X 1 ^ 2)

/-- A multivariate polynomial is PSD if it is non-negative for all real inputs
    (matching `Hilbert17.IsPositiveSemidefiniteMv` in the parent file). -/
def IsPSDMv (p : MvPolynomial (Fin 2) ℝ) : Prop :=
  ∀ v : Fin 2 → ℝ, 0 ≤ MvPolynomial.eval v p

/-- Evaluating `motzkinPoly` recovers the real function `motzkinFun`. -/
@[simp] theorem eval_motzkinPoly (c : ℝ) (v : Fin 2 → ℝ) :
    MvPolynomial.eval v (motzkinPoly c) = motzkinFun c (v 0) (v 1) := by
  unfold motzkinPoly motzkinFun
  simp only [map_add, map_sub, map_mul, map_pow, map_one, eval_X, eval_C]

/-- **Sharp PSD threshold (polynomial form).**  `motzkinPoly c` is PSD if and
    only if `c ≤ 3`. -/
theorem motzkinPoly_psd_iff (c : ℝ) : IsPSDMv (motzkinPoly c) ↔ c ≤ 3 := by
  unfold IsPSDMv
  constructor
  · intro h
    have h11 := h (fun _ => 1)
    simp only [eval_motzkinPoly] at h11
    -- `motzkinFun c 1 1 = 3 - c`, so `0 ≤ 3 - c`.
    unfold motzkinFun at h11
    norm_num at h11
    linarith
  · intro hc v
    rw [eval_motzkinPoly]
    exact motzkinFun_nonneg hc (v 0) (v 1)

/-- The Motzkin polynomial (`c = 3`) is PSD as a bivariate polynomial — the
    boundary member of the family. -/
theorem motzkinPoly_three_psd : IsPSDMv (motzkinPoly 3) :=
  (motzkinPoly_psd_iff 3).2 (le_refl 3)

/-! ## The SOS failure across the whole family

We prove that **every** member with `c > 0` fails to be a sum of squares of
polynomials.  The proof reuses the elementary coefficient machinery of the
parent non-SOS entry `Hilbert17MotzkinNotSOS`: the coefficient `[x²y²]` of any
SOS decomposition is a sum of real squares, hence `≥ 0`, whereas for
`motzkinPoly c` it equals `-c < 0`.  Only the `x²y²` coefficient carries `c`;
every pure-axis coefficient is `c`-independent and vanishes exactly as in the
`c = 3` case. -/

/-- Monomial normal form of the family polynomial, matching the `mon` bookkeeping
    of the parent non-SOS entry. -/
theorem motzkinPoly_eq (c : ℝ) :
    motzkinPoly c = monomial (mon 4 2) 1 + monomial (mon 2 4) 1
      + monomial (mon 0 0) 1 - monomial (mon 2 2) c := by
  have hc : (C c * (X 0 ^ 2 * X 1 ^ 2) : MvPolynomial (Fin 2) ℝ) = monomial (mon 2 2) c := by
    rw [Xpp 2 2, C_mul_monomial, mul_one]
  rw [motzkinPoly, Xpp 4 2, Xpp 2 4, hc,
    show (1 : MvPolynomial (Fin 2) ℝ) = monomial (mon 0 0) 1 by
      rw [show mon 0 0 = 0 by simp [mon], monomial_zero', map_one]]

/-- The needed coefficients of `motzkinPoly c`, read off from the monomial form. -/
private theorem coeff_mP (c : ℝ) (a b : ℕ) :
    coeff (mon a b) (motzkinPoly c) =
      (if (4 = a ∧ 2 = b) then 1 else 0) + (if (2 = a ∧ 4 = b) then 1 else 0)
        + (if (0 = a ∧ 0 = b) then 1 else 0) - (if (2 = a ∧ 2 = b) then c else 0) := by
  rw [motzkinPoly_eq]
  simp only [coeff_add, coeff_sub, coeff_monomial, mon_eq_iff]

theorem coeff_mP_22 (c : ℝ) : coeff (mon 2 2) (motzkinPoly c) = -c := by
  rw [coeff_mP]; norm_num
theorem coeff_mP_20 (c : ℝ) : coeff (mon 2 0) (motzkinPoly c) = 0 := by rw [coeff_mP]; norm_num
theorem coeff_mP_40 (c : ℝ) : coeff (mon 4 0) (motzkinPoly c) = 0 := by rw [coeff_mP]; norm_num
theorem coeff_mP_60 (c : ℝ) : coeff (mon 6 0) (motzkinPoly c) = 0 := by rw [coeff_mP]; norm_num
theorem coeff_mP_02 (c : ℝ) : coeff (mon 0 2) (motzkinPoly c) = 0 := by rw [coeff_mP]; norm_num
theorem coeff_mP_04 (c : ℝ) : coeff (mon 0 4) (motzkinPoly c) = 0 := by rw [coeff_mP]; norm_num
theorem coeff_mP_06 (c : ℝ) : coeff (mon 0 6) (motzkinPoly c) = 0 := by rw [coeff_mP]; norm_num

theorem totalDegree_motzkinPoly (c : ℝ) : (motzkinPoly c).totalDegree ≤ 6 := by
  rw [motzkinPoly_eq]
  have hm : ∀ a b : ℕ, a + b ≤ 6 → ∀ r : ℝ, (monomial (mon a b) r).totalDegree ≤ 6 := by
    intro a b hab r
    calc (monomial (mon a b) r).totalDegree ≤ (mon a b).degree := totalDegree_monomial_le _ _
      _ = a + b := degree_mon a b
      _ ≤ 6 := hab
  refine le_trans (totalDegree_sub _ _) (max_le ?_ (hm 2 2 (by norm_num) c))
  refine le_trans (totalDegree_add _ _) (max_le ?_ (hm 0 0 (by norm_num) 1))
  exact le_trans (totalDegree_add _ _) (max_le (hm 4 2 (by norm_num) 1) (hm 2 4 (by norm_num) 1))

/-- Generalised degree bound: if `∑ qᵢ² = p` with `totalDegree p ≤ 6`, then every
    `qᵢ` has total degree `≤ 3`.  (The parent's `degree_bound` is the `p = motzkin`
    specialisation; the argument only needs the degree cap, so it transfers.) -/
theorem degree_bound_gen {m : ℕ} (p : MvPolynomial (Fin 2) ℝ) (hp : p.totalDegree ≤ 6)
    (q : Fin m → MvPolynomial (Fin 2) ℝ) (h : ∑ i, (q i) ^ 2 = p) (j : Fin m) :
    (q j).totalDegree ≤ 3 := by
  by_contra hcon
  push_neg at hcon
  set D := Finset.univ.sup (fun i => (q i).totalDegree) with hDdef
  have hjD : (q j).totalDegree ≤ D :=
    Finset.le_sup (f := fun i => (q i).totalDegree) (Finset.mem_univ j)
  have hD1 : 1 ≤ D := by omega
  have hzero : homogeneousComponent (2 * D) p = 0 := by
    apply homogeneousComponent_eq_zero
    exact lt_of_le_of_lt hp (by omega)
  rw [← h, map_sum] at hzero
  have hterm : ∀ i, homogeneousComponent (2 * D) ((q i) ^ 2) = (homogeneousComponent D (q i)) ^ 2 :=
    fun i => topsq (q i) D hD1 (Finset.le_sup (f := fun i => (q i).totalDegree) (Finset.mem_univ i))
  rw [Finset.sum_congr rfl (fun i _ => hterm i)] at hzero
  have htop0 := sum_sq_eq_zero (fun i => homogeneousComponent D (q i)) hzero
  obtain ⟨i₀, _, hi₀⟩ :=
    Finset.exists_mem_eq_sup (Finset.univ) ⟨j, Finset.mem_univ j⟩ (fun i => (q i).totalDegree)
  have hi₀deg : (q i₀).totalDegree = D := by rw [hDdef, ← hi₀]
  have hqi0 : q i₀ ≠ 0 := by intro h0; rw [h0] at hi₀deg; simp at hi₀deg; omega
  have hne0 : homogeneousComponent D (q i₀) ≠ 0 := by
    rw [← hi₀deg]; exact topForm_ne_zero _ hqi0
  exact hne0 (htop0 i₀)

/-- **The whole Motzkin family is not SOS for `c > 0`.**  For every real `c > 0`,
    `motzkinPoly c = X₀⁴X₁² + X₀²X₁⁴ + 1 − c·X₀²X₁²` is not a sum of squares of
    polynomials.  (Taking `c = 3` recovers the parent entry's `motzkin_not_sos`.) -/
theorem motzkinPoly_not_sos {c : ℝ} (hc : 0 < c) :
    ¬ Hilbert17MotzkinNotSOS.IsSOS (motzkinPoly c) := by
  rintro ⟨m, q, hq⟩
  have hsum : ∑ i, (q i) ^ 2 = motzkinPoly c := hq.symm
  have htd : (motzkinPoly c).totalDegree ≤ 6 := totalDegree_motzkinPoly c
  -- Degree bound in coefficient form.
  have hdeg : ∀ j, ∀ μ : Fin 2 →₀ ℕ, 4 ≤ (μ 0 + μ 1) → coeff μ (q j) = 0 := by
    intro j μ hμ
    apply coeff_eq_zero_of_totalDegree_lt
    have hs : ∑ i ∈ μ.support, μ i = μ 0 + μ 1 := by
      rw [← Finsupp.degree_apply]; exact deg_eq μ
    rw [hs]; exact lt_of_le_of_lt (degree_bound_gen _ htd q hsum j) (by omega)
  -- Pure-`x`-axis vanishing (identical to the `c = 3` case, `c`-independent).
  have hpx : ∀ j, ∀ k, 1 ≤ k → coeff (mon k 0) (q j) = 0 := by
    intro j
    have e60 : ∑ i, (coeff (mon 3 0) (q i)) ^ 2 = 0 := by
      have : (∑ i, coeff (mon 6 0) (q i ^ 2)) = coeff (mon 6 0) (motzkinPoly c) := by
        rw [← coeff_sum, hsum]
      rw [coeff_mP_60] at this
      rw [← this]; apply Finset.sum_congr rfl; intro i _
      rw [pow_two (q i)]
      exact (pureX_extract (q i) (hdeg i) 3 (by intro k hk hk3; exact absurd hk3 (by omega))).symm
    have c30 : ∀ i, coeff (mon 3 0) (q i) = 0 := sum_sq_real_eq_zero _ e60
    have e40 : ∑ i, (coeff (mon 2 0) (q i)) ^ 2 = 0 := by
      have : (∑ i, coeff (mon 4 0) (q i ^ 2)) = coeff (mon 4 0) (motzkinPoly c) := by
        rw [← coeff_sum, hsum]
      rw [coeff_mP_40] at this
      rw [← this]; apply Finset.sum_congr rfl; intro i _
      rw [pow_two (q i)]
      exact (pureX_extract (q i) (hdeg i) 2 (by intro k hk hk3; interval_cases k; exact c30 i)).symm
    have c20 : ∀ i, coeff (mon 2 0) (q i) = 0 := sum_sq_real_eq_zero _ e40
    have e20 : ∑ i, (coeff (mon 1 0) (q i)) ^ 2 = 0 := by
      have : (∑ i, coeff (mon 2 0) (q i ^ 2)) = coeff (mon 2 0) (motzkinPoly c) := by
        rw [← coeff_sum, hsum]
      rw [coeff_mP_20] at this
      rw [← this]; apply Finset.sum_congr rfl; intro i _
      rw [pow_two (q i)]
      exact (pureX_extract (q i) (hdeg i) 1
        (by intro k hk hk3; interval_cases k; exacts [c20 i, c30 i])).symm
    have c10 : ∀ i, coeff (mon 1 0) (q i) = 0 := sum_sq_real_eq_zero _ e20
    intro k hk
    rcases Nat.lt_or_ge k 4 with h4 | h4
    · interval_cases k
      · exact c10 j
      · exact c20 j
      · exact c30 j
    · exact hdeg j _ (by simp; omega)
  -- Pure-`y`-axis vanishing.
  have hpy : ∀ j, ∀ k, 1 ≤ k → coeff (mon 0 k) (q j) = 0 := by
    intro j
    have e06 : ∑ i, (coeff (mon 0 3) (q i)) ^ 2 = 0 := by
      have : (∑ i, coeff (mon 0 6) (q i ^ 2)) = coeff (mon 0 6) (motzkinPoly c) := by
        rw [← coeff_sum, hsum]
      rw [coeff_mP_06] at this
      rw [← this]; apply Finset.sum_congr rfl; intro i _
      rw [pow_two (q i)]
      exact (pureY_extract (q i) (hdeg i) 3 (by intro k hk hk3; exact absurd hk3 (by omega))).symm
    have c03 : ∀ i, coeff (mon 0 3) (q i) = 0 := sum_sq_real_eq_zero _ e06
    have e04 : ∑ i, (coeff (mon 0 2) (q i)) ^ 2 = 0 := by
      have : (∑ i, coeff (mon 0 4) (q i ^ 2)) = coeff (mon 0 4) (motzkinPoly c) := by
        rw [← coeff_sum, hsum]
      rw [coeff_mP_04] at this
      rw [← this]; apply Finset.sum_congr rfl; intro i _
      rw [pow_two (q i)]
      exact (pureY_extract (q i) (hdeg i) 2 (by intro k hk hk3; interval_cases k; exact c03 i)).symm
    have c02 : ∀ i, coeff (mon 0 2) (q i) = 0 := sum_sq_real_eq_zero _ e04
    have e02 : ∑ i, (coeff (mon 0 1) (q i)) ^ 2 = 0 := by
      have : (∑ i, coeff (mon 0 2) (q i ^ 2)) = coeff (mon 0 2) (motzkinPoly c) := by
        rw [← coeff_sum, hsum]
      rw [coeff_mP_02] at this
      rw [← this]; apply Finset.sum_congr rfl; intro i _
      rw [pow_two (q i)]
      exact (pureY_extract (q i) (hdeg i) 1
        (by intro k hk hk3; interval_cases k; exacts [c02 i, c03 i])).symm
    have c01 : ∀ i, coeff (mon 0 1) (q i) = 0 := sum_sq_real_eq_zero _ e02
    intro k hk
    rcases Nat.lt_or_ge k 4 with h4 | h4
    · interval_cases k
      · exact c01 j
      · exact c02 j
      · exact c03 j
    · exact hdeg j _ (by simp; omega)
  -- The `x²y²` coefficient is a sum of real squares, hence `≥ 0`; but it is `-c`.
  have hfinal : coeff (mon 2 2) (motzkinPoly c) = ∑ i, (coeff (mon 1 1) (q i)) ^ 2 := by
    rw [← hsum, coeff_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [pow_two (q i)]
    exact coeff22_sq (q i) (hpx i) (hpy i) (hdeg i)
  rw [coeff_mP_22] at hfinal
  have hnn : (0 : ℝ) ≤ ∑ i, (coeff (mon 1 1) (q i)) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [← hfinal] at hnn
  linarith

/-- **PSD-but-not-SOS across the family.**  For every `0 < c ≤ 3`, `motzkinPoly c`
    is positive-semidefinite yet not a sum of squares of polynomials.  This is a
    genuine one-parameter family of witnesses to the PSD/SOS gap, with the Motzkin
    polynomial (`c = 3`) as the extreme, PSD-boundary member. -/
theorem motzkinPoly_psd_not_sos {c : ℝ} (hc0 : 0 < c) (hc3 : c ≤ 3) :
    IsPSDMv (motzkinPoly c) ∧ ¬ Hilbert17MotzkinNotSOS.IsSOS (motzkinPoly c) :=
  ⟨(motzkinPoly_psd_iff c).2 hc3, motzkinPoly_not_sos hc0⟩

/-- **The classical Motzkin polynomial is PSD but not a sum of squares.**
    `motzkinPoly 3 = X₀⁴X₁² + X₀²X₁⁴ + 1 − 3·X₀²X₁²` is Motzkin's (1967) first *explicit*
    example of a positive-semidefinite polynomial that is not a sum of squares of
    polynomials — the concrete witness that Hilbert's 17th problem genuinely requires
    rational functions (denominators), not just polynomials.  It is the `c = 3`
    PSD-boundary member of the family `motzkinPoly_psd_not_sos`, singled out here as the
    headline instance the whole file is built around. -/
theorem motzkin_classical_psd_not_sos :
    IsPSDMv (motzkinPoly 3) ∧ ¬ Hilbert17MotzkinNotSOS.IsSOS (motzkinPoly 3) :=
  motzkinPoly_psd_not_sos (by norm_num) (by norm_num)

/-- **SOS membership at `c ≤ 0`.** For a nonpositive coefficient the `−c·x²y²` term has a
    nonnegative sign, so `motzkinPoly c` is a genuine sum of four squares,

        Mₐ = (x²y)² + (xy²)² + 1² + (√(-c)·xy)²,

    the last square carrying the coefficient `(√(-c))² = -c ≥ 0`.  This is the exact
    complement of `motzkinPoly_not_sos` (which fails for `c > 0`). -/
theorem motzkinPoly_sos_of_nonpos {c : ℝ} (hc : c ≤ 0) :
    Hilbert17MotzkinNotSOS.IsSOS (motzkinPoly c) := by
  refine ⟨4, ![X 0 ^ 2 * X 1, X 0 * X 1 ^ 2, 1, C (Real.sqrt (-c)) * (X 0 * X 1)], ?_⟩
  have hsq : (C (Real.sqrt (-c)) : MvPolynomial (Fin 2) ℝ) ^ 2 = - C c := by
    rw [← map_pow, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ -c), map_neg]
  rw [motzkinPoly, Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three, mul_pow]
  rw [hsq]
  ring

/-- **Sharp SOS threshold of the Motzkin family: `SOS ⟺ c ≤ 0`.** Combining
    `motzkinPoly_sos_of_nonpos` (`c ≤ 0 ⟹ SOS`) with `motzkinPoly_not_sos`
    (`c > 0 ⟹ not SOS`).  The SOS threshold `c ≤ 0` sits strictly below the PSD
    threshold `c ≤ 3` (`motzkinPoly_psd_iff`): the entire segment `0 < c ≤ 3` is
    PSD-but-not-SOS, a one-parameter family of witnesses to the Hilbert-17 gap with the
    Motzkin polynomial (`c = 3`) at the far PSD-boundary end. -/
theorem motzkinPoly_sos_iff (c : ℝ) :
    Hilbert17MotzkinNotSOS.IsSOS (motzkinPoly c) ↔ c ≤ 0 := by
  constructor
  · intro hsos
    by_contra hc
    push_neg at hc
    exact motzkinPoly_not_sos hc hsos
  · exact motzkinPoly_sos_of_nonpos

/-! ## Structure of the family: the diagonal value, the boundary zero, monotonicity

Three elementary structural facts that expose *why* `c = 3` is the sharp threshold.
The whole threshold argument runs through the single diagonal evaluation
`Mₐ(1,1) = 3 − c`; naming it isolates that mechanism. From it, the boundary member
`c = 3` has an honest real *zero* at `(1,1)` (so it is PSD but not positive
definite — it sits *on* the PSD-cone boundary, not in its interior), while the
family decreases pointwise in `c`, which is exactly what makes the PSD region a
downward-closed half-line `c ≤ 3`. All `0`-axiom. -/

/-- **The diagonal evaluation** driving the threshold: `Mₐ(1,1) = 3 − c`. Every PSD
    obstruction in this family is detected here — the sign of `3 − c` is the whole
    story of `motzkinFun_psd_iff`. -/
theorem motzkinFun_at_one_one (c : ℝ) : motzkinFun c 1 1 = 3 - c := by
  unfold motzkinFun; ring

/-- **The boundary member has a real zero.** At the sharp threshold `c = 3` the
    Motzkin function vanishes at `(1,1)`: `M₃(1,1) = 0`. Combined with
    `motzkin_nonneg` (`M₃ ≥ 0`), this shows the boundary polynomial is PSD but *not*
    positive definite — it touches `0`, sitting exactly on the PSD-cone boundary,
    which is the geometric reason `c = 3` is extremal. -/
theorem motzkinFun_three_zero_at_one_one : motzkinFun 3 1 1 = 0 := by
  rw [motzkinFun_at_one_one]; norm_num

/-- **Strict positivity below the threshold at the critical point.** For `c < 3`
    the diagonal value `Mₐ(1,1) = 3 − c > 0` is strictly positive: the real zero of
    the boundary member `c = 3` appears *exactly* at the threshold and nowhere below
    it (at the critical point `(1,1)`). -/
theorem motzkinFun_pos_at_one_one_of_lt_three {c : ℝ} (hc : c < 3) :
    0 < motzkinFun c 1 1 := by
  rw [motzkinFun_at_one_one]; linarith

/-- **The family is antitone in the coefficient.** Raising `c` can only lower the
    value: `c₁ ≤ c₂ ⟹ Mₐ₂(x,y) ≤ Mₐ₁(x,y)` for all real `x, y`, since only the
    `−c·x²y²` term depends on `c` and `x²y² ≥ 0`. This monotonicity is precisely why
    the PSD region `{c | Mₐ is PSD}` is the downward-closed half-line `c ≤ 3`. -/
theorem motzkinFun_antitone_in_coeff {c₁ c₂ : ℝ} (h : c₁ ≤ c₂) (x y : ℝ) :
    motzkinFun c₂ x y ≤ motzkinFun c₁ x y := by
  unfold motzkinFun
  nlinarith [mul_nonneg (sub_nonneg.mpr h) (mul_nonneg (sq_nonneg x) (sq_nonneg y))]

end Hilbert17OQ03OQ05

-- Axiom audit: should list only propext, Classical.choice, Quot.sound.
#print axioms Hilbert17OQ03OQ05.motzkinPoly_not_sos
