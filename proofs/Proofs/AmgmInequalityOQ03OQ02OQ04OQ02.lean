/-
  AM-GM OQ-03-OQ-02-OQ-04-OQ-02: The HM ≤ GM ≤ AM chain as power means

  The power mean of a positive family x : ι → ℝ at exponent r is
    M_r(x) = (Σ xᵢ^r / n)^{1/r}    (r ≠ 0),     M_0(x) = (Π xᵢ)^{1/n}.
  Three classical means are the values at r = -1, 0, 1:
    M_{-1}(x) = n / (Σ xᵢ⁻¹)   = harmonic mean   (HM)
    M_0(x)    = (Π xᵢ)^{1/n}   = geometric mean  (GM)
    M_1(x)    = (Σ xᵢ) / n     = arithmetic mean (AM)

  We prove the two adjacent links of the power-mean monotonicity chain at these
  exponents, i.e. the full HM ≤ GM ≤ AM inequality:
    M_{-1}(x) ≤ M_0(x) ≤ M_1(x).

  The two inequalities are obtained from Mathlib's weighted mean inequalities
  (`Real.harm_mean_le_geom_mean_weighted`, `Real.geom_mean_le_arith_mean_weighted`)
  specialised to the uniform weights wᵢ = 1/n; the new content here is the
  identification of HM/GM/AM with the unified power-mean object M_r at the three
  exponents, packaging the classical chain inside the power-mean framework that
  the parent (amgm-inequality-oq-03-oq-02-oq-04) uses to study the r → ±∞ limits.

  Parent: amgm-inequality-oq-03-oq-02-oq-04 (extreme power-mean limits)
-/
import Mathlib

namespace AmgmOQ03OQ02OQ04OQ02

open Real Finset

variable {ι : Type*} [Fintype ι] [Nonempty ι]

-- ═══════════════════════════════════════════════════════════════
-- PART I: DEFINITIONS
-- ═══════════════════════════════════════════════════════════════

/-- Unweighted power mean at exponent `r` (matches the parent's definition). -/
noncomputable def powerMean (x : ι → ℝ) (r : ℝ) : ℝ :=
  if r = 0 then (∏ i : ι, x i) ^ ((Fintype.card ι : ℝ)⁻¹)
  else ((∑ i : ι, (x i) ^ r) / Fintype.card ι) ^ (1 / r)

/-- Arithmetic mean `(Σ xᵢ)/n`. -/
noncomputable def arithMean (x : ι → ℝ) : ℝ := (∑ i : ι, x i) / Fintype.card ι

/-- Geometric mean `(Π xᵢ)^{1/n}`. -/
noncomputable def geomMean (x : ι → ℝ) : ℝ := (∏ i : ι, x i) ^ ((Fintype.card ι : ℝ)⁻¹)

/-- Harmonic mean `n / (Σ xᵢ⁻¹)`. -/
noncomputable def harmMean (x : ι → ℝ) : ℝ := (Fintype.card ι : ℝ) / (∑ i : ι, (x i)⁻¹)

private lemma card_ne_zero : (Fintype.card ι : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr Fintype.card_pos.ne'

-- ═══════════════════════════════════════════════════════════════
-- PART II: THE THREE CLASSICAL MEANS AS POWER MEANS
-- ═══════════════════════════════════════════════════════════════

omit [Nonempty ι] in
/-- The power mean at exponent `1` is the arithmetic mean. -/
lemma powerMean_one (x : ι → ℝ) : powerMean x 1 = arithMean x := by
  rw [powerMean, if_neg one_ne_zero, arithMean]
  simp only [Real.rpow_one, div_one]

omit [Nonempty ι] in
/-- The power mean at exponent `0` is the geometric mean (by definition). -/
lemma powerMean_zero (x : ι → ℝ) : powerMean x 0 = geomMean x := by
  rw [powerMean, if_pos rfl]; rfl

omit [Nonempty ι] in
/-- The power mean at exponent `-1` is the harmonic mean. -/
lemma powerMean_neg_one (x : ι → ℝ) (hx : ∀ i, 0 < x i) :
    powerMean x (-1) = harmMean x := by
  have hne : (-1 : ℝ) ≠ 0 := by norm_num
  have hsum : ∑ i : ι, (x i) ^ (-1 : ℝ) = ∑ i : ι, (x i)⁻¹ := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.rpow_neg_one]
  have hbase : 0 ≤ (∑ i : ι, (x i)⁻¹) / (Fintype.card ι : ℝ) :=
    div_nonneg (Finset.sum_nonneg fun i _ => (inv_pos.2 (hx i)).le) (Nat.cast_nonneg _)
  rw [powerMean, if_neg hne, harmMean, hsum,
      show (1 : ℝ) / (-1) = -(1 : ℝ) by norm_num,
      Real.rpow_neg hbase, Real.rpow_one, inv_div]

-- ═══════════════════════════════════════════════════════════════
-- PART III: THE TWO LINKS OF THE CHAIN
-- ═══════════════════════════════════════════════════════════════

/-- **GM ≤ AM** (the link `M₀ ≤ M₁`): the geometric mean is at most the
    arithmetic mean. Specialises Mathlib's weighted AM-GM to uniform weights. -/
theorem geomMean_le_arithMean (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) :
    geomMean x ≤ arithMean x := by
  have hn' : (Fintype.card ι : ℝ) ≠ 0 := card_ne_zero
  have hw : ∀ i ∈ (univ : Finset ι), (0 : ℝ) ≤ (Fintype.card ι : ℝ)⁻¹ :=
    fun _ _ => by positivity
  have hw' : ∑ _i ∈ (univ : Finset ι), (Fintype.card ι : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ hn'
  have key := Real.geom_mean_le_arith_mean_weighted (univ : Finset ι)
    (fun _ => (Fintype.card ι : ℝ)⁻¹) x hw hw' (fun i _ => hx i)
  rw [geomMean, arithMean]
  calc (∏ i : ι, x i) ^ ((Fintype.card ι : ℝ)⁻¹)
      = ∏ i : ι, (x i) ^ ((Fintype.card ι : ℝ)⁻¹) :=
        (Real.finset_prod_rpow univ x (fun i _ => hx i) _).symm
    _ ≤ ∑ i : ι, (Fintype.card ι : ℝ)⁻¹ * x i := key
    _ = (∑ i : ι, x i) / Fintype.card ι := by
        rw [← Finset.mul_sum, div_eq_mul_inv, mul_comm]

/-- **HM ≤ GM** (the link `M₋₁ ≤ M₀`): the harmonic mean is at most the
    geometric mean. Specialises Mathlib's weighted HM-GM to uniform weights. -/
theorem harmMean_le_geomMean (x : ι → ℝ) (hx : ∀ i, 0 < x i) :
    harmMean x ≤ geomMean x := by
  have hn' : (Fintype.card ι : ℝ) ≠ 0 := card_ne_zero
  have hw : ∀ i ∈ (univ : Finset ι), (0 : ℝ) < (Fintype.card ι : ℝ)⁻¹ :=
    fun _ _ => by positivity
  have hw' : ∑ _i ∈ (univ : Finset ι), (Fintype.card ι : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ hn'
  have key := Real.harm_mean_le_geom_mean_weighted (univ : Finset ι)
    (fun _ => (Fintype.card ι : ℝ)⁻¹) x univ_nonempty hw hw' (fun i _ => hx i)
  rw [harmMean, geomMean]
  calc (Fintype.card ι : ℝ) / (∑ i : ι, (x i)⁻¹)
      = (∑ i : ι, (Fintype.card ι : ℝ)⁻¹ / x i)⁻¹ := by
        have hsum : ∑ i : ι, (Fintype.card ι : ℝ)⁻¹ / x i
            = (Fintype.card ι : ℝ)⁻¹ * ∑ i : ι, (x i)⁻¹ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => div_eq_mul_inv _ _)
        rw [hsum, mul_inv, inv_inv, div_eq_mul_inv]
    _ ≤ ∏ i : ι, (x i) ^ ((Fintype.card ι : ℝ)⁻¹) := key
    _ = (∏ i : ι, x i) ^ ((Fintype.card ι : ℝ)⁻¹) :=
        Real.finset_prod_rpow univ x (fun i _ => (hx i).le) _

-- ═══════════════════════════════════════════════════════════════
-- PART IV: THE FULL CHAIN
-- ═══════════════════════════════════════════════════════════════

/-- **HM ≤ GM ≤ AM** stated for the classical means. -/
theorem harm_le_geom_le_arith (x : ι → ℝ) (hx : ∀ i, 0 < x i) :
    harmMean x ≤ geomMean x ∧ geomMean x ≤ arithMean x :=
  ⟨harmMean_le_geomMean x hx, geomMean_le_arithMean x (fun i => (hx i).le)⟩

/-- **The power-mean chain `M₋₁ ≤ M₀ ≤ M₁`** stated for `powerMean`. -/
theorem powerMean_chain (x : ι → ℝ) (hx : ∀ i, 0 < x i) :
    powerMean x (-1) ≤ powerMean x 0 ∧ powerMean x 0 ≤ powerMean x 1 := by
  rw [powerMean_neg_one x hx, powerMean_zero, powerMean_one]
  exact harm_le_geom_le_arith x hx

end AmgmOQ03OQ02OQ04OQ02
