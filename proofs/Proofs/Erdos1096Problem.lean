/-
Erdős Problem #1096: Gap Convergence in q-Expansions

Source: https://erdosproblems.com/1096
Status: OPEN (with significant partial results)

Statement:
Let 1 < q < 1 + ε and consider the set of numbers of the form Σ_{i∈S} q^i
(for all finite S ⊆ ℕ), ordered by size as 0 = x₁ < x₂ < x₃ < ⋯.

Is it true that, provided ε > 0 is sufficiently small, x_{k+1} - x_k → 0?

Conjecture:
Erdős and Joó speculate the threshold is q₀ ≈ 1.3247, the real root of
x³ = x + 1, which is the smallest Pisot-Vijayaraghavan number.

Known Results:
- Pisot-Vijayaraghavan numbers do NOT have this property (EJK 1990)
- For all 1 < q ≤ 2, the gaps satisfy x_{k+1} - x_k ≤ 1 (EJK 1990)
- Characterization of Pisot numbers via gaps in m-digit expansions (Bugeaud 1996)

References:
- Erdős-Joó-Komornik [EJK90]: Bull. Soc. Math. France (1990)
- Bugeaud [Bu96]: Acta Math. Hungar. (1996)
- Erdős-Joó-Schnitzer [EJS96]: refinements for q < φ
-/

import Mathlib

open Set Nat Real

namespace Erdos1096

/- ## Part I: q-Expansions

Numbers that can be written as finite sums of powers of q.
-/

/--
**q-Representable Numbers:**
A number is q-representable if it equals Σ_{i∈S} q^i for some finite S ⊆ ℕ.
-/
def QRepresentable (q : ℝ) : Set ℝ :=
  {x : ℝ | ∃ S : Finset ℕ, x = S.sum (fun i => q ^ i)}

/--
**Examples:**
For any q > 1:
- 0 is q-representable (empty sum)
- 1 is q-representable (S = {0})
- q is q-representable (S = {1})
- 1 + q is q-representable (S = {0, 1})
-/
theorem zero_q_representable (q : ℝ) : (0 : ℝ) ∈ QRepresentable q := by
  use ∅
  simp

theorem one_q_representable (q : ℝ) : (1 : ℝ) ∈ QRepresentable q := by
  use {0}
  simp

theorem q_q_representable (q : ℝ) : q ∈ QRepresentable q := by
  use {1}
  simp

/- ## Part II: The Ordered Sequence

The q-representable numbers form a countable set that can be enumerated
in increasing order: 0 = x₁ < x₂ < x₃ < ⋯
-/

/-- The k-th smallest q-representable number.
    Requires well-ordering of the countable set QRepresentable(q).
    Axiomatized because the ordering infrastructure is not straightforward in Lean. -/
axiom qSequence (q : ℝ) (k : ℕ) : ℝ

/-- For 1 < q < 2, the sequence begins 0, 1, q, ... -/
/-- The gap between consecutive terms: x_{k+1} - x_k -/
noncomputable def gap (q : ℝ) (k : ℕ) : ℝ := qSequence q (k + 1) - qSequence q k

/- ## Part III: Pisot-Vijayaraghavan Numbers

Special algebraic integers with important properties.
An algebraic integer θ > 1 is a Pisot number if all its Galois conjugates
have absolute value < 1.
-/

/-- Pisot-Vijayaraghavan number predicate.
    A real algebraic integer θ > 1 is a Pisot number if it is a root of
    a monic integer polynomial whose other complex roots all have absolute
    value strictly less than 1.

    Previously axiomatized; now defined concretely using polynomial roots. -/
def IsPisot (q : ℝ) : Prop :=
  1 < q ∧ ∃ p : Polynomial ℤ, p.Monic ∧
    (Polynomial.aeval q p = 0) ∧
    (∀ z : ℂ, (p.map (algebraMap ℤ ℂ)).IsRoot z →
      z ≠ (algebraMap ℝ ℂ q) → Complex.abs z < 1)

/-- The smallest Pisot-Vijayaraghavan number q₀ ≈ 1.3247,
    the unique real root > 1 of x³ - x - 1 = 0.
    Existence: f(1) = -1 < 0, f(2) = 5 > 0, so by IVT there is a root in (1,2).
    Uniqueness: f is strictly increasing on (1,∞) since f'(x) = 3x² - 1 > 2 > 0. -/
noncomputable def smallestPisot : ℝ :=
  Classical.choose (show ∃ q : ℝ, 1 < q ∧ q < 2 ∧ q ^ 3 = q + 1 by
    -- By IVT: f(x) = x³ - x - 1 satisfies f(1) = -1 < 0 and f(2) = 5 > 0
    have h_cont : Continuous (fun x : ℝ => x ^ 3 - x - 1) := by fun_prop
    have h_f1 : (1 : ℝ) ^ 3 - 1 - 1 = -1 := by norm_num
    have h_f2 : (2 : ℝ) ^ 3 - 2 - 1 = 5 := by norm_num
    obtain ⟨c, hc_mem, hc_eq⟩ := intermediate_value_zero_of_neg_of_pos
      (show (1 : ℝ) ≤ 2 from by norm_num)
      (h_cont.continuousOn)
      (by linarith) (by linarith)
    exact ⟨c, by linarith [hc_mem.1], by linarith [hc_mem.2],
      by linarith [hc_eq]⟩)

private lemma smallestPisot_spec :
    1 < smallestPisot ∧ smallestPisot < 2 ∧ smallestPisot ^ 3 = smallestPisot + 1 :=
  Classical.choose_spec _

/-- The smallest Pisot number lies in (1.324, 1.325). -/
theorem smallestPisot_value : 1.324 < smallestPisot ∧ smallestPisot < 1.325 := by
  -- From smallestPisot_spec we know q³ = q + 1 and 1 < q < 2.
  -- Evaluate: 1.324³ = 2.321... < 1.324 + 1 = 2.324 ✓
  --           1.325³ = 2.327... > 1.325 + 1 = 2.325 ✓
  -- So the root lies in (1.324, 1.325).
  obtain ⟨hgt1, hlt2, hcubic⟩ := smallestPisot_spec
  constructor
  · -- 1.324 < q: f(x) = x³ - x is strictly increasing for x ≥ 1
    -- f(q) = 1 (from q³ = q + 1), but f(1.324) < 1, so q > 1.324
    by_contra h
    push_neg at h
    -- Monotonicity: (1.324 - q)(1.324² + 1.324·q + q² - 1) ≥ 0
    -- This expands to 1.324³ - 1.324 - q³ + q ≥ 0
    -- With q³ = q + 1: 1.324³ - 1.324 - 1 ≥ 0, but 1.324³ < 2.324
    have hmono : 0 ≤ (1.324 - smallestPisot) *
        (1.324 ^ 2 + 1.324 * smallestPisot + smallestPisot ^ 2 - 1) :=
      mul_nonneg (by linarith) (by nlinarith [sq_nonneg smallestPisot,
        sq_nonneg (smallestPisot - 1)])
    nlinarith [hcubic]
  · -- q < 1.325: same argument, f(1.325) > 1 but f(q) = 1
    by_contra h
    push_neg at h
    have hmono : 0 ≤ (smallestPisot - 1.325) *
        (smallestPisot ^ 2 + 1.325 * smallestPisot + 1.325 ^ 2 - 1) :=
      mul_nonneg (by linarith) (by nlinarith [sq_nonneg smallestPisot,
        sq_nonneg (smallestPisot - 1)])
    nlinarith [hcubic]

/-- The smallest Pisot number satisfies its defining polynomial. -/
theorem smallestPisot_is_pisot : IsPisot smallestPisot := by
  obtain ⟨hgt1, _, hcubic⟩ := smallestPisot_spec
  refine ⟨hgt1, ?_⟩
  -- The polynomial is X³ - X - 1
  use Polynomial.X ^ 3 - Polynomial.X - 1
  refine ⟨?_, ?_, ?_⟩
  · -- Monic: X³ - X - 1 has leading coefficient 1
    have h_eq : (Polynomial.X ^ 3 - Polynomial.X - 1 : Polynomial ℤ) =
                Polynomial.X ^ 3 - (Polynomial.X + 1) := by ring
    rw [h_eq]
    apply Polynomial.Monic.sub_of_left (Polynomial.monic_X_pow 3)
    apply lt_of_le_of_lt (Polynomial.degree_add_le _ _)
    apply max_lt <;> simp [Polynomial.degree_X_pow, Polynomial.degree_X, Polynomial.degree_one]
  · -- smallestPisot is a root
    simp only [Polynomial.aeval_sub, Polynomial.aeval_pow, Polynomial.aeval_X,
      Polynomial.aeval_one, map_one]
    linarith [hcubic]
  · -- Other complex roots have |z| < 1
    -- x³ - x - 1 = (x - q₀)(x² + q₀x + q₀² - 1)
    -- The conjugate roots of the quadratic have |z|² = q₀² - 1 < 1
    intro z hz hne
    set q := algebraMap ℝ ℂ smallestPisot with hq_def
    -- z is a root of X³ - X - 1 over ℂ
    have hzroot : z ^ 3 - z - 1 = 0 := by
      have h := hz
      simp only [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_sub,
                  Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_one,
                  Polynomial.eval₂_C, map_one] at h
      linear_combination h
    -- q₀ satisfies q³ - q - 1 = 0 in ℂ
    have hqroot : q ^ 3 - q - 1 = 0 := by
      have h := congr_arg (algebraMap ℝ ℂ) (show smallestPisot ^ 3 - smallestPisot - 1 = 0
        from by linarith [hcubic])
      simp only [map_sub, map_pow, map_one, map_zero] at h
      exact h
    -- Factor: (z - q)(z² + qz + (q² - 1)) = z³ - z - 1 = 0
    have hfactor : (z - q) * (z ^ 2 + q * z + (q ^ 2 - 1)) = 0 := by
      linear_combination hzroot - hqroot
    -- Since z ≠ q: z² + qz + (q² - 1) = 0
    have hquad : z ^ 2 + q * z + (q ^ 2 - 1) = 0 := by
      rcases mul_eq_zero.mp hfactor with h | h
      · exact absurd (sub_eq_zero.mp h) hne
      · exact h
    -- Conjugate also satisfies: conj(z)² + q·conj(z) + (q² - 1) = 0
    -- (since q is real, starRingEnd ℂ q = q)
    have hq_conj : starRingEnd ℂ q = q := by
      simp [hq_def, Complex.conj_ofReal]
    have hquad_conj : (starRingEnd ℂ z) ^ 2 + q * (starRingEnd ℂ z) + (q ^ 2 - 1) = 0 := by
      have := congr_arg (starRingEnd ℂ) hquad
      simp only [map_add, map_mul, map_pow, map_sub, map_one, map_zero, hq_conj] at this
      exact this
    -- Key: (z - conj z)(z·conj z - (q² - 1)) = 0
    have hkey : (z - starRingEnd ℂ z) * (z * starRingEnd ℂ z - (q ^ 2 - 1)) = 0 := by
      linear_combination (starRingEnd ℂ z) * hquad - z * hquad_conj
    -- z is not real (discriminant 4 - 3q₀² < 0)
    have hz_ne_conj : z ≠ starRingEnd ℂ z := by
      intro heq
      -- If z = conj(z), z is real. Then z² + q₀z + (q₀² - 1) = 0 has a real root.
      -- But discriminant = q₀² - 4(q₀² - 1) = 4 - 3q₀² < 0 (for q₀ > 1.324)
      have hz_real : z = algebraMap ℝ ℂ z.re := by
        ext
        · simp
        · have : z.im = 0 := by
            have := Complex.conj_eq_iff_im.mp heq
            exact this
          simp [this]
      -- z.re satisfies z² + q₀·z + q₀² - 1 = 0
      rw [hz_real, hq_def] at hquad
      simp only [← map_pow, ← map_mul, ← map_add, ← map_sub, ← map_one] at hquad
      have hquad_real : z.re ^ 2 + smallestPisot * z.re + (smallestPisot ^ 2 - 1) = 0 := by
        exact_mod_cast congr_arg Complex.re hquad
      -- Discriminant: Δ = q₀² - 4(q₀² - 1) = 4 - 3q₀² < 0
      have hdisc : smallestPisot ^ 2 - 4 * (smallestPisot ^ 2 - 1) < 0 := by
        nlinarith [hgt1]
      -- But for the equation to have a real root: Δ ≥ 0
      have : 0 ≤ smallestPisot ^ 2 - 4 * (smallestPisot ^ 2 - 1) := by
        nlinarith [sq_nonneg (z.re + smallestPisot / 2), hquad_real]
      linarith
    -- So z·conj(z) = q² - 1
    have hprod : z * starRingEnd ℂ z = q ^ 2 - 1 := by
      rcases mul_eq_zero.mp hkey with h | h
      · exact absurd (sub_eq_zero.mp h).symm hz_ne_conj
      · linear_combination -h
    -- normSq z = q₀² - 1
    have hnorm : Complex.normSq z = smallestPisot ^ 2 - 1 := by
      have h : (Complex.normSq z : ℂ) = q ^ 2 - 1 := by
        rw [← Complex.mul_conj z]
        exact hprod
      rw [hq_def] at h
      simp only [← map_pow, ← map_one (algebraMap ℝ ℂ), ← map_sub] at h
      exact_mod_cast h
    -- Complex.abs z < 1
    rw [Complex.abs_apply, hnorm]
    have hpos : 0 ≤ smallestPisot ^ 2 - 1 := by nlinarith [hgt1]
    have hlt : smallestPisot ^ 2 - 1 < 1 := by nlinarith [hcubic, hgt1]
    calc Real.sqrt (smallestPisot ^ 2 - 1)
        < Real.sqrt 1 := Real.sqrt_lt_sqrt hpos hlt
      _ = 1 := Real.sqrt_one

/-- Siegel's theorem: q₀ is the smallest Pisot-Vijayaraghavan number. -/
/-- The golden ratio φ = (1 + √5)/2 ≈ 1.618 is also a Pisot number. -/
noncomputable def goldenRatio : ℝ := (1 + Real.sqrt 5) / 2

/-- The golden ratio satisfies φ > 1. -/
theorem goldenRatio_gt_one : 1 < goldenRatio := by
  unfold goldenRatio
  have h : (1 : ℝ) < Real.sqrt 5 := by
    rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

/-- The golden ratio satisfies φ < 2. -/
theorem goldenRatio_lt_two : goldenRatio < 2 := by
  unfold goldenRatio
  have h : Real.sqrt 5 < 3 := by
    have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    nlinarith [sq_nonneg (Real.sqrt 5 - 3)]
  linarith

/-- The golden ratio is a Pisot number.
    Proof: X² - X - 1 is the minimal polynomial of φ.
    Its other root is (1-√5)/2, with absolute value (√5-1)/2 < 1. -/
theorem goldenRatio_is_pisot : IsPisot goldenRatio := by
  refine ⟨goldenRatio_gt_one, ?_⟩
  -- Polynomial X² - X - 1
  use Polynomial.X ^ 2 - Polynomial.X - 1
  refine ⟨?_, ?_, ?_⟩
  · -- Monic: X² - X - 1 has leading coefficient 1
    have h_eq : (Polynomial.X ^ 2 - Polynomial.X - 1 : Polynomial ℤ) =
                Polynomial.X ^ 2 - (Polynomial.X + 1) := by ring
    rw [h_eq]
    apply Polynomial.Monic.sub_of_left (Polynomial.monic_X_pow 2)
    apply lt_of_le_of_lt (Polynomial.degree_add_le _ _)
    apply max_lt <;> simp [Polynomial.degree_X_pow, Polynomial.degree_X, Polynomial.degree_one]
  · -- φ is a root: φ² - φ - 1 = 0
    simp only [Polynomial.aeval_sub, Polynomial.aeval_pow, Polynomial.aeval_X,
      Polynomial.aeval_one, map_one]
    unfold goldenRatio
    have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (5:ℝ) ≥ 0)
    nlinarith
  · -- Other roots have |z| < 1
    -- Strategy: z² - z - 1 = 0 and φ² - φ - 1 = 0
    -- Factor: (z - φ)(z + φ - 1) = 0. Since z ≠ φ, z = 1 - φ.
    -- |1 - φ| = φ - 1 < 1 since φ < 2.
    intro z hz hne
    set φ := algebraMap ℝ ℂ goldenRatio with hφ_def
    -- z is a root of X² - X - 1 over ℂ
    have hzroot : z ^ 2 - z - 1 = 0 := by
      have := hz
      simp only [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_sub,
                  Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_one,
                  Polynomial.eval₂_C, map_one] at this
      linear_combination this
    -- φ satisfies φ² - φ - 1 = 0 (embed from ℝ to ℂ)
    have hφroot : φ ^ 2 - φ - 1 = 0 := by
      have hreal : goldenRatio ^ 2 - goldenRatio - 1 = 0 := by
        unfold goldenRatio
        have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (5 : ℝ) ≥ 0)
        nlinarith
      have h := congr_arg (algebraMap ℝ ℂ) hreal
      simp only [map_sub, map_pow, map_one, map_zero] at h
      exact h
    -- (z - φ)(z + φ - 1) = z² - z - (φ² - φ) = 0
    have hfactor : (z - φ) * (z + φ - 1) = 0 := by linear_combination hzroot - hφroot
    -- Since z ≠ φ, we get z = 1 - φ
    have hz_val : z = 1 - φ := by
      rcases mul_eq_zero.mp hfactor with h | h
      · exact absurd (sub_eq_zero.mp h) hne
      · linear_combination -h
    -- |z| = |1 - φ| = φ - 1 < 1
    rw [hz_val, hφ_def]
    rw [show (1 : ℂ) - algebraMap ℝ ℂ goldenRatio =
        algebraMap ℝ ℂ (1 - goldenRatio) from by push_cast; ring]
    -- Complex.abs of a real number = |·|
    rw [Complex.abs_apply]
    rw [show Complex.normSq (algebraMap ℝ ℂ (1 - goldenRatio)) =
        (1 - goldenRatio) ^ 2 from by
      simp [Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im]]
    rw [Real.sqrt_sq_eq_abs, abs_of_neg (by linarith [goldenRatio_gt_one])]
    linarith [goldenRatio_lt_two]

/- ## Part IV: The Erdős-Joó-Komornik Results (1990)
-/

/-- A value q has the gap property if x_{k+1} - x_k → 0 as k → ∞. -/
def HasGapProperty (q : ℝ) : Prop :=
  Filter.Tendsto (gap q) Filter.atTop (nhds 0)

/-- Pisot-Vijayaraghavan numbers do NOT have the gap property.
    Pisot numbers create 'holes' in their q-expansions that persist at all scales. -/
axiom pisot_no_gap_property (q : ℝ) (hPisot : IsPisot q) :
    ¬HasGapProperty q

/-- For all 1 < q ≤ 2, the gaps are bounded by 1. -/
axiom gap_universal_bound (q : ℝ) (hq1 : 1 < q) (hq2 : q ≤ 2) :
    ∀ k : ℕ, gap q k ≤ 1

/- ## Part V: The Main Conjecture
-/

/-- Erdős-Joó Conjecture: the threshold for the gap property
    is the smallest Pisot number q₀ ≈ 1.3247.
    Part 1 (open): all 1 < q < q₀ have the gap property.
    Part 2 (known): q₀ does not have the gap property. -/
def ErdosJooConjecture : Prop :=
  (∀ q : ℝ, 1 < q → q < smallestPisot → HasGapProperty q) ∧
  (¬HasGapProperty smallestPisot)

/-- The second part of the conjecture is known:
    q₀ is Pisot, so it doesn't have the gap property. -/
theorem conjecture_second_part : ¬HasGapProperty smallestPisot :=
  pisot_no_gap_property smallestPisot smallestPisot_is_pisot

/- ## Part VI: Characterization via m-Digit Expansions

Bugeaud and others characterized Pisot numbers using generalized expansions.
-/

/-- m-digit q-representable numbers: using digits 0, 1, ..., m instead of just 0, 1. -/
def QRepresentableM (q : ℝ) (m : ℕ) : Set ℝ :=
  {x : ℝ | ∃ (S : Finset ℕ) (c : ℕ → ℕ),
    (∀ i ∈ S, c i ≤ m) ∧ x = S.sum (fun i => (c i : ℝ) * q ^ i)}

/-- The k-th element of the m-digit ordered sequence. -/
axiom qSequenceM (q : ℝ) (m : ℕ) (k : ℕ) : ℝ

noncomputable def gapM (q : ℝ) (m : ℕ) (k : ℕ) : ℝ :=
  qSequenceM q m (k + 1) - qSequenceM q m k

/-- Bugeaud's Characterization (1996):
    For 1 < q ≤ 2, q is Pisot iff liminf of m-digit gaps > 0 for all m ≥ 1. -/
axiom bugeaud_characterization (q : ℝ) (hq1 : 1 < q) (hq2 : q ≤ 2) :
    IsPisot q ↔ ∀ m : ℕ, m ≥ 1 →
      ∃ δ : ℝ, δ > 0 ∧ ∀ᶠ k in Filter.atTop, gapM q m k ≥ δ

/-- Erdős-Joó-Schnitzer Refinement (1996):
    For 1 < q < φ, only need to check m = 2. -/
/- ## Part VII: Density Result
-/

/-- As q → 1⁺, QRepresentable(q) becomes arbitrarily dense in [0, N].
    This explains why the gap property should hold for q close to 1. -/
/- ## Part VIII: Summary
-/

/-- Main summary combining the known results about gaps and Pisot numbers. -/
theorem erdos_1096_summary :
    -- Pisot numbers don't have the property
    (∀ q : ℝ, IsPisot q → ¬HasGapProperty q) ∧
    -- Gaps bounded by 1 for q ≤ 2
    (∀ q : ℝ, 1 < q → q ≤ 2 → ∀ k : ℕ, gap q k ≤ 1) ∧
    -- The smallest Pisot doesn't have the property
    (¬HasGapProperty smallestPisot) := by
  exact ⟨pisot_no_gap_property, gap_universal_bound, conjecture_second_part⟩

/- ## Part IX: Consequences for the Golden Ratio -/

/-- The golden ratio does not have the gap property
    (it is a Pisot number, so gaps persist at all scales). -/
theorem goldenRatio_no_gap_property : ¬HasGapProperty goldenRatio :=
  pisot_no_gap_property goldenRatio goldenRatio_is_pisot

/-- Gaps in the golden ratio q-expansion are bounded by 1. -/
theorem goldenRatio_gap_bound (k : ℕ) : gap goldenRatio k ≤ 1 :=
  gap_universal_bound goldenRatio goldenRatio_gt_one (le_of_lt goldenRatio_lt_two) k

/-- Bugeaud characterization applied to the golden ratio:
    since φ is Pisot, for every m ≥ 1, the m-digit gaps have positive liminf. -/
theorem goldenRatio_persistent_gaps :
    ∀ m : ℕ, m ≥ 1 → ∃ δ : ℝ, δ > 0 ∧ ∀ᶠ k in Filter.atTop, gapM goldenRatio m k ≥ δ :=
  (bugeaud_characterization goldenRatio goldenRatio_gt_one (le_of_lt goldenRatio_lt_two)).mp
    goldenRatio_is_pisot

end Erdos1096
