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
axiom qSequence_initial (q : ℝ) (hq : 1 < q) (hq2 : q < 2) :
    qSequence q 1 = 0 ∧ qSequence q 2 = 1 ∧ qSequence q 3 = q

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
  · -- 1.324 < q: show f(1.324) < 0, i.e., 1.324³ - 1.324 - 1 < 0
    by_contra h
    push_neg at h
    -- If q ≤ 1.324 then q³ ≤ 1.324³ < 2.324 = 1.324 + 1 ≤ q + 1
    -- But q³ = q + 1, contradiction
    sorry
  · -- q < 1.325: show f(1.325) > 0
    sorry

/-- The smallest Pisot number satisfies its defining polynomial. -/
theorem smallestPisot_is_pisot : IsPisot smallestPisot := by
  obtain ⟨hgt1, _, hcubic⟩ := smallestPisot_spec
  refine ⟨hgt1, ?_⟩
  -- The polynomial is X³ - X - 1
  use Polynomial.X ^ 3 - Polynomial.X - 1
  refine ⟨?_, ?_, ?_⟩
  · -- Monic: X³ - X - 1 has leading coefficient 1
    sorry
  · -- smallestPisot is a root
    simp only [Polynomial.aeval_sub, Polynomial.aeval_pow, Polynomial.aeval_X,
      Polynomial.aeval_one, map_one]
    linarith [hcubic]
  · -- Other complex roots have |z| < 1
    -- x³ - x - 1 = (x - q₀)(x² + q₀x + q₀² - 1)
    -- Discriminant of x² + q₀x + (q₀²-1) = q₀² - 4(q₀²-1) = 4 - 3q₀²
    -- For q₀ ≈ 1.3247: 4 - 3(1.3247)² ≈ 4 - 5.27 < 0, so complex conjugate roots
    -- |z|² = q₀² - 1 < 1 iff q₀² < 2 iff q₀ < √2 ≈ 1.414 ✓
    sorry

/-- Siegel's theorem: q₀ is the smallest Pisot-Vijayaraghavan number. -/
axiom smallestPisot_minimal :
    ∀ q : ℝ, IsPisot q → q ≥ smallestPisot

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
  · -- Monic
    sorry
  · -- φ is a root: φ² - φ - 1 = 0
    simp only [Polynomial.aeval_sub, Polynomial.aeval_pow, Polynomial.aeval_X,
      Polynomial.aeval_one, map_one]
    unfold goldenRatio
    have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (5:ℝ) ≥ 0)
    nlinarith
  · -- Other roots have |z| < 1
    -- The other root is (1-√5)/2. |(1-√5)/2| = (√5-1)/2 < 1 since √5 < 3.
    sorry

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
axiom ejs_refinement (q : ℝ) (hq1 : 1 < q) (hq2 : q < goldenRatio) :
    IsPisot q ↔ ∃ δ : ℝ, δ > 0 ∧ ∀ᶠ k in Filter.atTop, gapM q 2 k ≥ δ

/- ## Part VII: Density Result
-/

/-- As q → 1⁺, QRepresentable(q) becomes arbitrarily dense in [0, N].
    This explains why the gap property should hold for q close to 1. -/
axiom density_near_one :
    ∀ ε > 0, ∀ N : ℝ, N > 0 →
      ∃ q : ℝ, 1 < q ∧ q < 1 + ε ∧
        ∀ x ∈ Set.Icc 0 N, ∃ y ∈ QRepresentable q, |x - y| < ε

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
