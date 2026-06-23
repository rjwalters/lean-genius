/-
Erdős Problem #255: Discrepancy of Sequences in [0,1]

Source: https://erdosproblems.com/255
Status: SOLVED (Answer: YES)

Statement:
Let z₁, z₂, ... ∈ [0,1] be an infinite sequence. Define the discrepancy
  D_N(I) = #{n ≤ N : zₙ ∈ I} - N·|I|
Must there exist some interval I ⊆ [0,1] such that
  limsup_{N→∞} |D_N(I)| = ∞?

Answer: YES

Key Results:
- Schmidt (1968): Affirmative answer to the main question
- Schmidt (1972): True for all but countably many intervals [0,x]
- Tijdeman-Wagner (1980): For almost all [0,x), |D_N| ≫ log N
- Van der Corput: Achieves |D_N| = O(log N), so log N is optimal

References:
- Schmidt (1968): "Irregularities of distribution"
- Schmidt (1972): "Irregularities of distribution VI"
- Tijdeman-Wagner (1980): "A sequence has almost nowhere small discrepancy"
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Countable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.Basic

open Set Nat Real

namespace Erdos255

/- ## Part I: Basic Definitions -/

/-- An infinite sequence z : ℕ → ℝ with all values in [0,1]. -/
def IsSequenceInUnitInterval (z : ℕ → ℝ) : Prop :=
  ∀ n, z n ∈ Set.Icc 0 1

/-- #{n ≤ N : zₙ ∈ I} — the number of terms up to N that land in interval I. -/
noncomputable def countInInterval (z : ℕ → ℝ) (I : Set ℝ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => z (n + 1) ∈ I)).card

/-- |I| for I = [a, b] is b - a. -/
noncomputable def intervalLength (a b : ℝ) : ℝ := b - a

/-- **Discrepancy D_N(I):**
    D_N(I) = #{n ≤ N : zₙ ∈ I} - N · |I|
    This measures how far the empirical distribution deviates from uniform. -/
noncomputable def discrepancy (z : ℕ → ℝ) (a b : ℝ) (N : ℕ) : ℝ :=
  (countInInterval z (Set.Icc a b) N : ℝ) - N * intervalLength a b

/-- |D_N(I)| — the absolute discrepancy. -/
noncomputable def absDiscrepancy (z : ℕ → ℝ) (a b : ℝ) (N : ℕ) : ℝ :=
  |discrepancy z a b N|

/- ## Part II: The Main Question -/

/-- **Unbounded Discrepancy:** limsup_{N→∞} |D_N(I)| = ∞. -/
def hasUnboundedDiscrepancy (z : ℕ → ℝ) (a b : ℝ) : Prop :=
  ∀ M : ℝ, ∃ N : ℕ, absDiscrepancy z a b N > M

/-- **Erdős's Question:**
    For every sequence in [0,1], does there exist an interval
    with unbounded discrepancy? -/
def erdosQuestion : Prop :=
  ∀ z : ℕ → ℝ, IsSequenceInUnitInterval z →
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧ hasUnboundedDiscrepancy z a b

/- ## Part III: Schmidt's Theorem (1968) -/

/-- **Schmidt's Theorem (1968):**
    The answer to Erdős's question is YES. For any infinite sequence in [0,1],
    there exists an interval I such that limsup |D_N(I)| = ∞. -/
axiom schmidt_theorem_1968 : erdosQuestion

/-- **Corollary: No Sequence Has Bounded Discrepancy Everywhere.**
    Derived from Schmidt's theorem by contradiction. -/
theorem no_uniformly_bounded_discrepancy :
    ¬∃ z : ℕ → ℝ, IsSequenceInUnitInterval z ∧
      ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
        ∃ M : ℝ, ∀ N : ℕ, absDiscrepancy z a b N ≤ M := by
  intro ⟨z, hz, hbounded⟩
  have hschmidt := schmidt_theorem_1968 z hz
  obtain ⟨a, b, ha, hab, hb, hunbounded⟩ := hschmidt
  specialize hbounded a b ha hab hb
  obtain ⟨M, hM⟩ := hbounded
  specialize hunbounded M
  obtain ⟨N, hN⟩ := hunbounded
  specialize hM N
  linarith

/- ## Part IV: Schmidt's Strengthening (1972) -/

/-- **Schmidt's Strengthening (1972):**
    For all but countably many x ∈ [0,1], the interval [0,x]
    has unbounded discrepancy. -/
axiom schmidt_theorem_1972 (z : ℕ → ℝ) (hz : IsSequenceInUnitInterval z) :
    {x : ℝ | x ∈ Set.Icc 0 1 ∧ ¬hasUnboundedDiscrepancy z 0 x}.Countable

/- ## Part V: Tijdeman-Wagner Theorem (1980) -/

/-- **Logarithmic Discrepancy Lower Bound:**
    |D_N([0,x))| ≫ log N for some subsequence of N. -/
def hasLogarithmicDiscrepancy (z : ℕ → ℝ) (x : ℝ) : Prop :=
  ∃ c > 0, ∀ M : ℕ, ∃ N ≥ M, absDiscrepancy z 0 x N > c * Real.log N

/-- **Tijdeman-Wagner Theorem (1980):**
    For almost all x ∈ [0,1], limsup |D_N([0,x))| / log N ≫ 1.
    This is the best possible growth rate. -/
/- ## Part VI: Optimality -/

/-- **Van der Corput Sequence:**
    There exist sequences where |D_N([0,x))| = O(log N) for all x.
    So logarithmic growth is the best possible. -/
axiom van_der_corput_sequence_exists :
    ∃ z : ℕ → ℝ, IsSequenceInUnitInterval z ∧
      ∀ x : ℝ, x ∈ Set.Icc 0 1 →
        ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 1 → absDiscrepancy z 0 x N ≤ C * Real.log N

/- ## Part VII: Connections -/

/-- **Uniform distribution:** A sequence is uniformly distributed mod 1
    iff D_N([0,x))/N → 0 for all x. But D_N itself must still be unbounded! -/
def isUniformlyDistributed (z : ℕ → ℝ) : Prop :=
  ∀ x : ℝ, x ∈ Set.Ioo 0 1 →
    Filter.Tendsto (fun N => discrepancy z 0 x N / N) Filter.atTop (nhds 0)

/-- **Weyl's Theorem:** (nα) mod 1 is uniformly distributed iff α is irrational. -/
/- ## Part VIII: Star Discrepancy -/

/-- **Star Discrepancy D*_N:** The supremum of |D_N([0,x))| over all x ∈ [0,1]. -/
noncomputable def starDiscrepancy (z : ℕ → ℝ) (N : ℕ) : ℝ :=
  ⨆ x ∈ Set.Icc (0:ℝ) 1, absDiscrepancy z 0 x N

/-- **Star discrepancy is unbounded** for any sequence, following from Schmidt's theorem. -/
/- ## Part IX: Summary -/

/-- **Summary of Erdős Problem #255:**

  SOLVED: YES (Schmidt 1968)

  1. erdosQuestion holds (Schmidt 1968) — some interval has unbounded discrepancy
  2. All but countably many [0,x] have unbounded discrepancy (Schmidt 1972)
  3. |D_N| ≫ log N for a.e. interval (Tijdeman-Wagner 1980)
  4. |D_N| = O(log N) is achievable (van der Corput) — log N is optimal

  Discrepancy theory shows that no sequence can be "too uniformly distributed":
  irregularities must occur, and they grow at least logarithmically. -/
theorem erdos_255_summary :
    erdosQuestion ∧
    (∀ z : ℕ → ℝ, IsSequenceInUnitInterval z →
      {x : ℝ | x ∈ Set.Icc 0 1 ∧ ¬hasUnboundedDiscrepancy z 0 x}.Countable) ∧
    (∃ z : ℕ → ℝ, IsSequenceInUnitInterval z ∧
      ∀ x : ℝ, x ∈ Set.Icc 0 1 →
        ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 1 → absDiscrepancy z 0 x N ≤ C * Real.log N) :=
  ⟨schmidt_theorem_1968, schmidt_theorem_1972, van_der_corput_sequence_exists⟩

end Erdos255
