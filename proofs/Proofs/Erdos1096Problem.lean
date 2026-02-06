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

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Topology.MetricSpace.Basic

open Set Nat Real

namespace Erdos1096

/-
## Part I: q-Expansions

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

/-
## Part II: The Ordered Sequence

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
def gap (q : ℝ) (k : ℕ) : ℝ := qSequence q (k + 1) - qSequence q k

/-
## Part III: Pisot-Vijayaraghavan Numbers

Special algebraic integers with important properties.
An algebraic integer θ > 1 is a Pisot number if all its Galois conjugates
have absolute value < 1.
-/

/-- Pisot-Vijayaraghavan number predicate.
    Axiomatized because the full definition requires algebraic number theory. -/
axiom IsPisot (q : ℝ) : Prop

/-- The smallest Pisot-Vijayaraghavan number q₀ ≈ 1.3247,
    the real root of x³ - x - 1 = 0. -/
axiom smallestPisot : ℝ

axiom smallestPisot_value : 1.324 < smallestPisot ∧ smallestPisot < 1.325

axiom smallestPisot_is_pisot : IsPisot smallestPisot

axiom smallestPisot_minimal :
    ∀ q : ℝ, IsPisot q → q ≥ smallestPisot

/-- The golden ratio φ = (1 + √5)/2 ≈ 1.618 is also a Pisot number. -/
noncomputable def goldenRatio : ℝ := (1 + Real.sqrt 5) / 2

axiom goldenRatio_is_pisot : IsPisot goldenRatio

/-
## Part IV: The Erdős-Joó-Komornik Results (1990)
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

/-
## Part V: The Main Conjecture
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

/-
## Part VI: Characterization via m-Digit Expansions

Bugeaud and others characterized Pisot numbers using generalized expansions.
-/

/-- m-digit q-representable numbers: using digits 0, 1, ..., m instead of just 0, 1. -/
def QRepresentableM (q : ℝ) (m : ℕ) : Set ℝ :=
  {x : ℝ | ∃ (S : Finset ℕ) (c : ℕ → ℕ),
    (∀ i ∈ S, c i ≤ m) ∧ x = S.sum (fun i => (c i : ℝ) * q ^ i)}

/-- The k-th element of the m-digit ordered sequence. -/
axiom qSequenceM (q : ℝ) (m : ℕ) (k : ℕ) : ℝ

def gapM (q : ℝ) (m : ℕ) (k : ℕ) : ℝ :=
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

/-
## Part VII: Density Result
-/

/-- As q → 1⁺, QRepresentable(q) becomes arbitrarily dense in [0, N].
    This explains why the gap property should hold for q close to 1. -/
axiom density_near_one :
    ∀ ε > 0, ∀ N : ℝ, N > 0 →
      ∃ q : ℝ, 1 < q ∧ q < 1 + ε ∧
        ∀ x ∈ Set.Icc 0 N, ∃ y ∈ QRepresentable q, |x - y| < ε

/-
## Part VIII: Summary
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

end Erdos1096
