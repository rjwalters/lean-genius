/-
  Aristotle targets for Erdos Problem #265
  Routine supporting lemmas for automated proof search.
  See Erdos265Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture (limsup a_n^{1/2^n} > 1)
  - Known results likely provable from Mathlib
  - Clean theorem statements with no definition sorries
  - No axiom declarations
-/
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Erdos265Aristotle

open Filter

variable (a : ℕ → ℕ)

/-- A sequence of positive integers -/
def IsPositiveIntSeq : Prop := ∀ n, a n ≥ 1

noncomputable def singleExpGrowth (n : ℕ) : ℝ :=
  (a n : ℝ) ^ (1 / n : ℝ)

noncomputable def genExpGrowth (β : ℝ) (n : ℕ) : ℝ :=
  (a n : ℝ) ^ (1 / β ^ n)

-- TARGET 1: If a_n^{1/β^n} → ∞ for β > 1, then a_n^{1/n} → ∞
-- Strategy: For β > 1 and large n, β^n ≥ n, so 1/n ≥ 1/β^n.
--   Since a_n ≥ 1, rpow is monotone: (a_n)^{1/n} ≥ (a_n)^{1/β^n}.
--   By comparison, singleExpGrowth → ∞.
-- Key tools: Real.rpow_le_rpow_of_exponent_le, tendsto_pow_atTop_atTop_of_one_lt
theorem singleExp_of_genExp (β : ℝ) (hβ : β > 1)
    (hpos : IsPositiveIntSeq a)
    (htend : Tendsto (genExpGrowth a β) atTop atTop) :
    Tendsto (singleExpGrowth a) atTop atTop := by sorry

-- TARGET 2: For β > 1, eventually β^n ≥ n
-- Strategy: tendsto_pow_atTop_atTop_of_one_lt gives β^n → ∞,
--   so eventually β^n ≥ n
-- Key tools: tendsto_pow_atTop_atTop_of_one_lt, Filter.Tendsto.eventually_ge_atTop
theorem eventually_pow_ge_id (β : ℝ) (hβ : β > 1) :
    ∀ᶠ n in atTop, (n : ℝ) ≤ β ^ n := by sorry

-- TARGET 3: rpow monotonicity for base ≥ 1
-- Strategy: This should be in Mathlib as Real.rpow_le_rpow_of_exponent_le
-- Key tools: Real.rpow_le_rpow_of_exponent_le
theorem rpow_mono_exponent (x : ℝ) (hx : 1 ≤ x) (p q : ℝ) (hpq : p ≤ q) :
    x ^ p ≤ x ^ q :=
  Real.rpow_le_rpow_of_exponent_le hx hpq

end Erdos265Aristotle
