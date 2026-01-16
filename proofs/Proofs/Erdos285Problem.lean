/-
  Erdős Problem #285: Egyptian Fractions Asymptotics

  **Question**: Let f(k) be the minimal value of the largest denominator nₖ
  among all representations 1 = 1/n₁ + ··· + 1/nₖ with n₁ < n₂ < ··· < nₖ.
  Is it true that f(k) = (1 + o(1)) · e/(e-1) · k?

  **Answer**: YES — proved by Greg Martin (2000).

  The constant e/(e-1) ≈ 1.582 arises from the harmonic series structure:
  the reciprocals in [e, e·u] sum to approximately 1, contributing ~(e-1)·u terms.

  Reference: https://erdosproblems.com/285
  Key paper: Martin, Greg, "Denser Egyptian fractions" (2000)
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Topology.Instances.Real

namespace Erdos285

open Finset Filter Real BigOperators
open scoped Topology Real

/-! ## Background on Egyptian Fractions -/

/--
An Egyptian fraction representation of 1 using k terms is a strictly increasing
sequence n₁ < n₂ < ··· < nₖ of positive integers such that
1 = 1/n₁ + 1/n₂ + ··· + 1/nₖ

Note: k+1 terms because we index from 0 to k (Fin k.succ).
-/
def IsEgyptianRepresentation (k : ℕ) (n : Fin k.succ → ℕ) : Prop :=
  StrictMono n ∧ 0 ∉ Set.range n ∧ 1 = ∑ i, (1 : ℝ) / n i

/--
The set of k for which Egyptian fraction representations with k+1 terms exist.
(Representations always exist for k ≥ 2 since 1 = 1/2 + 1/3 + 1/6.)
-/
def ValidLengths : Set ℕ :=
  {k | ∃ n : Fin k.succ → ℕ, IsEgyptianRepresentation k n}

/--
f(k) is the minimal value of the largest denominator nₖ among all
Egyptian fraction representations of 1 using k+1 terms.
-/
noncomputable def f (k : ℕ) : ℕ :=
  sInf {n (Fin.last k) | n : Fin k.succ → ℕ, h : IsEgyptianRepresentation k n}

/-! ## The Main Asymptotic Result -/

/--
The constant e/(e-1) ≈ 1.5819... that appears in the asymptotics.
-/
noncomputable def egyptianConstant : ℝ := rexp 1 / (rexp 1 - 1)

/--
**Martin (2000)**: f(k) = (1 + o(1)) · e/(e-1) · k.

The minimal largest denominator in a k+1-term Egyptian fraction representation
of 1 is asymptotically e/(e-1) times k.
-/
axiom martin_egyptian_fractions :
    ∃ (o : ℕ → ℝ) (_ : Asymptotics.IsLittleO atTop o (fun _ : ℕ => (1 : ℝ))),
      ∀ k ∈ ValidLengths, (f k : ℝ) = (1 + o k) * egyptianConstant * (k + 1)

/-- Erdős Problem #285: The asymptotic formula holds -/
theorem erdos_285 :
    ∃ (o : ℕ → ℝ), (Asymptotics.IsLittleO atTop o (fun _ => (1 : ℝ))) ∧
      ∀ k ∈ ValidLengths, (f k : ℝ) = (1 + o k) * egyptianConstant * (k + 1) :=
  let ⟨o, ho, hf⟩ := martin_egyptian_fractions
  ⟨o, ho, hf⟩

/-! ## The Lower Bound (Trivial) -/

/--
**Trivial Lower Bound**: f(k) ≥ (1 + o(1)) · e/(e-1) · k.

This follows from the harmonic series: for any u ≥ 1,
∑_{e ≤ n ≤ eu} 1/n = 1 + o(1).

If the largest denominator is ~eu, we can have at most ~(e-1)u terms
from the interval [e, eu], so k ≤ (e-1)/e · f(k), giving f(k) ≥ e/(e-1) · k.
-/
axiom egyptian_lower_bound :
    ∃ (o : ℕ → ℝ) (_ : Asymptotics.IsLittleO atTop o (fun _ : ℕ => (1 : ℝ))),
      ∀ k ∈ ValidLengths, (1 + o k) * egyptianConstant * (k + 1) ≤ f k

/-! ## Understanding the Constant -/

/--
The value e/(e-1) ≈ 1.5819 means:
- For k=100 terms: f(100) ≈ 158 (largest denominator ~158)
- For k=1000 terms: f(1000) ≈ 1582

The constant arises because ln(e·u) - ln(e) = 1 for any u,
so the interval [e, e·u] contains approximately 1 unit of "harmonic mass".
-/

/-- e/(e-1) > 1, showing f(k) > k always -/
theorem egyptianConstant_gt_one : egyptianConstant > 1 := by
  unfold egyptianConstant
  have he : rexp 1 > 1 := Real.one_lt_exp_of_pos (by norm_num : (1 : ℝ) > 0)
  have hpos : rexp 1 - 1 > 0 := by linarith
  rw [gt_iff_lt, div_lt_iff_of_pos hpos]
  ring_nf
  exact he

/-- e/(e-1) < 2, so f(k) < 2k asymptotically -/
theorem egyptianConstant_lt_two : egyptianConstant < 2 := by
  sorry -- Requires: e > 2, so e/(e-1) = 1 + 1/(e-1) < 1 + 1 = 2

/-! ## Examples -/

/-- The classic 3-term representation: 1 = 1/2 + 1/3 + 1/6 -/
example : (1 : ℝ) / 2 + 1 / 3 + 1 / 6 = 1 := by norm_num

/-- Another representation: 1 = 1/2 + 1/4 + 1/5 + 1/20 -/
example : (1 : ℝ) / 2 + 1 / 4 + 1 / 5 + 1 / 20 = 1 := by norm_num

/-- And: 1 = 1/3 + 1/4 + 1/5 + 1/6 + 1/20 -/
example : (1 : ℝ) / 3 + 1 / 4 + 1 / 5 + 1 / 6 + 1 / 20 = 1 := by norm_num

end Erdos285
