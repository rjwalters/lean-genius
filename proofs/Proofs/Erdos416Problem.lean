/-
  Erdős Problem #416: Counting Totient Values

  Let V(x) count the number of n ≤ x such that φ(m) = n is solvable
  (i.e., n is in the range of Euler's totient function).

  **Questions**:
  (i)  Does V(2x)/V(x) → 2 as x → ∞?
  (ii) Is there an asymptotic formula for V(x)?

  **Status**: OPEN (main questions), but asymptotic bounds are well-understood

  **History**:
  - Pillai (1929): V(x) = o(x)
  - Erdős (1935): V(x) = x(log x)^(-1+o(1))
  - Maier-Pomerance (1988): V(x) = (x/log x) · e^((C+o(1))(log log log x)²)
  - Ford (1998): V(x) ≍ (x/log x) · e^(C₁(log log log x - log log log log x)² + ...)

  The problem asks whether these bounds can be refined to an actual asymptotic
  formula, and whether the doubling ratio V(2x)/V(x) tends to 2.

  Reference: https://erdosproblems.com/416
-/

import Mathlib

namespace Erdos416

open Set Filter BigOperators Asymptotics Classical
open scoped Topology

attribute [local instance] Classical.propDecidable

/-! ## The Counting Function V(x) -/

/--
**V(x)** counts the number of positive integers n ≤ x that are **totient values**,
meaning there exists some m with φ(m) = n.

Not every positive integer is a totient value:
- φ(1) = 1, φ(2) = 1, so 1 is a totient value
- φ(3) = 2, so 2 is a totient value
- No m has φ(m) = 3 (since φ(m) is even for m > 2), so 3 is NOT a totient value

The function V(x) counts how many n ≤ x ARE totient values.
-/
noncomputable def V (x : ℝ) : ℝ :=
  ((Finset.Icc 1 ⌊x⌋₊).filter (fun n => ∃ m : ℕ, m.totient = n)).card

/-! ## Basic Properties -/

/-- V is nonnegative -/
theorem V_nonneg (x : ℝ) : 0 ≤ V x := by
  unfold V
  exact Nat.cast_nonneg _

/-- V is monotone increasing -/
theorem V_mono : Monotone V := by
  intro x y hxy
  unfold V
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  apply Finset.Icc_subset_Icc (le_refl _) (Nat.floor_le_floor hxy)

/-- Small values: 1 is a totient value (φ(1) = 1 and φ(2) = 1) -/
theorem one_is_totient : ∃ m : ℕ, m.totient = 1 := ⟨1, rfl⟩

/-- Small values: 2 is a totient value (φ(3) = 2) -/
theorem two_is_totient : ∃ m : ℕ, m.totient = 2 := ⟨3, by native_decide⟩

/-- Small values: 4 is a totient value (φ(5) = 4) -/
theorem four_is_totient : ∃ m : ℕ, m.totient = 4 := ⟨5, by native_decide⟩

/-! ## Partial Results (Solved) -/

/--
**Pillai (1929)**: V(x) = o(x)

The density of totient values is 0. Most integers are NOT totient values.
This was the first quantitative result about the sparsity of totient values.
-/
axiom Pillai_1929 : V =o[atTop] id

/--
**Erdős (1935)**: V(x) = x · (log x)^(-1+o(1))

This refines Pillai's result: V(x) behaves like x/log x up to sub-polynomial
factors in the exponent. The density decays like 1/log x.
-/
axiom Erdos_1935 : ∃ f : ℝ → ℝ, f =o[atTop] (1 : ℝ → ℝ) ∧
    ∀ᶠ x in atTop, V x = x * x.log ^ (-1 + f x)

/--
**Maier-Pomerance (1988)**: V(x) = (x/log x) · e^((C+o(1))(log log log x)²)

A more precise asymptotic: the correction factor is exponential in (log log log x)².
The constant C is explicitly computable.
-/
axiom Maier_Pomerance_1988 :
    ∃ C : ℝ, 0 < C ∧ ∃ f : ℝ → ℝ, f =o[atTop] (1 : ℝ → ℝ) ∧
      ∀ᶠ x in atTop, V x = x / x.log * Real.exp ((C + f x) * x.log.log.log ^ 2)

/--
**Ford (1998)**: The most precise bound known

V(x) ≍ (x/log x) · exp(C₁(log log log x - log log log log x)² + C₂ log log log x - C₃ log log log log x)

This determines V(x) up to constant factors but still falls short of an asymptotic formula.
-/
axiom Ford_1998 :
    ∃ C₁ C₂ C₃ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧
    let G (x : ℝ) := x / x.log * Real.exp (
      C₁ * (x.log.log.log - x.log.log.log.log) ^ 2 +
      C₂ * x.log.log.log -
      C₃ * x.log.log.log.log)
    V =Θ[atTop] G

/-! ## Main Open Questions -/

/--
**Erdős Problem #416, Part (i)**: Does V(2x)/V(x) → 2?

This asks whether doubling the range roughly doubles the count of totient values.
If V(x) ~ c · x / log x for some constant c, this would follow.
But the complicated structure of Ford's bound makes this uncertain.
-/
def Erdos416_Part_i : Prop :=
  Tendsto (fun x => V (2 * x) / V x) atTop (𝓝 2)

/--
**Erdős Problem #416, Part (ii)**: Is there an asymptotic formula for V(x)?

This asks for V(x) ~ f(x) for some explicit function f, not just V(x) ≍ f(x).
Ford's result gives tight bounds but not an asymptotic.
-/
def Erdos416_Part_ii : Prop :=
  ∃ f : ℝ → ℝ, Tendsto (fun x => V x / f x) atTop (𝓝 1)

/-! ## The Main Conjecture -/

/--
**Erdős Problem #416**: Both questions remain OPEN.

Despite Ford's remarkable work determining V(x) up to constant factors,
neither the doubling ratio nor an asymptotic formula has been established.
-/
def Erdos416Conjecture : Prop := Erdos416_Part_i ∧ Erdos416_Part_ii

/-! ## Related Results -/

/-- 3 is NOT a totient value (no m has φ(m) = 3).
    Proof: φ(m) is even for m > 2, and φ(1) = φ(2) = 1. -/
axiom three_not_totient : ¬∃ m : ℕ, m.totient = 3

-- Note: The only odd totient value is 1, since φ(n) is even for n > 2

end Erdos416
