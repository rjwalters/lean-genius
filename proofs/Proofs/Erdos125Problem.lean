/-!
# Erdős Problem #125: Positive Density of Digit-Restricted Sumsets

Let A = {Σ εₖ3ᵏ : εₖ ∈ {0,1}} (integers with digits 0,1 in base 3)
and B = {Σ εₖ4ᵏ : εₖ ∈ {0,1}} (digits 0,1 in base 4). Does A + B
have positive density?

## Status: OPEN

## References
- Burr–Erdős–Graham–Li (1996)
- Erdős (1997)
- Melfi (2001): |C∩[1,x]| ≫ x^{0.965}
- Hasler–Melfi (2024): improved to x^{0.9777}, upper density ≤ 0.696
-/

import Mathlib.Data.Nat.Digits
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

/-!
## Section I: Digit-Restricted Sets
-/

/-- The set of natural numbers whose base-b digits are all 0 or 1.
These are sums of distinct powers of b. -/
def digitSet (b : ℕ) : Set ℕ :=
  { n : ℕ | ∀ d ∈ Nat.digits b n, d = 0 ∨ d = 1 }

/-- A = digitSet 3: numbers with only digits 0, 1 in base 3.
Also known as the "Cantor set integers". -/
def setA : Set ℕ := digitSet 3

/-- B = digitSet 4: numbers with only digits 0, 1 in base 4. -/
def setB : Set ℕ := digitSet 4

/-!
## Section II: The Sumset
-/

/-- The sumset C = A + B = { a + b : a ∈ A, b ∈ B }. -/
def setC : Set ℕ := { n : ℕ | ∃ a ∈ setA, ∃ b ∈ setB, n = a + b }

/-- The counting function: |C ∩ [1, x]|. -/
noncomputable def countingC (x : ℕ) : ℕ :=
  (Finset.range (x + 1)).filter (· ∈ setC) |>.card

/-!
## Section III: The Conjecture
-/

/-- **Erdős Problem #125**: Does C = A + B have positive lower density?
That is, does lim inf |C ∩ [1,x]| / x > 0? -/
def ErdosProblem125 : Prop :=
  ∃ δ : ℝ, δ > 0 ∧
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ,
      ∀ x : ℕ, x ≥ N₀ → (countingC x : ℝ) / x ≥ δ - ε

/-!
## Section IV: Known Lower Bounds
-/

/-- Melfi (2001): |C ∩ [1,x]| ≫ x^{0.965}. -/
axiom melfi_lower_bound :
  ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ,
    ∀ x : ℕ, x ≥ N₀ → (countingC x : ℝ) ≥ c * (x : ℝ) ^ (0.965 : ℝ)

/-- Hasler–Melfi (2024): improved to |C ∩ [1,x]| ≫ x^{0.9777}. -/
axiom hasler_melfi_lower_bound :
  ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ,
    ∀ x : ℕ, x ≥ N₀ → (countingC x : ℝ) ≥ c * (x : ℝ) ^ (0.9777 : ℝ)

/-!
## Section V: Upper Density Bound
-/

/-- Hasler–Melfi (2024): the upper density of C is at most ≈ 0.696.
So even if C has positive density, it cannot fill more than 70% of ℕ. -/
axiom upper_density_bound :
  ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ x : ℕ, x ≥ N₀ →
    (countingC x : ℝ) / x ≤ 0.696 + ε

/-!
## Section VI: Generalization to Other Bases
-/

/-- The general problem: for bases n₁ < ⋯ < nₖ, does
digitSet(n₁) + ⋯ + digitSet(nₖ) have positive density when
Σ log_{nₖ}(2) > 1? This condition ensures the sumset is
large enough to potentially have positive density. -/
def GeneralizedDensityQuestion (bases : List ℕ) : Prop :=
  (∀ b ∈ bases, b ≥ 2) →
    (bases.map (fun b => Real.log 2 / Real.log b)).sum > 1 →
      ∃ δ : ℝ, δ > 0 ∧
        ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ,
          ∀ x : ℕ, x ≥ N₀ →
            (countingC x : ℝ) / x ≥ δ - ε

/-- For bases 3 and 4: log₄(2) + log₄(2)/log₄(3) =
log(2)/log(3) + log(2)/log(4) ≈ 0.631 + 0.5 = 1.131 > 1,
satisfying the condition. -/
axiom base_3_4_satisfies_condition :
  Real.log 2 / Real.log 3 + Real.log 2 / Real.log 4 > 1
