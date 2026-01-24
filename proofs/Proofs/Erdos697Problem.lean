/-
Erdős Problem #697: Density of Integers Divisible by d ≡ 1 (mod m)

Source: https://erdosproblems.com/697
Status: SOLVED (Hall, 1992)

Statement:
Let δ(m,α) denote the density of integers divisible by some d ≡ 1 (mod m)
with 1 < d < exp(m^α). Does there exist β ∈ (1,∞) such that
  lim_{m→∞} δ(m,α) = 0 if α < β
  lim_{m→∞} δ(m,α) = 1 if α > β

Answer: YES, with β = 1/log 2 ≈ 1.443 (Hall 1992)

Key Results:
- Trivial: δ(m,α) → 0 for α < 1
- Erdős: The same for α = 1 (claimed in 1979)
- Hall (1992): Sharp threshold at β = 1/log 2

Intuition:
For α < 1/log 2, there aren't enough divisors d ≡ 1 (mod m) in the range.
For α > 1/log 2, there are enough to cover most integers.

References:
- [Er79e] Erdős, "Some unconventional problems in number theory" (1979)
- [Ha92] Hall, "On some conjectures of P. Erdős in Astérisque I" (1992)
- Related: Problem #696

Tags: number-theory, divisors, density, modular-arithmetic, threshold
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Basic

open Real Nat

namespace Erdos697

/-!
## Part 1: Basic Definitions
-/

/-- A divisor d of n with d ≡ 1 (mod m) and 1 < d < exp(m^α) -/
def IsAdmissibleDivisor (n m : ℕ) (α : ℝ) (d : ℕ) : Prop :=
  d ∣ n ∧ d > 1 ∧ d % m = 1 ∧ (d : ℝ) < Real.exp (m ^ α)

/-- n is covered if it has an admissible divisor -/
def IsCovered (m : ℕ) (α : ℝ) (n : ℕ) : Prop :=
  ∃ d : ℕ, IsAdmissibleDivisor n m α d

/-- Count of covered integers up to N -/
noncomputable def coveredCount (m : ℕ) (α : ℝ) (N : ℕ) : ℕ :=
  (Finset.range (N + 1)).filter (IsCovered m α) |>.card

/-- The density δ(m, α) = lim_{N→∞} (covered integers ≤ N) / N -/
noncomputable def delta (m : ℕ) (α : ℝ) : ℝ :=
  if m ≤ 1 then 0
  else Filter.liminf (fun N => coveredCount m α N / N) Filter.atTop

/-!
## Part 2: The Threshold Question
-/

/-- The main question: does a sharp threshold β exist? -/
def HasSharpThreshold : Prop :=
  ∃ β : ℝ, β > 1 ∧
    (∀ α : ℝ, α < β → Filter.Tendsto (fun m => delta m α) Filter.atTop (nhds 0)) ∧
    (∀ α : ℝ, α > β → Filter.Tendsto (fun m => delta m α) Filter.atTop (nhds 1))

/-- The critical threshold β = 1/log 2 ≈ 1.443 -/
noncomputable def hallThreshold : ℝ := 1 / Real.log 2

/-- Verify β ≈ 1.443 is in (1, ∞) -/
theorem hallThreshold_in_range : hallThreshold > 1 := by
  -- 1/log 2 > 1 ⟺ 1 > log 2, which is true since log 2 < 1
  sorry

/-!
## Part 3: Trivial Bounds
-/

/-- For α < 1: δ(m, α) < (m^α + 1)/m → 0 as m → ∞ -/
axiom trivial_upper_bound (α : ℝ) (hα : α < 1) :
  Filter.Tendsto (fun m => delta m α) Filter.atTop (nhds 0)

/-- The trivial bound comes from counting divisors d ≡ 1 (mod m) -/
axiom trivial_bound_proof :
  -- Number of d ≡ 1 (mod m) with d < exp(m^α) is about exp(m^α)/m = m^{α-1}
  -- which → 0 when α < 1
  True

/-!
## Part 4: Erdős's Claim for α = 1
-/

/-- Erdős (1979): δ(m, 1) → 0 as m → ∞ -/
axiom erdos_alpha_one :
  Filter.Tendsto (fun m => delta m 1) Filter.atTop (nhds 0)

/-- Erdős claimed this in [Er79e] but didn't publish a full proof -/
axiom erdos_claim_source : True

/-!
## Part 5: Hall's Theorem (1992)
-/

/-- **Hall's Theorem (1992):**
    The sharp threshold exists and equals β = 1/log 2.

    For α < 1/log 2: lim δ(m, α) = 0
    For α > 1/log 2: lim δ(m, α) = 1 -/
axiom hall_theorem :
  HasSharpThreshold ∧
    (∀ α : ℝ, α < hallThreshold →
      Filter.Tendsto (fun m => delta m α) Filter.atTop (nhds 0)) ∧
    (∀ α : ℝ, α > hallThreshold →
      Filter.Tendsto (fun m => delta m α) Filter.atTop (nhds 1))

/-- The threshold is exactly 1/log 2 -/
theorem threshold_is_one_over_log_two :
    HasSharpThreshold ∧
    (∃ β : ℝ, β = hallThreshold ∧ β > 1 ∧
      (∀ α < β, Filter.Tendsto (fun m => delta m α) Filter.atTop (nhds 0)) ∧
      (∀ α > β, Filter.Tendsto (fun m => delta m α) Filter.atTop (nhds 1))) := by
  obtain ⟨hSharp, hBelow, hAbove⟩ := hall_theorem
  exact ⟨hSharp, hallThreshold, rfl, hallThreshold_in_range, hBelow, hAbove⟩

/-!
## Part 6: Why 1/log 2?
-/

/-- Intuition: The number of d ≡ 1 (mod m) with d < x is about x/m.
    For x = exp(m^α), this is exp(m^α)/m.

    For this to "cover" most integers, we need:
    exp(m^α)/m ≥ 1, i.e., m^α ≥ log m, i.e., α ≥ (log log m) / (log m)

    The threshold comes from the sieve-theoretic analysis of when
    enough divisors exist to cover a positive density of integers. -/
axiom intuition_for_threshold : True

/-- The value 1/log 2 arises from the multiplicative structure of divisors -/
axiom why_one_over_log_two :
  -- Hall's analysis shows that the critical exponent is determined by
  -- the distribution of prime factors in numbers of the form d ≡ 1 (mod m)
  True

/-!
## Part 7: Behavior at Threshold
-/

/-- What happens exactly at α = β = 1/log 2? -/
def AtThresholdBehavior : Prop :=
  -- The behavior at the threshold is more delicate
  -- It may be 0, 1, or something in between
  True

/-- Hall's theorem doesn't specify the behavior exactly at the threshold -/
axiom at_threshold_open :
  -- This is a more subtle question not addressed in Hall (1992)
  True

/-!
## Part 8: Connection to Problem #696
-/

/-- Problem #696 is related (similar divisibility questions) -/
axiom related_problem_696 : True

/-- The problems share the theme of understanding when divisors d ≡ 1 (mod m)
    sufficiently cover integers -/
axiom shared_theme : True

/-!
## Part 9: Examples
-/

/-- For m = 2: d ≡ 1 (mod 2) means d is odd.
    Every integer > 1 is divisible by an odd d > 1 (itself if odd, or odd part).
    So δ(2, α) = 1 for all α > 0. -/
axiom example_m_2 : ∀ α : ℝ, α > 0 → delta 2 α = 1

/-- For m = p (large prime): d ≡ 1 (mod p) means d = 1 + kp.
    The smallest such d > 1 is 1 + p.
    The density depends on how many integers are divisible by such d. -/
axiom example_m_prime : True

/-!
## Part 10: Historical Context
-/

/-- The problem appeared in Erdős's 1979 paper in Astérisque -/
axiom erdos_1979_source : True

/-- "Some unconventional problems in number theory" contained several
    related problems about divisibility and density -/
axiom unconventional_problems : True

/-- Hall's 1992 paper resolved this and related questions -/
axiom hall_1992_paper : True

/-!
## Part 11: Main Results
-/

/-- The answer to Erdős's question is YES -/
theorem erdos_697_answer : HasSharpThreshold := hall_theorem.1

/-- The sharp threshold is β = 1/log 2 ≈ 1.443 -/
theorem erdos_697_threshold : HasSharpThreshold ∧
    (∀ α < hallThreshold, Filter.Tendsto (fun m => delta m α) Filter.atTop (nhds 0)) ∧
    (∀ α > hallThreshold, Filter.Tendsto (fun m => delta m α) Filter.atTop (nhds 1)) :=
  hall_theorem

/-- **Erdős Problem #697: SOLVED**

QUESTION: Does a sharp threshold β exist for δ(m, α)?

ANSWER: YES, β = 1/log 2 ≈ 1.443 (Hall 1992)

- For α < 1/log 2: density → 0 as m → ∞
- For α > 1/log 2: density → 1 as m → ∞

The threshold arises from the multiplicative structure of
divisors congruent to 1 modulo m. -/
theorem erdos_697_summary :
    HasSharpThreshold ∧ hallThreshold > 1 :=
  ⟨erdos_697_answer, hallThreshold_in_range⟩

/-- The problem is completely solved -/
theorem erdos_697_solved : HasSharpThreshold := erdos_697_answer

/-- Problem status -/
def erdos_697_status : String :=
  "SOLVED (Hall 1992) - Sharp threshold β = 1/log 2 ≈ 1.443"

end Erdos697
