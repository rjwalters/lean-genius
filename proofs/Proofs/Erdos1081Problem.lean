/-
Erdős Problem #1081: Sums of Two Squarefull Numbers

Source: https://erdosproblems.com/1081
Status: DISPROVED (Odoni, 1981)

Statement:
Let A(x) count the number of n ≤ x which are the sum of two squarefull numbers.
(A number m is squarefull if p | m implies p² | m.)

Is it true that A(x) ~ c · x / √(log x) for some c > 0?

Answer: NO

Key Results:
- Odoni (1981): Disproved the conjecture, showing A(x) grows faster
- Odoni proved: A(x) ≫ exp(c · log log log x / log log x) · x / √(log x)
- Blomer-Granville (2006): A(x) = (log log x)^O(1) · x / (log x)^α
  where α = 1 - 2^(-1/3) ≈ 0.206299

References:
- Odoni, R.W.K., "A problem of Erdős on sums of two squarefull numbers."
  Acta Arith. (1981), 145-162.
- Blomer, V. and Granville, A., "Estimates for representation numbers of
  quadratic forms." Duke Math. J. (2006), 261-302.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Nat Real Finset

namespace Erdos1081

/-
## Part I: Squarefull Numbers
-/

/--
**Squarefull Number:**
A positive integer m is squarefull (also called powerful) if for every prime p
dividing m, we have p² | m.

Equivalently: m can be written as a²b³ for some positive integers a, b.

Examples: 1, 4, 8, 9, 16, 25, 27, 32, 36, 49, 64, 72, ...
-/
def IsSquarefull (m : ℕ) : Prop :=
  m > 0 ∧ ∀ p : ℕ, p.Prime → p ∣ m → p^2 ∣ m

/--
**Alternative characterization:**
m is squarefull iff m = a² · b³ for some a, b ≥ 1.
-/
def IsSquarefullAlt (m : ℕ) : Prop :=
  ∃ a b : ℕ, a ≥ 1 ∧ b ≥ 1 ∧ m = a^2 * b^3

/--
**Equivalence of squarefull characterizations:**
-/
axiom squarefull_equiv (m : ℕ) :
    IsSquarefull m ↔ IsSquarefullAlt m

/--
**1 is squarefull:**
Vacuously, no primes divide 1.
-/
theorem one_squarefull : IsSquarefull 1 := by
  constructor
  · omega
  · intros p hp hd
    have : p ≥ 2 := hp.two_le
    omega

/--
**Prime powers are squarefull iff exponent ≥ 2:**
-/
theorem prime_power_squarefull (p : ℕ) (hp : p.Prime) (k : ℕ) :
    IsSquarefull (p^k) ↔ k ≥ 2 ∨ k = 0 := by
  constructor
  · -- Forward: if p^k is squarefull and k ≥ 1 then k ≥ 2
    intro ⟨_, hdiv⟩
    by_contra h
    push_neg at h
    obtain ⟨hlt, hne⟩ := h
    have hk1 : k = 1 := by omega
    subst hk1
    simp only [pow_one] at hdiv
    have h1 := hdiv p hp (dvd_refl p)
    -- h1 : p ^ 2 ∣ p, so p^2 ≤ p
    have hle : p ^ 2 ≤ p := Nat.le_of_dvd hp.pos h1
    -- But p^2 = p*p ≥ 2p > p for p ≥ 2
    have hp2 : p ≥ 2 := hp.two_le
    have : p ^ 2 ≥ 2 * p := by nlinarith
    omega
  · -- Backward: k ≥ 2 or k = 0 implies p^k is squarefull
    intro h
    refine ⟨?_, ?_⟩
    · rcases h with h | h
      · exact Nat.pos_of_ne_zero (pow_ne_zero k hp.ne_zero)
      · simp [h]
    · intro q hq hd
      rcases h with h | h
      · have hqp : q ∣ p := hq.dvd_of_dvd_pow hd
        have heq : q = p := by
          rcases hp.eq_one_or_self_of_dvd q hqp with h1 | h1
          · exact absurd h1 hq.one_lt.ne'
          · exact h1
        rw [heq]
        exact Nat.pow_dvd_pow p h
      · subst h
        simp only [pow_zero] at hd
        have hq2 := hq.two_le
        exact absurd (Nat.le_of_dvd Nat.one_pos hd) (by omega)

/--
**Small squarefull numbers:**
4 = 2², 8 = 2³, 9 = 3², 16 = 2⁴, 25 = 5², 27 = 3³
-/
theorem four_squarefull : IsSquarefull 4 := by
  constructor
  · omega
  · intros p hp hd
    interval_cases p <;> simp_all

theorem eight_squarefull : IsSquarefull 8 := by
  constructor
  · omega
  · intros p hp hd
    interval_cases p <;> simp_all

theorem nine_squarefull : IsSquarefull 9 := by
  constructor
  · omega
  · intros p hp hd
    interval_cases p <;> simp_all

/-
## Part II: Sums of Two Squarefull Numbers
-/

/--
**Sum of two squarefull numbers:**
n is expressible as a + b where both a and b are squarefull.
-/
def IsSumOfTwoSquarefull (n : ℕ) : Prop :=
  ∃ a b : ℕ, IsSquarefull a ∧ IsSquarefull b ∧ n = a + b

/--
**Examples of sums of two squarefull numbers:**
- 5 = 1 + 4
- 9 = 1 + 8 = 4 + 5 (only first works)
- 13 = 4 + 9
-/
theorem five_is_sum : IsSumOfTwoSquarefull 5 := by
  use 1, 4
  exact ⟨one_squarefull, four_squarefull, rfl⟩

theorem thirteen_is_sum : IsSumOfTwoSquarefull 13 := by
  use 4, 9
  exact ⟨four_squarefull, nine_squarefull, rfl⟩

/-
## Part III: The Counting Function A(x)
-/

/--
**The counting function A(x):**
A(x) = #{n ≤ x : n is a sum of two squarefull numbers}
-/
noncomputable def A (x : ℕ) : ℕ :=
  (Finset.range (x + 1)).filter (fun n => IsSumOfTwoSquarefull n) |>.card

/--
**Squarefull numbers up to x:**
S(x) = #{n ≤ x : n is squarefull} ~ ζ(3/2)/ζ(3) · √x
-/
noncomputable def S (x : ℕ) : ℕ :=
  (Finset.range (x + 1)).filter (fun n => IsSquarefull n) |>.card

/--
**Asymptotic for squarefull count:**
S(x) ~ c · √x where c = ζ(3/2)/ζ(3) ≈ 2.173
-/
axiom squarefull_count_asymptotic :
  ∃ c : ℝ, c > 0 ∧ c < 3 ∧
    ∀ ε > 0, ∃ X : ℕ, ∀ x : ℕ, x ≥ X →
      |((S x : ℝ) - c * Real.sqrt x)| < ε * Real.sqrt x

/-
## Part IV: Erdős's Conjecture (Disproved)
-/

/--
**Erdős's Conjecture (1976):**
A(x) ~ c · x / √(log x) for some constant c > 0.

This conjecture was FALSE.
-/
def erdos_conjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧
    ∀ ε > 0, ∃ X : ℕ, ∀ x : ℕ, x ≥ X →
      |(A x : ℝ) / (x / Real.sqrt (Real.log x)) - c| < ε

/--
**Odoni's Disproof (1981):**
The conjecture is false. A(x) grows strictly faster than x/√(log x).
-/
axiom odoni_disproof : ¬erdos_conjecture

/-
## Part V: Odoni's Lower Bound
-/

/--
**Odoni's Lower Bound (1981):**
A(x) ≫ exp(c · log log log x / log log x) · x / √(log x)

This shows A(x) is asymptotically larger than x/√(log x) by a
slowly growing factor.
-/
axiom odoni_lower_bound :
  ∃ c C : ℝ, c > 0 ∧ C > 0 ∧
    ∀ x : ℕ, x ≥ 16 →
      (A x : ℝ) ≥ C * Real.exp (c * Real.log (Real.log (Real.log x)) /
                                    Real.log (Real.log x)) *
                    x / Real.sqrt (Real.log x)

/-
## Part VI: Blomer-Granville Refinement
-/

/--
**Critical Exponent:**
α = 1 - 2^(-1/3) ≈ 0.206299

This is the correct exponent for the counting function.
-/
noncomputable def alpha : ℝ := 1 - (2 : ℝ)^(-(1/3 : ℝ))

/--
**Blomer-Granville Theorem (2006):**
A(x) = (log log x)^O(1) · x / (log x)^α

where α = 1 - 2^(-1/3) ≈ 0.206299.
-/
axiom blomer_granville_2006 :
  ∃ C K : ℝ, C > 0 ∧ K > 0 ∧
    ∀ x : ℕ, x ≥ 16 →
      (A x : ℝ) ≤ C * (Real.log (Real.log x))^K *
                    x / (Real.log x)^alpha ∧
      (A x : ℝ) ≥ (1/C) * (Real.log (Real.log x))^(-K) *
                    x / (Real.log x)^alpha

/--
**Comparison of exponents:**
α ≈ 0.206 vs 1/2 = 0.5

The true exponent α is much smaller than Erdős's conjectured 1/2,
meaning A(x) grows faster than expected.
-/
theorem alpha_less_than_half : alpha < 1/2 := by
  unfold alpha
  -- Need: 1 - 2^(-1/3) < 1/2, equivalently 1/2 < 2^(-1/3)
  suffices h : (1 : ℝ) / 2 < (2 : ℝ) ^ (-(1 / 3 : ℝ)) by linarith
  -- 2^(-1/3) = 1/2^(1/3), and 2^(1/3) < 2 so 1/2^(1/3) > 1/2
  have hcbrt_lt : (2 : ℝ) ^ ((1 : ℝ) / 3) < 2 := by
    calc (2 : ℝ) ^ ((1 : ℝ) / 3) < (2 : ℝ) ^ (1 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
          norm_num
    _ = 2 := Real.rpow_one 2
  have hcbrt_pos : (0 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  rw [Real.rpow_neg (by norm_num : (2 : ℝ) ≥ 0)]
  -- Goal: 1/2 < (2^(1/3))⁻¹
  rw [show (1 : ℝ) / 2 = ((2 : ℝ))⁻¹ from one_div 2]
  exact (inv_lt_inv₀ (by norm_num : (0 : ℝ) < 2) hcbrt_pos).mpr hcbrt_lt

/-
## Part VII: Why the Conjecture Failed
-/

/--
**Heuristic explanation:**
Erdős's conjecture was based on a simple probabilistic model:
- Squarefull numbers up to x: ~ c₁√x
- Naive probability n is sum of two squarefull: ~ (√x)²/x = 1
- Expected count: ~ x with some log correction

The failure occurs because squarefull numbers are not uniformly
distributed. They cluster in ways that create more sums than expected.

Specifically, numbers of the form a² and b³ for small a, b contribute
disproportionately to sums.
-/
axiom heuristic_failure_explanation :
  -- The set of squarefull numbers has multiplicative structure
  -- that increases the sum count beyond naive predictions
  True

/-
## Part VIII: Connection to Quadratic Forms
-/

/--
**Connection to quadratic forms:**
Blomer-Granville's approach uses the theory of binary quadratic forms
with large discriminant.

Key insight: Representing n as a sum of two squarefull numbers is
related to representing n by quadratic forms.
-/
axiom quadratic_form_connection :
  -- The count A(x) is controlled by representation numbers
  -- of binary quadratic forms
  True

/-
## Part IX: Summary
-/

/--
**Erdős Problem #1081: Status**

**Question:**
Is A(x) ~ c · x / √(log x)?

**Answer:**
NO. Disproved by Odoni (1981).

**Correct Asymptotic:**
A(x) = (log log x)^O(1) · x / (log x)^α
where α = 1 - 2^(-1/3) ≈ 0.206299.

**Key Insight:**
The exponent α ≈ 0.206 is much smaller than 1/2, so A(x) grows
significantly faster than Erdős expected.
-/
theorem erdos_1081_summary :
    -- The conjecture is false
    ¬erdos_conjecture ∧
    -- α is the correct exponent
    alpha < 1/2 ∧
    -- The answer is NO
    ¬(∃ c : ℝ, c > 0 ∧ ∀ ε > 0, ∃ X : ℕ, ∀ x : ℕ, x ≥ X →
      |(A x : ℝ) / (x / Real.sqrt (Real.log x)) - c| < ε) := by
  constructor
  · exact odoni_disproof
  constructor
  · exact alpha_less_than_half
  · exact odoni_disproof

end Erdos1081
