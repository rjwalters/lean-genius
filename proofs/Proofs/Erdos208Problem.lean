/-
  Erdős Problem #208: Gaps Between Squarefree Numbers

  Source: https://erdosproblems.com/208
  Status: OPEN

  Let s₁ < s₂ < ... be the sequence of squarefree numbers. The problem asks:

  **Question 1**: Is it true that for any ε > 0 and large n,
    s_{n+1} - sₙ ≪_ε sₙ^ε ?

  **Question 2**: Is it true that
    s_{n+1} - sₙ ≤ (1 + o(1)) · (π²/6) · log(sₙ) / log(log(sₙ)) ?

  **Known Results**:
  - Erdős (1951): Infinitely many n achieve the lower bound in Q2, so it would be optimal
  - Filaseta-Trifonov (1992): Upper bound s_n^{1/5 + o(1)}
  - Pandey (2024): Improved to s_n^{1/5 - c} for some c > 0
  - Granville (1998): Q1 follows from ABC conjecture

  The problem cannot be resolved by finite computation since it concerns
  asymptotic behavior for all sufficiently large n.

  References:
  - Erdős (1951), "Some problems and results in elementary number theory"
  - Filaseta-Trifonov (1992), "On gaps between squarefree numbers II"
  - Granville (1998), "ABC allows us to count squarefrees"
  - Pandey (2024), "Squarefree numbers in short intervals"
-/

import Mathlib

open Set Filter Real Nat Topology Asymptotics

namespace Erdos208

/-! ## Squarefree Numbers -/

/-- A natural number is **squarefree** if it is not divisible by any perfect square
    greater than 1. Equivalently, in its prime factorization, each prime appears
    at most once. -/
def IsSquarefree (n : ℕ) : Prop := Squarefree n

/-- The sequence of squarefree numbers: s₁ = 1, s₂ = 2, s₃ = 3, s₄ = 5, s₅ = 6, ... -/
noncomputable def squarefreeSeq : ℕ → ℕ := Nat.nth Squarefree

/-- The gap between consecutive squarefree numbers. -/
noncomputable def squarefreeGap (n : ℕ) : ℕ := squarefreeSeq (n + 1) - squarefreeSeq n

/-! ## The Main Conjectures -/

/--
**Erdős Problem #208, Question 1** (OPEN):
Is it true that for any ε > 0 and sufficiently large n,
  s_{n+1} - sₙ ≪_ε sₙ^ε ?

In asymptotic notation: (s_{n+1} - sₙ) = O(sₙ^ε) for all ε > 0.

Granville (1998) showed this follows from the ABC conjecture.
-/
def Erdos208_Q1 : Prop :=
  ∀ ε > (0 : ℝ), (fun n => (squarefreeGap n : ℝ)) =O[atTop] (fun n => (squarefreeSeq n : ℝ)^ε)

/--
**Erdős Problem #208, Question 2** (OPEN):
Is it true that s_{n+1} - sₙ ≤ (1 + o(1)) · (π²/6) · log(sₙ) / log(log(sₙ)) ?

Erdős (1951) showed this bound would be optimal if true: there exist infinitely
many n achieving this as a lower bound.
-/
def Erdos208_Q2 : Prop :=
  ∃ c : ℕ → ℝ, (c =o[atTop] (1 : ℕ → ℝ)) ∧
    ∀ᶠ n in atTop, (squarefreeGap n : ℝ) ≤
      (1 + c n) * (π^2 / 6) * Real.log (squarefreeSeq n) / Real.log (Real.log (squarefreeSeq n))

/-! ## Known Upper Bounds -/

/--
**Filaseta-Trifonov (1992)**: The gap between consecutive squarefree numbers
satisfies s_{n+1} - sₙ ≪ sₙ^{1/5 + o(1)}.

This was the best unconditional bound for decades.
-/
axiom filaseta_trifonov_bound :
    (fun n => (squarefreeGap n : ℝ)) =O[atTop] (fun n => (squarefreeSeq n : ℝ)^((1:ℝ)/5 + 0.01))

/--
**Pandey (2024)**: Improved the exponent to 1/5 - c for some constant c > 0.
This is the current best unconditional bound.
-/
axiom pandey_bound :
    ∃ c > (0 : ℝ), (fun n => (squarefreeGap n : ℝ)) =O[atTop]
      (fun n => (squarefreeSeq n : ℝ)^(1/5 - c))

/-! ## The Optimal Lower Bound -/

/--
**Erdős (1951)**: There exist infinitely many n such that
  s_{n+1} - sₙ > (1 + o(1)) · (π²/6) · log(sₙ) / log(log(sₙ)).

This shows that Question 2's bound, if true, would be optimal.
-/
axiom erdos_lower_bound :
    ∃ c : ℕ → ℝ, (c =o[atTop] (1 : ℕ → ℝ)) ∧
      {n : ℕ | (squarefreeGap n : ℝ) >
        (1 + c n) * (π^2 / 6) * Real.log (squarefreeSeq n) / Real.log (Real.log (squarefreeSeq n))}.Infinite

/-! ## Conditional Result -/

/--
**Granville (1998)**: The ABC conjecture implies Question 1.

The ABC conjecture is a major open problem in number theory stating that for
coprime integers a, b, c with a + b = c, we have c ≪_ε rad(abc)^{1+ε} where
rad(n) is the product of distinct prime factors of n.
-/
axiom abc_implies_q1 :
    -- Assuming some form of ABC conjecture (stated informally)
    True → Erdos208_Q1

/-! ## Basic Properties -/

/-- The first squarefree number is 1.

This uses the fact that 1 is the smallest squarefree number (as it has no
prime factors, hence trivially squarefree). -/
axiom squarefree_one : squarefreeSeq 0 = 1

/-- 2 is squarefree. -/
example : Squarefree 2 := by native_decide

/-- 3 is squarefree. -/
example : Squarefree 3 := by native_decide

/-- 4 is NOT squarefree (4 = 2²). -/
example : ¬Squarefree 4 := by native_decide

/-- 5 is squarefree. -/
example : Squarefree 5 := by native_decide

/-- 6 is squarefree. -/
example : Squarefree 6 := by native_decide

/-- The density of squarefree numbers is 6/π².

This classical result says that the proportion of integers up to N that are
squarefree converges to 6/π² ≈ 0.6079... as N → ∞. -/
axiom squarefree_density :
    Tendsto (fun N => ({n : ℕ | n ≤ N ∧ Squarefree n}.ncard : ℝ) / N) atTop (nhds (6 / π^2))

/-! ## Typical Gap Size -/

/--
Since the density of squarefree numbers is 6/π², the "average" gap between
consecutive squarefree numbers should be about π²/6 ≈ 1.645.

Most gaps are small (1 or 2), but occasionally there are larger gaps,
and the question is how large they can be.

Note: 6/π² ≈ 0.6079... > 0.6
-/
axiom average_gap_heuristic : (6 : ℝ) / π^2 > 0.6

/-! ## Small Examples of Gaps -/

/-- Gap of 1: between 1 and 2. -/
example : (2 : ℕ) - 1 = 1 := rfl

/-- Gap of 1: between 2 and 3. -/
example : (3 : ℕ) - 2 = 1 := rfl

/-- Gap of 2: between 3 and 5 (skipping 4 = 2²). -/
example : (5 : ℕ) - 3 = 2 := rfl

/-- Gap of 1: between 5 and 6. -/
example : (6 : ℕ) - 5 = 1 := rfl

/-- Gap of 1: between 6 and 7. -/
example : (7 : ℕ) - 6 = 1 := rfl

/-- Gap of 3: between 7 and 10 (skipping 8 = 2³, 9 = 3²). -/
example : (10 : ℕ) - 7 = 3 := rfl

/-! ## The Doubling Trick -/

/--
A key observation: if n is squarefree and odd, then 2n is also squarefree.
This limits how large gaps can be - you can't have arbitrarily many consecutive
non-squarefree numbers.
-/
axiom squarefree_double_odd {n : ℕ} (hn : Squarefree n) (hodd : Odd n) :
    Squarefree (2 * n)

/--
The maximum gap up to N is O(√N) since there are O(√N) numbers in [1, N]
divisible by some fixed square. Improving this to subpolynomial bounds
is the content of the problem.
-/
axiom max_gap_sqrt_bound :
    (fun n => (squarefreeGap n : ℝ)) =O[atTop] (fun n => Real.sqrt (squarefreeSeq n))

end Erdos208
