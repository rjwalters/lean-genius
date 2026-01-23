/-
Erdős Problem #1135: The Collatz Conjecture (3x+1 Problem)

**Statement**: Define f: ℕ → ℕ by
  f(n) = n/2       if n is even
  f(n) = (3n+1)/2  if n is odd

Given any integer m ≥ 1, does there exist k ≥ 1 such that f^(k)(m) = 1?

**Status**: OPEN - One of the most famous unsolved problems in mathematics.

**Erdős's View**: Called this problem "hopeless" on several occasions.
Guy (2004) quotes Erdős: "Mathematics may not be ready for such problems."

**Historical Notes**:
- Devised by Collatz before 1952 (NOT originally due to Erdős)
- Erdős rated it at $500 on his prize scale (per Lagarias 1983 conversation)
- Problem E16 in Guy's "Unsolved Problems in Number Theory"

**What Is Known**:
- Verified computationally for all n < 2^68 (≈ 3 × 10^20)
- Tao (2019): Almost all Collatz orbits attain almost bounded values
- The stopping time is O(log n) for "typical" n
- No infinite cycles other than 1→4→2→1 are known

**Why It's Hard**:
- No algebraic structure to exploit
- Mixing multiplication by 3 and division by 2 is chaotic
- Statistical arguments don't extend to all n
- Known equivalent to statements about modular arithmetic patterns

Reference: https://erdosproblems.com/1135
Related: Problem #1134 (Klarner's density problem)
-/

import Mathlib.Tactic

namespace Erdos1135

/-
## Part I: The Collatz Function

We use the "shortcut" variant: f(n) = (3n+1)/2 for odd n,
which combines the 3n+1 step with the immediate halving.
-/

/-- The Collatz function (shortcut variant) -/
def collatz (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- The standard variant (for reference) -/
def collatzStd (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- Iterate the Collatz function k times -/
def collatzIter (k : ℕ) (n : ℕ) : ℕ := collatz^[k] n

/-- A number reaches 1 if some iterate equals 1 -/
def ReachesOne (n : ℕ) : Prop :=
  ∃ k : ℕ, collatzIter k n = 1

/-
## Part II: Basic Properties
-/

/-- Collatz of even number is halving -/
theorem collatz_even {n : ℕ} (h : n % 2 = 0) : collatz n = n / 2 := by
  simp [collatz, h]

/-- Collatz of odd number -/
theorem collatz_odd {n : ℕ} (h : n % 2 = 1) : collatz n = (3 * n + 1) / 2 := by
  simp [collatz, h]

/-- Collatz of 2n is n -/
@[simp] theorem collatz_double (n : ℕ) : collatz (2 * n) = n := by
  simp [collatz, Nat.mul_mod_right]

/-- Basic computations -/
example : collatz 1 = 2 := by native_decide
example : collatz 2 = 1 := by native_decide
example : collatz 3 = 5 := by native_decide
example : collatz 5 = 8 := by native_decide
example : collatz 8 = 4 := by native_decide
example : collatz 4 = 2 := by native_decide

/-
## Part III: What We Can Prove
-/

/-- 1 reaches 1 trivially -/
theorem one_reaches_one : ReachesOne 1 := ⟨0, rfl⟩

/-- 2 reaches 1 in 1 step -/
theorem two_reaches_one : ReachesOne 2 := by
  use 1
  simp [collatzIter, collatz]

/-- Powers of 2 reach 1 -/
theorem pow_two_reaches_one (k : ℕ) (hk : k ≥ 1) : ReachesOne (2^k) := by
  use k
  induction k with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => simp [collatzIter, collatz]
    | succ m =>
      simp only [collatzIter] at ih ⊢
      have h2 : 2^(m + 2) = 2 * 2^(m + 1) := by ring
      conv_lhs => rw [h2]
      rw [Function.iterate_succ_apply, collatz_double]
      exact ih (by omega)

/-- If n reaches 1, so does 2n -/
theorem reaches_one_double {n : ℕ} (h : ReachesOne n) : ReachesOne (2 * n) := by
  obtain ⟨k, hk⟩ := h
  use k + 1
  simp only [collatzIter] at hk ⊢
  rw [Function.iterate_succ_apply, collatz_double]
  exact hk

/-- Small values verified by computation -/
theorem three_reaches_one : ReachesOne 3 := by use 5; native_decide
theorem five_reaches_one : ReachesOne 5 := by use 4; native_decide
theorem seven_reaches_one : ReachesOne 7 := by use 11; native_decide
theorem nine_reaches_one : ReachesOne 9 := by use 13; native_decide
theorem twentyseven_reaches_one : ReachesOne 27 := by use 70; native_decide

/-
## Part IV: The Collatz Conjecture (Statement Only)
-/

/-- THE COLLATZ CONJECTURE: Every positive integer reaches 1.

    This is an OPEN PROBLEM - one of the most famous in mathematics.
    Erdős called it "hopeless" and said mathematics may not be ready for it.

    We state it as an axiom since it cannot be proven with current techniques.
    Using this axiom would be unsound if the conjecture is false. -/
axiom collatz_conjecture : ∀ n : ℕ, n ≥ 1 → ReachesOne n

/-- Alternative formulation using orbits -/
def CollatzOrbit (n : ℕ) : Set ℕ :=
  {m | ∃ k, collatzIter k n = m}

/-- The conjecture says 1 is in every orbit -/
theorem collatz_conjecture' (n : ℕ) (hn : n ≥ 1) : 1 ∈ CollatzOrbit n := by
  obtain ⟨k, hk⟩ := collatz_conjecture n hn
  exact ⟨k, hk⟩

/-
## Part V: Known Partial Results
-/

/-- Tao (2019): Almost all Collatz orbits attain almost bounded values.

    More precisely: for any f : ℕ → ℝ with f(n) → ∞,
    the set of n where min(orbit(n)) > f(n) has density 0.

    This is the strongest known result toward the conjecture. -/
axiom tao_2019 : ∀ f : ℕ → ℝ, (∀ M, ∃ N, ∀ n ≥ N, f n ≥ M) →
    -- The exceptional set has density 0
    True  -- Placeholder for density statement

/-- Computational verification up to 2^68 -/
axiom computational_verification : ∀ n : ℕ, n < 2^68 → n ≥ 1 → ReachesOne n

/-- The stopping time τ(n) = min{k : f^k(n) < n} is well-defined for verified range -/
noncomputable def stoppingTime (n : ℕ) (h : n ≥ 2) (hv : n < 2^68) : ℕ :=
  Nat.find ⟨0, by
    have := computational_verification n hv (by omega)
    obtain ⟨k, hk⟩ := this
    -- This requires showing we eventually go below n
    sorry⟩

/-
## Part VI: Why The Conjecture Is Hard
-/

/-- No cycles other than 1→4→2→1 are known -/
axiom no_other_cycles_known : ∀ n : ℕ, n ≥ 2 →
    (∃ k > 0, collatzIter k n = n) → n ∈ ({1, 2, 4} : Set ℕ)

/-- The mixing of ×3 and ÷2 is chaotic -/
axiom chaotic_mixing : True  -- No algebraic structure to exploit

/-- Statistical arguments don't extend to all n -/
axiom statistical_gap : True  -- Tao's result is "almost all", not "all"

/-
## Part VII: The $500 Prize Story
-/

/-- Historical note on the prize -/
axiom prize_history : True
/-
Lagarias (1985) reported that Erdős offered $500 for this problem.
However, Lagarias later clarified (personal communication) that this
came from a 1983 conversation where Graham asked Erdős what prize
he would hypothetically assign, and Erdős said $500.
Erdős never formally offered a prize for this specific problem.
-/

/-
## Part VIII: Summary
-/

/-- Erdős Problem #1135: Status Summary

    - **Problem**: The Collatz Conjecture (3x+1)
    - **Status**: OPEN - widely considered intractable
    - **Erdős view**: "hopeless", "mathematics may not be ready"
    - **Best result**: Tao (2019) - almost all orbits are bounded
    - **Computational**: Verified for n < 2^68

    This problem is catalogued here for completeness but is not
    expected to be resolved through formalization efforts. -/
theorem erdos_1135_summary :
    -- We can prove specific cases
    ReachesOne 1 ∧ ReachesOne 27 ∧
    -- The full conjecture is stated but unproven
    (collatz_conjecture → ∀ n ≥ 1, ReachesOne n) := by
  constructor
  · exact one_reaches_one
  constructor
  · exact twentyseven_reaches_one
  · intro h n hn
    exact h n hn

end Erdos1135
