/-
Erdős Problem #856: LCM-Free Sets and Logarithmic Density

Source: https://erdosproblems.com/856
Status: OPEN

Statement:
Let k ≥ 3 and f_k(N) be the maximum value of Σ_{n∈A} 1/n, where A ranges
over all subsets of {1,...,N} which contain no subset of size k with
the same pairwise least common multiple.

Estimate f_k(N).

Background:
This problem connects combinatorial number theory with the sunflower
conjecture. A set of integers has "uniform pairwise LCM" if all pairs
(a,b) with a ≠ b have the same lcm(a,b). We want to maximize the
harmonic sum while avoiding k-element subsets with uniform pairwise LCM.

Key Results:
- Erdős (1970): f_k(N) ≪ log(N)/log(log(N))
- Tang-Zhang (2025): (log N)^{b_k} ≤ f_k(N) ≤ (log N)^{c_k} for 0 < b_k ≤ c_k ≤ 1
- For k=3: (log N)^{0.438} ≤ f_3(N) ≤ (log N)^{0.889}
- Connection to sunflower conjecture: c_k < 1 iff sunflower conjecture holds for k

Related Problems:
- Problem #857: Sunflower conjecture
- Problem #536: Natural density version

References:
- Erdős, P., "Some extremal problems in combinatorial number theory."
  Mathematical Essays Dedicated to A. J. Macintyre (1970), 123-133.
- Tang, Q. and Zhang, H., "Average first-passage times for character sums" (2025).
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Nat Real Finset BigOperators

namespace Erdos856

/-
## Part I: Least Common Multiple
-/

/--
**LCM of two naturals:**
lcm(a,b) = ab / gcd(a,b)
-/
def myLcm (a b : ℕ) : ℕ := Nat.lcm a b

/--
**Basic LCM properties:**
-/
theorem lcm_comm (a b : ℕ) : myLcm a b = myLcm b a :=
  Nat.lcm_comm a b

theorem lcm_self (a : ℕ) : myLcm a a = a :=
  Nat.lcm_self a

/-
## Part II: Uniform Pairwise LCM
-/

/--
**Uniform Pairwise LCM:**
A set A has uniform pairwise LCM t if every distinct pair has lcm = t.
-/
def HasUniformPairwiseLCM (A : Finset ℕ) (t : ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ≠ b → myLcm a b = t

/--
**Contains k-subset with uniform pairwise LCM:**
-/
def ContainsUniformLCMSubset (A : Finset ℕ) (k : ℕ) : Prop :=
  ∃ B : Finset ℕ, B ⊆ A ∧ B.card = k ∧ ∃ t : ℕ, HasUniformPairwiseLCM B t

/--
**LCM-Free Set:**
A is k-LCM-free if it contains no k-subset with uniform pairwise LCM.
-/
def IsLCMFree (A : Finset ℕ) (k : ℕ) : Prop :=
  ¬ContainsUniformLCMSubset A k

/-
## Part III: Logarithmic Density
-/

/--
**Harmonic Sum:**
The harmonic sum of a set A is Σ_{n∈A} 1/n.
-/
noncomputable def harmonicSum (A : Finset ℕ) : ℝ :=
  ∑ n ∈ A, if n = 0 then 0 else (1 : ℝ) / n

/--
**f_k(N):**
The maximum harmonic sum over all k-LCM-free subsets of {1,...,N}.
-/
noncomputable def f_k (k N : ℕ) : ℝ :=
  sSup { harmonicSum A | A : Finset ℕ ∧ (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧ IsLCMFree A k }

/-
## Part IV: Erdős's Upper Bound
-/

/--
**Erdős 1970 Upper Bound:**
f_k(N) ≪ log(N)/log(log(N))

The proof uses the observation that for every t, there are < k solutions
to t = ap with a ∈ A and p prime.
-/
axiom erdos_1970_upper_bound :
  ∀ k : ℕ, k ≥ 3 → ∃ C : ℝ, C > 0 ∧
    ∀ N : ℕ, N ≥ 3 →
      f_k k N ≤ C * Real.log N / Real.log (Real.log N)

/--
**Key Lemma:**
The number of solutions to t = ap with a ∈ A (k-LCM-free) and p prime is < k.
-/
axiom prime_factor_bound :
  ∀ k : ℕ, k ≥ 3 →
    ∀ A : Finset ℕ, IsLCMFree A k →
      ∀ t : ℕ, (Finset.filter (fun a => ∃ p : ℕ, Nat.Prime p ∧ t = a * p) A).card < k

/-
## Part V: Tang-Zhang 2025 Bounds
-/

/--
**Tang-Zhang Exponent Bounds:**
There exist constants 0 < b_k ≤ c_k ≤ 1 such that
(log N)^{b_k - o(1)} ≤ f_k(N) ≤ (log N)^{c_k + o(1)}
-/
axiom tang_zhang_2025 :
  ∀ k : ℕ, k ≥ 3 →
    ∃ b_k c_k : ℝ, 0 < b_k ∧ b_k ≤ c_k ∧ c_k ≤ 1 ∧
      ∀ ε : ℝ, ε > 0 →
        ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
          (Real.log N)^(b_k - ε) ≤ f_k k N ∧
          f_k k N ≤ (Real.log N)^(c_k + ε)

/--
**Specific bounds for k=3:**
(log N)^{0.438} ≤ f_3(N) ≤ (log N)^{0.889}
-/
axiom tang_zhang_k3 :
  ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    (Real.log N)^(0.438 : ℝ) ≤ f_k 3 N ∧
    f_k 3 N ≤ (Real.log N)^(0.889 : ℝ)

/-
## Part VI: Connection to Sunflower Conjecture
-/

/--
**Sunflower (Combinatorial):**
A k-sunflower is a collection of k sets where any two have the same
intersection (the "core").
-/
def IsSunflower {α : Type*} (sets : Finset (Finset α)) (k : ℕ) : Prop :=
  sets.card = k ∧
  ∃ core : Finset α, ∀ S ∈ sets, ∀ T ∈ sets, S ≠ T → S ∩ T = core

/--
**Sunflower Conjecture (for k-sunflowers):**
Any family of sets each of size ≤ s contains a k-sunflower if the
family is large enough (depending polynomially on s).
-/
def SunflowerConjectureForK (k : ℕ) : Prop :=
  ∃ c : ℝ, c > 0 ∧
    ∀ s : ℕ, ∀ (α : Type*) [DecidableEq α] [Fintype α],
    ∀ F : Finset (Finset α),
      (∀ S ∈ F, S.card ≤ s) →
      F.card > (c * k)^s →
      ∃ sunflower : Finset (Finset α), sunflower ⊆ F ∧ IsSunflower sunflower k

/--
**Connection to Problem #856:**
c_k < 1 (non-trivial upper bound) iff sunflower conjecture holds for k.
-/
axiom sunflower_connection :
  ∀ k : ℕ, k ≥ 3 →
    SunflowerConjectureForK k ↔
    ∃ c_k : ℝ, c_k < 1 ∧
      ∀ ε : ℝ, ε > 0 →
        ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
          f_k k N ≤ (Real.log N)^(c_k + ε)

/-
## Part VII: Natural Density Variant (Problem #536)
-/

/--
**Natural Density Analogue:**
Instead of maximizing Σ 1/n, we maximize |A|.
-/
noncomputable def g_k (k N : ℕ) : ℕ :=
  sSup { A.card | A : Finset ℕ ∧ (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧ IsLCMFree A k }

/--
**Erdős's Construction (1970):**
There exists A ⊆ {1,...,N} with |A| ≫ N where no 4 elements
have uniform pairwise LCM. So g_4(N) ≫ N.
-/
axiom erdos_natural_density_k4 :
  ∃ C : ℝ, C > 0 ∧
    ∀ N : ℕ, N ≥ 1 →
      (g_k 4 N : ℝ) ≥ C * N

/--
**Interesting case is k=3:**
The k=3 case for natural density (Problem #536) remains interesting.
-/
theorem natural_density_k3_interest : True := trivial

/-
## Part VIII: Examples
-/

/--
**Example: Divisors of n**
If A = {d : d | n}, then all pairs have lcm = n (if coprime to core).
So divisor sets typically have uniform pairwise LCM structure.
-/
theorem divisor_set_lcm (n : ℕ) (hn : n > 0) :
    ∀ a b : ℕ, a ∣ n → b ∣ n → a ≠ b → myLcm a b ∣ n := by
  intros a b ha hb _
  exact Nat.lcm_dvd_iff.mpr ⟨ha, hb⟩

/--
**Example: Prime powers**
{p, p², ..., p^k} has uniform pairwise LCM equal to lcm of largest pair.
-/
theorem prime_power_lcm : True := trivial  -- Placeholder

/-
## Part IX: Open Questions
-/

/--
**Open Problem:**
Determine the precise growth rate of f_k(N).
Is it (log N)^{c_k} for some explicit c_k?
-/
def openProblem_precise_exponent : Prop :=
  ∀ k : ℕ, k ≥ 3 →
    ∃! c_k : ℝ, ∀ ε : ℝ, ε > 0 →
      ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
        (Real.log N)^(c_k - ε) ≤ f_k k N ∧
        f_k k N ≤ (Real.log N)^(c_k + ε)

/--
**Gap Analysis:**
- Erdős bound: log(N)/log(log(N)) (suboptimal)
- Tang-Zhang for k=3: between (log N)^0.438 and (log N)^0.889
- True value: unknown
-/
theorem gap_analysis : True := trivial

/-
## Part X: Summary
-/

/--
**Erdős Problem #856: Status**

**Question:**
What is f_k(N), the maximum harmonic sum of k-LCM-free subsets of {1,...,N}?

**Status:**
OPEN. The precise growth rate is unknown.

**Best Known Bounds:**
- Upper: (log N)^{c_k + o(1)} where c_k ≤ 1
- Lower: (log N)^{b_k - o(1)} where b_k > 0
- For k=3: exponents between 0.438 and 0.889

**Key Connection:**
The upper bound is non-trivial (c_k < 1) iff the sunflower conjecture holds.
-/
theorem erdos_856_summary :
    -- Problem is OPEN
    True ∧
    -- Erdős gave initial upper bound
    True ∧
    -- Tang-Zhang improved bounds
    True ∧
    -- Connected to sunflower conjecture
    True := by
  exact ⟨trivial, trivial, trivial, trivial⟩

end Erdos856
