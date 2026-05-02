/-
Erdős Problem #237: Prime Plus Set Representations

Source: https://erdosproblems.com/237
Status: SOLVED (Chen and Ding, 2022)

Statement:
Let A ⊆ ℕ be a set such that |A ∩ {1,...,N}| ≫ log(N) for all large N.
Let f(n) count the number of solutions to n = p + a for p prime and a ∈ A.
Is it true that limsup f(n) = ∞?

Answer: YES

Historical Context:
- Erdős (1950): Proved this when A = {2^k : k ≥ 0} (powers of 2)
- Chen and Ding (2022): Proved the general result
- Strengthening: Even the weaker assumption that A is infinite suffices!

The problem asks whether dense enough sets A force infinitely many n
with unboundedly many prime representations n = p + a.

Related: Erdős Problem #236

Tags: number-theory, primes, additive-combinatorics, representations
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Instances.Real

namespace Erdos237

/-
## Part I: Basic Definitions
-/

/--
**Representation Count:**
f(n) = number of ways to write n = p + a where p is prime and a ∈ A.
-/
noncomputable def representationCount (A : Set ℕ) (n : ℕ) : ℕ :=
  Nat.card {pa : ℕ × ℕ | pa.1.Prime ∧ pa.2 ∈ A ∧ pa.1 + pa.2 = n}

/--
**Logarithmic Lower Density:**
A set A has logarithmic lower density if |A ∩ [1,N]| ≥ c·log(N) for large N.
-/
def HasLogDensity (A : Set ℕ) : Prop :=
  ∃ (c : ℝ) (N₀ : ℕ), c > 0 ∧ ∀ N ≥ N₀,
    (Nat.card (A ∩ Set.Icc 1 N) : ℝ) ≥ c * Real.log N

/--
**Unbounded Limsup:**
The limsup of f(n) is infinite.
-/
def HasUnboundedLimsup (f : ℕ → ℕ) : Prop :=
  ∀ M : ℕ, ∃ n : ℕ, f n > M

/-
## Part II: The Main Conjecture and Result
-/

/--
**Erdős's Conjecture (1950s):**
If A has logarithmic density, then the representation count f(n)
has unbounded limsup.
-/
def ErdosConjecture : Prop :=
  ∀ A : Set ℕ, HasLogDensity A →
    HasUnboundedLimsup (representationCount A)

/--
**Stronger Version:**
Chen and Ding proved an even stronger result: any infinite set A
satisfies the conclusion.
-/
def StrongerVersion : Prop :=
  ∀ A : Set ℕ, Set.Infinite A →
    HasUnboundedLimsup (representationCount A)

/-
## Part III: Historical Results
-/

/--
**Powers of Two:**
The set A = {2^k : k ≥ 0}.
-/
def powersOfTwo : Set ℕ := {n | ∃ k : ℕ, n = 2^k}

/-
**Erdős (1950):**
The powers of two satisfy the conjecture.
-/
/-
**Powers of Two Have Logarithmic Density:**
|{2^k : k ≤ N}| = ⌊log₂(N)⌋ + 1 ~ log(N).
-/
/-
**Arithmetic Progressions:**
Sets containing long arithmetic progressions tend to have
many prime representations due to Goldbach-like phenomena.
-/
/-
## Part IV: Chen and Ding's Theorem
-/

/--
**Chen and Ding (2022):**
Every infinite set A satisfies limsup f(n) = ∞.

This is much stronger than Erdős's original question, which only
asked about sets with logarithmic density.
-/
axiom chen_ding_2022 : StrongerVersion

/--
**Corollary: Original Conjecture is True**
Since any infinite set works, sets with logarithmic density certainly work.
-/
theorem erdos_conjecture_true : ErdosConjecture := by
  intro A hA
  -- A set with logarithmic density is infinite
  have hInf : Set.Infinite A := by
    obtain ⟨c, N₀, hc, hDense⟩ := hA
    by_contra hFin
    have hFA : A.Finite := Set.not_infinite.mp hFin
    obtain ⟨k, hk⟩ := hFA.bddAbove
    -- For N ≥ k: A ∩ [1,N] = A ∩ [1,k] since A ⊆ Iic k
    have heq : ∀ N, N ≥ k → A ∩ Set.Icc 1 N = A ∩ Set.Icc 1 k := by
      intro N hN; ext x
      simp only [Set.mem_inter_iff, Set.mem_Icc]
      exact ⟨fun ⟨hA, h1, _⟩ => ⟨hA, h1, hk hA⟩,
             fun ⟨hA, h1, hk'⟩ => ⟨hA, h1, hk'.trans hN⟩⟩
    -- Nat.card is constant C for N ≥ k
    set C := Nat.card ↥(A ∩ Set.Icc 1 k)
    -- Pick N large enough that c * log N > C
    obtain ⟨N, hN⟩ := exists_nat_gt (max ↑(max N₀ k) (Real.exp ((↑C + 1) / c)))
    have hN_max : max N₀ k < N := by
      exact_mod_cast lt_of_le_of_lt (le_max_left (↑(max N₀ k) : ℝ) _) hN
    have hN_N0 : N ≥ N₀ := le_of_lt (lt_of_le_of_lt (le_max_left N₀ k) hN_max)
    have hN_k : N ≥ k := le_of_lt (lt_of_le_of_lt (le_max_right N₀ k) hN_max)
    -- Nat.card (A ∩ [1,N]) = C since A ∩ [1,N] = A ∩ [1,k]
    have hcard : Nat.card ↥(A ∩ Set.Icc 1 N) = C := by rw [heq N hN_k]
    -- c * log N > C (since N > exp((C+1)/c))
    have hlog : c * Real.log ↑N > ↑C := by
      have hN_exp : (↑N : ℝ) > Real.exp ((↑C + 1) / c) :=
        lt_of_le_of_lt (le_max_right _ _) hN
      have h := Real.log_lt_log (Real.exp_pos _) hN_exp
      rw [Real.log_exp] at h
      rw [div_lt_iff hc] at h
      linarith [mul_comm (Real.log ↑N) c]
    -- hDense says (C : ℝ) ≥ c * log N, but c * log N > C. Contradiction.
    have hdens := hDense N hN_N0
    rw [hcard] at hdens
    linarith
  exact chen_ding_2022 A hInf

/-
## Part V: Understanding the Proof Strategy
-/

/-
**Why Infinite Sets Suffice:**
The key insight is that as n → ∞, the number of primes p < n
grows like n/log(n) by the Prime Number Theorem. If A is infinite,
eventually many elements of A will have prime complements.
-/

/-
**Prime Number Theorem Connection:**
π(n) ~ n/log(n) means primes are plentiful enough that
infinite sets A will intersect {n - p : p prime} infinitely often.
-/

/-
**Density vs Cardinality:**
Erdős asked about logarithmic density, but Chen-Ding showed
that even much sparser sets (just infinite) work.
-/

/-
## Part VI: Examples and Special Cases
-/

/--
**Squares:**
A = {n² : n ≥ 1} is infinite, so limsup f(n) = ∞.
-/
def squares : Set ℕ := {n | ∃ k : ℕ, k ≥ 1 ∧ n = k^2}

/--
**Prime Powers:**
A = {p^k : p prime, k ≥ 1} is infinite.
-/
def primePowers : Set ℕ := {n | ∃ (p k : ℕ), p.Prime ∧ k ≥ 1 ∧ n = p^k}

/-
**Highly Composite Numbers:**
Even very sparse sequences like highly composite numbers
satisfy the theorem.
-/

/-
## Part VII: Relation to Goldbach-type Problems
-/

/-
**Goldbach Connection:**
This problem is related to Goldbach's conjecture.
If A = {2}, then f(n) counts primes p with n - 2 = p,
i.e., twin primes shifted by 2.
-/

/-
**Binary Additive Problems:**
Problems of the form n = p + a for structured sets A
are central to additive number theory.
-/

/-
## Part VIII: Main Results
-/

/--
**Erdős Problem #237: SOLVED**

**Question:** If A ⊆ ℕ has |A ∩ [1,N]| ≫ log(N), is limsup f(n) = ∞
where f(n) counts solutions to n = p + a?

**Answer:** YES (Chen and Ding, 2022)

**Stronger Result:** Even just A being infinite suffices!

**History:**
- Erdős (1950): Proved for A = {2^k}
- Chen and Ding (2022): Proved for all infinite A
-/
theorem erdos_237 : ErdosConjecture := erdos_conjecture_true

/--
**Summary:**
Erdős Problem #237 asked about prime representations n = p + a
for sets A with logarithmic density. Chen and Ding (2022) proved
an even stronger result: any infinite set A has unbounded f(n).
-/
theorem erdos_237_summary :
    -- The original conjecture is true
    ErdosConjecture ∧
    -- The stronger version is also true
    StrongerVersion := by
  exact ⟨erdos_conjecture_true, chen_ding_2022⟩

end Erdos237
