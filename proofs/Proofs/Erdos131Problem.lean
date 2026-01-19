/-
  Erdős Problem #131: Non-Dividing Sets

  Source: https://erdosproblems.com/131
  Status: OPEN (original question resolved, but exact growth rate unknown)

  Statement:
  Let F(N) be the maximal size of A ⊆ {1, ..., N} such that no a ∈ A
  divides the sum of any distinct elements of A \ {a}. Estimate F(N).

  Original question: Is F(N) > N^{1/2 - o(1)}?
  Answer: NO (Pham-Zakharov 2024)

  Background:
  A set A is called "non-dividing" if no element divides the sum of other
  distinct elements. This property implies non-averaging (no element is the
  average of others), connecting to Problem #186.

  Known Results:
  Upper bounds:
  - ELRSS (1999): F(N) < 3√N + 1
  - Pham-Zakharov (2024): F(N) ≤ N^{1/4 + o(1)} (via non-averaging connection)

  Lower bounds:
  - Csaba: F(N) ≫ N^{1/5}
  - Straus: F(N) > exp((√(2/log 2) + o(1))√(log N))

  Erdős originally thought F(N) < (log N)^O(1) but Straus showed it grows faster.

  References:
  - [Er75b] Erdős (1975), problems in combinatorial number theory
  - [ELRSS99] Erdős, Lev, Rauzy, Sándor, Sárközy (1999)
  - [PhZa24] Pham-Zakharov (2024), non-averaging sets
  - [Gu04] Guy, Problem C16
-/

import Mathlib

namespace Erdos131

/-! ## Basic Definitions -/

/-- A set A is non-dividing if no a ∈ A divides the sum of any
    distinct elements from A \ {a}. -/
def IsNonDividing (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ S : Finset ℕ, S ⊆ A.erase a → S.card ≥ 2 →
    ¬(a ∣ S.sum id)

/-- Alternative formulation: no element divides any proper subset sum -/
def IsNonDividingAlt (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ B : Finset ℕ, B ⊆ A → a ∉ B → B.Nonempty →
    ¬(a ∣ B.sum id)

/-- The two definitions are equivalent for sets with at least 2 elements -/
theorem nondividing_equiv (A : Finset ℕ) (hA : A.card ≥ 2) :
    IsNonDividing A ↔ IsNonDividingAlt A := by
  sorry

/-- A set is non-averaging if no element is the average of distinct others -/
def IsNonAveraging (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ S : Finset ℕ, S ⊆ A.erase a → S.card ≥ 2 →
    (S.sum id : ℚ) / S.card ≠ a

/-! ## Relationship: Non-dividing implies Non-averaging -/

/-- Every non-dividing set is non-averaging -/
theorem nondividing_implies_nonaveraging (A : Finset ℕ) (hA : A.card ≥ 2)
    (hND : IsNonDividing A) : IsNonAveraging A := by
  intro a ha S hS hCard
  intro hAvg
  -- If S.sum / |S| = a, then S.sum = a * |S|, so a | S.sum
  have hdiv : a ∣ S.sum id := by
    have : (S.sum id : ℚ) = a * S.card := by
      rw [hAvg, mul_comm]
      ring
    sorry -- Extract divisibility from the rational equation
  exact hND a ha S hS hCard hdiv

/-! ## The Function F(N) -/

/-- F(N) is the maximum size of a non-dividing subset of {1, ..., N} -/
noncomputable def F (N : ℕ) : ℕ :=
  (Finset.filter (fun A => A ⊆ Finset.Icc 1 N ∧ IsNonDividing A)
    (Finset.powerset (Finset.Icc 1 N))).sup Finset.card

/-- F is monotonic in N -/
theorem F_monotonic : ∀ N M : ℕ, N ≤ M → F N ≤ F M := by
  intro N M hNM
  sorry

/-! ## Upper Bounds -/

/-- ELRSS (1999): F(N) < 3√N + 1 -/
theorem elrss_upper_bound (N : ℕ) (hN : N ≥ 1) :
    (F N : ℝ) < 3 * Real.sqrt N + 1 := by
  sorry -- Erdős, Lev, Rauzy, Sándor, Sárközy (1999)

/-- Pham-Zakharov (2024): F(N) ≤ N^{1/4 + o(1)}
    This resolves the original question negatively. -/
theorem pham_zakharov_upper_bound :
    ∃ (ε : ℕ → ℝ), (∀ δ > 0, ∃ N₀, ∀ N ≥ N₀, |ε N| < δ) ∧
    ∀ N : ℕ, N ≥ 2 → (F N : ℝ) ≤ (N : ℝ)^(1/4 + ε N) := by
  sorry -- Pham-Zakharov (2024), via non-averaging connection

/-- The original question "Is F(N) > N^{1/2 - o(1)}?" is answered NO -/
theorem original_question_answered_no :
    ¬(∀ (ε : ℕ → ℝ), (∀ δ > 0, ∃ N₀, ∀ N ≥ N₀, |ε N| < δ) →
      ∃ N₀, ∀ N ≥ N₀, (F N : ℝ) > (N : ℝ)^(1/2 - ε N)) := by
  -- Follows from Pham-Zakharov: F(N) ≤ N^{1/4+o(1)} < N^{1/2-o(1)} for large N
  sorry

/-! ## Lower Bounds -/

/-- Csaba's construction: F(N) ≫ N^{1/5} -/
theorem csaba_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ N : ℕ, N ≥ 1 → (F N : ℝ) ≥ c * (N : ℝ)^(1/5) := by
  sorry -- Csaba, credited by Erdős

/-- Straus's lower bound: F(N) > exp((√(2/log 2) + o(1))√(log N)) -/
theorem straus_lower_bound :
    ∃ (ε : ℕ → ℝ), (∀ δ > 0, ∃ N₀, ∀ N ≥ N₀, |ε N| < δ) ∧
    ∀ N : ℕ, N ≥ 2 →
      (F N : ℝ) > Real.exp ((Real.sqrt (2 / Real.log 2) + ε N) *
                            Real.sqrt (Real.log N)) := by
  sorry -- Straus

/-- The constant √(2/log 2) ≈ 1.699 -/
theorem straus_constant_value :
    Real.sqrt (2 / Real.log 2) > 1.6 ∧ Real.sqrt (2 / Real.log 2) < 1.8 := by
  sorry

/-! ## The Open Question -/

/-- Erdős Problem #131 (OPEN): What is the correct growth rate of F(N)?

    Known bounds:
    - Upper: F(N) ≤ N^{1/4 + o(1)} (Pham-Zakharov 2024)
    - Lower: F(N) ≥ exp(c√(log N)) (Straus)

    The gap between N^{1/4} and exp(√(log N)) is substantial. -/
def erdos_131_open_question : Prop :=
  ∃ (f : ℕ → ℝ),
    (∀ N, (F N : ℝ) ≤ f N) ∧
    (∀ N, (F N : ℝ) ≥ f N / 2) ∧
    -- f captures the true asymptotic growth
    True

/-- The original conjecture F(N) < (log N)^O(1) was disproved by Straus -/
theorem erdos_original_conjecture_false :
    ¬(∃ c : ℝ, c > 0 ∧ ∀ N : ℕ, N ≥ 2 → (F N : ℝ) ≤ (Real.log N)^c) := by
  -- Straus's bound shows F grows faster than any power of log N
  sorry

/-! ## Small Examples -/

/-- {1} is trivially non-dividing -/
theorem singleton_nondividing (n : ℕ) (hn : n ≥ 1) :
    IsNonDividing {n} := by
  intro a ha S hS hCard
  simp only [Finset.mem_singleton] at ha
  subst ha
  -- S ⊆ {n}.erase n = ∅, but S has ≥ 2 elements
  simp at hS
  have : S = ∅ := Finset.subset_empty.mp hS
  rw [this] at hCard
  simp at hCard

/-- {2, 3} is non-dividing: 2 ∤ 3 and 3 ∤ 2 -/
theorem two_three_nondividing : IsNonDividing {2, 3} := by
  intro a ha S hS hCard
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · -- a = 2: need to show 2 ∤ sum of subset of {3}
    -- S ⊆ {2,3}.erase 2 = {3}, but |S| ≥ 2, contradiction
    simp at hS
    sorry
  · -- a = 3: need to show 3 ∤ sum of subset of {2}
    simp at hS
    sorry

/-- Primes form a non-dividing set in their range -/
theorem primes_nondividing_example :
    ∀ N : ℕ, IsNonDividing (Finset.filter Nat.Prime (Finset.Icc 2 N)) := by
  intro N a ha S hS hCard
  simp at ha
  -- Prime a cannot divide sum of other primes (if all > a)
  sorry

/-! ## Connection to Non-Averaging Sets -/

/-- The non-averaging function g(N) from Problem #186 -/
noncomputable def g (N : ℕ) : ℕ :=
  (Finset.filter (fun A => A ⊆ Finset.Icc 1 N ∧ IsNonAveraging A)
    (Finset.powerset (Finset.Icc 1 N))).sup Finset.card

/-- F(N) ≤ g(N) since non-dividing implies non-averaging -/
theorem F_le_g (N : ℕ) : F N ≤ g N := by
  sorry

/-- Pham-Zakharov's bound on g(N) implies bound on F(N) -/
theorem pham_zakharov_chain :
    (∀ N : ℕ, N ≥ 2 → ∃ (ε : ℝ), |ε| < 0.01 ∧ (g N : ℝ) ≤ (N : ℝ)^(1/4 + ε)) →
    (∀ N : ℕ, N ≥ 2 → ∃ (ε : ℝ), |ε| < 0.01 ∧ (F N : ℝ) ≤ (N : ℝ)^(1/4 + ε)) := by
  intro hg N hN
  obtain ⟨ε, hε, hbound⟩ := hg N hN
  exact ⟨ε, hε, le_trans (Nat.cast_le.mpr (F_le_g N)) hbound⟩

/-! ## Summary

**Problem Status: OPEN (original question resolved)**

The original question "Is F(N) > N^{1/2-o(1)}?" was answered NO by Pham-Zakharov (2024),
who showed F(N) ≤ N^{1/4+o(1)}.

**Current State:**
- Upper bound: F(N) ≤ N^{1/4+o(1)}
- Lower bound: F(N) > exp(c√(log N))

The gap between polynomial (N^{1/4}) and subexponential (exp(√(log N))) growth
remains to be closed.
-/

end Erdos131
