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

open scoped Classical

/- ## Basic Definitions -/

/-- A set A is non-dividing if no a ∈ A divides the sum of any
    distinct elements from A \ {a}. -/
def IsNonDividing (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ S : Finset ℕ, S ⊆ A.erase a → S.card ≥ 2 →
    ¬(a ∣ S.sum id)

/-- Alternative formulation: no element divides any proper subset sum -/
def IsNonDividingAlt (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ B : Finset ℕ, B ⊆ A → a ∉ B → B.Nonempty →
    ¬(a ∣ B.sum id)

/-- IsNonDividingAlt is strictly stronger than IsNonDividing:
    Alt requires no element divides ANY nonempty subset sum (including singletons),
    while the standard version only forbids divisibility of sums of ≥ 2 elements.
    Counterexample for the converse: {2, 4} satisfies IsNonDividing (vacuously,
    since no S ⊆ {4} or S ⊆ {2} has card ≥ 2) but NOT IsNonDividingAlt
    (since 2 ∈ {2,4}, B = {4}, and 2 ∣ 4). -/
theorem nondividingAlt_implies_nondividing (A : Finset ℕ) :
    IsNonDividingAlt A → IsNonDividing A := by
  intro hAlt a ha S hS hCard hdvd
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  have ha_notin : a ∉ S := fun h => (Finset.mem_erase.mp (hS h)).1 rfl
  have hSA : S ⊆ A := hS.trans (Finset.erase_subset a A)
  exact hAlt a ha S hSA ha_notin hne hdvd

/-- Counterexample: {2, 4} is non-dividing (vacuously) but not non-dividing-alt -/
theorem nondividing_not_iff_alt :
    ∃ A : Finset ℕ, A.card ≥ 2 ∧ IsNonDividing A ∧ ¬IsNonDividingAlt A := by
  refine ⟨{2, 4}, by simp, ?_, ?_⟩
  · -- {2,4} is non-dividing: erase sets have card ≤ 1
    intro a ha S hS hCard
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · have : S.card ≤ (({2, 4} : Finset ℕ).erase 2).card := Finset.card_le_card hS
      simp at this; omega
    · have : S.card ≤ (({2, 4} : Finset ℕ).erase 4).card := Finset.card_le_card hS
      simp at this; omega
  · -- {2,4} is NOT non-dividing-alt: a=2, B={4}, 2 ∣ 4
    intro h
    apply h 2 (by simp) {4} (by simp) (by simp) (by simp)
    simp [Finset.sum_singleton]

/-- A set is non-averaging if no element is the average of distinct others -/
def IsNonAveraging (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ S : Finset ℕ, S ⊆ A.erase a → S.card ≥ 2 →
    ↑(S.sum id) / (S.card : ℚ) ≠ (a : ℚ)

/- ## Relationship: Non-dividing implies Non-averaging -/

/-- Every non-dividing set is non-averaging -/
theorem nondividing_implies_nonaveraging (A : Finset ℕ) (_hA : A.card ≥ 2)
    (hND : IsNonDividing A) : IsNonAveraging A := by
  unfold IsNonAveraging
  intro a ha S hS hCard hAvg
  -- If S.sum / |S| = a, then S.sum = a * |S|, so a | S.sum
  have hdiv : a ∣ S.sum id := by
    have hcard_ne : (S.card : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h : (↑(S.sum id) : ℚ) = ↑a * ↑S.card := (div_eq_iff hcard_ne).mp hAvg
    exact ⟨S.card, by exact_mod_cast h⟩
  exact hND a ha S hS hCard hdiv

/- ## The Function F(N) -/

/-- F(N) is the maximum size of a non-dividing subset of {1, ..., N} -/
noncomputable def F (N : ℕ) : ℕ :=
  (Finset.filter (fun A => A ⊆ Finset.Icc 1 N ∧ IsNonDividing A)
    (Finset.powerset (Finset.Icc 1 N))).sup Finset.card

/-- F is monotonic in N -/
theorem F_monotonic : ∀ N M : ℕ, N ≤ M → F N ≤ F M := by
  intro N M hNM
  simp only [F]
  apply Finset.sup_le
  intro A hA
  simp only [Finset.mem_filter, Finset.mem_powerset] at hA
  have hAM : A ⊆ Finset.Icc 1 M := by
    exact hA.1.trans (Finset.Icc_subset_Icc_right hNM)
  exact Finset.le_sup (Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr hAM, hAM, hA.2.2⟩)

/- ## Upper Bounds -/

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

/- ## Lower Bounds -/

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

/- ## The Open Question -/

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

/- ## Small Examples -/

/-- {1} is trivially non-dividing -/
theorem singleton_nondividing (n : ℕ) (_hn : n ≥ 1) :
    IsNonDividing {n} := by
  unfold IsNonDividing
  intro a ha S hS hCard
  exfalso
  have h1 : S.card ≤ ({n} : Finset ℕ).card :=
    (Finset.card_le_card hS).trans Finset.card_erase_le
  simp at h1
  omega

/-- {2, 3} is non-dividing: 2 ∤ 3 and 3 ∤ 2 -/
theorem two_three_nondividing : IsNonDividing {2, 3} := by
  intro a ha S hS hCard
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · -- a = 2: S ⊆ {2,3}.erase 2, which has card 1
    have : S.card ≤ (({2, 3} : Finset ℕ).erase 2).card := Finset.card_le_card hS
    simp at this; omega
  · -- a = 3: S ⊆ {2,3}.erase 3, which has card 1
    have : S.card ≤ (({2, 3} : Finset ℕ).erase 3).card := Finset.card_le_card hS
    simp at this; omega

/-- Primes do NOT generally form a non-dividing set:
    {2, 3, 5} fails because 2 ∣ (3 + 5) = 8.
    In fact, any set containing 2 and two odd primes whose sum is even
    violates the non-dividing property. -/
theorem primes_not_nondividing :
    ¬IsNonDividing {2, 3, 5} := by
  intro h
  apply h 2 (by simp) {3, 5}
  · -- {3,5} ⊆ {2,3,5}.erase 2
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    rcases hx with rfl | rfl <;> constructor <;> omega
  · -- card ≥ 2
    simp
  · -- 2 ∣ (3 + 5) = 8
    simp [Finset.sum_insert, Finset.sum_singleton]

/- ## Connection to Non-Averaging Sets -/

/-- The non-averaging function g(N) from Problem #186 -/
noncomputable def g (N : ℕ) : ℕ :=
  (Finset.filter (fun A => A ⊆ Finset.Icc 1 N ∧ IsNonAveraging A)
    (Finset.powerset (Finset.Icc 1 N))).sup Finset.card

/-- F(N) ≤ g(N) since non-dividing implies non-averaging -/
theorem F_le_g (N : ℕ) : F N ≤ g N := by
  simp only [F, g]
  apply Finset.sup_le
  intro A hA
  have hAmem : A ∈ Finset.powerset (Finset.Icc 1 N) :=
    (Finset.mem_filter.mp hA).1
  have hAcond := (Finset.mem_filter.mp hA).2
  have hAsub : A ⊆ Finset.Icc 1 N := hAcond.1
  have hAnd : IsNonDividing A := hAcond.2
  have hNA : IsNonAveraging A := by
    unfold IsNonAveraging
    intro a ha S hS hScard
    intro hAvg
    have hcard_ne : (S.card : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    exact hAnd a ha S hS hScard ⟨S.card, by exact_mod_cast (div_eq_iff hcard_ne).mp hAvg⟩
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hAsub, hAsub, hNA⟩)

/-- Pham-Zakharov's bound on g(N) implies bound on F(N) -/
theorem pham_zakharov_chain :
    (∀ N : ℕ, N ≥ 2 → ∃ (ε : ℝ), |ε| < 0.01 ∧ (g N : ℝ) ≤ (N : ℝ)^(1/4 + ε)) →
    (∀ N : ℕ, N ≥ 2 → ∃ (ε : ℝ), |ε| < 0.01 ∧ (F N : ℝ) ≤ (N : ℝ)^(1/4 + ε)) := by
  intro hg N hN
  obtain ⟨ε, hε, hbound⟩ := hg N hN
  exact ⟨ε, hε, le_trans (Nat.cast_le.mpr (F_le_g N)) hbound⟩

/- ## Summary

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
