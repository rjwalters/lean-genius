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
/-- Pham-Zakharov (2024): F(N) ≤ N^{1/4 + o(1)}
    This resolves the original question negatively. -/
axiom pham_zakharov_upper_bound :
    ∃ (ε : ℕ → ℝ), (∀ δ > 0, ∃ N₀, ∀ N ≥ N₀, |ε N| < δ) ∧
    ∀ N : ℕ, N ≥ 2 → (F N : ℝ) ≤ (N : ℝ)^(1/4 + ε N)

/-- The original question "Is F(N) > N^{1/2 - o(1)}?" is answered NO.
    Proof: instantiate with ε ≡ 0, then F(N) > N^{1/2} for large N.
    But Pham-Zakharov gives F(N) ≤ N^{1/4+o(1)} < N^{1/2}, contradiction. -/
theorem original_question_answered_no :
    ¬(∀ (ε : ℕ → ℝ), (∀ δ > 0, ∃ N₀, ∀ N ≥ N₀, |ε N| < δ) →
      ∃ N₀, ∀ N ≥ N₀, (F N : ℝ) > (N : ℝ)^(1/2 - ε N)) := by
  intro h
  obtain ⟨ε', hε', hbound⟩ := pham_zakharov_upper_bound
  -- Apply h to ε ≡ 0 (trivially o(1))
  obtain ⟨N₀, hN₀⟩ := h (fun _ => 0)
    (fun δ hδ => ⟨0, fun _ _ => by simpa using hδ⟩)
  -- Get N₁ where |ε'(N)| < 1/4
  obtain ⟨N₁, hN₁⟩ := hε' (1/4) (by positivity)
  -- Pick M ≥ max(N₀, N₁, 2)
  set M := max N₀ (max N₁ 2)
  -- F(M) > M^(1/2) (from h with ε = 0, since 1/2 - 0 = 1/2)
  have hF_lower := hN₀ M (le_max_left _ _)
  simp only [sub_zero] at hF_lower
  -- F(M) ≤ M^(1/4 + ε'(M)) (from Pham-Zakharov)
  have hF_upper := hbound M
    (le_trans (le_max_right N₁ 2) (le_max_right N₀ _))
  -- 1/4 + ε'(M) < 1/2 (from |ε'(M)| < 1/4, so ε'(M) < 1/4)
  have hexp_lt : 1/4 + ε' M < 1/2 := by
    linarith [(abs_lt.mp (hN₁ M
      (le_trans (le_max_left N₁ 2) (le_max_right N₀ _)))).2]
  -- M > 1 as ℝ (since M ≥ 2)
  have hM_gt : (1 : ℝ) < (↑M : ℝ) := by
    exact_mod_cast (show 1 < M by omega)
  -- M^(1/4 + ε'(M)) < M^(1/2) by rpow monotonicity
  have hrpow := Real.rpow_lt_rpow_of_exponent_lt hM_gt hexp_lt
  -- Contradiction: F(M) ≤ M^(1/4+ε'(M)) < M^(1/2) < F(M)
  linarith

/- ## Lower Bounds -/

/-- Csaba's construction: F(N) ≫ N^{1/5} -/
axiom csaba_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ N : ℕ, N ≥ 1 → (F N : ℝ) ≥ c * (N : ℝ)^((1 : ℝ)/5)

/-- Straus's lower bound: F(N) > exp((√(2/log 2) + o(1))√(log N)) -/
/-- exp(3/4) > 2, via Taylor sum of order 3:
    1 + 3/4 + 9/32 = 65/32 > 2 -/
private theorem exp_three_fourths_gt_two : (2 : ℝ) < Real.exp (3/4) := by
  calc (2 : ℝ) < 65/32 := by norm_num
    _ ≤ ∑ i ∈ Finset.range 3, ((3 : ℝ)/4) ^ i / ↑(i.factorial) := by
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
        norm_num
    _ ≤ Real.exp (3/4) := Real.sum_le_exp_of_nonneg (by norm_num) 3

/-- log 2 < 3/4 -/
private theorem log_two_lt : Real.log 2 < 3/4 :=
  (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).mpr exp_three_fourths_gt_two

/-- exp(2/3) < 2, via exp_bound upper bound -/
private theorem exp_two_thirds_lt_two : Real.exp (2/3) < (2 : ℝ) := by
  have hbound := Real.exp_bound (by norm_num : |(2 : ℝ)/3| ≤ 1) (n := 5) (by norm_num)
  rw [abs_le] at hbound
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.succ_eq_add_one] at hbound
  norm_num at hbound ⊢
  linarith [hbound.2]

/-- log 2 > 2/3 -/
private theorem log_two_gt : (2 : ℝ)/3 < Real.log 2 :=
  (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 2)).mpr exp_two_thirds_lt_two

/-- The constant √(2/log 2) ≈ 1.699 -/
theorem straus_constant_value :
    Real.sqrt (2 / Real.log 2) > 1.6 ∧ Real.sqrt (2 / Real.log 2) < 1.8 := by
  have hlog_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  constructor
  · rw [gt_iff_lt, Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1.6)]
    norm_num
    rw [lt_div_iff₀ hlog_pos]
    nlinarith [log_two_lt]
  · rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1.8)]
    norm_num
    rw [div_lt_iff₀ hlog_pos]
    nlinarith [log_two_gt]

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

/-- The original conjecture F(N) < (log N)^O(1) was disproved by Csaba's polynomial lower bound.
    Proof: Csaba gives F(N) ≥ c₀·N^{1/5}. If F(N) ≤ (log N)^C, then using
    log(x) ≤ x^δ/δ (for δ = 1/(10C)), we get (log N)^C ≤ (10C)^C · N^{1/10},
    so c₀·N^{1/5} ≤ (10C)^C · N^{1/10}, i.e., c₀·N^{1/10} ≤ (10C)^C.
    But N^{1/10} → ∞, contradiction. -/
theorem erdos_original_conjecture_false :
    ¬(∃ c : ℝ, c > 0 ∧ ∀ N : ℕ, N ≥ 2 → (F N : ℝ) ≤ (Real.log N)^c) := by
  intro ⟨C, hC, hbound⟩
  obtain ⟨c₀, hc₀, hcsaba⟩ := csaba_lower_bound
  -- Pick M : ℕ large enough to derive contradiction
  set L := (10 * C) ^ C / c₀ + 1 with hL_def
  have hL_pos : (0 : ℝ) < L := by positivity
  obtain ⟨M₀, hM₀⟩ := exists_nat_gt (L ^ (10 : ℝ))
  set M := max M₀ 2 with hM_def
  have hM_ge_2 : M ≥ 2 := le_max_right _ _
  have hM_gt : L ^ (10 : ℝ) < ↑M :=
    lt_of_lt_of_le hM₀ (Nat.cast_le.mpr (le_max_left M₀ 2))
  have hM_nn : (0 : ℝ) ≤ ↑M := Nat.cast_nonneg M
  have hM_pos : (0 : ℝ) < ↑M := Nat.cast_pos.mpr (by omega)
  -- Step 1: log M ≤ 10C · M^{1/(10C)} (from log_le_rpow_div with δ = 1/(10C))
  have hδ : (0 : ℝ) < 1 / (10 * C) := by positivity
  have hlog_bound : Real.log ↑M ≤ 10 * C * (↑M : ℝ) ^ ((1 : ℝ) / (10 * C)) := by
    have h := Real.log_le_rpow_div hM_nn hδ
    have : (↑M : ℝ) ^ ((1 : ℝ) / (10 * C)) / ((1 : ℝ) / (10 * C)) =
           10 * C * (↑M : ℝ) ^ ((1 : ℝ) / (10 * C)) := by field_simp
    linarith
  -- Step 2: (log M)^C ≤ (10C)^C · M^{1/10}
  have hlog_nn : (0 : ℝ) ≤ Real.log ↑M :=
    Real.log_nonneg (Nat.one_le_cast.mpr (by omega))
  have h_rpow_bound : (Real.log ↑M) ^ C ≤ (10 * C) ^ C * (↑M : ℝ) ^ ((1 : ℝ) / 10) := by
    calc (Real.log ↑M) ^ C
        ≤ (10 * C * (↑M : ℝ) ^ ((1 : ℝ) / (10 * C))) ^ C :=
          Real.rpow_le_rpow hlog_nn hlog_bound (le_of_lt hC)
      _ = (10 * C) ^ C * ((↑M : ℝ) ^ ((1 : ℝ) / (10 * C))) ^ C :=
          Real.mul_rpow (by positivity : (0 : ℝ) ≤ 10 * C) (Real.rpow_nonneg hM_nn _)
      _ = (10 * C) ^ C * (↑M : ℝ) ^ ((1 : ℝ) / 10) := by
          congr 1; rw [← Real.rpow_mul hM_nn]; congr 1; field_simp
  -- Step 3: c₀ · M^{1/5} ≤ (10C)^C · M^{1/10}
  have h_csaba := hcsaba M (show M ≥ 1 by omega)
  have h_bound := hbound M hM_ge_2
  have h_le : c₀ * (↑M : ℝ) ^ ((1 : ℝ) / 5) ≤ ↑(F M) := h_csaba
  have h_combined : c₀ * (↑M : ℝ) ^ ((1 : ℝ) / 5) ≤
                    (10 * C) ^ C * (↑M : ℝ) ^ ((1 : ℝ) / 10) :=
    le_trans h_le (le_trans h_bound h_rpow_bound)
  -- Step 4: M^{1/5} = M^{1/10} · M^{1/10}, so c₀ · M^{1/10} ≤ (10C)^C
  have h_split : (↑M : ℝ) ^ ((1 : ℝ) / 5) =
                 (↑M : ℝ) ^ ((1 : ℝ) / 10) * (↑M : ℝ) ^ ((1 : ℝ) / 10) := by
    rw [← Real.rpow_add hM_pos]; norm_num
  have hM_rpow_pos : (0 : ℝ) < (↑M : ℝ) ^ ((1 : ℝ) / 10) :=
    Real.rpow_pos_of_pos hM_pos _
  have h_cancel : c₀ * (↑M : ℝ) ^ ((1 : ℝ) / 10) ≤ (10 * C) ^ C := by
    rw [h_split] at h_combined; nlinarith
  -- Step 5: But M^{1/10} > L > (10C)^C/c₀, so c₀ · M^{1/10} > (10C)^C
  have hL_nn : (0 : ℝ) ≤ L := le_of_lt hL_pos
  have h_rpow_mono : L < (↑M : ℝ) ^ ((1 : ℝ) / 10) := by
    have h1 : (L ^ (10 : ℝ)) ^ ((1 : ℝ) / 10) < (↑M : ℝ) ^ ((1 : ℝ) / 10) :=
      Real.rpow_lt_rpow (Real.rpow_nonneg hL_nn _) hM_gt (by norm_num)
    rwa [← Real.rpow_mul hL_nn, show (10 : ℝ) * ((1 : ℝ) / 10) = 1 from by norm_num,
        Real.rpow_one] at h1
  have h_contra : (10 * C) ^ C < c₀ * (↑M : ℝ) ^ ((1 : ℝ) / 10) := by
    have hL_gt : (10 * C) ^ C / c₀ < L := by simp only [L]; linarith
    calc (10 * C) ^ C < c₀ * L := by
            rw [div_lt_iff₀ hc₀] at hL_gt; linarith
      _ < c₀ * (↑M : ℝ) ^ ((1 : ℝ) / 10) :=
          mul_lt_mul_of_pos_left h_rpow_mono hc₀
  -- Contradiction: h_cancel says ≤, h_contra says >
  linarith

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

/- ## Structural Results -/

/-- Element 1 cannot belong to any non-dividing set of size ≥ 3:
    Since 1 divides every natural number, the non-dividing condition
    for a = 1 fails whenever there exists S ⊆ A \ {1} with |S| ≥ 2. -/
theorem one_not_in_large_nondividing (A : Finset ℕ) (h1 : 1 ∈ A) (hcard : A.card ≥ 3) :
    ¬IsNonDividing A := by
  intro hND
  have herase_card : (A.erase 1).card ≥ 2 := by
    rw [Finset.card_erase_of_mem h1]; omega
  exact hND 1 h1 (A.erase 1) (Finset.Subset.refl _) herase_card (one_dvd _)

/-- Helper: if S ⊆ T, |S| ≥ 2, and |T| ≤ 2, then S = T -/
private lemma finset_eq_of_subset_of_card_two {S T : Finset ℕ}
    (hsub : S ⊆ T) (hS : S.card ≥ 2) (hT : T.card ≤ 2) : S = T :=
  Finset.eq_of_subset_of_card_le hsub (by omega)

/-- {2, 4, 5} is non-dividing: 2 ∤ 9, 4 ∤ 7, 5 ∤ 6.
    This provides F(5) ≥ 3, a concrete lower bound. -/
theorem two_four_five_nondividing : IsNonDividing ({2, 4, 5} : Finset ℕ) := by
  intro a ha S hS hCard hdvd
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl
  · -- a = 2: S ⊆ {4,5}, S = {4,5}, sum = 9, 2 ∤ 9
    have hle : (({2, 4, 5} : Finset ℕ).erase 2).card ≤ 2 := by decide
    have hseq : S = ({2, 4, 5} : Finset ℕ).erase 2 :=
      finset_eq_of_subset_of_card_two hS hCard hle
    subst hseq; exact absurd hdvd (by decide)
  · -- a = 4: S ⊆ {2,5}, S = {2,5}, sum = 7, 4 ∤ 7
    have hle : (({2, 4, 5} : Finset ℕ).erase 4).card ≤ 2 := by decide
    have hseq : S = ({2, 4, 5} : Finset ℕ).erase 4 :=
      finset_eq_of_subset_of_card_two hS hCard hle
    subst hseq; exact absurd hdvd (by decide)
  · -- a = 5: S ⊆ {2,4}, S = {2,4}, sum = 6, 5 ∤ 6
    have hle : (({2, 4, 5} : Finset ℕ).erase 5).card ≤ 2 := by decide
    have hseq : S = ({2, 4, 5} : Finset ℕ).erase 5 :=
      finset_eq_of_subset_of_card_two hS hCard hle
    subst hseq; exact absurd hdvd (by decide)

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

/- ## Constructive Non-Dividing Sets -/

/-- Observation: Finding non-dividing sets with ≥ 3 elements is nontrivial.
    {3,5,7} fails (3 ∣ 5+7=12), {3,7,11} fails (3 ∣ 7+11=18).
    The difficulty illustrates why F(N) grows slowly. -/
theorem nondividing_hard_to_find :
    ¬IsNonDividing {3, 5, 7} := by
  intro h
  apply h 3 (by simp) {5, 7}
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    rcases hx with rfl | rfl <;> constructor <;> omega
  · simp
  · simp [Finset.sum_insert, Finset.sum_singleton]

/- ## Parity Constraint: Sets Containing 2 -/

/-- If 2 ∈ A and A is non-dividing, then |A| ≤ 3.
    Proof: Among any 3 positive integers, at least two share parity,
    and their sum is even (divisible by 2). So A \ {2} has ≤ 2 elements.
    Example: {2, 4, 5} achieves |A| = 3 (see two_four_five_nondividing). -/
theorem two_in_nondividing_bound (A : Finset ℕ) (h2 : 2 ∈ A) (hND : IsNonDividing A) :
    A.card ≤ 3 := by
  by_contra hge
  push_neg at hge
  set B := A.erase 2
  have hBcard : 3 ≤ B.card := by rw [Finset.card_erase_of_mem h2]; omega
  -- Split B by parity (mod 2)
  set Be := B.filter (fun n => n % 2 = 0)
  set Bo := B.filter (fun n => ¬(n % 2 = 0))
  have hBsplit : B.card = Be.card + Bo.card :=
    (Finset.filter_card_add_filter_neg_card_eq_card (fun n => n % 2 = 0)).symm
  -- Pigeonhole: one of Be, Bo has ≥ 2 elements
  have hge2 : 2 ≤ Be.card ∨ 2 ≤ Bo.card := by omega
  -- Extract two elements of same parity and show 2 | their sum
  suffices ∀ (F : Finset ℕ), F ⊆ B → 1 < F.card →
      (∀ x ∈ F, x % 2 = 0) ∨ (∀ x ∈ F, ¬(x % 2 = 0)) → False by
    rcases hge2 with h | h
    · exact this Be (Finset.filter_subset _ _) (by omega)
        (Or.inl (fun x hx => (Finset.mem_filter.mp hx).2))
    · exact this Bo (Finset.filter_subset _ _) (by omega)
        (Or.inr (fun x hx => (Finset.mem_filter.mp hx).2))
  intro F hFB hFcard hparity
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hFcard
  have hdvd : 2 ∣ ({a, b} : Finset ℕ).sum id := by
    rw [Finset.sum_pair hab]; simp only [id]
    apply Nat.dvd_of_mod_eq_zero
    rcases hparity with h | h
    · have := h a ha; have := h b hb; omega  -- even + even
    · have := h a ha; have := h b hb; omega  -- odd + odd
  exact hND 2 h2 {a, b}
    (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> exact hFB (by assumption))
    (by rw [Finset.card_pair hab])
    hdvd

/-- Helper: for S ⊆ T with |S| ≥ 2 and |T| = 3, non-divisibility reduces
    to checking the full sum and each "pair sum" T.sum - x for x ∈ T. -/
private lemma nondividing_three_subset {a : ℕ} {T : Finset ℕ} (hT : T.card = 3)
    (h_full : ¬(a ∣ T.sum id))
    (h_pairs : ∀ x ∈ T, ¬(a ∣ T.sum id - x))
    {S : Finset ℕ} (hS : S ⊆ T) (hCard : S.card ≥ 2) : ¬(a ∣ S.sum id) := by
  have hScard_le : S.card ≤ 3 := (Finset.card_le_card hS).trans hT.le
  intro hdvd
  rcases Nat.eq_or_lt_of_le hCard with h2 | h3
  · -- |S| = 2: T \ S has exactly 1 element
    have hTdiff_card : (T \ S).card = 1 := by
      rw [Finset.card_sdiff hS, hT]; omega
    obtain ⟨x, hx_eq⟩ := Finset.card_eq_one.mp hTdiff_card
    have hxT : x ∈ T := by
      have : x ∈ T \ S := hx_eq ▸ Finset.mem_singleton_self x
      exact Finset.sdiff_subset this
    -- T.sum = S.sum + x (via Finset.sum_sdiff)
    have hsum : (T \ S).sum id + S.sum id = T.sum id := Finset.sum_sdiff hS
    rw [hx_eq, Finset.sum_singleton] at hsum
    -- So T.sum - x = S.sum
    have hsub : T.sum id - x = S.sum id := by omega
    exact h_pairs x hxT (hsub ▸ hdvd)
  · -- |S| = 3 = |T|, so S = T
    exact h_full (Finset.eq_of_subset_of_card_le hS (by omega) ▸ hdvd)

/-- {3, 5, 11, 18} is non-dividing.
    Verification: For each a ∈ {3,5,11,18}, all subset sums of A \ {a}
    with ≥ 2 elements are not divisible by a.
    Sums: a=3→{16,23,29,34}, a=5→{14,21,29,32},
          a=11→{8,21,23,26}, a=18→{8,14,16,19}. -/
theorem three_five_eleven_eighteen_nondividing :
    IsNonDividing ({3, 5, 11, 18} : Finset ℕ) := by
  intro a ha S hS hCard hdvd
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · -- a = 3: T = {5, 11, 18}
    have : ({3, 5, 11, 18} : Finset ℕ).erase 3 = {5, 11, 18} := by decide
    exact absurd hdvd (nondividing_three_subset (by decide)
      (by decide) (by decide) (this ▸ hS) hCard)
  · -- a = 5: T = {3, 11, 18}
    have : ({3, 5, 11, 18} : Finset ℕ).erase 5 = {3, 11, 18} := by decide
    exact absurd hdvd (nondividing_three_subset (by decide)
      (by decide) (by decide) (this ▸ hS) hCard)
  · -- a = 11: T = {3, 5, 18}
    have : ({3, 5, 11, 18} : Finset ℕ).erase 11 = {3, 5, 18} := by decide
    exact absurd hdvd (nondividing_three_subset (by decide)
      (by decide) (by decide) (this ▸ hS) hCard)
  · -- a = 18: T = {3, 5, 11}
    have : ({3, 5, 11, 18} : Finset ℕ).erase 18 = {3, 5, 11} := by decide
    exact absurd hdvd (nondividing_three_subset (by decide)
      (by decide) (by decide) (this ▸ hS) hCard)

/- ## Bound Exponent Comparison -/

/-- The upper bound exponent 1/4 is strictly less than the original conjectured 1/2. -/
theorem quarter_lt_half : (1 : ℚ) / 4 < 1 / 2 := by norm_num

/-- The lower bound exponent 1/5 (Csaba) is less than 1/4 (Pham-Zakharov upper). -/
theorem fifth_lt_quarter : (1 : ℚ) / 5 < 1 / 4 := by norm_num

/-- The gap between known bounds: 1/4 - 1/5 = 1/20. -/
theorem polynomial_exponent_gap : (1 : ℚ) / 4 - 1 / 5 = 1 / 20 := by norm_num

/- ## Summary

**Problem Status: OPEN (original question resolved)**

The original question "Is F(N) > N^{1/2-o(1)}?" was answered NO by Pham-Zakharov (2024),
who showed F(N) ≤ N^{1/4+o(1)}.

**Current State:**
- Upper bound: F(N) ≤ N^{1/4+o(1)} (Pham-Zakharov 2024)
- Lower bound: F(N) > exp(c√(log N)) (Straus), F(N) ≫ N^{1/5} (Csaba)

The gap between polynomial (N^{1/4}) and subexponential (exp(√(log N))) growth
remains to be closed. The polynomial exponent gap (1/4 vs 1/5) is 1/20.

**Proved theorems (sorry-free):**
- IsNonDividing, IsNonDividingAlt, IsNonAveraging definitions
- nondividing_implies_nonaveraging
- original_question_answered_no (from pham_zakharov_upper_bound)
- erdos_original_conjecture_false (from csaba_lower_bound, via log ≤ x^δ/δ)
- F monotonic, F ≤ g
- Concrete examples: {2,3}, {2,4,5}, {3,5,11,18} non-dividing; {2,3,5} not non-dividing
- Structural: 1 ∉ large non-dividing sets; 2 ∈ A ⇒ |A| ≤ 3 (parity constraint)
- Exponent comparisons: 1/4 < 1/2, 1/5 < 1/4, gap = 1/20
-/

end Erdos131
