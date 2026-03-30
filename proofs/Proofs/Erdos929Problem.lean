/-
# Erdős Problem #929 — Small Prime Factors in Consecutive Blocks

Let k ≥ 2 and let S(k) be the minimal x such that there exists a positive
density set of n where each of n+1, n+2, …, n+k has a prime factor ≤ x.

Estimate S(k). Is S(k) ≥ k^{1−o(1)}?

## Semantic Note

The original Erdős formulation says the numbers are "divisible by primes ≤ x,"
meaning each has AT LEAST ONE prime factor ≤ x (not that ALL prime factors are
≤ x, which would be x-smoothness). With x-smoothness, the density of x-smooth
numbers → 0 for any fixed x, making the existence claim false.

## Status: OPEN

## Key Results

- **Trivial upper bound**: S(k) ≤ k+1 (take n ≡ 1 mod (k+1)!).
- **Rosser's sieve**: S(k) > k^{1/2−o(1)}.
- **Ford–Green–Konyagin–Maynard–Tao (2018)**:
  S(k) ≪ k · (log log log k) / (log log k · log log log log k).

The conjecture S(k) ≥ k^{1−o(1)} remains open.

*Reference:* [erdosproblems.com/929](https://www.erdosproblems.com/929)
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Filter Finset

/- ## Core Definitions -/

/-- A natural number n has a prime factor ≤ x. Equivalently, its least
prime factor is at most x. For n ≤ 1, handled by Nat.minFac:
minFac 0 = 2, minFac 1 = 1. -/
def HasSmallFactor (n : ℕ) (x : ℕ) : Prop :=
  n.minFac ≤ x

/-- A block of k consecutive integers starting at n+1 each has a
prime factor ≤ x. -/
def SmoothBlock (n k x : ℕ) : Prop :=
  ∀ i : ℕ, 1 ≤ i → i ≤ k → HasSmallFactor (n + i) x

/-- The set of n for which the block n+1, …, n+k all have small factors. -/
def smoothBlockSet (k x : ℕ) : Set ℕ :=
  { n | SmoothBlock n k x }

/-- Asymptotic upper density of a set of naturals. -/
noncomputable def Set.upperDensity (S : Set ℕ) : ℝ :=
  Filter.limsup (fun n =>
    (Finset.card (@Finset.filter _ (· ∈ S) (Classical.decPred (· ∈ S))
      (Finset.range (n + 1))) : ℝ)
    / (↑(n + 1) : ℝ)) atTop

/- ## Helper Lemmas -/

/-- Every positive integer m ≤ n divides n!. -/
theorem dvd_factorial_of_pos_le {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    m ∣ n.factorial := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [Nat.factorial_succ]
    rcases Nat.eq_or_lt_of_le hmn with h | h
    · subst h; exact dvd_mul_right _ _
    · exact dvd_mul_of_dvd_right (ih (by omega)) _

/- ## Density Monotonicity -/

/-- The density counting ratio at N: |S ∩ {0,…,N}| / (N+1). -/
noncomputable abbrev densityRatio (S : Set ℕ) (N : ℕ) : ℝ :=
  (Finset.card (@Finset.filter _ (· ∈ S) (Classical.decPred (· ∈ S))
    (Finset.range (N + 1))) : ℝ) / (↑(N + 1) : ℝ)

theorem densityRatio_nonneg (S : Set ℕ) (N : ℕ) : 0 ≤ densityRatio S N :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem densityRatio_le_one (S : Set ℕ) (N : ℕ) : densityRatio S N ≤ 1 := by
  unfold densityRatio
  rw [div_le_one (by positivity : (0 : ℝ) < ↑(N + 1))]
  have h1 := @Finset.card_filter_le ℕ (Finset.range (N + 1)) (· ∈ S) (Classical.decPred _)
  rw [Finset.card_range] at h1
  exact_mod_cast h1

theorem densityRatio_mono {A B : Set ℕ} (h : A ⊆ B) (N : ℕ) :
    densityRatio A N ≤ densityRatio B N := by
  unfold densityRatio
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨hx.1, h hx.2⟩

theorem densityRatio_isBoundedUnder (S : Set ℕ) :
    IsBoundedUnder (· ≤ ·) atTop (densityRatio S) := by
  refine ⟨1, ?_⟩
  rw [Filter.eventually_map]
  exact Eventually.of_forall (densityRatio_le_one S)

theorem densityRatio_isCoboundedUnder (S : Set ℕ) :
    IsCoboundedUnder (· ≤ ·) atTop (densityRatio S) := by
  refine ⟨0, ?_⟩; intro a ha
  by_contra hlt; push_neg at hlt
  simp only [eventually_map] at ha
  obtain ⟨N, hN⟩ := ha.exists
  linarith [densityRatio_nonneg S N]

/-- If A ⊆ B, then upper density of A ≤ upper density of B. -/
theorem upperDensity_mono {A B : Set ℕ} (h : A ⊆ B) :
    A.upperDensity ≤ B.upperDensity := by
  show limsup (fun n => densityRatio A n) atTop ≤
       limsup (fun n => densityRatio B n) atTop
  exact Filter.limsup_le_limsup
    (Eventually.of_forall (fun N => densityRatio_mono h N))
    (densityRatio_isCoboundedUnder A)
    (densityRatio_isBoundedUnder B)

/- ## Smooth Block Existence -/

/-- For n ≡ 1 mod (k+1)!, each n+i (1 ≤ i ≤ k) has factor (i+1) ≤ k+1.

Proof: n+i = (k+1)!·t + (i+1). Since (i+1) | (k+1)! (as 2 ≤ i+1 ≤ k+1),
we get (i+1) | (n+i), so minFac(n+i) ≤ (i+1) ≤ k+1. -/
theorem smoothBlock_of_factorial_cong (k t : ℕ) :
    SmoothBlock ((k + 1).factorial * t + 1) k (k + 1) := by
  intro i hi1 hik
  show ((k + 1).factorial * t + 1 + i).minFac ≤ k + 1
  have heq : (k + 1).factorial * t + 1 + i = (k + 1).factorial * t + (i + 1) := by omega
  rw [heq]
  have hdvd_fact : (i + 1) ∣ (k + 1).factorial :=
    dvd_factorial_of_pos_le (by omega) (by omega)
  have hdvd : (i + 1) ∣ ((k + 1).factorial * t + (i + 1)) :=
    dvd_add (dvd_trans hdvd_fact (dvd_mul_right _ _)) (dvd_refl _)
  exact le_trans (Nat.minFac_le_of_dvd (by omega : 2 ≤ i + 1) hdvd) (by omega)

/-- The AP {(k+1)!·t + 1 : t ∈ ℕ} ⊆ smoothBlockSet k (k+1). -/
theorem arithProg_subset_smoothBlockSet (k t : ℕ) :
    (k + 1).factorial * t + 1 ∈ smoothBlockSet k (k + 1) :=
  smoothBlock_of_factorial_cong k t

/-- The AP {M*j+1 : j = 0,…,t} gives ≥ t+1 elements in the density filter. -/
private theorem ap_count_bound (k t : ℕ) :
    t + 1 ≤ (@Finset.filter ℕ (· ∈ smoothBlockSet k (k + 1))
      (Classical.decPred _) (Finset.range ((k + 1).factorial * (t + 1) + 1))).card := by
  have hinj : Function.Injective (fun j : ℕ => (k + 1).factorial * j + 1) := by
    intro a b hab; dsimp at hab
    have hmul : (k + 1).factorial * a = (k + 1).factorial * b := by omega
    exact mul_left_cancel₀ (Nat.factorial_ne_zero (k + 1)) hmul
  calc (t + 1)
      = (Finset.range (t + 1)).card := (Finset.card_range _).symm
    _ = ((Finset.range (t + 1)).image (fun j => (k + 1).factorial * j + 1)).card :=
        (Finset.card_image_of_injective _ hinj).symm
    _ ≤ _ := by
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_image, Finset.mem_range] at hx
      obtain ⟨j, hj, rfl⟩ := hx
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by nlinarith [Nat.factorial_pos (k + 1)],
        arithProg_subset_smoothBlockSet k j⟩

/-- smoothBlockSet k (k+1) has positive upper density. The AP
{(k+1)!·t + 1 : t ≥ 0} ⊆ smoothBlockSet gives density ≥ 1/(2·(k+1)!) > 0. -/
theorem smoothBlockSet_pos_density (k : ℕ) :
    0 < (smoothBlockSet k (k + 1)).upperDensity := by
  set S := smoothBlockSet k (k + 1) with hS
  set M := (k + 1).factorial with hM
  have hM_pos : (0 : ℝ) < ↑M := Nat.cast_pos.mpr (Nat.factorial_pos _)
  -- Strategy: show limsup ≥ 1/(2M) > 0 by contradiction.
  -- If limsup ≤ 0 < 1/(2M), extract "eventually densityRatio ≤ a" for some a.
  -- But at N = M*(t+1), densityRatio ≥ 1/(2M), contradicting "eventually ≤ a < 1/(2M)".
  suffices hsuff : 1 / (2 * (↑M : ℝ)) ≤ S.upperDensity by
    linarith [show (0 : ℝ) < 1 / (2 * ↑M) from by positivity]
  -- limsup = sInf {a | eventually densityRatio ≤ a}; show 1/(2M) is a lower bound
  show 1 / (2 * (↑M : ℝ)) ≤ Filter.limsup (fun n => densityRatio S n) atTop
  unfold Filter.limsup Filter.limsSup
  apply le_csInf
  · -- Set {a | eventually ≤ a} is nonempty (from boundedness ≤ 1)
    exact densityRatio_isBoundedUnder S
  · -- 1/(2M) is a lower bound: any eventual upper bound a satisfies 1/(2M) ≤ a
    intro a ha
    by_contra hlt; push_neg at hlt
    -- hlt : a < 1/(2M)
    -- Extract N₀ from the eventual bound
    have ha' : ∀ᶠ N in atTop, densityRatio S N ≤ a :=
      Filter.eventually_map.mp ha
    rw [Filter.eventually_atTop] at ha'
    obtain ⟨N₀, hN₀⟩ := ha'
    -- At N = M*(N₀+1), densityRatio ≥ (N₀+1)/(M*(N₀+1)+1) ≥ 1/(2M) > a
    have hge : N₀ ≤ M * (N₀ + 1) :=
      le_trans (Nat.le_succ _) (Nat.le_mul_of_pos_left _ (Nat.factorial_pos _))
    have hbnd := hN₀ _ hge
    -- hbnd : densityRatio S (M*(N₀+1)) ≤ a
    -- Count: AP gives ≥ N₀+1 elements in the filter at this point
    have hcount := ap_count_bound k N₀
    -- Density ratio bound: (N₀+1)/(M*(N₀+1)+1) ≤ densityRatio S (M*(N₀+1))
    have hdr : (↑(N₀ + 1) : ℝ) / (↑(M * (N₀ + 1) + 1) : ℝ) ≤
        densityRatio S (M * (N₀ + 1)) := by
      show (↑(N₀ + 1) : ℝ) / (↑(M * (N₀ + 1) + 1) : ℝ) ≤
        (↑(@Finset.filter ℕ (· ∈ S) (Classical.decPred _)
          (Finset.range (M * (N₀ + 1) + 1))).card : ℝ) / (↑(M * (N₀ + 1) + 1) : ℝ)
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hcount
    -- Arithmetic: (N₀+1)/(M*(N₀+1)+1) ≥ 1/(2M)
    -- Since M*(N₀+1)+1 ≤ 2M*(N₀+1), dividing by bigger denom gives smaller result
    have harith : 1 / (2 * (↑M : ℝ)) ≤ (↑(N₀ + 1) : ℝ) / (↑(M * (N₀ + 1) + 1) : ℝ) := by
      have key : (↑(M * (N₀ + 1) + 1) : ℝ) ≤ 2 * ↑M * ↑(N₀ + 1) := by
        push_cast
        have : (1 : ℝ) ≤ ↑M := by exact_mod_cast Nat.factorial_pos (k + 1)
        nlinarith
      have step : ↑(N₀ + 1) / (2 * ↑M * ↑(N₀ + 1)) ≤
          ↑(N₀ + 1) / (↑(M * (N₀ + 1) + 1) : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) key
      have heq : (1 : ℝ) / (2 * ↑M) = ↑(N₀ + 1) / (2 * ↑M * ↑(N₀ + 1)) := by
        field_simp
      linarith
    linarith

/-- For any k, ∃ x with smoothBlockSet k x having positive density. -/
theorem smooth_block_exists (k : ℕ) :
    ∃ x : ℕ, 0 < (smoothBlockSet k x).upperDensity :=
  ⟨k + 1, smoothBlockSet_pos_density k⟩

/-- S(k) is the minimal x such that smoothBlockSet k x has positive
upper density. -/
noncomputable def smoothThreshold (k : ℕ) : ℕ :=
  Nat.find (smooth_block_exists k)

/- ## Main Conjecture -/

/-- **Erdős Problem #929 (Open).**
S(k) ≥ k^{1−o(1)}, meaning for every ε > 0 and all sufficiently
large k, S(k) ≥ k^{1−ε}. -/
def Erdos929Conjecture : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ (k : ℕ) in atTop,
    (smoothThreshold k : ℝ) ≥ (k : ℝ) ^ (1 - ε)

/- ## Known Bounds -/

/-- **Trivial upper bound.** S(k) ≤ k+1.
The AP {(k+1)!·t + 1} witnesses positive density for x = k+1,
so Nat.find returns ≤ k+1. -/
theorem trivial_upper (k : ℕ) (_hk : 2 ≤ k) :
    smoothThreshold k ≤ k + 1 := by
  exact Nat.find_le (smoothBlockSet_pos_density k)

/-- **Rosser's sieve.** S(k) > k^{1/2−o(1)}.
For every ε > 0 and large enough k, S(k) ≥ k^{1/2−ε}. -/
/-- **Ford–Green–Konyagin–Maynard–Tao (2018).**
S(k) ≪ k · log log log k / (log log k · log log log log k). -/
/- ## Structural Observations -/

/-- If k₁ ≤ k₂, the small-factor block set for k₂ is contained in that for k₁. -/
theorem smoothBlockSet_antitone (k₁ k₂ x : ℕ) (h : k₁ ≤ k₂) :
    smoothBlockSet k₂ x ⊆ smoothBlockSet k₁ x :=
  fun _ hn i hi1 hi2 => hn i hi1 (le_trans hi2 h)

/-- S(k) is monotone non-decreasing: more consecutive small-factor
conditions can only increase the threshold. -/
theorem smoothThreshold_mono (k₁ k₂ : ℕ) (h : k₁ ≤ k₂)
    (_hk : 2 ≤ k₁) : smoothThreshold k₁ ≤ smoothThreshold k₂ := by
  unfold smoothThreshold
  apply Nat.find_le
  -- Goal: 0 < (smoothBlockSet k₁ (Nat.find (smooth_block_exists k₂))).upperDensity
  have hk₂ := Nat.find_spec (smooth_block_exists k₂)
  -- hk₂ : 0 < (smoothBlockSet k₂ (find ...)).upperDensity
  exact lt_of_lt_of_le hk₂
    (upperDensity_mono (smoothBlockSet_antitone k₁ k₂ _ h))

/-- smoothBlockSet 2 x is empty for x ≤ 1. At i=1, need (n+1).minFac ≤ x.
For x=0: minFac ≥ 1 > 0 always. For x=1: minFac (n+1) ≤ 1 only if n+1 ≤ 1,
but then n+2 ≥ 2 has minFac 2 > 1. -/
private theorem smoothBlockSet_two_empty_of_le_one {x : ℕ} (hx : x ≤ 1) :
    smoothBlockSet 2 x = ∅ := by
  ext n; simp only [smoothBlockSet, SmoothBlock, HasSmallFactor, Set.mem_setOf_eq,
    Set.mem_empty_iff_false, iff_false, not_forall, exists_prop]
  interval_cases x
  · -- x = 0: minFac (n+1) ≥ 1 > 0
    exact ⟨1, le_refl 1, by omega, not_le.mpr (Nat.minFac_pos _)⟩
  · -- x = 1: if n = 0, minFac 2 = 2 > 1; if n ≥ 1, minFac (n+1) ≥ 2 > 1
    by_cases hn : n = 0
    · subst hn; exact ⟨2, by omega, le_refl 2, by decide⟩
    · exact ⟨1, le_refl 1, by omega, not_le.mpr (by
        exact lt_of_lt_of_le (by omega) (Nat.minFac_prime (by omega)).two_le)⟩

/-- smoothBlockSet 2 2 ⊆ {0}: for n ≥ 1, consecutive n+1, n+2 can't both
have minFac ≤ 2 (one is odd ≥ 3, with minFac ≥ 3). -/
private theorem smoothBlockSet_two_two_sub_zero :
    smoothBlockSet 2 2 ⊆ {0} := by
  intro n hn
  simp only [Set.mem_singleton_iff]
  by_contra h; push_neg at h
  have hn_pos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h
  -- Both n+1 ≥ 2 and n+2 ≥ 3 must have minFac ≤ 2
  have h1 := hn 1 (le_refl 1) (by omega : 1 ≤ 2)  -- minFac(n+1) ≤ 2
  have h2 := hn 2 (by omega) (le_refl 2)  -- minFac(n+2) ≤ 2
  -- One of n+1, n+2 is odd. An odd number m ≥ 3 has minFac ≥ 3.
  have hodd : ¬ 2 ∣ (n + 1) ∨ ¬ 2 ∣ (n + 2) := by omega
  rcases hodd with hodd1 | hodd2
  · -- n+1 is odd ≥ 2, so minFac(n+1) is an odd prime, hence ≥ 3
    have hprime := Nat.minFac_prime (by omega : n + 1 ≠ 1)
    have hne2 : (n + 1).minFac ≠ 2 := by
      intro heq
      have := Nat.minFac_dvd (n + 1)
      rw [heq] at this; exact hodd1 this
    exact absurd (le_antisymm h1 hprime.two_le) hne2
  · -- n+2 is odd ≥ 3, so minFac(n+2) is an odd prime, hence ≥ 3
    have hprime := Nat.minFac_prime (by omega : n + 2 ≠ 1)
    have hne2 : (n + 2).minFac ≠ 2 := by
      intro heq
      have := Nat.minFac_dvd (n + 2)
      rw [heq] at this; exact hodd2 this
    exact absurd (le_antisymm h2 hprime.two_le) hne2

/-- Upper density of {0} is ≤ 0: densityRatio {0} N = 1/(N+1) → 0. -/
private theorem upperDensity_singleton_zero : ({0} : Set ℕ).upperDensity ≤ 0 := by
  suffices h : ∀ ε : ℝ, 0 < ε → ({0} : Set ℕ).upperDensity ≤ ε by
    by_contra hlt; push_neg at hlt
    linarith [h _ (half_pos hlt)]
  intro ε hε
  show Filter.limsup (fun n => densityRatio {(0 : ℕ)} n) atTop ≤ ε
  apply Filter.limsup_le_of_le (densityRatio_isCoboundedUnder _)
  rw [Filter.eventually_atTop]
  refine ⟨⌈(1 : ℝ)/ε⌉₊, fun N hN => ?_⟩
  -- densityRatio {0} N ≤ 1/(N+1) ≤ ε
  -- Step 1: card of filter ≤ 1
  have hcard : (@Finset.filter ℕ (· ∈ ({0} : Set ℕ)) (Classical.decPred _)
      (Finset.range (N + 1))).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    simp only [Finset.mem_filter, Set.mem_singleton_iff] at ha hb
    rw [ha.2, hb.2]
  -- Step 2: densityRatio ≤ 1/(N+1) ≤ ε
  -- First bound: count ≤ 1 gives densityRatio ≤ 1/(N+1)
  -- Second bound: N ≥ ⌈1/ε⌉ gives 1/(N+1) ≤ ε
  have h1 : (1 : ℝ) / ε ≤ ↑(N + 1) := calc
    (1 : ℝ) / ε ≤ ↑⌈(1 : ℝ)/ε⌉₊ := Nat.le_ceil _
    _ ≤ (↑N : ℝ) := by exact_mod_cast hN
    _ ≤ ↑(N + 1) := by push_cast; linarith
  -- densityRatio ≤ card/(N+1) ≤ 1/(N+1) ≤ 1/(1/ε) = ε
  calc densityRatio ({0} : Set ℕ) N
      ≤ 1 / (↑(N + 1) : ℝ) := by
        show (↑(@Finset.filter ℕ (· ∈ ({0} : Set ℕ)) (Classical.decPred _)
          (Finset.range (N + 1))).card : ℝ) / (↑(N + 1) : ℝ) ≤ 1 / (↑(N + 1) : ℝ)
        exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ ≤ 1 / (1 / ε) := by
        exact div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1) (by positivity) h1
    _ = ε := one_div_one_div ε

/-- For k = 2, S(2) = 3. The AP n ≡ 2 mod 6 gives 3∣(n+1) and 2∣(n+2),
so x = 3 works with density 1/6. For x ≤ 2: consecutive integers can't
both have all prime factors ≤ 2, so density = 0. -/
theorem smooth_threshold_2 : smoothThreshold 2 = 3 := by
  unfold smoothThreshold
  rw [Nat.find_eq_iff]
  refine ⟨smoothBlockSet_pos_density 2, fun m hm => ?_⟩
  -- For m < 3, show ¬ (0 < (smoothBlockSet 2 m).upperDensity)
  push_neg
  interval_cases m
  · -- m = 0: smoothBlockSet 2 0 = ∅, density = 0
    have := smoothBlockSet_two_empty_of_le_one (show (0 : ℕ) ≤ 1 by omega)
    rw [this]; exact le_of_eq (by simp [Set.upperDensity, Filter.limsup_const])
  · -- m = 1: smoothBlockSet 2 1 = ∅, density = 0
    have := smoothBlockSet_two_empty_of_le_one (show (1 : ℕ) ≤ 1 by omega)
    rw [this]; exact le_of_eq (by simp [Set.upperDensity, Filter.limsup_const])
  · -- m = 2: smoothBlockSet 2 2 ⊆ {0}, density ≤ density({0}) = 0
    calc (smoothBlockSet 2 2).upperDensity
        ≤ ({0} : Set ℕ).upperDensity := upperDensity_mono smoothBlockSet_two_two_sub_zero
      _ ≤ 0 := upperDensity_singleton_zero
