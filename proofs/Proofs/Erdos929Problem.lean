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

/-- smoothBlockSet k (k+1) has positive upper density: the AP
{(k+1)!·t + 1 : t ≥ 0} is contained in it and has density 1/(k+1)!.

Proof: The AP {M·i + 1 : i ∈ ℕ} (M = (k+1)!) is contained in S = smoothBlockSet k (k+1)
by `arithProg_subset_smoothBlockSet`. At index n = M·t, the AP contributes ≥ t members
to {0,...,n}, giving densityRatio S n ≥ t/(M·t+1) ≥ 1/(M+1) > 0 for t ≥ 1.
Since this happens frequently, limsup ≥ 1/(M+1) > 0. -/
theorem smoothBlockSet_pos_density (k : ℕ) :
    0 < (smoothBlockSet k (k + 1)).upperDensity := by
  set M := (k + 1).factorial with hM_def
  set S := smoothBlockSet k (k + 1) with hS_def
  have hM_pos : (0 : ℕ) < M := Nat.factorial_pos _
  -- Suffices: 1/(M+1) ≤ upperDensity S, since 1/(M+1) > 0
  apply lt_of_lt_of_le (show (0 : ℝ) < 1 / (↑M + 1) from by positivity)
  -- Use: if f is frequently ≥ c and bounded above, then limsup f ≥ c
  apply Filter.le_limsup_of_frequently_le
  · -- Show densityRatio S n ≥ 1/(M+1) frequently
    rw [Filter.frequently_atTop]
    intro N
    -- Choose n = M * (N + 1)
    set t := N + 1 with ht_def
    refine ⟨M * t, by nlinarith, ?_⟩
    -- Goal is: 1/(M+1) ≤ (fun n => densityRatio S n) (M*t)
    -- which reduces to: 1/(M+1) ≤ densityRatio S (M*t)
    change 1 / ((↑M : ℝ) + 1) ≤ densityRatio S (M * t)
    -- densityRatio S (M*t) = card(filter (· ∈ S) (range(M*t+1))) / (M*t+1)
    unfold densityRatio
    -- Step 1: The AP {M*0+1, M*1+1, ..., M*(t-1)+1} gives card ≥ t
    have hcard : t ≤ (@Finset.filter _ (· ∈ S) (Classical.decPred (· ∈ S))
        (Finset.range (M * t + 1))).card := by
      -- Injection: (range t).image (M * · + 1) ⊆ filter, with card = t
      have hsub : (Finset.range t).image (fun i => M * i + 1) ⊆
          @Finset.filter _ (· ∈ S) (Classical.decPred (· ∈ S))
            (Finset.range (M * t + 1)) := by
        intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        rw [Finset.mem_range] at hi
        refine @Finset.mem_filter _ (· ∈ S) (Classical.decPred (· ∈ S)) _ _ |>.mpr
          ⟨Finset.mem_range.mpr
            (show M * i + 1 < M * t + 1 from
              Nat.add_lt_add_right (mul_lt_mul_of_pos_left hi hM_pos) 1),
           arithProg_subset_smoothBlockSet k i⟩
      calc t = (Finset.range t).card := (Finset.card_range t).symm
        _ = ((Finset.range t).image (fun i => M * i + 1)).card := by
            rw [Finset.card_image_of_injOn]
            intro a _ b _ hab
            have hmul : M * a = M * b := by linarith
            exact mul_left_cancel₀ (by omega : M ≠ 0) hmul
        _ ≤ (@Finset.filter _ (· ∈ S) (Classical.decPred (· ∈ S))
            (Finset.range (M * t + 1))).card :=
            Finset.card_le_card hsub
    -- Step 2: 1/(M+1) ≤ card/(M*t+1)
    -- Cross-multiply: M*t+1 ≤ card*(M+1)
    -- Since card ≥ t and t*(M+1) = M*t+t ≥ M*t+1 (t ≥ 1)
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < ↑M + 1)
        (by positivity : (0 : ℝ) < (↑(M * t + 1) : ℝ))]
    have ht_pos : (1 : ℝ) ≤ ↑t := by exact_mod_cast (show 1 ≤ t from by omega)
    have hcard_real : (↑t : ℝ) ≤
        (↑(@Finset.filter _ (· ∈ S) (Classical.decPred (· ∈ S))
          (Finset.range (M * t + 1))).card : ℝ) := by exact_mod_cast hcard
    push_cast [Nat.cast_mul]
    nlinarith
  · -- IsBoundedUnder (· ≤ ·) atTop (densityRatio S)
    exact densityRatio_isBoundedUnder S

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
axiom rosser_lower :
  ∀ ε : ℝ, 0 < ε → ∀ᶠ (k : ℕ) in atTop,
    (smoothThreshold k : ℝ) ≥ (k : ℝ) ^ (1/2 - ε)

/-- **Ford–Green–Konyagin–Maynard–Tao (2018).**
S(k) ≪ k · log log log k / (log log k · log log log log k). -/
axiom fgkmt_upper :
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ (k : ℕ) in atTop,
    (smoothThreshold k : ℝ) ≤ C * (k : ℝ) *
      Real.log (Real.log (Real.log (k : ℝ))) /
      (Real.log (Real.log (k : ℝ)) * Real.log (Real.log (Real.log (Real.log (k : ℝ)))))

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

/-- For k = 2, S(2) = 3: the AP n ≡ 2 mod 6 gives 3∣(n+1) and 2∣(n+2),
so x = 3 works with density 1/6. For x ≤ 2: consecutive integers can't
both have all prime factors ≤ 2, so density = 0. -/
axiom smooth_threshold_2 : smoothThreshold 2 = 3
