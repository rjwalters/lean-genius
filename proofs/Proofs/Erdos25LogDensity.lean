/-
  Erdős Problem #25: Logarithmic Density of Residue-Avoiding Sets

  Source: https://erdosproblems.com/25
  Status: OPEN

  Statement:
  Let n₁ < n₂ < ... be an arbitrary sequence of integers, each with an
  associated residue class aᵢ (mod nᵢ). Let A be the set of integers n
  such that for every i either n < nᵢ or n ≢ aᵢ (mod nᵢ).
  Must the logarithmic density of A exist?

  Key Definitions:
  - **Logarithmic density** of a set A ⊆ ℕ:
    lim_{N→∞} (1/log N) · Σ_{n ∈ A, n ≤ N} (1/n)

  - **Residue-avoiding set**: Given sequence {nᵢ} with residues {aᵢ},
    A = {n : ∀ i, n < nᵢ ∨ n ≢ aᵢ (mod nᵢ)}

  Background:
  - Davenport-Erdős theorem: For multiples of a sequence, log density = lower density
  - Natural density doesn't always exist; log density is more robust
  - Related to Problem 486 (very similar structure)

  What We Can Do:
  1. Define logarithmic density (upper, lower, and exact)
  2. Define the residue-avoiding set construction
  3. State the conjecture formally
  4. Prove basic properties of log density
  5. Show examples where log density exists

  Tags: number-theory, density, modular-arithmetic, erdos-problem
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic

namespace Erdos25

open Filter Finset Real BigOperators Classical

attribute [local instance] Classical.dec Classical.decPred

/- ## Part I: Logarithmic Density -/

/-- The harmonic sum Σ_{n=1}^{N} 1/n. Uses Mathlib's harmonic function. -/
noncomputable def harmonicSum (N : ℕ) : ℝ := harmonic N

/-- Our harmonicSum equals Mathlib's harmonic (coerced to ℝ). -/
theorem harmonicSum_eq_harmonic (N : ℕ) : harmonicSum N = harmonic N := rfl

/-- Key asymptotic: harmonic N / log N → 1 as N → ∞.
    This follows from harmonic N - log N → γ (Euler-Mascheroni). -/
theorem tendsto_harmonic_div_log :
    Tendsto (fun n : ℕ => harmonicSum n / Real.log (n : ℝ)) atTop (nhds 1) := by
  -- From tendsto_harmonic_sub_log: harmonic n - log n → γ
  -- We need: harmonic n / log n → 1
  -- Since log n → ∞ and (harmonic n - log n) → γ, we have harmonic n / log n → 1
  have h1 : Tendsto (fun n : ℕ => (↑(harmonic n) - Real.log (n : ℝ)) / Real.log (n : ℝ))
      atTop (nhds 0) := by
    apply Tendsto.div_atTop Real.tendsto_harmonic_sub_log
    exact Tendsto.comp tendsto_log_atTop tendsto_natCast_atTop_atTop
  have h2 : ∀ᶠ (n : ℕ) in atTop, Real.log (n : ℝ) ≠ 0 := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    have hn' : (1 : ℝ) < n := by exact_mod_cast hn
    exact Real.log_ne_zero_of_pos_of_ne_one (by positivity) (ne_of_gt hn')
  have h3 : (fun n : ℕ => 1 + (↑(harmonic n) - Real.log (n : ℝ)) / Real.log (n : ℝ)) =ᶠ[atTop]
      (fun n : ℕ => harmonicSum n / Real.log (n : ℝ)) := by
    filter_upwards [h2, eventually_gt_atTop 0] with n hlog hn0
    unfold harmonicSum
    field_simp [hlog]
    ring
  rw [show (1 : ℝ) = 1 + 0 by ring]
  exact Tendsto.congr' h3 (Tendsto.const_add 1 h1)

/-- The weighted count for logarithmic density: Σ_{n ∈ A, n ≤ N} 1/n. -/
noncomputable def logWeightedCount (A : Set ℕ) (N : ℕ) : ℝ :=
  ∑ n ∈ range (N + 1), if n ∈ A ∧ n ≠ 0 then (1 : ℝ) / n else 0

/-- The weighted count is non-negative (sum of non-negative terms). -/
theorem logWeightedCount_nonneg (A : Set ℕ) (N : ℕ) : 0 ≤ logWeightedCount A N := by
  unfold logWeightedCount
  apply Finset.sum_nonneg
  intro n _
  split_ifs
  · exact div_nonneg zero_le_one (Nat.cast_nonneg _)
  · exact le_refl _

/-- Monotonicity: if A ⊆ B then the weighted count of A is at most that of B. -/
theorem logWeightedCount_mono {A B : Set ℕ} (h : A ⊆ B) (N : ℕ) :
    logWeightedCount A N ≤ logWeightedCount B N := by
  unfold logWeightedCount
  apply Finset.sum_le_sum
  intro n _
  by_cases hA : n ∈ A ∧ n ≠ 0
  · have hB : n ∈ B ∧ n ≠ 0 := ⟨h hA.1, hA.2⟩
    simp [hA, hB]
  · simp only [if_neg hA]
    split_ifs
    · exact div_nonneg zero_le_one (Nat.cast_nonneg _)
    · exact le_refl _

/-- The logarithmic density ratio: (Σ_{n ∈ A, n ≤ N} 1/n) / log(N). -/
noncomputable def logDensityRatio (A : Set ℕ) (N : ℕ) : ℝ :=
  if N ≤ 1 then 0
  else logWeightedCount A N / Real.log N

/-- The density ratio is non-negative for all N. -/
theorem logDensityRatio_nonneg (A : Set ℕ) (N : ℕ) : 0 ≤ logDensityRatio A N := by
  unfold logDensityRatio
  split_ifs with h
  · exact le_refl _
  · apply div_nonneg (logWeightedCount_nonneg A N)
    exact le_of_lt (Real.log_pos (by exact_mod_cast (show 1 < N from by omega)))

/-- Monotonicity: if A ⊆ B then logDensityRatio A N ≤ logDensityRatio B N. -/
theorem logDensityRatio_mono {A B : Set ℕ} (h : A ⊆ B) (N : ℕ) :
    logDensityRatio A N ≤ logDensityRatio B N := by
  unfold logDensityRatio
  split_ifs with hN
  · exact le_refl _
  · have hlog : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N from by omega))
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (logWeightedCount_mono h N) (inv_nonneg.mpr hlog.le)

/-- A set A has logarithmic density d if lim_{N→∞} logDensityRatio(A, N) = d. -/
def HasLogDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (logDensityRatio A) atTop (nhds d)

/-- The upper logarithmic density (limsup). -/
noncomputable def upperLogDensity (A : Set ℕ) : ℝ :=
  limsup (logDensityRatio A) atTop

/-- The lower logarithmic density (liminf). -/
noncomputable def lowerLogDensity (A : Set ℕ) : ℝ :=
  liminf (logDensityRatio A) atTop

/- ## Part II: Residue-Avoiding Sets -/

/-- The set of integers avoiding residue class a_i (mod n_i) for all i where n ≤ n_i.
    A = {n : ∀ i, n < seq_n i ∨ n ≢ seq_a i (mod seq_n i)} -/
def residueAvoidingSet (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) : Set ℕ :=
  { x : ℕ | ∀ i, (x : ℤ) < seq_n i ∨ ¬((x : ℤ) ≡ seq_a i [ZMOD seq_n i]) }

/-- Alternative: For finite sequences. -/
def residueAvoidingSetFinite (moduli : List ℕ) (residues : List ℤ) : Set ℕ :=
  { x : ℕ | ∀ i : Fin moduli.length,
    (x : ℤ) < moduli[i] ∨ ¬((x : ℤ) ≡ residues[i]! [ZMOD moduli[i]]) }

/- ## Part III: The Main Conjecture -/

/-- **Erdős Problem #25** (Positive Formulation)

    For any strictly increasing sequence {n_i} of positive integers
    and any sequence {a_i} of residue classes, the logarithmic density
    of the residue-avoiding set must exist. -/
def erdos_25_positive : Prop :=
  ∀ (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ),
    (∀ i, 0 < seq_n i) →
    StrictMono seq_n →
    ∃ d, HasLogDensity (residueAvoidingSet seq_n seq_a) d

/-- **Erdős Problem #25** (Negative Formulation)

    There exists a strictly increasing sequence {n_i} and residue classes {a_i}
    such that the logarithmic density of the avoiding set does NOT exist. -/
def erdos_25_negative : Prop :=
  ∃ (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ),
    (∀ i, 0 < seq_n i) ∧
    StrictMono seq_n ∧
    ¬∃ d, HasLogDensity (residueAvoidingSet seq_n seq_a) d

/-- The official statement: exactly one of positive/negative holds. -/
theorem erdos_25_dichotomy : erdos_25_positive ↔ ¬erdos_25_negative := by
  constructor
  · intro hpos ⟨seq_n, seq_a, hpos_seq, hmono, hneg⟩
    exact hneg (hpos seq_n seq_a hpos_seq hmono)
  · intro hnneg seq_n seq_a hpos hmono
    by_contra hc
    exact hnneg ⟨seq_n, seq_a, hpos, hmono, hc⟩

/- ## Part IV: Basic Properties of Log Density -/

/-- The empty set has log density 0. -/
theorem logDensity_empty : HasLogDensity ∅ 0 := by
  unfold HasLogDensity logDensityRatio logWeightedCount
  simp only [Set.mem_empty_iff_false, false_and, ite_false, sum_const_zero, zero_div, ite_self]
  exact tendsto_const_nhds

/-- logWeightedCount of ℕ⁺ equals the harmonic sum.
    Technical: relates our sum over {1,...,N} to Mathlib's harmonic. -/
theorem logWeightedCount_full (N : ℕ) :
    logWeightedCount (Set.univ \ {0}) N = harmonicSum N := by
  unfold logWeightedCount harmonicSum
  simp only [Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff, true_and, ne_eq, and_self]
  -- Goal: ∑ n ∈ range (N+1), if ¬n = 0 then 1/n else 0 = harmonic N
  have hsub : Finset.Icc 1 N ⊆ Finset.range (N + 1) := by
    intro n hn; simp only [Finset.mem_Icc] at hn; simp only [Finset.mem_range]; omega
  have h_cond : ∑ n ∈ Finset.range (N + 1), (if ¬n = 0 then (1 : ℝ) / n else 0) =
                ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n := by
    rw [← Finset.sum_subset hsub]
    · apply Finset.sum_congr rfl
      intro n hn
      simp only [Finset.mem_Icc] at hn
      have hn' : ¬(n = 0) := by omega
      simp [hn']
    · intro n hn_range hn_not_Icc
      simp only [Finset.mem_range] at hn_range
      simp only [Finset.mem_Icc, not_and, not_le] at hn_not_Icc
      have h0 : n = 0 := by
        by_contra hne
        have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hne
        specialize hn_not_Icc this; omega
      simp [h0]
  rw [h_cond]
  -- Relate ∑ n ∈ Icc 1 N, 1/n to harmonic N via reindexing
  have himage : (Finset.range N).image (· + 1) = Finset.Icc 1 N := by
    ext x; simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨i, hi, rfl⟩; omega
    · intro ⟨h1, h2⟩; exact ⟨x - 1, by omega, by omega⟩
  rw [← himage, Finset.sum_image]
  · simp only [harmonic, one_div]; push_cast; rfl
  · intro x _ y _ h; have : x + 1 = y + 1 := h; omega

/-- The weighted count of any set is at most the harmonic sum. -/
theorem logWeightedCount_le_harmonicSum (A : Set ℕ) (N : ℕ) :
    logWeightedCount A N ≤ harmonicSum N := by
  rw [← logWeightedCount_full]
  unfold logWeightedCount
  apply Finset.sum_le_sum
  intro n _
  by_cases hA : n ∈ A ∧ n ≠ 0
  · -- n ∈ A and n ≠ 0: both ifs evaluate to 1/n
    have hU : n ∈ (Set.univ \ {0}) ∧ n ≠ 0 :=
      ⟨Set.mem_diff_singleton.mpr ⟨Set.mem_univ n, hA.2⟩, hA.2⟩
    simp [hA, hU]
  · -- n ∉ A or n = 0: first if is 0, second is ≥ 0
    simp only [if_neg hA]
    split_ifs
    · positivity
    · exact le_refl _

/-- The density ratio is bounded by harmonicSum N / log N. -/
theorem logDensityRatio_le_harmonic_ratio (A : Set ℕ) (N : ℕ) (hN : 2 ≤ N) :
    logDensityRatio A N ≤ harmonicSum N / Real.log (N : ℝ) := by
  unfold logDensityRatio
  simp only [show ¬(N ≤ 1) by omega, if_false]
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N from by omega))
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (logWeightedCount_le_harmonicSum A N) (inv_nonneg.mpr hlog.le)

/-- The full set of positive integers has log density 1.
    This uses that Σ_{n≤N} 1/n ~ log(N). -/
theorem logDensity_full : HasLogDensity (Set.univ \ {0}) 1 := by
  unfold HasLogDensity logDensityRatio
  have h_eq : (fun n : ℕ => harmonicSum n / Real.log (n : ℝ)) =ᶠ[atTop]
      (fun N => if N ≤ 1 then 0 else logWeightedCount (Set.univ \ {0}) N / Real.log N) := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    simp only [show ¬(n ≤ 1) by omega, if_false]
    rw [logWeightedCount_full]
  exact Tendsto.congr' h_eq tendsto_harmonic_div_log

/-- The density ratio is eventually bounded above: it converges to at most 1,
    so it is eventually below 2. (The previous axiom claiming ratio ≤ 1 for all
    N ≥ 2 was incorrect since H_N / log N > 1 for all finite N.) -/
theorem logDensityRatio_eventually_le_two (A : Set ℕ) :
    ∀ᶠ N in atTop, logDensityRatio A N ≤ 2 := by
  have h_tend := tendsto_harmonic_div_log
  have h_ev : ∀ᶠ n in atTop, harmonicSum n / Real.log (↑n) < 2 :=
    h_tend.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))
  filter_upwards [h_ev, eventually_ge_atTop 2] with n hn hN
  exact le_trans (logDensityRatio_le_harmonic_ratio A n hN) (le_of_lt hn)

/-- The density ratio is bounded in [0, 2] for all sufficiently large N. -/
theorem logDensityRatio_bounded_eventually (A : Set ℕ) :
    ∀ᶠ N in atTop, 0 ≤ logDensityRatio A N ∧ logDensityRatio A N ≤ 2 := by
  filter_upwards [logDensityRatio_eventually_le_two A] with N hN
  exact ⟨logDensityRatio_nonneg A N, hN⟩

/-- logDensityRatio is bounded under atTop (needed for limsup arguments). -/
theorem logDensityRatio_isBoundedUnder (A : Set ℕ) :
    Filter.IsBoundedUnder (· ≤ ·) atTop (logDensityRatio A) :=
  ⟨2, logDensityRatio_eventually_le_two A⟩

/-- logDensityRatio is cobounded under atTop (needed for limsup arguments). -/
theorem logDensityRatio_isCoboundedUnder (A : Set ℕ) :
    Filter.IsCoboundedUnder (· ≤ ·) atTop (logDensityRatio A) := by
  use 0
  intro a ha
  by_contra hlt
  push_neg at hlt
  simp only [Filter.eventually_map] at ha
  obtain ⟨N, hN⟩ := ha.exists
  linarith [logDensityRatio_nonneg A N]

/-- logDensityRatio is bounded below under atTop (needed for tendsto arguments). -/
theorem logDensityRatio_isBoundedUnder_ge (A : Set ℕ) :
    Filter.IsBoundedUnder (· ≥ ·) atTop (logDensityRatio A) := by
  refine ⟨0, ?_⟩
  simp only [Filter.eventually_map]
  exact Eventually.of_forall (fun N => logDensityRatio_nonneg A N)

/-- Monotonicity of upper log density: if A ⊆ B then
    upperLogDensity A ≤ upperLogDensity B. -/
theorem upperLogDensity_mono {A B : Set ℕ} (h : A ⊆ B) :
    upperLogDensity A ≤ upperLogDensity B := by
  unfold upperLogDensity
  exact Filter.limsup_le_limsup
    (Eventually.of_forall (fun N => logDensityRatio_mono h N))
    (logDensityRatio_isCoboundedUnder A)
    (logDensityRatio_isBoundedUnder B)

/-- Log density exists iff upper and lower log densities both equal d.
    Forward: Tendsto → limsup = liminf = d (via Mathlib).
    Backward: limsup = liminf = d → Tendsto (standard characterization). -/
theorem hasLogDensity_iff_eq (A : Set ℕ) (d : ℝ) :
    HasLogDensity A d ↔ upperLogDensity A = d ∧ lowerLogDensity A = d := by
  unfold HasLogDensity upperLogDensity lowerLogDensity
  constructor
  · intro h
    exact ⟨h.limsup_eq, h.liminf_eq⟩
  · intro ⟨hsup, hinf⟩
    exact tendsto_of_le_liminf_of_limsup_le
      (le_of_eq hinf.symm) (le_of_eq hsup)
      (logDensityRatio_isBoundedUnder A)
      (logDensityRatio_isBoundedUnder_ge A)

/- ## Part V: Examples -/

/-- logWeightedCount increments by the conditional term at N+1. -/
private theorem logWeightedCount_succ (A : Set ℕ) (N : ℕ) :
    logWeightedCount A (N + 1) = logWeightedCount A N +
    (if (N + 1) ∈ A ∧ (N + 1) ≠ 0 then (1 : ℝ) / (↑(N + 1)) else 0) := by
  simp only [logWeightedCount, Finset.sum_range_succ]

/-- harmonicSum stepping in ℝ. -/
private theorem harmonicSum_succ' (k : ℕ) :
    harmonicSum (k + 1) = harmonicSum k + 1 / ((↑k : ℝ) + 1) := by
  show (↑(harmonic (k + 1)) : ℝ) = ↑(harmonic k) + 1 / (↑k + 1)
  rw [harmonic_succ]
  push_cast
  ring

/-- The weighted count of even positive numbers equals half the harmonic sum of ⌊N/2⌋.
    Proof: induction on N. Even steps add 1/(2k) = (1/2)·(1/k), odd steps add nothing. -/
theorem logWeightedCount_evens (N : ℕ) :
    logWeightedCount {n : ℕ | Even n ∧ n ≠ 0} N = (1 / 2 : ℝ) * harmonicSum (N / 2) := by
  induction N with
  | zero => simp [logWeightedCount, harmonicSum, harmonic_zero]
  | succ n ih =>
    rw [logWeightedCount_succ]
    by_cases heven : Even (n + 1)
    · -- n+1 is even: contributes 1/(n+1), and (n+1)/2 = n/2 + 1
      have hmem : (n + 1) ∈ {m : ℕ | Even m ∧ m ≠ 0} ∧ (n + 1) ≠ 0 :=
        ⟨⟨heven, Nat.succ_ne_zero n⟩, Nat.succ_ne_zero n⟩
      rw [if_pos hmem, ih]
      have hdiv : (n + 1) / 2 = n / 2 + 1 := by
        obtain ⟨k, hk⟩ := heven; omega
      rw [hdiv, harmonicSum_succ', mul_add]
      congr 1
      -- 1 / ↑(n+1) = 1/2 * (1 / (↑(n/2) + 1))
      have h2k : n + 1 = 2 * (n / 2 + 1) := by omega
      have hN : (↑(n + 1) : ℝ) = 2 * ((↑(n / 2) : ℝ) + 1) := by exact_mod_cast h2k
      rw [hN]; field_simp
    · -- n+1 is odd: no contribution, (n+1)/2 = n/2
      have hmem : ¬((n + 1) ∈ {m : ℕ | Even m ∧ m ≠ 0} ∧ (n + 1) ≠ 0) := by
        intro ⟨⟨he, _⟩, _⟩; exact heven he
      rw [if_neg hmem, add_zero, ih]
      have hne : Even n := by rwa [Nat.even_add_one, not_not] at heven
      have hdiv : (n + 1) / 2 = n / 2 := by obtain ⟨k, hk⟩ := hne; omega
      rw [hdiv]

/-- ⌊N/2⌋ → ∞ as N → ∞. -/
private theorem tendsto_nat_div_two : Tendsto (fun n : ℕ => n / 2) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  exact ⟨2 * b + 1, fun n hn => by omega⟩

/-- log(⌊N/2⌋) / log(N) → 1 as N → ∞.
    Proof: squeeze between 1 - log(3)/log(N) and 1. -/
private theorem tendsto_log_half_div_log :
    Tendsto (fun N : ℕ => Real.log (↑(N / 2) : ℝ) / Real.log (↑N)) atTop (nhds 1) := by
  have hlog_atTop : Tendsto (fun N : ℕ => Real.log (↑N : ℝ)) atTop atTop :=
    Tendsto.comp tendsto_log_atTop tendsto_natCast_atTop_atTop
  -- Write as 1 - correction, show correction → 0
  rw [show (1 : ℝ) = 1 - 0 from by ring]
  have h_eq : (fun N : ℕ => 1 - (Real.log (↑N) - Real.log (↑(N / 2) : ℝ)) / Real.log (↑N)) =ᶠ[atTop]
      (fun N : ℕ => Real.log (↑(N / 2) : ℝ) / Real.log (↑N)) := by
    filter_upwards [eventually_gt_atTop 1] with N hN
    have hlog : Real.log (↑N : ℝ) ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by positivity) (ne_of_gt (by exact_mod_cast hN))
    field_simp; ring
  apply Filter.Tendsto.congr' h_eq
  apply Tendsto.sub tendsto_const_nhds
  -- (log N - log(N/2)) / log N → 0
  -- Squeeze: ‖f(N)‖ ≤ log(3)/log(N) → 0
  have h_norm_bound : ∀ᶠ (N : ℕ) in atTop,
      ‖(Real.log (↑N : ℝ) - Real.log (↑(N / 2) : ℝ)) / Real.log (↑N)‖ ≤
      Real.log 3 / Real.log (↑N) := by
    filter_upwards [eventually_ge_atTop (4 : ℕ)] with N (hN : 4 ≤ N)
    have hN2_pos : (0 : ℝ) < ↑(N / 2) := by exact_mod_cast (show 0 < N / 2 by omega)
    have hNr_pos : (0 : ℝ) < ↑N := by exact_mod_cast (show 0 < N by omega)
    have hlog_pos : 0 < Real.log (↑N : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have h_sub_nn : 0 ≤ Real.log (↑N : ℝ) - Real.log (↑(N / 2) : ℝ) := by
      apply sub_nonneg.mpr; apply Real.log_le_log hN2_pos
      exact_mod_cast (Nat.div_le_self N 2)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg h_sub_nn hlog_pos.le)]
    -- a/c ≤ b/c via a * c⁻¹ ≤ b * c⁻¹
    simp only [div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hlog_pos.le)
    -- log N - log(N/2) ≤ log 3
    calc Real.log (↑N : ℝ) - Real.log (↑(N / 2) : ℝ)
        = Real.log ((↑N : ℝ) / ↑(N / 2)) :=
          (Real.log_div (ne_of_gt hNr_pos) (ne_of_gt hN2_pos)).symm
      _ ≤ Real.log 3 := by
          apply Real.log_le_log (div_pos hNr_pos hN2_pos)
          have h3 : (↑N : ℝ) ≤ 3 * ↑(N / 2) := by exact_mod_cast (show N ≤ 3 * (N / 2) by omega)
          calc (↑N : ℝ) / ↑(N / 2) = ↑N * (↑(N / 2))⁻¹ := div_eq_mul_inv _ _
            _ ≤ 3 * ↑(N / 2) * (↑(N / 2))⁻¹ :=
                mul_le_mul_of_nonneg_right h3 (inv_nonneg.mpr hN2_pos.le)
            _ = 3 := by field_simp [ne_of_gt hN2_pos]
  exact squeeze_zero_norm' h_norm_bound
    (Tendsto.div_atTop tendsto_const_nhds hlog_atTop)

/-- harmonicSum(⌊N/2⌋) / log(N) → 1 as N → ∞.
    Proof: factor as (harmonicSum(N/2) / log(N/2)) · (log(N/2) / log(N)), both → 1. -/
private theorem tendsto_harmonicSum_half_div_log :
    Tendsto (fun N : ℕ => harmonicSum (N / 2) / Real.log (↑N)) atTop (nhds 1) := by
  have hfactor : (fun N : ℕ => harmonicSum (N / 2) / Real.log (↑(N / 2) : ℝ) *
      (Real.log (↑(N / 2) : ℝ) / Real.log (↑N))) =ᶠ[atTop]
      (fun N : ℕ => harmonicSum (N / 2) / Real.log (↑N)) := by
    filter_upwards [eventually_ge_atTop 6] with N hN
    have hlog : Real.log (↑(N / 2) : ℝ) ≠ 0 := by
      have h2 : 1 < (↑(N / 2) : ℝ) := by exact_mod_cast (show 1 < N / 2 by omega)
      exact ne_of_gt (Real.log_pos h2)
    field_simp
  rw [show (1 : ℝ) = 1 * 1 from by ring]
  exact Filter.Tendsto.congr' hfactor
    (Tendsto.mul
      (tendsto_harmonic_div_log.comp tendsto_nat_div_two)
      tendsto_log_half_div_log)

/-- **Even numbers have log density 1/2**.
    Proof: logWeightedCount(evens, N) = (1/2) · H_{⌊N/2⌋} and H_{⌊N/2⌋}/log(N) → 1. -/
theorem logDensity_evens : HasLogDensity {n : ℕ | Even n ∧ n ≠ 0} (1/2) := by
  unfold HasLogDensity logDensityRatio
  have h_eq : (fun N : ℕ => (1 / 2 : ℝ) * (harmonicSum (N / 2) / Real.log (↑N))) =ᶠ[atTop]
      (fun N => if N ≤ 1 then (0 : ℝ)
        else logWeightedCount {n : ℕ | Even n ∧ n ≠ 0} N / Real.log (↑N)) := by
    filter_upwards [eventually_gt_atTop 1] with N hN
    simp only [show ¬(N ≤ 1) by omega, ↓reduceIte]
    rw [logWeightedCount_evens]; ring
  have h_tend : Tendsto (fun N : ℕ => (1 / 2 : ℝ) * (harmonicSum (N / 2) / Real.log (↑N)))
      atTop (nhds (1 / 2 : ℝ)) := by
    have h := Tendsto.mul (tendsto_const_nhds (x := (1 / 2 : ℝ)))
      tendsto_harmonicSum_half_div_log
    simp only [mul_one] at h
    exact h
  exact Filter.Tendsto.congr' h_eq h_tend

/-- Splitting: logWeightedCount of a disjoint union equals the sum of parts. -/
theorem logWeightedCount_union_disjoint {A B : Set ℕ} (h : Disjoint A B) (N : ℕ) :
    logWeightedCount (A ∪ B) N = logWeightedCount A N + logWeightedCount B N := by
  unfold logWeightedCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : n = 0
  · subst hn; simp
  · by_cases hA : n ∈ A
    · have hB : n ∉ B := fun hb => Set.disjoint_left.mp h hA hb
      rw [if_pos ⟨Set.mem_union_left B hA, hn⟩, if_pos ⟨hA, hn⟩,
          if_neg (show ¬(n ∈ B ∧ n ≠ 0) from fun ⟨hb, _⟩ => hB hb)]
      ring
    · by_cases hB : n ∈ B
      · rw [if_pos ⟨Set.mem_union_right A hB, hn⟩,
            if_neg (show ¬(n ∈ A ∧ n ≠ 0) from fun ⟨ha, _⟩ => hA ha),
            if_pos ⟨hB, hn⟩]
        ring
      · rw [if_neg (show ¬(n ∈ (A ∪ B) ∧ n ≠ 0) from fun ⟨hab, _⟩ => hab.elim hA hB),
            if_neg (show ¬(n ∈ A ∧ n ≠ 0) from fun ⟨ha, _⟩ => hA ha),
            if_neg (show ¬(n ∈ B ∧ n ≠ 0) from fun ⟨hb, _⟩ => hB hb)]
        ring

/-- Every positive natural number is either even or odd. -/
private theorem even_odd_partition :
    (Set.univ : Set ℕ) \ {0} = {n : ℕ | Even n ∧ n ≠ 0} ∪ {n : ℕ | Odd n} := by
  ext n
  simp only [Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff, true_and,
    Set.mem_union, Set.mem_setOf_eq]
  constructor
  · intro hne
    rcases Nat.even_or_odd n with he | ho
    · exact Or.inl ⟨he, hne⟩
    · exact Or.inr ho
  · rintro (⟨_, hne⟩ | ho)
    · exact hne
    · obtain ⟨k, hk⟩ := ho; omega

/-- Even and odd positive numbers are disjoint. -/
private theorem even_odd_disjoint :
    Disjoint {n : ℕ | Even n ∧ n ≠ 0} {n : ℕ | Odd n} := by
  rw [Set.disjoint_left]
  intro n ⟨he, _⟩ ho
  obtain ⟨k, hk⟩ := he; obtain ⟨j, hj⟩ := ho; omega

/-- Odd numbers have log density 1/2.
    Proved from logDensity_full and logDensity_evens via complementation:
    {evens⁺} ∪ {odds} = ℕ⁺, so density(odds) = 1 - 1/2 = 1/2.
    (Previously axiomatized; now derived.) -/
theorem logDensity_odds : HasLogDensity {n : ℕ | Odd n} (1/2) := by
  -- Strategy: show odds = ℕ⁺ \ evens⁺, then use density subtraction
  have hfull := logDensity_full
  have hevens := logDensity_evens
  have hunion := even_odd_partition
  have hdisj := even_odd_disjoint
  -- logDensityRatio of odds = logDensityRatio of ℕ⁺ - logDensityRatio of evens⁺
  -- because logDensityRatio of (A ∪ B) = logDensityRatio A + logDensityRatio B (for N > 1)
  suffices h : HasLogDensity {n : ℕ | Odd n} (1 - 1/2) by
    norm_num at h; exact h
  unfold HasLogDensity at *
  -- Eventually, the ratios split
  have hev_split : ∀ᶠ N in atTop,
      logDensityRatio {n : ℕ | Odd n} N =
      logDensityRatio (Set.univ \ {0}) N - logDensityRatio {n | Even n ∧ n ≠ 0} N := by
    filter_upwards [eventually_gt_atTop 1] with N hN
    have h1 : ¬(N ≤ 1) := by omega
    unfold logDensityRatio
    simp only [h1, ↓reduceIte]
    rw [hunion, logWeightedCount_union_disjoint hdisj N, add_div]
    ring
  refine Filter.Tendsto.congr' ?_ (Tendsto.sub hfull hevens)
  exact hev_split.mono (fun N hN => hN.symm)

/-- ⌊N/m⌋ → ∞ as N → ∞ for any fixed m ≥ 1. -/
private theorem tendsto_nat_div_m (m : ℕ) (hm : 1 ≤ m) :
    Tendsto (fun n : ℕ => n / m) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b; exact ⟨m * b, fun n hn => by omega⟩

/-- log(⌊N/m⌋) / log(N) → 1 as N → ∞ for any fixed m ≥ 2.
    Proof: squeeze between 1 - log(2m)/log(N) and 1. -/
private theorem tendsto_log_div_m_div_log (m : ℕ) (hm : 2 ≤ m) :
    Tendsto (fun N : ℕ => Real.log (↑(N / m) : ℝ) / Real.log (↑N)) atTop (nhds 1) := by
  have hlog_atTop : Tendsto (fun N : ℕ => Real.log (↑N : ℝ)) atTop atTop :=
    Tendsto.comp tendsto_log_atTop tendsto_natCast_atTop_atTop
  rw [show (1 : ℝ) = 1 - 0 from by ring]
  have h_eq : (fun N : ℕ => 1 - (Real.log (↑N) - Real.log (↑(N / m) : ℝ)) / Real.log (↑N))
      =ᶠ[atTop] (fun N : ℕ => Real.log (↑(N / m) : ℝ) / Real.log (↑N)) := by
    filter_upwards [eventually_gt_atTop 1] with N hN
    have hlog : Real.log (↑N : ℝ) ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by positivity) (ne_of_gt (by exact_mod_cast hN))
    field_simp; ring
  apply Filter.Tendsto.congr' h_eq
  apply Tendsto.sub tendsto_const_nhds
  apply squeeze_zero_norm'
  · filter_upwards [eventually_ge_atTop (2 * m)] with N (hN : 2 * m ≤ N)
    have hNm_pos : (0 : ℝ) < ↑(N / m) := by exact_mod_cast (show 0 < N / m by omega)
    have hNr_pos : (0 : ℝ) < ↑N := by exact_mod_cast (show 0 < N by omega)
    have hlog_pos : 0 < Real.log (↑N : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have h_sub_nn : 0 ≤ Real.log (↑N : ℝ) - Real.log (↑(N / m) : ℝ) := by
      apply sub_nonneg.mpr; apply Real.log_le_log hNm_pos
      exact_mod_cast (Nat.div_le_self N m)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg h_sub_nn hlog_pos.le)]
    simp only [div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hlog_pos.le)
    calc Real.log (↑N : ℝ) - Real.log (↑(N / m) : ℝ)
        = Real.log ((↑N : ℝ) / ↑(N / m)) :=
          (Real.log_div (ne_of_gt hNr_pos) (ne_of_gt hNm_pos)).symm
      _ ≤ Real.log (2 * m) := by
          apply Real.log_le_log (div_pos hNr_pos hNm_pos)
          -- N/(N/m) ≤ 2m: since N ≤ 2m * (N/m), dividing by N/m gives ≤ 2m
          rw [div_le_iff hNm_pos]
          push_cast [Nat.cast_le]
          -- Need: ↑N ≤ 2 * ↑m * ↑(N / m) in ℝ, from ℕ inequality
          have hnat : N ≤ 2 * m * (N / m) := by
            have := Nat.div_add_mod N m
            have := Nat.mod_lt N (show 0 < m by omega)
            nlinarith [Nat.le_div_iff_mul_le (show 0 < m by omega) |>.mpr (by omega : 2 * m ≤ N)]
          exact_mod_cast hnat
  · exact Tendsto.div_atTop tendsto_const_nhds hlog_atTop

/-- H_{⌊N/m⌋} / log(N) → 1 as N → ∞.
    Factors as (H_{N/m} / log(N/m)) · (log(N/m) / log(N)), both → 1. -/
private theorem tendsto_harmonicSum_div_m_div_log (m : ℕ) (hm : 2 ≤ m) :
    Tendsto (fun N : ℕ => harmonicSum (N / m) / Real.log (↑N)) atTop (nhds 1) := by
  have hfactor : (fun N : ℕ => harmonicSum (N / m) / Real.log (↑(N / m) : ℝ) *
      (Real.log (↑(N / m) : ℝ) / Real.log (↑N))) =ᶠ[atTop]
      (fun N : ℕ => harmonicSum (N / m) / Real.log (↑N)) := by
    filter_upwards [eventually_ge_atTop (2 * m + 2)] with N hN
    have hlog : Real.log (↑(N / m) : ℝ) ≠ 0 := by
      have h2 : 1 < (↑(N / m) : ℝ) := by exact_mod_cast (show 1 < N / m by omega)
      exact ne_of_gt (Real.log_pos h2)
    field_simp
  rw [show (1 : ℝ) = 1 * 1 from by ring]
  exact Filter.Tendsto.congr' hfactor
    (Tendsto.mul
      (tendsto_harmonic_div_log.comp (tendsto_nat_div_m m (by omega)))
      (tendsto_log_div_m_div_log m hm))

/-- The weighted count of multiples of m equals (1/m) · H_{⌊N/m⌋}. -/
theorem logWeightedCount_multiples (m : ℕ) (hm : 1 ≤ m) (N : ℕ) :
    logWeightedCount {n : ℕ | m ∣ n ∧ n ≠ 0} N = (1 / (m : ℝ)) * harmonicSum (N / m) := by
  induction N with
  | zero => simp [logWeightedCount, harmonicSum, harmonic_zero]
  | succ n ih =>
    rw [logWeightedCount_succ]
    by_cases hdvd : m ∣ (n + 1)
    · have hmem : (n + 1) ∈ {k : ℕ | m ∣ k ∧ k ≠ 0} ∧ (n + 1) ≠ 0 :=
        ⟨⟨hdvd, Nat.succ_ne_zero n⟩, Nat.succ_ne_zero n⟩
      rw [if_pos hmem, ih]
      have hdiv : (n + 1) / m = n / m + 1 := by
        rw [Nat.succ_div n m, if_pos hdvd]
      rw [hdiv, harmonicSum_succ', mul_add]
      congr 1
      obtain ⟨k, hk⟩ := hdvd
      have hk_pos : 0 < k := by omega
      have h_eq : (↑(n + 1) : ℝ) = (m : ℝ) * ((↑(n / m) : ℝ) + 1) := by
        have : n / m + 1 = k := by rw [Nat.succ_div n m, if_pos hdvd]; ring
        rw [this]; push_cast; linarith [hk]
      rw [h_eq]; field_simp
    · have hmem : ¬((n + 1) ∈ {k : ℕ | m ∣ k ∧ k ≠ 0} ∧ (n + 1) ≠ 0) := by
        intro ⟨⟨hd, _⟩, _⟩; exact hdvd hd
      rw [if_neg hmem, add_zero, ih]
      have hdiv : (n + 1) / m = n / m := by
        rw [Nat.succ_div n m, if_neg hdvd, add_zero]
      rw [hdiv]

/-- Multiples and non-multiples of m partition ℕ⁺. -/
private theorem multiples_partition (m : ℕ) (hm : 1 ≤ m) :
    (Set.univ : Set ℕ) \ {0} = {n : ℕ | n ≠ 0 ∧ m ∣ n} ∪ {n : ℕ | n ≠ 0 ∧ ¬(m ∣ n)} := by
  ext n; simp only [Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff, true_and,
    Set.mem_union, Set.mem_setOf_eq]
  tauto

/-- Multiples and non-multiples of m are disjoint. -/
private theorem multiples_disjoint (m : ℕ) :
    Disjoint {n : ℕ | n ≠ 0 ∧ m ∣ n} {n : ℕ | n ≠ 0 ∧ ¬(m ∣ n)} := by
  rw [Set.disjoint_left]; intro n ⟨_, hd⟩ ⟨_, hnd⟩; exact hnd hd

/-- **Numbers ≢ 0 (mod m) have log density (m-1)/m**.
    Proof: multiples of m have density 1/m (via weighted count = (1/m)·H_{⌊N/m⌋}),
    so non-multiples have density 1 - 1/m = (m-1)/m by complementation. -/
theorem logDensity_avoid_one_residue (m : ℕ) (hm : 2 ≤ m) :
    HasLogDensity {n : ℕ | n ≠ 0 ∧ ¬(m ∣ n)} ((m - 1 : ℝ) / m) := by
  -- First prove multiples of m have density 1/m
  have h_mult : HasLogDensity {n : ℕ | n ≠ 0 ∧ m ∣ n} (1 / m) := by
    unfold HasLogDensity logDensityRatio
    have h_eq : (fun N : ℕ => (1 / (m : ℝ)) * (harmonicSum (N / m) / Real.log (↑N)))
        =ᶠ[atTop] (fun N => if N ≤ 1 then (0 : ℝ)
          else logWeightedCount {n : ℕ | n ≠ 0 ∧ m ∣ n} N / Real.log (↑N)) := by
      filter_upwards [eventually_gt_atTop 1] with N hN
      simp only [show ¬(N ≤ 1) by omega, ↓reduceIte]
      -- Swap the set to match logWeightedCount_multiples
      have hset : {n : ℕ | n ≠ 0 ∧ m ∣ n} = {n : ℕ | m ∣ n ∧ n ≠ 0} := by ext; tauto
      rw [hset, logWeightedCount_multiples m (by omega) N]; ring
    exact Filter.Tendsto.congr' h_eq
      (show Tendsto (fun N => (1 / (m : ℝ)) * (harmonicSum (N / m) / Real.log (↑N)))
          atTop (nhds (1 / m)) from by
        have h := Tendsto.mul (tendsto_const_nhds (x := (1 / (m : ℝ))))
          (tendsto_harmonicSum_div_m_div_log m hm)
        simp only [mul_one] at h; exact h)
  -- Then use complement splitting: density(non-mult) = 1 - 1/m = (m-1)/m
  have hfull := logDensity_full
  have hunion := multiples_partition m (by omega)
  have hdisj := multiples_disjoint m
  suffices h : HasLogDensity {n : ℕ | n ≠ 0 ∧ ¬(m ∣ n)} (1 - 1 / (m : ℝ)) by
    convert h using 1; field_simp
  unfold HasLogDensity at *
  have hev_split : ∀ᶠ N in atTop,
      logDensityRatio {n : ℕ | n ≠ 0 ∧ ¬(m ∣ n)} N =
      logDensityRatio (Set.univ \ {0}) N - logDensityRatio {n | n ≠ 0 ∧ m ∣ n} N := by
    filter_upwards [eventually_gt_atTop 1] with N hN
    have h1 : ¬(N ≤ 1) := by omega
    unfold logDensityRatio
    simp only [h1, ↓reduceIte]
    rw [hunion, logWeightedCount_union_disjoint hdisj N, add_div]; ring
  exact Filter.Tendsto.congr' (hev_split.mono (fun N hN => hN.symm))
    (Tendsto.sub hfull h_mult)

/- ## Part VI: Connection to Natural Density -/

/-- Natural (asymptotic) density: lim_{N→∞} |A ∩ [1,N]| / N. -/
noncomputable def HasNaturalDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun N : ℕ => (Finset.filter (· ∈ A) (range (N + 1))).card / (N : ℝ)) atTop (nhds d)

/-- **Axiom: Natural density implies log density**.

If natural density exists, then log density exists and equals it.
(The converse is false in general.)

**Proof sketch**: If |A ∩ [1,N]| / N → d, then
Σ_{n ∈ A, n ≤ N} 1/n ≈ d · H_N by summation by parts.
So logDensityRatio → d · H_N / log N → d.

**Proof status**: HARD (~100 lines) - requires summation by parts or
Cesàro-type argument relating counting function to weighted sum. -/
axiom naturalDensity_implies_logDensity (A : Set ℕ) (d : ℝ) :
    HasNaturalDensity A d → HasLogDensity A d

/-- **Axiom: Log density is strictly weaker than natural density**.

There exist sets with log density but no natural density.
Example: {n : n has more 1's than 0's in binary}.

**Proof status**: HARD (~150 lines) - requires constructing a specific set
and proving its oscillatory natural density but convergent log density. -/
axiom exists_logDensity_no_naturalDensity :
    ∃ A : Set ℕ, (∃ d, HasLogDensity A d) ∧ ¬∃ d, HasNaturalDensity A d

/- ## Part VII: Davenport-Erdős Theorem -/

/-- For the set of multiples of a sequence, log density = lower natural density.
    This is a known theorem that motivates the study of log density. -/
axiom davenport_erdos :
  ∀ (seq : ℕ → ℕ), (∀ i, 0 < seq i) →
  let multiples := {n : ℕ | ∃ i, seq i ∣ n}
  ∃ d, HasLogDensity multiples d

#check erdos_25_positive
#check erdos_25_negative
#check HasLogDensity
#check residueAvoidingSet

end Erdos25
