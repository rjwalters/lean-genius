/-
Erdős Problem #726 — Residues in the Upper Half Interval

**Conjecture (Erdős–Graham–Ruzsa–Straus, 1975):**
As n → ∞ over integers,
  Σ_{p ≤ n, n mod p ∈ (p/2, p)} 1/p ~ (log log n) / 2

Here n mod p ∈ (p/2, p) means the least nonneg. residue r of n mod p
satisfies p/2 < r < p.

By Mertens' theorem, Σ_{p ≤ n} 1/p ~ log log n. The conjecture says
that the "upper half" residues contribute exactly half of Mertens' sum.

**Status:** OPEN

**Reference:** erdosproblems.com/726, EGRS75
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-
## Core Definitions
-/

/-- Whether n mod p lies in the "upper half" interval (p/2, p).
    Equivalently, the least nonneg. residue r = n % p satisfies p/2 < r. -/
def isUpperHalfResidue (n p : ℕ) : Prop :=
  p / 2 < n % p

/-- Decidable instance for isUpperHalfResidue. -/
instance isUpperHalfResidueDecidable (n p : ℕ) : Decidable (isUpperHalfResidue n p) :=
  inferInstanceAs (Decidable (p / 2 < n % p))

/-- The primes up to n. -/
noncomputable def primesUpTo (n : ℕ) : Finset ℕ :=
  (Finset.Icc 2 n).filter Nat.Prime

/-- The weighted sum: Σ_{p ≤ n, p prime, n mod p ∈ (p/2, p)} 1/p. -/
noncomputable def upperHalfSum (n : ℕ) : ℝ :=
  (Finset.Icc 2 n).filter (fun p => p.Prime ∧ isUpperHalfResidue n p)
    |>.sum (fun p => (1 : ℝ) / p)

/-- The "lower half" sum: residues in [0, p/2]. -/
noncomputable def lowerHalfSum (n : ℕ) : ℝ :=
  (Finset.Icc 2 n).filter (fun p => p.Prime ∧ ¬isUpperHalfResidue n p)
    |>.sum (fun p => (1 : ℝ) / p)

/-- The full Mertens sum over primes ≤ n. -/
noncomputable def mertensSum (n : ℕ) : ℝ :=
  (primesUpTo n).sum (fun p => (1 : ℝ) / p)

/-
## Main Conjecture (OPEN)
-/

/-- Mertens' theorem: Σ_{p ≤ n} 1/p ~ log log n. -/
axiom mertens_theorem :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      |mertensSum n - Real.log (Real.log n)| < ε

/-- **Erdős–Graham–Ruzsa–Straus Conjecture (1975):**
    The sum over primes p ≤ n where n mod p ∈ (p/2, p) is
    asymptotically (log log n)/2. -/
axiom erdos_726_conjecture :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      |upperHalfSum n - Real.log (Real.log n) / 2| < ε

/-
## Basic Residue Properties
-/

/-- The residue n % p is always in [0, p). -/
theorem residue_bound (n p : ℕ) (hp : p > 0) : n % p < p :=
  Nat.mod_lt n hp

/-- 0 is not an upper half residue for any prime p ≥ 2. -/
theorem zero_not_upper_half (p : ℕ) (hp : p ≥ 2) : ¬isUpperHalfResidue 0 p := by
  unfold isUpperHalfResidue
  simp
  omega

/-- If n % p = 0 (i.e., p | n), then n is not an upper half residue. -/
theorem dvd_not_upper_half (n p : ℕ) (h : p ∣ n) : ¬isUpperHalfResidue n p := by
  unfold isUpperHalfResidue
  rw [Nat.dvd_iff_mod_eq_zero.mp h]
  omega

/-- For prime p ≥ 3, the upper half (p/2, p) has exactly ⌊(p-1)/2⌋ elements. -/
theorem upper_half_count (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    ((Finset.Icc 1 (p - 1)).filter (fun r => p / 2 < r)).card = (p - 1) / 2 := by
  have hp_odd : p % 2 = 1 := by
    rcases Nat.even_or_odd p with ⟨k, hk⟩ | ⟨k, hk⟩
    · have := hp.eq_one_or_self_of_dvd 2 ⟨k, by omega⟩; omega
    · omega
  have h_eq : (Finset.Icc 1 (p - 1)).filter (fun r => p / 2 < r) =
      Finset.Icc (p / 2 + 1) (p - 1) := by
    ext r; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [h_eq, Finset.Nat.card_Icc]
  omega

/-- For p = 2, no integer is in the upper half: n % 2 ∈ {0, 1} and
    2/2 = 1, so the upper half condition 1 < n%2 is never met. -/
theorem two_not_upper_half_residue (n : ℕ) : ¬isUpperHalfResidue n 2 := by
  unfold isUpperHalfResidue
  have : n % 2 < 2 := Nat.mod_lt n (by omega)
  omega

/-
## Sum Partition Properties
-/

/-- The upper half sum is nonneg. -/
theorem upperHalfSum_nonneg (n : ℕ) : 0 ≤ upperHalfSum n := by
  unfold upperHalfSum
  apply Finset.sum_nonneg
  intro p _
  positivity

/-- The lower half sum is nonneg. -/
theorem lowerHalfSum_nonneg (n : ℕ) : 0 ≤ lowerHalfSum n := by
  unfold lowerHalfSum
  apply Finset.sum_nonneg
  intro p _
  positivity

/-- The Mertens sum is nonneg. -/
theorem mertensSum_nonneg (n : ℕ) : 0 ≤ mertensSum n := by
  unfold mertensSum
  apply Finset.sum_nonneg
  intro p _
  positivity

/-- The upper half sum is at most the Mertens sum. -/
theorem upperHalfSum_le_mertens (n : ℕ) :
    upperHalfSum n ≤ mertensSum n := by
  unfold upperHalfSum mertensSum primesUpTo
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1⟩
  · intro p _ _
    positivity

/-- The lower half sum is at most the Mertens sum. -/
theorem lowerHalfSum_le_mertens (n : ℕ) :
    lowerHalfSum n ≤ mertensSum n := by
  unfold lowerHalfSum mertensSum primesUpTo
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1⟩
  · intro p _ _
    positivity

/-- For n < 2, the upper half sum is 0 (no primes ≤ n). -/
theorem upperHalfSum_lt_2 (n : ℕ) (hn : n < 2) : upperHalfSum n = 0 := by
  unfold upperHalfSum
  apply Finset.sum_eq_zero
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_Icc] at hp
  omega

/-- For n < 2, the Mertens sum is 0. -/
theorem mertensSum_lt_2 (n : ℕ) (hn : n < 2) : mertensSum n = 0 := by
  unfold mertensSum primesUpTo
  apply Finset.sum_eq_zero
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_Icc] at hp
  omega

/-
## Heuristic: Each Prime Contributes ~1/2
-/

/-- For an odd prime p, there are exactly (p-1)/2 residues r in {1,...,p-1}
    with r > p/2. Follows from upper_half_count. -/
theorem heuristic_half_fraction (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    (((Finset.Icc 1 (p - 1)).filter (fun r => p / 2 < r)).card : ℝ) / (p - 1) = 1 / 2 := by
  rw [upper_half_count p hp hp3]
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (3 : ℝ) ≤ (p : ℝ) := Nat.ofNat_le_cast.mpr hp3; linarith
  have hodd : ¬ 2 ∣ p := Nat.Prime.not_dvd_of_lt hp (by omega)
  have heven : 2 ∣ (p - 1) := by omega
  rw [Nat.cast_div heven (by norm_num)]
  field_simp

/-
## Sum Partition and Implications
-/

/-- Partition: mertensSum = upperHalfSum + lowerHalfSum.
    Primes split into those with upper-half residues and those without. -/
theorem sum_partition (n : ℕ) :
    mertensSum n = upperHalfSum n + lowerHalfSum n := by
  unfold mertensSum upperHalfSum lowerHalfSum primesUpTo
  rw [← Finset.sum_filter_add_sum_filter_not
    ((Finset.Icc 2 n).filter Nat.Prime) (fun p => isUpperHalfResidue n p)]
  congr 1 <;> (congr 1; ext p; simp [Finset.mem_filter]; tauto)

/-- The conjecture implies the lower half also contributes ~ (log log n)/2.
    Proof: lowerHalfSum = mertensSum - upperHalfSum, and both limits are known. -/
theorem lower_half_also_half :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      |lowerHalfSum n - Real.log (Real.log n) / 2| < ε := by
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := mertens_theorem (ε / 2) (by linarith)
  obtain ⟨N₂, hN₂⟩ := erdos_726_conjecture (ε / 2) (by linarith)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have h1 := hN₁ n (le_trans (le_max_left N₁ N₂) hn)
  have h2 := hN₂ n (le_trans (le_max_right N₁ N₂) hn)
  have hlower : lowerHalfSum n = mertensSum n - upperHalfSum n := by
    linarith [sum_partition n]
  rw [hlower, show mertensSum n - upperHalfSum n - Real.log (Real.log n) / 2 =
    (mertensSum n - Real.log (Real.log n)) -
    (upperHalfSum n - Real.log (Real.log n) / 2) from by ring]
  rw [abs_lt] at h1 h2 ⊢
  constructor <;> linarith

/-- The upper and lower half sums are asymptotically equal: their
    difference → 0. Follows from Mertens + conjecture via partition. -/
theorem upper_lower_asymptotic :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      |upperHalfSum n - lowerHalfSum n| < ε := by
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := mertens_theorem (ε / 3) (by linarith)
  obtain ⟨N₂, hN₂⟩ := erdos_726_conjecture (ε / 3) (by linarith)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have h1 := hN₁ n (le_trans (le_max_left _ _) hn)
  have h2 := hN₂ n (le_trans (le_max_right _ _) hn)
  have hpart := sum_partition n
  have heq : upperHalfSum n - lowerHalfSum n =
    2 * (upperHalfSum n - Real.log (Real.log n) / 2) -
    (mertensSum n - Real.log (Real.log n)) := by linarith
  rw [heq, abs_lt]
  rw [abs_lt] at h1 h2
  constructor <;> linarith

/-- The conjecture implies the ratio upperHalfSum/mertensSum → 1/2.
    Proof: |u/m − 1/2| = |2u − m|/(2m). Since u ≈ L/2 and m ≈ L
    (where L = log log n), |2u − m| < ε while m → ∞, so the ratio → 1/2. -/
theorem ratio_converges_to_half :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      mertensSum n > 0 →
      |upperHalfSum n / mertensSum n - 1 / 2| < ε := by
  intro ε hε
  -- Get approximations with δ = ε/3
  obtain ⟨N₁, hM⟩ := mertens_theorem (ε / 3) (by linarith)
  obtain ⟨N₂, hC⟩ := erdos_726_conjecture (ε / 3) (by linarith)
  -- Ensure mertensSum is large: get N₃ with |m − L| < 1/2
  obtain ⟨N₃, hM2⟩ := mertens_theorem (1 / 2) (by norm_num)
  -- log(log n) → ∞, so eventually ≥ 2 (ensuring mertensSum > 3/2)
  have h_tendsto : Filter.Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ)))
      Filter.atTop Filter.atTop :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp tendsto_natCast_atTop_atTop
  rw [Filter.tendsto_atTop_atTop] at h_tendsto
  obtain ⟨N₄, hN₄⟩ := h_tendsto 2
  -- Take N = max of all thresholds
  refine ⟨max (max N₁ N₂) (max N₃ N₄), fun n hn hm_pos => ?_⟩
  have hn1 : n ≥ N₁ := by omega
  have hn2 : n ≥ N₂ := by omega
  have hn3 : n ≥ N₃ := by omega
  have hn4 : n ≥ N₄ := by omega
  set m := mertensSum n with hm_def
  set u := upperHalfSum n with hu_def
  set L := Real.log (Real.log (n : ℝ)) with hL_def
  -- Key bounds from our approximation theorems
  have hm_approx : |m - L| < ε / 3 := hM n hn1
  have hu_approx : |u - L / 2| < ε / 3 := hC n hn2
  have hm_tight : |m - L| < 1 / 2 := hM2 n hn3
  have hL_ge : (2 : ℝ) ≤ L := hN₄ n hn4
  -- mertensSum > 1/2 (from L ≥ 2 and |m − L| < 1/2)
  have hm_large : m > 1 / 2 := by
    have := (abs_lt.mp hm_tight).1; linarith
  -- |2u − m| < ε (triangle inequality via u ≈ L/2 and m ≈ L)
  have h_num : |2 * u - m| < ε := by
    have h1 := abs_lt.mp hu_approx
    have h2 := abs_lt.mp hm_approx
    rw [abs_lt]; constructor <;> linarith
  -- |u/m − 1/2| = |2u − m|/(2m) < ε/(2m) ≤ ε (since 2m > 1)
  have h2m_pos : (0 : ℝ) < 2 * m := by linarith
  rw [show u / m - 1 / 2 = (2 * u - m) / (2 * m) from by
    have : m ≠ 0 := ne_of_gt hm_pos; field_simp; ring]
  rw [abs_div, abs_of_pos h2m_pos, div_lt_iff h2m_pos]
  calc |2 * u - m| < ε := h_num
    _ ≤ ε * (2 * m) := le_mul_of_one_le_right (le_of_lt hε) (by linarith)

/-
## Monotonicity and Growth
-/

/-- The Mertens sum is non-decreasing (adding more primes can only add). -/
theorem mertensSum_mono (m n : ℕ) (h : m ≤ n) : mertensSum m ≤ mertensSum n := by
  unfold mertensSum primesUpTo
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1, le_trans hp.1.2 h⟩, hp.2⟩
  · intro p _ _
    positivity

/-- For n ≥ 2, the Mertens sum is positive (at least 1/2 from p=2). -/
theorem mertensSum_pos (n : ℕ) (hn : n ≥ 2) : 0 < mertensSum n := by
  unfold mertensSum primesUpTo
  apply lt_of_lt_of_le _ (Finset.single_le_sum (fun p _ => by positivity) _)
  · simp
  · simp only [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨le_refl 2, hn⟩, Nat.prime_iff.mpr ⟨by omega, fun d hd => by omega⟩⟩

/-
## Problem Status
-/

def erdos_726_status : String := "OPEN"
