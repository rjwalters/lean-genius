/-
# Divisor Sum Identity via GCD Partition of Unity

## What This Proves
The classical identity n = Σ_{d|n} φ(d) by explicitly constructing the
**partition of {0,...,n-1} by GCD classes**:

  S_d = { k ∈ {0,...,n-1} : gcd(k, n) = d }

Each class S_d has exactly φ(n/d) elements (via the bijection k ↦ k/d),
giving the identity.

## Approach
Rather than citing Mathlib's `Nat.sum_totient` directly, we give an
explicit constructive proof that reveals *why* the identity holds:
1. Define S_d := { k ∈ range n : gcd(k, n) = d }
2. Show these sets form a partition of {0,...,n-1}
3. Show |S_d| = φ(n/d) via the bijection k ↦ k/d
4. Derive n = Σ_{d|n} φ(n/d) = Σ_{d|n} φ(d)

## Mathlib Dependencies
- Nat.totient, Nat.sum_totient (for cross-validation)
- Finset, Nat.gcd, Nat.Coprime
-/

import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic

open Finset Nat

namespace EulerTotientOQ04

-- ============================================================================
-- Part I: GCD Classes — Partition of {0,...,n-1}
-- ============================================================================

/-- The GCD class S_d(n) = { k ∈ {0,...,n-1} : gcd(k, n) = d }. -/
def gcdClass (n d : ℕ) : Finset ℕ :=
  (range n).filter (fun k => Nat.gcd k n = d)

theorem mem_gcdClass {n d k : ℕ} :
    k ∈ gcdClass n d ↔ k < n ∧ Nat.gcd k n = d := by
  simp [gcdClass, mem_filter, mem_range]

-- ============================================================================
-- Part II: Partition Structure
-- ============================================================================

/-- Every element belongs to the class indexed by its gcd. -/
theorem mem_gcdClass_of_gcd (n k : ℕ) (hk : k < n) :
    k ∈ gcdClass n (Nat.gcd k n) :=
  mem_gcdClass.mpr ⟨hk, rfl⟩

/-- GCD classes for different divisors are disjoint. -/
theorem gcdClass_disjoint {n d₁ d₂ : ℕ} (h : d₁ ≠ d₂) :
    Disjoint (gcdClass n d₁) (gcdClass n d₂) := by
  simp only [gcdClass, Finset.disjoint_filter]
  intro k _; exact fun h1 h2 => absurd (h1.symm.trans h2) h

/-- GCD classes indexed by divisors cover {0,...,n-1}. -/
theorem range_eq_biUnion_gcdClass (n : ℕ) (hn : 0 < n) :
    range n = n.divisors.biUnion (gcdClass n) := by
  ext k; simp only [mem_range, mem_biUnion, Nat.mem_divisors]
  constructor
  · intro hk
    exact ⟨Nat.gcd k n, ⟨Nat.gcd_dvd_right k n, by omega⟩,
           mem_gcdClass_of_gcd n k hk⟩
  · intro ⟨_, _, hk⟩; exact (mem_gcdClass.mp hk).1

-- ============================================================================
-- Part III: Cardinality — |S_d(n)| = φ(n/d)
-- ============================================================================

/-- **Key Lemma**: The bijection k ↦ k/d maps S_d(n) to the coprime set of q = n/d.

    For k with gcd(k,n) = d:
    - d | k, so k/d is well-defined
    - 0 ≤ k/d < q (since k < n = dq)
    - gcd(k/d, q) = gcd(k,n)/d = d/d = 1
    Inverse: m ↦ d·m. -/
theorem card_gcdClass_eq_totient (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (hdvd : d ∣ n) :
    (gcdClass n d).card = Nat.totient (n / d) := by
  set q := n / d with hq_def
  have hq_pos : 0 < q := Nat.div_pos (Nat.le_of_dvd hn hdvd) hd
  have hdn : d * q = n := by rw [mul_comm]; exact Nat.div_mul_cancel hdvd
  -- The totient set: {m ∈ range q : gcd(q, m) = 1}
  set T := (range q).filter (Nat.Coprime q) with hT_def
  -- |T| = φ(q) by definition
  change (gcdClass n d).card = T.card
  -- Bijection: k ↦ k / d
  apply Finset.card_bij (fun k _ => k / d)
  · -- Maps gcdClass n d → T
    intro k hk
    rw [mem_gcdClass] at hk; obtain ⟨hk_lt, hk_gcd⟩ := hk
    rw [hT_def, mem_filter, mem_range]
    have hdvd_k : d ∣ k := hk_gcd ▸ Nat.gcd_dvd_left k n
    obtain ⟨a, ha⟩ := hdvd_k
    rw [ha, Nat.mul_div_cancel_left _ hd]
    constructor
    · -- a < q: from d*a = k < n = d*q
      have : d * a < d * q := by rw [ha] at hk_lt; linarith [hdn]
      exact (Nat.mul_lt_mul_left hd).mp this
    · -- Coprime q a: from gcd(d*a, d*q) = d, so gcd(a,q) = 1
      rw [Nat.Coprime, Nat.gcd_comm]
      have hg1 : Nat.gcd (d * a) n = d := by rw [← ha]; exact hk_gcd
      rw [← hdn] at hg1
      rw [Nat.gcd_mul_left] at hg1
      exact mul_left_cancel₀ (by omega : d ≠ 0) (by rw [mul_one]; exact hg1)
  · -- Injective
    intro k₁ hk₁ k₂ hk₂ heq
    rw [mem_gcdClass] at hk₁ hk₂
    have hd1 : d ∣ k₁ := hk₁.2 ▸ Nat.gcd_dvd_left k₁ n
    have hd2 : d ∣ k₂ := hk₂.2 ▸ Nat.gcd_dvd_left k₂ n
    calc k₁ = k₁ / d * d := (Nat.div_mul_cancel hd1).symm
      _ = k₂ / d * d := by rw [heq]
      _ = k₂ := Nat.div_mul_cancel hd2
  · -- Surjective
    intro m hm
    rw [hT_def, mem_filter, mem_range] at hm
    obtain ⟨hm_lt, hm_cop⟩ := hm
    refine ⟨d * m, ?_, ?_⟩
    · -- d * m ∈ gcdClass n d
      rw [mem_gcdClass]
      constructor
      · -- d * m < n = d * q
        calc d * m < d * q := (Nat.mul_lt_mul_left hd).mpr hm_lt
          _ = n := hdn
      · -- gcd(d * m, n) = d
        rw [← hdn, Nat.gcd_mul_left]
        rw [Nat.Coprime, Nat.gcd_comm] at hm_cop
        rw [hm_cop, mul_one]
    · -- d * m / d = m
      exact Nat.mul_div_cancel_left m hd

-- ============================================================================
-- Part IV: The Divisor Sum Identity
-- ============================================================================

/-- **The Divisor Sum Identity via GCD Partition**

    n = Σ_{d|n} φ(n/d)

    Proved by partitioning {0,...,n-1} into GCD classes S_d = {k : gcd(k,n) = d}:
    each class has |S_d| = φ(n/d) elements, and they cover all n values. -/
theorem divisor_sum_totient_div (n : ℕ) (hn : 0 < n) :
    n.divisors.sum (fun d => Nat.totient (n / d)) = n := by
  -- n = |range n| = Σ |gcdClass n d| via partition
  have hpart := range_eq_biUnion_gcdClass n hn
  have hdisj : (n.divisors : Set ℕ).PairwiseDisjoint (gcdClass n) :=
    fun _ _ _ _ hne => gcdClass_disjoint hne
  have hcard : n = n.divisors.sum (fun d => (gcdClass n d).card) := by
    conv_lhs => rw [← card_range n]
    rw [hpart]
    exact card_biUnion (fun d hd₁ d' hd₂ h => hdisj hd₁ hd₂ h)
  -- Replace |gcdClass n d| with φ(n/d)
  have hsame : n.divisors.sum (fun d => (gcdClass n d).card) =
      n.divisors.sum (fun d => Nat.totient (n / d)) := by
    apply Finset.sum_congr rfl
    intro d hd
    simp only [Nat.mem_divisors] at hd
    have hd_pos : 0 < d := Nat.pos_of_ne_zero fun h => by subst h; simp at hd
    exact card_gcdClass_eq_totient n d hn hd_pos hd.1
  linarith

/-- **Standard form**: n = Σ_{d|n} φ(d).

    Cross-validation with Mathlib's `Nat.sum_totient`. -/
theorem divisor_sum_totient (n : ℕ) :
    n.divisors.sum Nat.totient = n :=
  Nat.sum_totient n

-- ============================================================================
-- Part V: The "Partition of Unity" Formulation
-- ============================================================================

/-- Partition of unity over ℚ: Σ_{d|n} φ(n/d)/n = 1.

    Probabilistic interpretation: picking k uniformly from {0,...,n-1},
    the probability that gcd(k,n) = d is exactly φ(n/d)/n. -/
theorem partition_of_unity (n : ℕ) (hn : 0 < n) :
    n.divisors.sum (fun d => (Nat.totient (n / d) : ℚ) / n) = 1 := by
  have hn_pos : (0 : ℚ) < n := Nat.cast_pos.mpr hn
  rw [← Finset.sum_div, div_eq_one_iff_eq (ne_of_gt hn_pos)]
  exact_mod_cast divisor_sum_totient_div n hn

-- ============================================================================
-- Part VI: Per-Class Combinatorial Meaning
-- ============================================================================

/-- Each summand has a combinatorial meaning:
    φ(n/d) = |{k ∈ {0,...,n-1} : gcd(k,n) = d}| -/
theorem totient_counts_gcd_class (n d : ℕ) (hn : 0 < n) (hd : d ∈ n.divisors) :
    (gcdClass n d).card = Nat.totient (n / d) := by
  simp only [Nat.mem_divisors] at hd
  exact card_gcdClass_eq_totient n d hn
    (Nat.pos_of_ne_zero fun h => by subst h; simp at hd) hd.1

-- ============================================================================
-- Part VII: Concrete Verifications
-- ============================================================================

/-- For n=6: divisors are {1,2,3,6}, φ values are {1,1,2,2}, sum = 6. -/
example : (6 : ℕ).divisors.sum Nat.totient = 6 := by native_decide

/-- For n=12: sum of φ over divisors = 12. -/
example : (12 : ℕ).divisors.sum Nat.totient = 12 := by native_decide

/-- For n=30: sum of φ over divisors = 30. -/
example : (30 : ℕ).divisors.sum Nat.totient = 30 := by native_decide

/-- GCD class sizes for n=6:
    S_1 = {1,5} → |S_1| = 2 = φ(6)
    S_2 = {2,4} → |S_2| = 2 = φ(3)
    S_3 = {3} → |S_3| = 1 = φ(2)
    S_6 = {0} → |S_6| = 1 = φ(1) -/
example : (gcdClass 6 1).card = 2 := by native_decide
example : (gcdClass 6 2).card = 2 := by native_decide
example : (gcdClass 6 3).card = 1 := by native_decide
example : (gcdClass 6 6).card = 1 := by native_decide

/-- For prime p=7: S_1 has 6 elements, S_7 has 1 element (k=0). -/
example : (gcdClass 7 1).card = 6 := by native_decide
example : (gcdClass 7 7).card = 1 := by native_decide

#check divisor_sum_totient_div
#check partition_of_unity
#check totient_counts_gcd_class

end EulerTotientOQ04
