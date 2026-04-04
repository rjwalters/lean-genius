/-
  Aristotle targets for Erdős Problem #433: Maximum Frobenius Numbers
  Arithmetic helper lemmas supporting the g_two proof.
  See Erdos433Problem.lean for the main formalization.

  These theorems are submitted to Aristotle for automated proof search.
  Sorries mark goals where Aristotle is expected to fill in the proof.
-/
import Mathlib

namespace Erdos433Aristotle

open Nat Finset

-- ═══════════════════════════════════════════════════════════════════
-- Section 1: Arithmetic Identities for g(2, n)
-- ═══════════════════════════════════════════════════════════════════

/-- For n ≥ 3, the Dixmier lower bound for k=2 equals n²-3n+1. -/
theorem dixmier_k2_arith (n : ℕ) (hn : n ≥ 3) :
    (n - 2) * (n - 2 + 1) - 1 = n ^ 2 - 3 * n + 1 := by
  -- Substitute n = m + 3 so all ℕ subtractions vanish
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  -- Expand products linearly in m*m so omega can close the goal
  have hprod1 : (m + 3 - 2) * (m + 3 - 2 + 1) = m * m + 3 * m + 2 := by
    simp only [show m + 3 - 2 = m + 1 from by omega, show m + 1 + 1 = m + 2 from by omega]
    ring
  have hprod2 : (m + 3) ^ 2 = m * m + 6 * m + 9 := by ring
  have hprod3 : 3 * (m + 3) = 3 * m + 9 := by ring
  rw [hprod1, hprod2, hprod3]
  -- Goal is now linear in m*m, which omega treats as an atom
  omega

/-- Alternate form: (n-1)*n - (n-1) - n = n²-3n+1 for n ≥ 3. -/
theorem frobenius_pair_max (n : ℕ) (hn : n ≥ 3) :
    (n - 1) * n - (n - 1) - n = n ^ 2 - 3 * n + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  simp only [show m + 3 - 1 = m + 2 from by omega]
  rw [Nat.sub_sub]
  have hprod1 : (m + 2) * (m + 3) = m * m + 5 * m + 6 := by ring
  have hprod2 : (m + 3) ^ 2 = m * m + 6 * m + 9 := by ring
  have hprod3 : 3 * (m + 3) = 3 * m + 9 := by ring
  rw [hprod1, hprod2, hprod3]
  omega

/-- n²-3n+1 ≥ 0 for n ≥ 3 (well-definedness of ℕ subtraction). -/
theorem g_two_nonneg (n : ℕ) (hn : n ≥ 3) : n ^ 2 ≥ 3 * n - 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have : (m + 3) ^ 2 = m * m + 6 * m + 9 := by ring
  rw [this]
  omega

-- ═══════════════════════════════════════════════════════════════════
-- Section 2: Coprimality of Consecutive Integers
-- ═══════════════════════════════════════════════════════════════════

/-- Consecutive integers n-1 and n are coprime. -/
theorem coprime_pred_self (n : ℕ) (hn : n ≥ 1) : Nat.Coprime (n - 1) n := by
  -- Work in ℤ where subtraction is not truncated
  rw [Nat.Coprime]
  apply Nat.dvd_one.mp
  have h1 : (Nat.gcd (n - 1) n : ℤ) ∣ ↑(n - 1 : ℕ) := by
    exact_mod_cast Nat.gcd_dvd_left _ _
  have h2 : (Nat.gcd (n - 1) n : ℤ) ∣ (n : ℤ) := by
    exact_mod_cast Nat.gcd_dvd_right _ _
  have h3 : (Nat.gcd (n - 1) n : ℤ) ∣ 1 := by
    have hsub := dvd_sub h2 h1
    have heq : (n : ℤ) - ↑(n - 1 : ℕ) = 1 := by
      push_cast [show 1 ≤ n from hn]; omega
    rwa [heq] at hsub
  exact_mod_cast h3

/-- gcd(n-1, n) = 1 for n ≥ 1. -/
theorem gcd_pred_self (n : ℕ) (hn : n ≥ 1) : Nat.gcd (n - 1) n = 1 :=
  coprime_pred_self n hn

-- ═══════════════════════════════════════════════════════════════════
-- Section 3: Frobenius Number Arithmetic Bound
-- ═══════════════════════════════════════════════════════════════════

/-- The product bound in ℤ: for a ≤ n-1 and b ≤ n,
    a*b - a - b ≤ n²-3n+1 as integers. -/
theorem frobenius_bound_int (a b n : ℕ) (hn : n ≥ 3)
    (han : a ≤ n - 1) (hbn : b ≤ n) :
    (a : ℤ) * b - a - b ≤ n ^ 2 - 3 * n + 1 := by
  have hn' : (n : ℤ) ≥ 3 := by exact_mod_cast hn
  have ha' : (a : ℤ) ≥ 0 := by positivity
  have hb' : (b : ℤ) ≥ 0 := by positivity
  -- Convert han : a ≤ n - 1 (ℕ) to (a : ℤ) ≤ n - 1 (ℤ)
  have han' : (a : ℤ) ≤ (n : ℤ) - 1 := by
    zify [show 1 ≤ n from by omega] at han; linarith
  have hbn' : (b : ℤ) ≤ n := by exact_mod_cast hbn
  -- Witnesses: the products (n-1-a)*(n-b) ≥ 0, a*(n-b) ≥ 0, (n-1-a)*b ≥ 0, a*b ≥ 0
  -- These four quadratic hints suffice for the degree-2 Positivstellensatz certificate.
  have h1 : (n : ℤ) - 1 - a ≥ 0 := by linarith
  have h2 : (n : ℤ) - b ≥ 0 := by linarith
  nlinarith [mul_nonneg h1 h2, mul_nonneg ha' h2, mul_nonneg h1 hb', mul_nonneg ha' hb']

/-- For 1 ≤ a, b with a ≤ n-1 and b ≤ n, a*b - a - b ≤ n²-3n+1 in ℕ. -/
theorem frobenius_ub_pair (a b n : ℕ) (hn : n ≥ 3)
    (ha1 : a ≥ 1) (hb1 : b ≥ 1)
    (han : a ≤ n - 1) (hbn : b ≤ n) :
    a * b - a - b ≤ n ^ 2 - 3 * n + 1 := by
  -- Lift the ℤ bound and convert back to ℕ
  have hZ := frobenius_bound_int a b n hn han hbn
  have hnn : n ^ 2 ≥ 3 * n - 1 := g_two_nonneg n hn
  have hn3 : 3 * n ≤ n ^ 2 := by nlinarith
  -- Case split: does ℕ subtraction a*b - a - b underflow?
  rcases le_or_lt (a + b) (a * b) with h | h
  · -- No underflow: use zify with side conditions to convert to ℤ
    have ha_le : a ≤ a * b := by omega
    have hb_le : b ≤ a * b - a := by omega
    zify [ha_le, hb_le, hn3]
    linarith
  · -- Underflow: a*b < a+b, so a*b - a - b = 0 ≤ anything
    simp [show a * b - a - b = 0 from by omega]

/-- Special case: if a = 0, then a*b - a - b = 0 ≤ n²-3n+1. -/
theorem frobenius_ub_zero_left (b n : ℕ) (hn : n ≥ 3) :
    0 * b - 0 - b ≤ n ^ 2 - 3 * n + 1 := by
  simp

/-- The pair {n-1, n} is a 2-element subset of {0,...,n} for n ≥ 2. -/
theorem pair_subset_range (n : ℕ) (hn : n ≥ 2) :
    ({n - 1, n} : Finset ℕ) ⊆ Finset.range (n + 1) := by
  intro x hx
  simp [Finset.mem_range, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  omega

/-- {n-1, n} has cardinality 2 for n ≥ 1. -/
theorem pair_card (n : ℕ) (hn : n ≥ 1) :
    ({n - 1, n} : Finset ℕ).card = 2 := by
  rw [Finset.card_insert_of_notMem]
  · simp
  · simp; omega

-- ═══════════════════════════════════════════════════════════════════
-- Section 4: GCD Identity for {n-1, n}
-- ═══════════════════════════════════════════════════════════════════

/-- The GCD of the set {n-1, n} equals 1 for n ≥ 1. -/
theorem finset_gcd_pred_self (n : ℕ) (hn : n ≥ 1) :
    ({n - 1, n} : Finset ℕ).gcd id = 1 := by
  -- Show ({n-1,n}).gcd id divides 1 via Nat.dvd_gcd + coprimality
  apply Nat.dvd_one.mp
  have hd1 : ({n - 1, n} : Finset ℕ).gcd id ∣ (n - 1) := by
    have := Finset.gcd_dvd (f := id) (Finset.mem_insert_self (n - 1) {n})
    simpa using this
  have hd2 : ({n - 1, n} : Finset ℕ).gcd id ∣ n := by
    have := Finset.gcd_dvd (f := id) (s := {n - 1, n})
      (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self n)))
    simpa using this
  have hcop := coprime_pred_self n hn  -- Nat.gcd (n-1) n = 1
  have := Nat.dvd_gcd hd1 hd2         -- ... ∣ Nat.gcd (n-1) n
  rwa [hcop] at this

end Erdos433Aristotle
