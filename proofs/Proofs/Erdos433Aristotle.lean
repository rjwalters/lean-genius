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
  -- Any common divisor of n-1 and n divides n-(n-1)=1, so equals 1
  have hdvd : Nat.gcd (n - 1) n ∣ n - (n - 1) :=
    Nat.dvd_sub (Nat.gcd_dvd_right (n - 1) n) (Nat.gcd_dvd_left (n - 1) n)
  have hone : n - (n - 1) = 1 := by omega
  rw [hone] at hdvd
  exact Nat.dvd_one.mp hdvd

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
  -- Key identity: (n-1-a)*(n-b) ≥ 0 combined with product expansion
  have ha_int : (a : ℤ) ≤ (n : ℤ) - 1 := by
    have h : (n - 1 : ℕ) + 1 = n := Nat.sub_add_cancel (by omega)
    have : (a : ℤ) ≤ ((n - 1 : ℕ) : ℤ) := by exact_mod_cast han
    simp only [Nat.cast_sub (show 1 ≤ n by omega)] at this
    linarith
  have hb_int : (b : ℤ) ≤ (n : ℤ) := by exact_mod_cast hbn
  have ha_nn : (0 : ℤ) ≤ (a : ℤ) := Int.natCast_nonneg a
  have hb_nn : (0 : ℤ) ≤ (b : ℤ) := Int.natCast_nonneg b
  nlinarith [mul_nonneg (show (0:ℤ) ≤ (n:ℤ) - 1 - (a:ℤ) by linarith) hb_nn,
             mul_nonneg (show (0:ℤ) ≤ (n:ℤ) - (b:ℤ) by linarith) ha_nn,
             mul_nonneg (show (0:ℤ) ≤ (n:ℤ) - 1 - (a:ℤ) by linarith)
                        (show (0:ℤ) ≤ (n:ℤ) - (b:ℤ) by linarith)]

/-- For 1 ≤ a, b with a ≤ n-1 and b ≤ n, a*b - a - b ≤ n²-3n+1 in ℕ. -/
theorem frobenius_ub_pair (a b n : ℕ) (hn : n ≥ 3)
    (ha1 : a ≥ 1) (hb1 : b ≥ 1)
    (han : a ≤ n - 1) (hbn : b ≤ n) :
    a * b - a - b ≤ n ^ 2 - 3 * n + 1 := by
  -- Substitute n = m+3 so the RHS becomes m*m+3*m+1 (no ℕ subtraction to cast)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  simp only [show m + 3 - 1 = m + 2 from by omega] at han
  have hrhs : (m + 3) ^ 2 - 3 * (m + 3) + 1 = m * m + 3 * m + 1 := by
    have h1 : (m + 3) ^ 2 = m * m + 6 * m + 9 := by ring
    have h2 : 3 * (m + 3) = 3 * m + 9 := by ring
    rw [h1, h2]; omega
  rw [hrhs]
  by_cases hab : a + b ≤ a * b
  · -- a*b ≥ a+b: cast to ℤ; RHS m*m+3*m+1 has no subtraction so cast is trivial
    have lhs_eq : (↑(a * b - a - b) : ℤ) = (a : ℤ) * b - a - b := by
      rw [Nat.sub_sub, Nat.cast_sub hab]; push_cast; ring
    have h : (↑(a * b - a - b) : ℤ) ≤ ↑(m * m + 3 * m + 1) := by
      rw [lhs_eq]; push_cast
      have ha_le : (a : ℤ) ≤ m + 2 := by exact_mod_cast han
      have hb_le : (b : ℤ) ≤ m + 3 := by exact_mod_cast hbn
      have ha_pos : (1 : ℤ) ≤ a := by exact_mod_cast ha1
      have hb_pos : (1 : ℤ) ≤ b := by exact_mod_cast hb1
      -- Key identity: a*b-a-b = (a-1)*(b-1)-1 ≤ (m+1)*(m+2)-1 = m*m+3*m+1
      have key : (a : ℤ) * b - a - b = (a - 1) * (b - 1) - 1 := by ring
      rw [key]
      -- Certificate: m*m+3*m+2-(a-1)*(b-1) = (m+2-a)*(b-1)+(m+1)*(m+3-b) ≥ 0
      nlinarith [mul_nonneg (show (0:ℤ) ≤ (m:ℤ) + 2 - a by linarith)
                             (show (0:ℤ) ≤ (b:ℤ) - 1 by linarith),
                 mul_nonneg (show (0:ℤ) ≤ (m:ℤ) + 1 by linarith)
                             (show (0:ℤ) ≤ (m:ℤ) + 3 - b by linarith)]
    exact_mod_cast h
  · -- a*b < a+b: a*b - a - b = 0 in ℕ
    push_neg at hab; omega

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
  simp only [Finset.gcd_insert, Finset.gcd_singleton, id, normalize_eq]
  exact coprime_pred_self n hn

end Erdos433Aristotle
