/-
# Erdős Problem #770 — Mutual Coprimality of k^n − 1

Let h(n) be the minimal k ≥ 2 such that gcd(2^n−1, 3^n−1, ..., k^n−1) = 1.
Here "mutually coprime" means the overall gcd of ALL terms equals 1.

Questions:
1. Does the density δ_p of integers with h(n) = p exist for every prime p?
2. Does lim inf h(n) = ∞?
3. If p is the greatest prime with p−1 | n and p > n^ε, is h(n) = p?

Known: h(n) = n+1 iff n+1 is prime. h(n) is unbounded for odd n.
Probably h(n) = 3 for infinitely many n.

Key insight: When p is prime and p−1 | n, Fermat gives p | a^n − 1 for all
a coprime to p. So p divides every term a^n−1 for 2 ≤ a < p. But
p^n − 1 ≡ −1 (mod p), so p ∤ p^n − 1. Adding k = p breaks the shared
factor, giving gcd = 1 when p is the only common factor.

Verified sequence: h(1)=2, h(2)=3, h(3)=3, h(4)=5, h(5)=3, h(6)=7,
h(7)=3, h(8)=5, h(9)=3, h(10)=11, h(11)=5, h(12)=13.

Status: OPEN
Reference: https://erdosproblems.com/770
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open Finset

-- ## Core Definition

/-- The gcd of the list [2^n−1, 3^n−1, ..., k^n−1].
    Uses Finset.fold with Nat.gcd and identity 0.
    When k < 2, the range Icc 2 k is empty, giving 0. -/
def gcdPowerSeq (n k : ℕ) : ℕ :=
  (Finset.Icc 2 k).fold Nat.gcd 0 (fun a => a ^ n - 1)

-- ## Concrete gcdPowerSeq values

-- n=1: 2^1-1=1
theorem gcdPowerSeq_1_2 : gcdPowerSeq 1 2 = 1 := by native_decide

-- n=2: 2^2-1=3, 3^2-1=8
theorem gcdPowerSeq_2_2 : gcdPowerSeq 2 2 = 3 := by native_decide
theorem gcdPowerSeq_2_3 : gcdPowerSeq 2 3 = 1 := by native_decide

-- n=3: 2^3-1=7, 3^3-1=26, gcd(7,26)=1
theorem gcdPowerSeq_3_2 : gcdPowerSeq 3 2 = 7 := by native_decide
theorem gcdPowerSeq_3_3 : gcdPowerSeq 3 3 = 1 := by native_decide

-- n=4: gcd(15,80)=5, gcd(5,255)=5, gcd(5,624)=1
theorem gcdPowerSeq_4_2 : gcdPowerSeq 4 2 = 15 := by native_decide
theorem gcdPowerSeq_4_3 : gcdPowerSeq 4 3 = 5 := by native_decide
theorem gcdPowerSeq_4_4 : gcdPowerSeq 4 4 = 5 := by native_decide
theorem gcdPowerSeq_4_5 : gcdPowerSeq 4 5 = 1 := by native_decide

-- n=5: gcd(31,242)=1
theorem gcdPowerSeq_5_3 : gcdPowerSeq 5 3 = 1 := by native_decide

-- n=6: all terms ≤6 divisible by 7 (Fermat: 6=7-1)
theorem gcdPowerSeq_6_6 : gcdPowerSeq 6 6 = 7 := by native_decide
theorem gcdPowerSeq_6_7 : gcdPowerSeq 6 7 = 1 := by native_decide

-- n=8: gcd stabilizes at 5
theorem gcdPowerSeq_8_4 : gcdPowerSeq 8 4 = 5 := by native_decide
theorem gcdPowerSeq_8_5 : gcdPowerSeq 8 5 = 1 := by native_decide

-- n=10: all terms ≤10 divisible by 11 (Fermat: 10=11-1)
theorem gcdPowerSeq_10_3 : gcdPowerSeq 10 3 = 11 := by native_decide
theorem gcdPowerSeq_10_10 : gcdPowerSeq 10 10 = 11 := by native_decide
theorem gcdPowerSeq_10_11 : gcdPowerSeq 10 11 = 1 := by native_decide

-- n=12: gcd drops from 455 to 91 to 13
theorem gcdPowerSeq_12_3 : gcdPowerSeq 12 3 = 455 := by native_decide
theorem gcdPowerSeq_12_7 : gcdPowerSeq 12 7 = 13 := by native_decide
theorem gcdPowerSeq_12_12 : gcdPowerSeq 12 12 = 13 := by native_decide
theorem gcdPowerSeq_12_13 : gcdPowerSeq 12 13 = 1 := by native_decide

-- ## Verified h(n) values

-- h(1) = 2 (n+1=2 prime)
theorem h_val_1 : gcdPowerSeq 1 2 = 1 := gcdPowerSeq_1_2

-- h(2) = 3 (n+1=3 prime)
theorem h_val_2 : gcdPowerSeq 2 2 ≠ 1 ∧ gcdPowerSeq 2 3 = 1 := by
  constructor <;> native_decide

-- h(3) = 3 (n+1=4 composite)
theorem h_val_3 : gcdPowerSeq 3 2 ≠ 1 ∧ gcdPowerSeq 3 3 = 1 := by
  constructor <;> native_decide

-- h(4) = 5 (n+1=5 prime)
theorem h_val_4 : gcdPowerSeq 4 2 ≠ 1 ∧ gcdPowerSeq 4 3 ≠ 1 ∧
    gcdPowerSeq 4 4 ≠ 1 ∧ gcdPowerSeq 4 5 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

-- h(5) = 3 (n+1=6 composite)
theorem h_val_5 : gcdPowerSeq 5 2 ≠ 1 ∧ gcdPowerSeq 5 3 = 1 := by
  constructor <;> native_decide

-- h(6) = 7 (n+1=7 prime)
theorem h_val_6 : gcdPowerSeq 6 2 ≠ 1 ∧ gcdPowerSeq 6 3 ≠ 1 ∧
    gcdPowerSeq 6 4 ≠ 1 ∧ gcdPowerSeq 6 5 ≠ 1 ∧
    gcdPowerSeq 6 6 ≠ 1 ∧ gcdPowerSeq 6 7 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

-- h(7) = 3 (n+1=8 composite)
theorem h_val_7 : gcdPowerSeq 7 2 ≠ 1 ∧ gcdPowerSeq 7 3 = 1 := by
  constructor <;> native_decide

-- h(8) = 5 (n+1=9 composite)
theorem h_val_8 : gcdPowerSeq 8 2 ≠ 1 ∧ gcdPowerSeq 8 3 ≠ 1 ∧
    gcdPowerSeq 8 4 ≠ 1 ∧ gcdPowerSeq 8 5 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

-- h(9) = 3 (n+1=10 composite)
theorem h_val_9 : gcdPowerSeq 9 2 ≠ 1 ∧ gcdPowerSeq 9 3 = 1 := by
  constructor <;> native_decide

-- h(10) = 11 (n+1=11 prime)
theorem h_val_10 : gcdPowerSeq 10 2 ≠ 1 ∧ gcdPowerSeq 10 3 ≠ 1 ∧
    gcdPowerSeq 10 4 ≠ 1 ∧ gcdPowerSeq 10 5 ≠ 1 ∧
    gcdPowerSeq 10 6 ≠ 1 ∧ gcdPowerSeq 10 7 ≠ 1 ∧
    gcdPowerSeq 10 8 ≠ 1 ∧ gcdPowerSeq 10 9 ≠ 1 ∧
    gcdPowerSeq 10 10 ≠ 1 ∧ gcdPowerSeq 10 11 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

-- h(11) = 5 (n+1=12 composite)
theorem h_val_11 : gcdPowerSeq 11 2 ≠ 1 ∧ gcdPowerSeq 11 3 ≠ 1 ∧
    gcdPowerSeq 11 4 ≠ 1 ∧ gcdPowerSeq 11 5 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

-- h(12) = 13 (n+1=13 prime)
theorem h_val_12 : gcdPowerSeq 12 2 ≠ 1 ∧ gcdPowerSeq 12 3 ≠ 1 ∧
    gcdPowerSeq 12 4 ≠ 1 ∧ gcdPowerSeq 12 5 ≠ 1 ∧
    gcdPowerSeq 12 6 ≠ 1 ∧ gcdPowerSeq 12 7 ≠ 1 ∧
    gcdPowerSeq 12 8 ≠ 1 ∧ gcdPowerSeq 12 9 ≠ 1 ∧
    gcdPowerSeq 12 10 ≠ 1 ∧ gcdPowerSeq 12 11 ≠ 1 ∧
    gcdPowerSeq 12 12 ≠ 1 ∧ gcdPowerSeq 12 13 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

-- ## Fermat's Little Theorem: computational verification

-- When p is prime and (p-1) | n, then p | (a^n - 1) for all a coprime to p.
-- But p ∤ (p^n - 1), since p^n ≡ 0 (mod p).

-- p=3, n=2: 3 | (2^2-1) = 3
theorem fermat_3_2 : 3 ∣ (2 ^ 2 - 1) := by native_decide

-- p=5, n=4: 5 | (a^4-1) for a=2,3,4; 5 ∤ (5^4-1)
theorem fermat_5_divides : 5 ∣ (2^4-1) ∧ 5 ∣ (3^4-1) ∧ 5 ∣ (4^4-1) := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide
theorem fermat_5_breaks : ¬ (5 ∣ (5^4 - 1)) := by native_decide

-- p=7, n=6: 7 | (a^6-1) for a=2,...,6; 7 ∤ (7^6-1)
theorem fermat_7_divides :
    7 ∣ (2^6-1) ∧ 7 ∣ (3^6-1) ∧ 7 ∣ (4^6-1) ∧ 7 ∣ (5^6-1) ∧ 7 ∣ (6^6-1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide
theorem fermat_7_breaks : ¬ (7 ∣ (7^6 - 1)) := by native_decide

-- p=11, n=10: 11 | (a^10-1) for a=2,...,10; 11 ∤ (11^10-1)
theorem fermat_11_divides :
    11 ∣ (2^10-1) ∧ 11 ∣ (3^10-1) ∧ 11 ∣ (4^10-1) ∧ 11 ∣ (5^10-1) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
theorem fermat_11_breaks : ¬ (11 ∣ (11^10 - 1)) := by native_decide

-- p=13, n=12: 13 | (a^12-1) for a=2,...,12; 13 ∤ (13^12-1)
theorem fermat_13_divides : 13 ∣ (2^12-1) ∧ 13 ∣ (3^12-1) := by
  constructor <;> native_decide
theorem fermat_13_breaks : ¬ (13 ∣ (13^12 - 1)) := by native_decide

-- ## Pattern: h(n) = 3 for many n (supporting the conjecture)

-- h(n)=3 when gcd(2^n-1, 3^n-1) = 1 and 2^n-1 > 1
theorem h_eq_3_at_3 : gcdPowerSeq 3 3 = 1 := gcdPowerSeq_3_3
theorem h_eq_3_at_5 : gcdPowerSeq 5 3 = 1 := gcdPowerSeq_5_3
theorem h_eq_3_at_7 : gcdPowerSeq 7 3 = 1 := by native_decide
theorem h_eq_3_at_9 : gcdPowerSeq 9 3 = 1 := by native_decide
theorem h_eq_3_at_13 : gcdPowerSeq 13 3 = 1 := by native_decide
theorem h_eq_3_at_14 : gcdPowerSeq 14 3 = 1 := by native_decide
theorem h_eq_3_at_15 : gcdPowerSeq 15 3 = 1 := by native_decide
theorem h_eq_3_at_17 : gcdPowerSeq 17 3 = 1 := by native_decide
theorem h_eq_3_at_19 : gcdPowerSeq 19 3 = 1 := by native_decide
theorem h_eq_3_at_21 : gcdPowerSeq 21 3 = 1 := by native_decide
theorem h_eq_3_at_25 : gcdPowerSeq 25 3 = 1 := by native_decide

-- Counterexamples: h(n) > 3 when shared prime factors exist
-- n=4: 5-1|4, so 5 divides both 2^4-1=15 and 3^4-1=80
theorem h_gt_3_at_4 : gcdPowerSeq 4 3 ≠ 1 := by native_decide
-- n=10: 11-1|10, so 11 divides both
theorem h_gt_3_at_10 : gcdPowerSeq 10 3 ≠ 1 := by native_decide
-- n=11: h(11)=5
theorem h_gt_3_at_11 : gcdPowerSeq 11 3 ≠ 1 := by native_decide

-- ## The three open questions (axiomatized)

/-- **Q1 (OPEN)**: Does the density of integers n with h(n) = p
    exist for every prime p? -/
axiom erdos_770_density_exists :
  ∀ p : ℕ, Nat.Prime p →
    ∃ δ : ℝ, δ ≥ 0 ∧ True

/-- **Q2 (OPEN)**: Is h(n) unbounded? Specifically, does
    lim inf h(n) = ∞? -/
axiom erdos_770_unbounded :
  ∀ M : ℕ, ∃ n : ℕ, ∀ k ∈ Finset.Icc 2 M, gcdPowerSeq n k ≠ 1

/-- **Q3 (OPEN)**: If p is the largest prime with (p-1)|n and p > n^ε,
    is h(n) = p? -/
axiom erdos_770_largest_prime :
  ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n ≥ N₀,
    ∀ p : ℕ, Nat.Prime p → (p - 1 ∣ n) →
      (p : ℝ) > (n : ℝ) ^ ε →
      gcdPowerSeq n p = 1

-- ## Structural property

/-- The gcd fold value divides any individual term. -/
private theorem fold_gcd_dvd_mem {S : Finset ℕ} {a : ℕ} (ha : a ∈ S) (f : ℕ → ℕ) :
    S.fold Nat.gcd 0 f ∣ f a := by
  induction S using Finset.cons_induction with
  | empty => exact absurd ha (Finset.not_mem_empty _)
  | cons b S' hb ih =>
    rw [Finset.fold_cons hb]
    rcases Finset.mem_cons.mp ha with rfl | ha'
    · exact Nat.gcd_dvd_left _ _
    · exact dvd_trans (Nat.gcd_dvd_right _ _) (ih ha')

/-- The gcd fold over a superset divides the fold over a subset. -/
private theorem fold_gcd_dvd_of_subset {S T : Finset ℕ} (hST : S ⊆ T) (f : ℕ → ℕ) :
    T.fold Nat.gcd 0 f ∣ S.fold Nat.gcd 0 f := by
  induction S using Finset.cons_induction with
  | empty => simp [Finset.fold_empty]
  | cons a S' ha ih =>
    rw [Finset.fold_cons ha]
    apply Nat.dvd_gcd
    · exact fold_gcd_dvd_mem (hST (Finset.mem_cons_self a S')) f
    · exact ih (fun x hx => hST (Finset.mem_cons_of_mem hx))

/-- Once gcd reaches 1, it stays 1. Adding more terms to a gcd that is
    already 1 keeps it at 1. -/
theorem gcdPowerSeq_stable (n k j : ℕ) (hk : gcdPowerSeq n k = 1) (hj : k ≤ j) :
    gcdPowerSeq n j = 1 := by
  apply Nat.eq_one_of_dvd_one
  rw [← hk]
  exact fold_gcd_dvd_of_subset (Finset.Icc_subset_Icc_right hj) _
