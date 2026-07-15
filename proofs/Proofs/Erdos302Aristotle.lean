/-
  Aristotle targets for Erdős Problem #302
  Routine supporting lemmas for automated proof search.
  See Erdos302Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture (asymptotic density of f(N))
  - Routine rational algebra identities and cardinality bounds
  - Clean theorem statements with no definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos302Aristotle

open Finset

-- Routine: The unit fraction identity 1/a = 1/b + 1/c ↔ bc = a(b+c)
theorem unit_fraction_equiv (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) :
    (1 : ℚ) / a = (1 : ℚ) / b + (1 : ℚ) / c ↔ b * c = a * (b + c) := by
  have ha' : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hb' : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hc' : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [div_add_div _ _ hb' hc', div_eq_div_iff ha' (mul_ne_zero hb' hc')]
  constructor
  · intro h
    have hq : (b : ℚ) * c = a * (b + c) := by linarith
    exact_mod_cast hq
  · intro h
    have hq : (b : ℚ) * c = a * (b + c) := by exact_mod_cast h
    linarith

-- Routine: Equivalent algebraic form bc = ab + ac
theorem unit_fraction_algebraic (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) :
    (1 : ℚ) / a = (1 : ℚ) / b + (1 : ℚ) / c ↔ (b : ℚ) * c = a * b + a * c := by
  rw [unit_fraction_equiv a b c ha hb hc]
  constructor
  · intro h
    have hq : (b : ℚ) * c = a * (b + c) := by exact_mod_cast h
    linarith
  · intro h
    have hq : (b : ℚ) * c = a * (b + c) := by linarith
    exact_mod_cast hq

-- Routine: Standard decomposition pattern 1/n = 1/(n+1) + 1/(n(n+1))
theorem standard_decomposition (n : ℕ) (hn : n > 0) :
    (1 : ℚ) / n = 1 / (n + 1) + 1 / (n * (n + 1)) := by
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn1 : (n : ℚ) + 1 ≠ 0 := by positivity
  have hn2 : (n : ℚ) * (n + 1) ≠ 0 := mul_ne_zero hn' hn1
  field_simp

-- Routine: If A ⊆ Finset.range (N+1), then A.card ≤ N+1
theorem subset_range_card_bound (A : Finset ℕ) (N : ℕ) (h : A ⊆ Finset.range (N + 1)) :
    A.card ≤ N + 1 := by
  calc A.card ≤ (Finset.range (N + 1)).card := Finset.card_le_card h
    _ = N + 1 := Finset.card_range _

-- Routine: Odd integers in [1,N] have cardinality approximately N/2
theorem odd_count_bound (N : ℕ) :
    ((Finset.range (N + 1)).filter (fun n => n > 0 ∧ n % 2 = 1)).card ≤ (N + 1) / 2 := by
  have hsub : ((Finset.range (N + 1)).filter (fun n => n > 0 ∧ n % 2 = 1)) ⊆
      (Finset.range ((N + 1) / 2)).image (fun i => 2 * i + 1) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnN, hn0, hnodd⟩ := hn
    simp only [Finset.mem_image, Finset.mem_range]
    exact ⟨n / 2, by omega, by omega⟩
  calc ((Finset.range (N + 1)).filter (fun n => n > 0 ∧ n % 2 = 1)).card
      ≤ ((Finset.range ((N + 1) / 2)).image (fun i => 2 * i + 1)).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.range ((N + 1) / 2)).card := Finset.card_image_le
    _ = (N + 1) / 2 := Finset.card_range _

-- Routine: The product of two odd numbers is odd
theorem odd_mul_odd (a b : ℕ) (ha : a % 2 = 1) (hb : b % 2 = 1) :
    (a * b) % 2 = 1 := by
  obtain ⟨a', rfl⟩ : ∃ a', a = 2 * a' + 1 := ⟨a / 2, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = 2 * b' + 1 := ⟨b / 2, by omega⟩
  have : (2 * a' + 1) * (2 * b' + 1) = 2 * (2 * a' * b' + a' + b') + 1 := by ring
  rw [this]
  omega

-- Routine: The sum of two odd numbers is even
theorem odd_add_odd (a b : ℕ) (ha : a % 2 = 1) (hb : b % 2 = 1) :
    (a + b) % 2 = 0 := by omega

-- Routine: 5/8 > 1/2 (lower bound improvement)
theorem cambie_improves : (5 : ℚ) / 8 > 1 / 2 := by norm_num

end Erdos302Aristotle