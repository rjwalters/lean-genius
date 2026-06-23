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
  push_cast
  constructor <;> intro h <;> nlinarith

-- Routine: Equivalent algebraic form bc = ab + ac
theorem unit_fraction_algebraic (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) :
    (1 : ℚ) / a = (1 : ℚ) / b + (1 : ℚ) / c ↔ (b : ℚ) * c = a * b + a * c := by
  rw [unit_fraction_equiv a b c ha hb hc]
  push_cast; constructor <;> intro h <;> nlinarith

-- Routine: Standard decomposition pattern 1/n = 1/(n+1) + 1/(n(n+1))
theorem standard_decomposition (n : ℕ) (hn : n > 0) :
    (1 : ℚ) / n = 1 / (n + 1) + 1 / (n * (n + 1)) := by
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn1 : (n : ℚ) + 1 ≠ 0 := by positivity
  have hn2 : (n : ℚ) * (n + 1) ≠ 0 := mul_ne_zero hn' hn1
  field_simp
  ring

-- Routine: If A ⊆ Finset.range (N+1), then A.card ≤ N+1
theorem subset_range_card_bound (A : Finset ℕ) (N : ℕ) (h : A ⊆ Finset.range (N + 1)) :
    A.card ≤ N + 1 := by
  calc A.card ≤ (Finset.range (N + 1)).card := Finset.card_le_card h
    _ = N + 1 := Finset.card_range _

-- Routine: Odd integers in [1,N] have cardinality approximately N/2
theorem odd_count_bound (N : ℕ) :
    ((Finset.range (N + 1)).filter (fun n => n > 0 ∧ n % 2 = 1)).card ≤ (N + 1) / 2 := by
  rw [ Finset.card_eq_of_bijective ];
  use fun i hi => 2 * i + 1;
  · exact fun a ha => ⟨ a / 2, by norm_num at *; omega, by linarith [ Nat.mod_add_div a 2, Finset.mem_filter.mp ha ] ⟩;
  · grind;
  · aesop

-- Routine: The product of two odd numbers is odd
theorem odd_mul_odd (a b : ℕ) (ha : a % 2 = 1) (hb : b % 2 = 1) :
    (a * b) % 2 = 1 := by omega

-- Routine: The sum of two odd numbers is even
theorem odd_add_odd (a b : ℕ) (ha : a % 2 = 1) (hb : b % 2 = 1) :
    (a + b) % 2 = 0 := by omega

-- Routine: 5/8 > 1/2 (lower bound improvement)
theorem cambie_improves : (5 : ℚ) / 8 > 1 / 2 := by norm_num

end Erdos302Aristotle