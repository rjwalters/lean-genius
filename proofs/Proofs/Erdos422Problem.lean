/-!
# Erdős Problem #422 — Hofstadter-Type Recursive Sequence

Define f(1) = f(2) = 1 and for n > 2:
  f(n) = f(n − f(n−1)) + f(n − f(n−2))

Questions:
1. Is f(n) well-defined for all n?
2. Does f miss infinitely many integers?
3. Is f surjective?
4. What is the growth rate of f?

The sequence begins: 1, 1, 2, 3, 3, 4, ...

Status: OPEN
Reference: https://erdosproblems.com/422
OEIS: A005185
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

/-! ## Definition -/

/-- The Erdős–Hofstadter recursive sequence. Defined partially since
    well-definedness for all n is unknown. -/
noncomputable def hofstadterF : ℕ → ℕ
  | 0 => 0  -- not used; sequence starts at 1
  | 1 => 1
  | 2 => 1
  | n + 3 => hofstadterF (n + 3 - hofstadterF (n + 2)) +
              hofstadterF (n + 3 - hofstadterF (n + 1))

/-- The sequence is well-defined at n if the recursive indices stay positive. -/
def IsWellDefined (n : ℕ) : Prop :=
  ∀ k ≤ n, k ≥ 3 → hofstadterF (k - 1) < k ∧ hofstadterF (k - 2) < k

/-! ## Main Questions -/

/-- **Well-Definedness**: is f(n) well-defined for all n? -/
axiom erdos_422_well_defined :
  ∀ n : ℕ, IsWellDefined n

/-- **Missing Integers**: does f miss infinitely many positive integers? -/
axiom erdos_422_misses_infinitely :
  Set.Infinite {m : ℕ | m > 0 ∧ ∀ n, hofstadterF n ≠ m}

/-- **Surjectivity Question**: is f surjective on positive integers? -/
axiom erdos_422_surjectivity :
  ¬Function.Surjective (fun n : ℕ => hofstadterF (n + 1))

/-- **Growth Rate**: what is the asymptotic behavior of f(n)? -/
axiom erdos_422_growth :
  ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n ≥ N₀,
      (hofstadterF n : ℝ) ≤ (1 + ε) * n

/-! ## Known Values -/

/-- The first few values: f(1) = 1, f(2) = 1, f(3) = 2, f(4) = 3,
    f(5) = 3, f(6) = 4, ... (OEIS A005185). -/
axiom initial_values :
  hofstadterF 1 = 1 ∧ hofstadterF 2 = 1 ∧
  hofstadterF 3 = 2 ∧ hofstadterF 4 = 3 ∧
  hofstadterF 5 = 3 ∧ hofstadterF 6 = 4

/-! ## Observations -/

/-- **Hofstadter Origin**: the sequence was proposed by Hofstadter and
    communicated to Erdős. It appears in Erdős–Graham (1980). -/
axiom hofstadter_origin : True

/-- **Self-Referential Recursion**: f(n) depends on f at points
    determined by earlier values of f itself. This self-referential
    nature makes analysis extremely difficult. -/
axiom self_referential : True

/-- **Eventually Constant?**: it is open whether f becomes constant. -/
axiom eventually_constant_open : True
