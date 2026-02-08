/-
Erdős Problem #1140: Primes of the Form n - 2x²

Source: https://erdosproblems.com/1140
Status: DISPROVED (Epure-Gica, 2010)

Statement:
Do there exist infinitely many n such that n - 2x² is prime
for all x with 2x² < n?

Answer: NO — Only finitely many n exist: {2, 5, 7, 13, 31, 61, 181, 199}
(with at most one additional exception).

History:
- Erdős: Posed the question
- Epure-Gica (2010): Proved only finitely many n exist
  - For n ≡ 1 (mod 4): only 5, 13, 61, 181
  - For n ≡ 3 (mod 4): only 7, 31, 199, and at most one exception
- Mollin-Williams (1989): Key supporting result for n ≡ 3 case

Tags: number-theory, primes, quadratic-forms, disproved
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic

namespace Erdos1140

/-
## Part I: Basic Definitions
-/

/-- The property that n - 2x² is prime for all valid x. -/
def AllShiftsArePrime (n : ℕ) : Prop :=
  ∀ x : ℕ, 2 * x ^ 2 < n → Nat.Prime (n - 2 * x ^ 2)

/-- The known values satisfying the property. -/
def KnownValues : Finset ℕ := {2, 5, 7, 13, 31, 61, 181, 199}

/-
## Part II: Small Verified Examples
-/

/-- n = 2: only x = 0 applies, and 2 - 0 = 2 is prime. -/
theorem n_eq_2 : AllShiftsArePrime 2 := by
  intro x hx
  simp at hx
  omega

/-- n = 5: x ∈ {0, 1}, giving 5 and 3, both prime. -/
theorem n_eq_5 : AllShiftsArePrime 5 := by
  intro x hx
  interval_cases x <;> simp_all <;> decide

/-- n = 7: x ∈ {0, 1}, giving 7 and 5, both prime. -/
theorem n_eq_7 : AllShiftsArePrime 7 := by
  intro x hx
  interval_cases x <;> simp_all <;> decide

/-- n = 13: x ∈ {0, 1, 2}, giving 13, 11, 5, all prime. -/
theorem n_eq_13 : AllShiftsArePrime 13 := by
  intro x hx
  interval_cases x <;> simp_all <;> decide

/-- n = 4 fails: 4 - 0 = 4 is not prime. -/
theorem n_eq_4_fails : ¬AllShiftsArePrime 4 := by
  intro h
  have := h 0 (by omega)
  simp at this

/-
## Part III: Epure-Gica Theorem
-/

/-- **Epure-Gica (2010), case n ≡ 1 (mod 4):**
    The only values n ≡ 1 (mod 4) with AllShiftsArePrime are 5, 13, 61, 181. -/
axiom epure_gica_mod_1 (n : ℕ) :
    n % 4 = 1 → AllShiftsArePrime n → n ∈ ({5, 13, 61, 181} : Finset ℕ)

/-- **Epure-Gica (2010), case n ≡ 3 (mod 4):**
    The only values n ≡ 3 (mod 4) with AllShiftsArePrime are 7, 31, 199,
    and at most one additional exception. -/
axiom epure_gica_mod_3 (n : ℕ) :
    n % 4 = 3 → AllShiftsArePrime n →
    n ∈ ({7, 31, 199} : Finset ℕ) ∨ n > 199

/-- **Even case:** For even n > 2, n - 2·0² = n is even and > 2, so not prime. -/
theorem even_case (n : ℕ) (hn : n > 2) (heven : 2 ∣ n) :
    ¬AllShiftsArePrime n := by
  intro h
  have h0 := h 0 (by omega)
  simp at h0
  exact Nat.Prime.not_dvd_one h0 (by omega)

/-
## Part IV: Main Result
-/

/-- **Erdős Problem #1140: DISPROVED**

    There are only finitely many n such that n - 2x² is prime for all
    valid x. The known values are {2, 5, 7, 13, 31, 61, 181, 199}. -/
axiom erdos_1140_finite :
    ∃ B : ℕ, ∀ n > B, ¬AllShiftsArePrime n

/-- The answer to Erdős Problem #1140. -/
theorem erdos_1140 : ¬(∀ N : ℕ, ∃ n > N, AllShiftsArePrime n) := by
  intro h
  obtain ⟨B, hB⟩ := erdos_1140_finite
  obtain ⟨n, hn, hn'⟩ := h B
  exact hB n (by omega) hn'

end Erdos1140
