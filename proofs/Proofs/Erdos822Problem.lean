/-
Erdős Problem #822: Positive Density of n + φ(n)

Does the set of integers of the form n + φ(n) have positive lower density?

**Answer**: YES - proved by Gabdullin, Iudelevich, and Luca (2024)

The totient function φ(n) counts integers less than n that are coprime to n.
The question is whether the set {n + φ(n) : n ∈ ℕ} contains a positive fraction
of all natural numbers. This was resolved affirmatively using analytic number
theory techniques including estimates on the distribution of totient values.

Reference: https://erdosproblems.com/822
-/

import Mathlib.Data.Nat.Totient
import Mathlib.Data.Set.Function
import Mathlib.Order.Filter.Basic

namespace Erdos822

open Nat

/-- The function n + φ(n), where φ is Euler's totient function.
    This is the key function studied in Problem 822. -/
def nPlusTotient (n : ℕ) : ℕ := n + Nat.totient n

/-- The set of all values of n + φ(n) for positive n. -/
def nPlusTotientValues : Set ℕ := Set.range fun n => n + Nat.totient n

/-- The counting function: how many m ≤ N are of the form n + φ(n). -/
noncomputable def countValues (N : ℕ) : ℕ :=
  (Finset.range (N + 1)).filter (fun m => ∃ n, n + Nat.totient n = m) |>.card

/- ## Concrete Examples

We verify specific values of n + φ(n) computationally. -/

/-- Example: 1 + φ(1) = 2 -/
example : nPlusTotient 1 = 2 := by native_decide

/-- Example: 2 + φ(2) = 3 -/
example : nPlusTotient 2 = 3 := by native_decide

/-- Example: 3 + φ(3) = 5 -/
example : nPlusTotient 3 = 5 := by native_decide

/-- Example: 4 + φ(4) = 6 -/
example : nPlusTotient 4 = 6 := by native_decide

/-- Example: 5 + φ(5) = 9 -/
example : nPlusTotient 5 = 9 := by native_decide

/-- Example: 6 + φ(6) = 8 -/
example : nPlusTotient 6 = 8 := by native_decide

/-- Example: 10 + φ(10) = 14 -/
example : nPlusTotient 10 = 14 := by native_decide

/-- 2 is in the range (from n = 1) -/
example : 2 ∈ nPlusTotientValues := ⟨1, rfl⟩

/-- 3 is in the range (from n = 2) -/
example : 3 ∈ nPlusTotientValues := ⟨2, rfl⟩

/- ## Basic Properties -/

/-- n + φ(n) ≥ n for all n -/
theorem nPlusTotient_ge (n : ℕ) : nPlusTotient n ≥ n := by
  unfold nPlusTotient
  omega

/-- For even n ≥ 2, n + φ(n) is always even (since φ(n) is even for n ≥ 3).
    For odd primes p, p + φ(p) = p + (p-1) = 2p - 1 is odd.
    So odd values in the range come from primes (and from n = 1, 2). -/
/- ## Main Theorem

The main result requires deep analytic number theory from
Gabdullin–Iudelevich–Luca (2024). We state it as an axiom. -/

/-- **Axiom (Gabdullin–Iudelevich–Luca 2024):**
    The set {n + φ(n) : n ∈ ℕ} has positive lower natural density.

    Formally: lim inf (|{m ≤ N : m = n + φ(n) for some n}| / N) > 0 as N → ∞

    This was proved using sophisticated techniques from analytic number theory,
    including estimates on the distribution of totient values and sieve methods. -/
axiom nPlusTotientValues_hasPosDensity :
    ∃ c : ℝ, c > 0 ∧ ∀ ε > 0, ∃ N₀ : ℕ, ∀ M ≥ N₀,
    (nPlusTotientValues ∩ Set.Iio M).ncard ≥ (c - ε) * M

/- ## Generalizations

The same result holds for other arithmetic functions. -/

/-- The set {n + σ(n) : n ∈ ℕ} where σ is the sum of divisors. -/
def nPlusSigmaValues (sigma : ℕ → ℕ) : Set ℕ :=
  Set.range fun n => n + sigma n

/-- **Axiom:** The density result extends to n + σ(n) and similar functions
    (Gabdullin–Iudelevich–Luca 2024). -/
/- ## Summary -/

/-- **Erdős Problem 822: Summary**

    The set {n + φ(n) : n ∈ ℕ} has positive lower density, and n + φ(n) ≥ n for all n.
    The density result was proved by Gabdullin–Iudelevich–Luca (2024). -/
theorem erdos_822_summary :
    (∃ c : ℝ, c > 0 ∧ ∀ ε > 0, ∃ N₀ : ℕ, ∀ M ≥ N₀,
      (nPlusTotientValues ∩ Set.Iio M).ncard ≥ (c - ε) * M) ∧
    (∀ n, nPlusTotient n ≥ n) :=
  ⟨nPlusTotientValues_hasPosDensity, nPlusTotient_ge⟩

end Erdos822
