/-
Erdős Problem #694: Preimages of Euler's Totient Function

**Question**: Let f_max(n) be the largest m with φ(m) = n, and f_min(n) be the smallest.
Investigate max_{n≤x} f_max(n)/f_min(n).

**Related Questions**:
1. (Carmichael's Totient Conjecture - OPEN): Is there an n for which φ(m) = n
   has exactly one solution? I.e., does f_max(n)/f_min(n) = 1 ever occur?

2. (Erdős - SOLVED): If such an n exists, then infinitely many such n must exist.

**Status**: The main investigation is OPEN. Erdős's conditional result is SOLVED.

The preimage set φ⁻¹(n) = {m : φ(m) = n} is finite for each n (since φ(m) ≥ √(m/2)
for large m). The question asks about the spread of this set.

References:
- https://erdosproblems.com/694
- https://erdosproblems.com/51 (related)
- [Er79e] Erdős, Problems and results on number theoretic properties
-/

import Mathlib.Data.Nat.Totient
import Mathlib.Data.Set.Finite.Basic

namespace Erdos694

open Nat Set

/-! ## The Totient Preimage

The preimage φ⁻¹(n) = {m : φ(m) = n} is the set of all integers with totient n.
-/

/-- The preimage of n under Euler's totient function: all m with φ(m) = n. -/
def totientPreimage (n : ℕ) : Set ℕ := {m | Nat.totient m = n}

/-- The preimage is always finite (axiomatized).
This follows from φ(m) ≥ √(m/2) for m > 1. -/
axiom totientPreimage_finite (n : ℕ) : (totientPreimage n).Finite

/-! ## Largest and Smallest Preimages

For each n in the range of φ, we define the largest and smallest m with φ(m) = n.
We axiomatize these functions rather than constructing them directly.
-/

/-- f_max(n) is the largest m such that φ(m) = n. Returns 0 if no such m exists. -/
axiom f_max : ℕ → ℕ

/-- f_min(n) is the smallest m such that φ(m) = n. Returns 0 if no such m exists. -/
axiom f_min : ℕ → ℕ

/-! ## Basic Properties -/

/-- If n is in the range of φ, then f_max(n) is in the preimage. -/
axiom f_max_mem (n : ℕ) (h : (totientPreimage n).Nonempty) :
    f_max n ∈ totientPreimage n

/-- If n is in the range of φ, then f_min(n) is in the preimage. -/
axiom f_min_mem (n : ℕ) (h : (totientPreimage n).Nonempty) :
    f_min n ∈ totientPreimage n

/-- f_max is indeed the maximum. -/
axiom f_max_is_max (n m : ℕ) (hm : m ∈ totientPreimage n) :
    m ≤ f_max n

/-- f_min is indeed the minimum. -/
axiom f_min_is_min (n m : ℕ) (hm : m ∈ totientPreimage n) :
    f_min n ≤ m

/-- f_min(n) ≤ f_max(n) for all n in the range of φ. -/
axiom f_min_le_f_max (n : ℕ) (h : (totientPreimage n).Nonempty) :
    f_min n ≤ f_max n

/-! ## The Main Open Question

The question asks to investigate the maximum ratio f_max(n)/f_min(n) over n ≤ x.
-/

/-- The ratio f_max(n)/f_min(n), which equals 1 iff the preimage has exactly one element. -/
noncomputable def preimageRatio (n : ℕ) : ℚ :=
  if f_min n = 0 then 0 else (f_max n : ℚ) / f_min n

/-- (OPEN) Investigation of the maximum preimage ratio.
What is max_{n ≤ x} f_max(n)/f_min(n)? How does it grow with x?
-/
axiom erdos_694_open (x : ℕ) :
    ∃ (n : ℕ), n ≤ x ∧ (totientPreimage n).Nonempty ∧
      ∀ (m : ℕ), m ≤ x → (totientPreimage m).Nonempty →
        preimageRatio m ≤ preimageRatio n

/-! ## Carmichael's Totient Conjecture

Carmichael (1907) conjectured that the equation φ(m) = n never has exactly one solution.
Equivalently: the ratio f_max(n)/f_min(n) is never exactly 1.

This remains OPEN. Ford (1999) showed that if a counterexample exists, it must be > 10^10^10.
-/

/-- A totient value n is called a **Carmichael number** if φ(m) = n has a unique solution. -/
def isCarmichaelTotient (n : ℕ) : Prop :=
  ∃ m, Nat.totient m = n ∧ ∀ k, Nat.totient k = n → k = m

/-- Carmichael's Totient Conjecture (OPEN): No Carmichael totient exists. -/
def CarmichaelConjecture : Prop := ∀ n, ¬ isCarmichaelTotient n

/-- The negation of Carmichael's conjecture: at least one Carmichael totient exists. -/
def CarmichaelCounterexample : Prop := ∃ n, isCarmichaelTotient n

/-! ## Erdős's Conditional Result (SOLVED)

Erdős proved: If Carmichael's conjecture is false (i.e., some n has a unique preimage),
then infinitely many such n must exist.
-/

/-- The set of all Carmichael totients. -/
def carmichaelTotients : Set ℕ := {n | isCarmichaelTotient n}

/--
**Erdős (SOLVED)**: If there exists any Carmichael totient, then infinitely many exist.

The proof uses the multiplicative structure of φ: if φ(m) = n is unique, then
the behavior of n under multiplication by certain primes forces more unique preimages.
-/
axiom erdos_conditional_infinite :
    CarmichaelCounterexample → carmichaelTotients.Infinite

/-! ## Known Partial Results -/

/-- Ford (1999): Any Carmichael totient must exceed 10^10^10. -/
axiom ford_lower_bound :
    ∀ n, isCarmichaelTotient n → n > 10^(10^10)

/-- The totient function is surjective onto its range (the "totient values"). -/
def totientValues : Set ℕ := {n | ∃ m, Nat.totient m = n}

/-- 1 is a totient value: φ(1) = 1 and φ(2) = 1. -/
theorem one_is_totient_value : 1 ∈ totientValues := ⟨1, rfl⟩

/-- 2 is a totient value: φ(3) = 2 and φ(4) = 2 and φ(6) = 2. -/
theorem two_is_totient_value : 2 ∈ totientValues := ⟨3, rfl⟩

/-- Every even number ≥ 2 is a totient value (axiomatized). -/
axiom even_totient_values : ∀ n : ℕ, n ≥ 2 → Even n → n ∈ totientValues

/-! ## Examples of Preimage Sizes -/

/-- φ(1) = 1 -/
example : Nat.totient 1 = 1 := rfl

/-- φ(2) = 1, so 1 has multiple preimages (not a Carmichael totient). -/
example : Nat.totient 2 = 1 := rfl

/-- φ(3) = 2 -/
example : Nat.totient 3 = 2 := rfl

/-- φ(4) = 2, so 2 has multiple preimages. -/
example : Nat.totient 4 = 2 := rfl

/-- φ(6) = 2, another preimage of 2. -/
example : Nat.totient 6 = 2 := rfl

/-! ## Non-Carmichael Verification

We verify that small totient values are not Carmichael totients
(they have multiple preimages).
-/

/-- 1 is not a Carmichael totient: both 1 and 2 have totient 1. -/
theorem one_not_carmichael : ¬ isCarmichaelTotient 1 := by
  intro ⟨m, _, huniq⟩
  have h1 : Nat.totient 1 = 1 := rfl
  have h2 : Nat.totient 2 = 1 := rfl
  have eq1 := huniq 1 h1
  have eq2 := huniq 2 h2
  have : (1 : ℕ) = 2 := eq1.trans eq2.symm
  norm_num at this

/-- 2 is not a Carmichael totient: 3, 4, and 6 all have totient 2. -/
theorem two_not_carmichael : ¬ isCarmichaelTotient 2 := by
  intro ⟨m, _, huniq⟩
  have h3 : Nat.totient 3 = 2 := rfl
  have h4 : Nat.totient 4 = 2 := rfl
  have eq3 := huniq 3 h3
  have eq4 := huniq 4 h4
  have : (3 : ℕ) = 4 := eq3.trans eq4.symm
  norm_num at this

/-! ## Summary -/

/-- **Erdős Problem #694** Summary:

1. OPEN: Investigate max_{n≤x} f_max(n)/f_min(n)
2. OPEN: Carmichael's conjecture (no n has a unique preimage)
3. SOLVED: If any Carmichael totient exists, infinitely many do (Erdős)
4. KNOWN: Any Carmichael totient > 10^10^10 (Ford 1999)
-/
theorem erdos_694_summary :
    -- Small totient values are not Carmichael totients
    ¬ isCarmichaelTotient 1 ∧ ¬ isCarmichaelTotient 2 :=
  ⟨one_not_carmichael, two_not_carmichael⟩

end Erdos694
