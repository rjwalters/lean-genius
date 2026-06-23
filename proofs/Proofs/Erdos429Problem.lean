/-
Erdős Problem #429: Sparse Admissible Sets and Prime Shifts

Source: https://erdosproblems.com/429
Status: SOLVED (Weisenberg 2024) - Answer is NO

Statement:
Is it true that if A ⊆ ℕ is sparse enough and does not cover all residue classes
modulo p for any prime p, then there exists some n such that n + a is prime for
all a ∈ A?

Answer: NO (Weisenberg 2024)

Background:
The question asks whether "admissibility" (avoiding all residue classes mod p)
combined with sparsity is sufficient to guarantee a prime shift exists. This
is related to the classical admissible set conjecture but with a sparsity twist.

An admissible set is one that does not cover all residue classes mod p for any
prime p. Such sets cannot be ruled out from having all shifts prime by simple
mod p arguments. The famous Hardy-Littlewood prime tuples conjecture says
dense finite admissible sets should have infinitely many prime shifts.

Weisenberg showed that even arbitrarily sparse admissible sets can fail to have
any prime shift, disproving the conjecture.

References:
- [We24] D. Weisenberg, "Sparse Admissible Sets and a Problem of Erdős and Graham",
  Integers (2024)
- Related: Prime tuples conjecture, Admissible sets, Covering congruences

Tags: number-theory, primes, admissible-sets, covering-systems
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Int.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

open Nat Set

namespace Erdos429

/- ## Part I: Basic Definitions -/

/-- **Residue Class Coverage:**
A set A covers residue class r mod m if some a ∈ A satisfies a ≡ r (mod m). -/
def CoversResidue (A : Set ℕ) (m : ℕ) (r : ℕ) : Prop :=
  ∃ a ∈ A, a % m = r

/-- **Covers All Residue Classes:**
A set A covers all residue classes mod m if for every r < m, some a ∈ A ≡ r (mod m). -/
def CoversAllResidues (A : Set ℕ) (m : ℕ) : Prop :=
  ∀ r < m, CoversResidue A m r

/-- **Admissible Set:**
A ⊆ ℕ is admissible if it does NOT cover all residue classes mod p for any prime p.
Equivalently, for each prime p, there exists a residue class mod p avoided by A. -/
def IsAdmissible (A : Set ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → ¬CoversAllResidues A p

/-- **Avoided Residue:**
If A is admissible, for each prime p there exists r such that no a ∈ A ≡ r (mod p). -/
def AvoidedResidue (A : Set ℕ) (p : ℕ) (r : ℕ) : Prop :=
  r < p ∧ ∀ a ∈ A, a % p ≠ r

/-- **Admissibility Characterization:**
A is admissible iff every prime has an avoided residue. -/
theorem admissible_iff_avoided (A : Set ℕ) :
    IsAdmissible A ↔ ∀ p, Nat.Prime p → ∃ r, AvoidedResidue A p r := by
  constructor
  · intro hA p hp
    specialize hA p hp
    simp only [CoversAllResidues, CoversResidue, not_forall, not_exists] at hA
    obtain ⟨r, hr, hAr⟩ := hA
    exact ⟨r, hr, fun a ha => hAr a ha⟩
  · intro hA p hp hcov
    obtain ⟨r, hr, havoid⟩ := hA p hp
    exact havoid _ (hcov r hr).choose_spec.1 (hcov r hr).choose_spec.2

/- ## Part II: Prime Shifts and the Conjecture -/

/-- **All Primes in Shift:**
All elements of n + A are prime. -/
def AllPrimesInShift (A : Set ℕ) (n : ℕ) : Prop :=
  ∀ a ∈ A, Nat.Prime (n + a)

/-- **Has Prime Shift:**
There exists n such that all elements of n + A are prime. -/
def HasPrimeShift (A : Set ℕ) : Prop :=
  ∃ n : ℕ, AllPrimesInShift A n

/- ## Part III: Sparsity Conditions -/

/-- **Zero Density:**
A has density 0 if |A ∩ [1,N]|/N → 0 as N → ∞. -/
def HasZeroDensity (A : Set ℕ) : Prop :=
  ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ({n ∈ A | n ≤ N} : Set ℕ).ncard < ε * N

/-- **Lacunary:**
A is lacunary if a_{n+1}/a_n → ∞. -/
def IsLacunary (A : List ℕ) (hA : A.Sorted (· < ·)) : Prop :=
  ∀ c : ℕ, ∃ N : ℕ, ∀ i, i + 1 < A.length → i ≥ N →
    A.get ⟨i + 1, by omega⟩ > c * A.get ⟨i, by omega⟩

/- ## Part IV: The Erdős Conjecture and Its Refutation -/

/-- **The Erdős Conjecture (Disproved):**
If A is sparse enough and admissible, then A has a prime shift. -/
def ErdosConjecture429 : Prop :=
  ∀ A : Set ℕ, HasZeroDensity A → IsAdmissible A → HasPrimeShift A

/-- **Weisenberg's Theorem (2024):**
The Erdős conjecture is FALSE. There exist arbitrarily sparse admissible sets
with no prime shift. -/
axiom weisenberg_theorem :
  ∃ A : Set ℕ, HasZeroDensity A ∧ IsAdmissible A ∧ ¬HasPrimeShift A

/-- **Stronger Result:**
Even lacunary admissible sets may fail to have prime shifts. -/
axiom weisenberg_lacunary :
  ∃ (A : List ℕ) (hA : A.Sorted (· < ·)),
    IsLacunary A hA ∧
    IsAdmissible (A.toFinset : Set ℕ) ∧
    ¬HasPrimeShift (A.toFinset : Set ℕ)

/-- **The Conjecture is FALSE:** -/
theorem erdos_429_disproved : ¬ErdosConjecture429 := by
  intro hconj
  obtain ⟨A, hdens, hadm, hno⟩ := weisenberg_theorem
  exact hno (hconj A hdens hadm)

/- ## Part V: Covering Systems -/

/-- **Covering System:**
A covering system {(aᵢ, mᵢ)} covers all integers if every n ≡ aᵢ (mod mᵢ) for some i.
Weisenberg's construction uses covering systems to ensure every shift n
has some a ∈ A with n + a composite. -/
def IsCoveringSystem (covers : List (ℕ × ℕ)) : Prop :=
  ∀ n : ℤ, ∃ ⟨a, m⟩ ∈ covers, n % m = a

/-- **Admissibility is necessary for prime shifts:**
If A has a prime shift, then A must be admissible. -/
axiom admissibility_necessary (A : Set ℕ) (hne : A.Nonempty) :
    HasPrimeShift A → IsAdmissible A

/- ## Part VI: Summary -/

/-- **Summary of Erdős Problem #429:**

PROBLEM: If A ⊆ ℕ is sparse and admissible (avoids one residue class mod p
for each prime p), must there exist n with all n + a prime?

ANSWER: NO (Weisenberg 2024)

KEY RESULT: Weisenberg constructed arbitrarily sparse admissible sets
with no prime shift at all, even lacunary ones.

TECHNIQUE: Uses ideas from covering congruences to ensure every potential
shift n has some a ∈ A with n + a composite. -/
theorem erdos_429_summary :
    ¬ErdosConjecture429 ∧
    (∃ A : Set ℕ, HasZeroDensity A ∧ IsAdmissible A ∧ ¬HasPrimeShift A) ∧
    (∃ (A : List ℕ) (hA : A.Sorted (· < ·)),
      IsLacunary A hA ∧
      IsAdmissible (A.toFinset : Set ℕ) ∧
      ¬HasPrimeShift (A.toFinset : Set ℕ)) :=
  ⟨erdos_429_disproved, weisenberg_theorem, weisenberg_lacunary⟩

end Erdos429
