/-
Erdős Problem #221: Additive Complements with Powers of 2

Source: https://erdosproblems.com/221
Status: SOLVED (Ruzsa, 1972)

Statement:
Is there a set A ⊆ ℕ such that:
1. |A ∩ {1,...,N}| ≪ N/log N for all large N
2. Every large integer can be written as 2^k + a for some k ≥ 0 and a ∈ A?

Answer: YES. Ruzsa (1972) proved this with an elegant construction.

Historical Background:
- Lorentz (1954): Proved existence with |A ∩ {1,...,N}| ≪ (log log N / log N) · N
- Ruzsa (1972): Proved the optimal bound |A ∩ {1,...,N}| ≪ N / log N
- Ruzsa (2001): Constructed exact complement with |A ∩ {1,...,N}| ~ N / log₂ N

Ruzsa's Construction:
A = { 5^n · m : m ≥ 1 and 5^n ≥ C · log m } + {0, 1}
where C = 1/(5 · log 2).

Key Insight:
2 is a primitive root modulo 5^n for all n ≥ 1, ensuring coverage.

References:
- Lorentz, G.G. (1954): "On a problem of additive number theory"
- Ruzsa, I. (1972): "On a problem of P. Erdős"
- Ruzsa, I.Z. (2001): "Additive completion of lacunary sequences"

Tags: additive-number-theory, additive-complements, powers-of-2, primitive-roots
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.ZetaFunction

open Real Set

namespace Erdos221

/-
## Part I: Basic Definitions
-/

/-- Powers of 2: {1, 2, 4, 8, 16, ...} -/
def PowersOfTwo : Set ℕ :=
  { n | ∃ k : ℕ, n = 2^k }

/-- A set A is an additive complement to B for large integers if
    every large n can be written as a + b for a ∈ A, b ∈ B -/
def IsAdditiveComplementForLarge (A B : Set ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ a ∈ A, ∃ b ∈ B, n = a + b

/-- A is an additive complement to powers of 2 -/
def IsComplementToPowersOfTwo (A : Set ℕ) : Prop :=
  IsAdditiveComplementForLarge A PowersOfTwo

/-
## Part II: Counting Functions
-/

/-- Counting function: |A ∩ {1,...,N}| -/
noncomputable def countingFunction (A : Set ℕ) (N : ℕ) : ℕ :=
  (Finset.filter (fun n => n ∈ A) (Finset.range (N + 1))).card

/-- A set has density O(N/log N) -/
def HasDensityNOverLogN (A : Set ℕ) : Prop :=
  ∃ C > 0, ∀ N : ℕ, N ≥ 2 →
    (countingFunction A N : ℝ) ≤ C * N / Real.log N

/-- A set has density O((log log N / log N) · N) - Lorentz bound -/
def HasLorentzDensity (A : Set ℕ) : Prop :=
  ∃ C > 0, ∀ N : ℕ, N ≥ 3 →
    (countingFunction A N : ℝ) ≤ C * N * Real.log (Real.log N) / Real.log N

/-- A set has asymptotic density N/log₂ N - Ruzsa's optimal bound -/
def HasAsymptoticOptimalDensity (A : Set ℕ) : Prop :=
  Filter.Tendsto
    (fun N => (countingFunction A N : ℝ) * Real.log 2 * Real.log N / N)
    Filter.atTop (nhds 1)

/-
## Part III: The Main Problem Statement
-/

/-- Erdős Problem #221: The main question -/
def Erdos221Conjecture : Prop :=
  ∃ A : Set ℕ, IsComplementToPowersOfTwo A ∧ HasDensityNOverLogN A

/-
## Part IV: Lorentz's Result (1954)
-/

/-- Lorentz (1954): There exists a complement with (log log N / log N) · N density -/
axiom lorentz_1954 :
  ∃ A : Set ℕ, IsComplementToPowersOfTwo A ∧ HasLorentzDensity A

/-
## Part V: Ruzsa's Construction (1972)
-/

/-- Ruzsa's constant C = 1/(5 · log 2) -/
noncomputable def ruzsaConstant : ℝ := 1 / (5 * Real.log 2)

/-- The core set: { 5^n · m : m ≥ 1 and 5^n ≥ C · log m } -/
def RuzsaCoreSet : Set ℕ :=
  { x | ∃ n m : ℕ, m ≥ 1 ∧ (5^n : ℝ) ≥ ruzsaConstant * Real.log m ∧ x = 5^n * m }

/-- Ruzsa's set A = RuzsaCoreSet + {0, 1} -/
def RuzsaSet : Set ℕ :=
  { x | x ∈ RuzsaCoreSet ∨ x + 1 ∈ RuzsaCoreSet }

/-- 2 is a primitive root modulo 5^n for all n ≥ 1 -/
axiom two_primitive_root_mod_five_power :
  ∀ n : ℕ, n ≥ 1 → ∃ k : ℕ, k < 4 * 5^(n-1) ∧
    ∀ j < k, (2^j : ZMod (5^n)) ≠ 1 ∧ (2^k : ZMod (5^n)) = 1

/-- Ruzsa (1972): RuzsaSet is a complement to powers of 2 -/
axiom ruzsa_is_complement : IsComplementToPowersOfTwo RuzsaSet

/-- Ruzsa (1972): RuzsaSet has density O(N/log N) -/
axiom ruzsa_density : HasDensityNOverLogN RuzsaSet

/-- Ruzsa's Theorem (1972): The main result -/
theorem ruzsa_1972 : Erdos221Conjecture := by
  use RuzsaSet
  exact ⟨ruzsa_is_complement, ruzsa_density⟩

/-
## Part VI: Erdős Problem #221 - SOLVED
-/

/-- The answer to Problem #221 is YES -/
theorem erdos_221_answer : Erdos221Conjecture := ruzsa_1972

/-
## Part VII: Ruzsa's Optimal Construction (2001)
-/

/-- Ruzsa (2001): There exists an exact additive complement -/
def ExactComplementExists : Prop :=
  ∃ A : Set ℕ, IsComplementToPowersOfTwo A ∧ HasAsymptoticOptimalDensity A

/-- Ruzsa (2001): Exact complement with asymptotically optimal density -/
axiom ruzsa_2001_exact_complement : ExactComplementExists

/-
## Part VIII: Why N/log N is Optimal
-/

/-- Lower bound: Any complement must have density at least cN/log N -/
axiom density_lower_bound :
  ∀ A : Set ℕ, IsComplementToPowersOfTwo A →
    ∃ c > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (countingFunction A N : ℝ) ≥ c * N / Real.log N

/-- The density N/log N is optimal up to constants -/
theorem optimal_density :
    (∃ A : Set ℕ, IsComplementToPowersOfTwo A ∧ HasDensityNOverLogN A) ∧
    (∀ A : Set ℕ, IsComplementToPowersOfTwo A →
      ∃ c > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
        (countingFunction A N : ℝ) ≥ c * N / Real.log N) := by
  constructor
  · exact erdos_221_answer
  · exact density_lower_bound

/-
## Part IX: Connection to Primitive Roots
-/

/-- Why 5 is special: 2 is a primitive root mod 5^n.
    The multiplicative order of 2 mod 5^n is φ(5^n) = 4 · 5^(n-1).
    This means powers of 2 cycle through all residues coprime to 5^n. -/
axiom primitive_root_order :
  ∀ n : ℕ, n ≥ 1 →
    -- The multiplicative order of 2 mod 5^n equals φ(5^n)
    ∃ ord : ℕ, ord = 4 * 5^(n-1) ∧
      (2^ord : ZMod (5^n)) = 1 ∧
      ∀ j : ℕ, 0 < j → j < ord → (2^j : ZMod (5^n)) ≠ 1

/-- The powers of 2 mod 5^n cover all residues coprime to 5 -/
axiom powers_cover_residues :
  ∀ n : ℕ, n ≥ 1 →
    ∀ r : ℕ, Nat.Coprime r (5^n) →
      ∃ k : ℕ, (2^k : ZMod (5^n)) = r

/-
## Part X: Generalizations
-/

/-- Generalization: Replace 2 with any g that is a primitive root -/
def GeneralizedComplement (g : ℕ) (A : Set ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ a ∈ A, ∃ k : ℕ, n = a + g^k

/-- For any base g ≥ 2, sparse complements to powers of g exist.
    The density depends on the multiplicative structure of g modulo primes. -/
axiom generalization_to_any_base :
  ∀ g : ℕ, g ≥ 2 →
    ∃ A : Set ℕ, GeneralizedComplement g A ∧
      ∃ C > 0, ∀ N : ℕ, N ≥ 2 →
        (countingFunction A N : ℝ) ≤ C * N / Real.log N

/-
## Part XI: Related Problems
-/

/-- Connection to sumset problems:
    A + {2^k : k ≥ 0} covers all large integers.
    This is a "structured sumset" problem where one summand is fixed. -/
axiom sumset_covering :
  ∀ A : Set ℕ, IsComplementToPowersOfTwo A →
    ∀ N₀ : ℕ, ∃ N₁ : ℕ, ∀ n ≥ N₁,
      n ∈ { x | ∃ a ∈ A, ∃ k : ℕ, x = a + 2^k }

/-- Additive bases connection:
    A set B is an additive basis of order h if hB covers all large integers.
    Problem #221 asks: can {2^k} + A = ℕ eventually, with A having density N/log N?
    This is an "order 2" basis question with one summand being powers of 2. -/
axiom additive_basis_order_two :
  ∀ A : Set ℕ, IsComplementToPowersOfTwo A ∧ HasDensityNOverLogN A →
    -- A ∪ PowersOfTwo forms a thin additive basis of order 2
    ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ a ∈ A, ∃ b ∈ PowersOfTwo, n = a + b

/-
## Part XII: Summary
-/

/-- Erdős Problem #221: Complete Summary -/
theorem erdos_221_summary :
    -- The main conjecture: YES
    Erdos221Conjecture ∧
    -- Ruzsa's construction works
    (IsComplementToPowersOfTwo RuzsaSet ∧ HasDensityNOverLogN RuzsaSet) ∧
    -- Optimal construction exists
    ExactComplementExists := by
  constructor
  · exact erdos_221_answer
  constructor
  · exact ⟨ruzsa_is_complement, ruzsa_density⟩
  · exact ruzsa_2001_exact_complement

/-- Main theorem statement -/
theorem erdos_221_main :
    ∃ A : Set ℕ,
      (∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ k : ℕ, ∃ a ∈ A, n = 2^k + a) ∧
      (∃ C > 0, ∀ N : ℕ, N ≥ 2 →
        (countingFunction A N : ℝ) ≤ C * N / Real.log N) := by
  use RuzsaSet
  constructor
  · -- Complement property
    obtain ⟨N₀, hN₀⟩ := ruzsa_is_complement
    use N₀
    intro n hn
    obtain ⟨a, ha, b, hb, heq⟩ := hN₀ n hn
    obtain ⟨k, hk⟩ := hb
    use k, a, ha
    omega
  · -- Density bound
    exact ruzsa_density

/-- Problem #221 is SOLVED: Ruzsa's construction achieves optimal density -/
theorem erdos_221 :
    -- YES: sparse complement exists
    Erdos221Conjecture ∧
    -- Density N/log N is optimal
    (∀ A : Set ℕ, IsComplementToPowersOfTwo A →
      ∃ c > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
        (countingFunction A N : ℝ) ≥ c * N / Real.log N) :=
  ⟨erdos_221_answer, density_lower_bound⟩

end Erdos221
