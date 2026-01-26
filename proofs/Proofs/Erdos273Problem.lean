/-!
# Erdős Problem #273: Covering Systems with Prime-Minus-One Moduli

Is there a covering system all of whose moduli are of the form p - 1
for some primes p ≥ 5?

## Status: OPEN

## References
- Erdős–Graham, "Old and New Problems and Results in Combinatorial Number Theory" (1980), p.24
- Selfridge: covering system with moduli dividing 360 when p = 3 is allowed
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-!
## Section I: Covering Systems
-/

/-- A covering system is a finite collection of residue classes
a_i (mod m_i) whose union is all of ℤ. -/
structure CoveringSystem where
  /-- The index type for the residue classes. -/
  n : ℕ
  /-- The moduli (all ≥ 2). -/
  moduli : Fin n → ℕ
  /-- The residues. -/
  residues : Fin n → ℤ
  /-- Every modulus is at least 2. -/
  moduli_ge_two : ∀ i, moduli i ≥ 2
  /-- Every integer is covered by at least one residue class. -/
  covers : ∀ z : ℤ, ∃ i, z % (moduli i : ℤ) = residues i % (moduli i : ℤ)

/-!
## Section II: Prime-Minus-One Moduli
-/

/-- A modulus has the p-1 form for primes ≥ k if m = p - 1 for some prime p ≥ k. -/
def IsPrimeMinusOne (k : ℕ) (m : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ k ≤ p ∧ m = p - 1

/-- All moduli in a covering system have the p-1 form for primes ≥ k. -/
def AllModuliPrimeMinusOne (k : ℕ) (cs : CoveringSystem) : Prop :=
  ∀ i, IsPrimeMinusOne k (cs.moduli i)

/-!
## Section III: The Main Problem
-/

/-- **Erdős Problem #273**: Is there a covering system all of whose moduli
are of the form p - 1 for some primes p ≥ 5?

Since 5 - 1 = 4, 7 - 1 = 6, 11 - 1 = 10, 13 - 1 = 12, etc.,
the allowed moduli are {4, 6, 10, 12, 16, 18, 22, 28, 30, ...}. -/
def ErdosProblem273 : Prop :=
  ∃ cs : CoveringSystem, AllModuliPrimeMinusOne 5 cs

/-!
## Section IV: The Selfridge Example (p ≥ 3)
-/

/-- When p ≥ 3 is allowed, Selfridge found a covering system.
The key is that 2 = 3 - 1 is now an allowed modulus, and the
divisors of 360 = 2³ · 3² · 5 provide sufficient moduli.
The moduli are all of the form p - 1 for primes p ≥ 3. -/
axiom selfridge_example :
  ∃ cs : CoveringSystem, AllModuliPrimeMinusOne 3 cs

/-!
## Section V: Covering System Basics
-/

/-- The LCM of all moduli in a covering system. -/
noncomputable def CoveringSystem.lcm (cs : CoveringSystem) : ℕ :=
  (Finset.univ : Finset (Fin cs.n)).lcm cs.moduli

/-- In any covering system, the sum of reciprocals of moduli is ≥ 1.
This is a necessary condition. -/
axiom covering_reciprocal_sum (cs : CoveringSystem) :
  (Finset.univ : Finset (Fin cs.n)).sum
    (fun i => (1 : ℚ) / (cs.moduli i : ℚ)) ≥ 1

/-- A distinct covering system has all moduli different.
Erdős conjectured (and Hough proved) that distinct covering systems
must have a modulus ≡ 0 (mod 2). -/
def IsDistinct (cs : CoveringSystem) : Prop :=
  Function.Injective cs.moduli

/-!
## Section VI: Connection to Other Problems
-/

/-- The set of primes p ≥ 5 such that p - 1 divides 360.
These are the "easy" primes for constructing covering systems.
360 = 2³ · 3² · 5, and p - 1 | 360 for p ∈ {5, 7, 13, 19, 37, 61, 181}. -/
def easyPrimes : Finset ℕ :=
  {5, 7, 13, 19, 37, 61, 181}

/-- For p ≥ 5, the allowed moduli (p - 1 values) all have
smallest prime factor ≥ 2. The difficulty is that 2 = 3 - 1
is excluded, making it hard to cover all even integers. -/
axiom difficulty_even_coverage :
  ∀ cs : CoveringSystem, AllModuliPrimeMinusOne 5 cs →
    ∀ i, 2 < cs.moduli i

/-- The key obstacle: without modulus 2 (since 3 is excluded),
every modulus is ≥ 4. This severely constrains the covering. -/
axiom min_modulus_ge_4 :
  ∀ cs : CoveringSystem, AllModuliPrimeMinusOne 5 cs →
    ∀ i, cs.moduli i ≥ 4
