/-
Erdős Problem #275: Covering Congruences

Source: https://erdosproblems.com/275
Status: SOLVED (Selfridge 1970, Crittenden-Vanden Eynden 1970)

Statement:
If a finite system of r congruences {aᵢ (mod nᵢ) : 1 ≤ i ≤ r}
covers 2^r consecutive integers, then it covers all integers.

This bound is best possible: the system {2^(i-1) (mod 2^i) : 1 ≤ i ≤ r}
covers exactly the integers NOT divisible by 2^r, so needs exactly 2^r
consecutive integers to guarantee covering all integers.

Key Insight:
The result is about "covering systems" - collections of congruences
that together hit every integer. The theorem says: if you can cover
2^r consecutive integers with r congruences, you cover everything.

Reference: https://erdosproblems.com/275
-/

import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

namespace Erdos275

/- ## Part I: Basic Definitions -/

/--
**Congruence Class:**
The set of integers congruent to a (mod n).
{a, a ± n, a ± 2n, ...}
-/
def CongruenceClass (a : ℤ) (n : ℕ) : Set ℤ :=
  {x : ℤ | x ≡ a [ZMOD n]}

/--
**Covering System (finite):**
A finite collection of congruence classes.
-/
structure CoveringSystem where
  size : ℕ
  residues : Fin size → ℤ
  moduli : Fin size → ℕ
  moduli_pos : ∀ i, moduli i > 0

/--
**Covered by System:**
An integer x is covered if it belongs to at least one congruence class.
-/
def IsCovered (C : CoveringSystem) (x : ℤ) : Prop :=
  ∃ i : Fin C.size, x ∈ CongruenceClass (C.residues i) (C.moduli i)

/--
**Covers a Set:**
The system covers a set S if every element of S is covered.
-/
def CoversSet (C : CoveringSystem) (S : Set ℤ) : Prop :=
  ∀ x ∈ S, IsCovered C x

/--
**Covers All Integers:**
The system is a complete covering system.
-/
def CoversAll (C : CoveringSystem) : Prop :=
  ∀ x : ℤ, IsCovered C x

/--
**Consecutive Integers:**
The set {a, a+1, ..., a+n-1} of n consecutive integers starting at a.
-/
def ConsecutiveIntegers (a : ℤ) (n : ℕ) : Set ℤ :=
  {x : ℤ | a ≤ x ∧ x < a + n}

/- ## Part II: The 2^r Bound -/

/--
**Erdős Problem #275 (Main Theorem):**
If r congruence classes cover 2^r consecutive integers,
they cover all integers.
-/
axiom erdos_275_theorem (C : CoveringSystem) (a : ℤ) :
    CoversSet C (ConsecutiveIntegers a (2 ^ C.size)) →
    CoversAll C

/--
**Alternative Formulation (Crittenden-Vanden Eynden 1970):**
If r arithmetic progressions cover the first 2^r positive integers,
they cover all integers.
-/
/- ## Part III: Optimality — The 2^r Bound is Tight -/

/--
**The Optimal Example:**
The system {2^(i-1) (mod 2^i) : 1 ≤ i ≤ r} covers everything except
multiples of 2^r.

More precisely: x ∈ 2^(i-1) (mod 2^i) iff the i-th bit of x is 1.
-/
def OptimalExample (r : ℕ) : CoveringSystem where
  size := r
  residues := fun i => 2^(i : ℕ)
  moduli := fun i => 2^((i : ℕ) + 1)
  moduli_pos := fun i => by simp [Nat.pos_pow_of_pos]

/--
**What the Optimal Example Covers:**
x is covered iff x is NOT divisible by 2^r.
-/
/--
**Consecutive Integers Not Covered:**
Among any 2^r - 1 consecutive integers, there's always at least one
multiple of 2^r missing from the coverage of r classes.
-/
axiom not_covered_2r_minus_1 (r : ℕ) (hr : r ≥ 1) :
    ∃ (C : CoveringSystem), C.size = r ∧
    ∃ a : ℤ, CoversSet C (ConsecutiveIntegers a (2^r - 1)) ∧
    ¬CoversAll C

/- ## Part IV: Related Definitions -/

/--
**Covering System predicate:**
A covering system is a finite set of congruence classes that
cover all integers.
-/
def IsCoveringSystem (C : CoveringSystem) : Prop :=
  CoversAll C

/--
**Exactly Covering Systems:**
A system where each integer is covered exactly k times.
For k = 1, these are "disjoint covering systems."
-/
def IsExactlyCovering (C : CoveringSystem) (k : ℕ) : Prop :=
  ∀ x : ℤ, (Finset.univ.filter (fun i =>
    x ∈ CongruenceClass (C.residues i) (C.moduli i))).card = k

/- ## Part V: Summary -/

/--
**Erdős Problem #275: Summary**

Status: SOLVED

**Theorem:** If r congruences cover 2^r consecutive integers,
they cover all integers.

**Optimality:** The bound 2^r is tight.
Example: {2^(i-1) (mod 2^i) : 1 ≤ i ≤ r} needs exactly 2^r
consecutive integers.

**Solvers:**
- John Selfridge (independently)
- Crittenden and Vanden Eynden (1970)
-/
theorem erdos_275 :
    -- Main theorem: 2^r consecutive integers suffice
    (∀ (C : CoveringSystem) (a : ℤ),
      CoversSet C (ConsecutiveIntegers a (2 ^ C.size)) →
      CoversAll C) ∧
    -- The bound is tight
    (∀ r : ℕ, r ≥ 1 →
      ∃ (C : CoveringSystem), C.size = r ∧
      ∃ a : ℤ, CoversSet C (ConsecutiveIntegers a (2^r - 1)) ∧
      ¬CoversAll C) :=
  ⟨erdos_275_theorem, not_covered_2r_minus_1⟩

end Erdos275
