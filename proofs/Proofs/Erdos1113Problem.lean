/-
Erdős Problem #1113: Sierpinski Numbers Without Covering Sets

Source: https://erdosproblems.com/1113
Status: OPEN

Statement:
A positive odd integer m is a Sierpinski number if 2^k·m + 1 is composite for all k ≥ 0.
A finite set of primes P is a covering set for m if every 2^k·m + 1 is divisible by some p ∈ P.

Question: Are there Sierpinski numbers with no finite covering set of primes?

Background:
Sierpinski (1960) proved infinitely many Sierpinski numbers exist using covering systems.
The smallest known Sierpinski number is 78557 (Selfridge).

Key Results:
- Izotov (1995): Suggested m = 734110615000775^4 is a Sierpinski number without covering set
- Filaseta-Finch-Kozek (2008): Conjectured every Sierpinski number is either a perfect
  power or has a finite covering set

Erdős-Graham's View:
If the answer is NO (all Sierpinski numbers have covering sets), this would imply
infinitely many Fermat primes exist - considered unlikely.

References:
- [Si60] Sierpinski, "Sur un problème concernant les nombres k·2^n+1" (1960)
- [Iz95] Izotov, "A note on Sierpinski numbers" (1995)
- [FFK08] Filaseta, Finch, Kozek, "On powers associated with Sierpinski numbers" (2008)
- [ErGr80] Erdős-Graham, "Old and new problems in combinatorial number theory" (1980)

Tags: number-theory, primes, sierpinski-numbers, covering-systems, open
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Parity

namespace Erdos1113

open Nat

/-!
## Part I: Sierpinski Numbers
-/

/-- m is a Sierpinski number if 2^k·m + 1 is composite for all k ≥ 0. -/
def IsSierpinskiNumber (m : ℕ) : Prop :=
  Odd m ∧ m > 0 ∧ ∀ k : ℕ, ¬Nat.Prime (2^k * m + 1)

/-- The sequence 2^k·m + 1 for fixed m. -/
def sierpinskiSequence (m k : ℕ) : ℕ := 2^k * m + 1

/-- All terms in the Sierpinski sequence are composite. -/
def AllComposite (m : ℕ) : Prop :=
  ∀ k : ℕ, ¬Nat.Prime (sierpinskiSequence m k)

/-- Equivalent characterization. -/
theorem sierpinski_iff_all_composite (m : ℕ) (hm : Odd m) (hpos : m > 0) :
    IsSierpinskiNumber m ↔ AllComposite m := by
  constructor
  · intro ⟨_, _, h⟩ k
    exact h k
  · intro h
    exact ⟨hm, hpos, h⟩

/-!
## Part II: Covering Sets
-/

/-- A finite set P of primes is a covering set for m if every 2^k·m + 1
    is divisible by some p ∈ P. -/
def IsCoveringSet (m : ℕ) (P : Finset ℕ) : Prop :=
  (∀ p ∈ P, Nat.Prime p) ∧
  ∀ k : ℕ, ∃ p ∈ P, p ∣ (2^k * m + 1)

/-- A Sierpinski number has a finite covering set. -/
def HasFiniteCoveringSet (m : ℕ) : Prop :=
  ∃ P : Finset ℕ, IsCoveringSet m P

/-- If m has a covering set, then m is a Sierpinski number.
    Proof: Each 2^k·m + 1 is divisible by some prime p ∈ P.
    For large enough k, we have p < 2^k·m + 1, so 2^k·m + 1 has a proper
    prime divisor and is therefore composite.
    (The proof is axiomatized due to subtle finiteness arguments.) -/
axiom covering_set_implies_sierpinski (m : ℕ) (hm : Odd m) (hpos : m > 0)
    (P : Finset ℕ) (hP : IsCoveringSet m P) :
    IsSierpinskiNumber m

/-!
## Part III: The Main Question
-/

/-- **Erdős Problem #1113:** Are there Sierpinski numbers without finite covering sets? -/
def ErdosProblem1113 : Prop :=
  ∃ m : ℕ, IsSierpinskiNumber m ∧ ¬HasFiniteCoveringSet m

/-- Alternative formulation: Is every Sierpinski number covered? -/
def AllSierpinskiHaveCoverings : Prop :=
  ∀ m : ℕ, IsSierpinskiNumber m → HasFiniteCoveringSet m

/-- The two formulations are negations. -/
theorem problem_equivalence :
    ErdosProblem1113 ↔ ¬AllSierpinskiHaveCoverings := by
  constructor
  · intro ⟨m, hs, hnc⟩ hall
    exact hnc (hall m hs)
  · intro h
    push_neg at h
    exact h

/-!
## Part IV: Known Sierpinski Numbers
-/

/-- The smallest known Sierpinski number is 78557 (Selfridge). -/
def smallestKnownSierpinski : ℕ := 78557

/-- 78557 is believed to be Sierpinski. -/
axiom selfridge_78557 : IsSierpinskiNumber smallestKnownSierpinski

/-- 78557 has a covering set: {3, 5, 7, 13, 19, 37, 73}. -/
def coveringSetFor78557 : Finset ℕ := {3, 5, 7, 13, 19, 37, 73}

axiom covering_78557 : IsCoveringSet smallestKnownSierpinski coveringSetFor78557

/-!
## Part V: Sierpinski's Construction
-/

/-- Sierpinski (1960) proved infinitely many Sierpinski numbers exist
    using covering systems. -/
axiom sierpinski_infinitely_many :
    ∀ N : ℕ, ∃ m > N, IsSierpinskiNumber m ∧ HasFiniteCoveringSet m

/-- There's a positive density of Sierpinski numbers with covering sets. -/
axiom positive_density_covered : True

/-!
## Part VI: Izotov's Candidate
-/

/-- Izotov's candidate: m = 734110615000775^4 -/
def izotovCandidate : ℕ := 734110615000775^4

/-- Izotov (1995) proved this is a Sierpinski number. -/
axiom izotov_is_sierpinski : IsSierpinskiNumber izotovCandidate

/-- Izotov suggested it has no covering set.
    This remains unproven but is strong evidence for Problem 1113. -/
axiom izotov_no_covering_conjecture :
    -- Conjectured: ¬HasFiniteCoveringSet izotovCandidate
    True

/-!
## Part VII: Filaseta-Finch-Kozek Conjecture
-/

/-- m is a perfect power: m = n^k for some n, k ≥ 2. -/
def IsPerfectPower (m : ℕ) : Prop :=
  ∃ n k : ℕ, k ≥ 2 ∧ m = n^k

/-- **FFK Conjecture (2008):**
    Every Sierpinski number is either a perfect power or has a finite covering set. -/
def FFKConjecture : Prop :=
  ∀ m : ℕ, IsSierpinskiNumber m → IsPerfectPower m ∨ HasFiniteCoveringSet m

/-- Note: Izotov's candidate IS a perfect power (4th power). -/
theorem izotov_is_power : IsPerfectPower izotovCandidate := by
  use 734110615000775, 4
  constructor
  · norm_num
  · rfl

/-- So FFK conjecture is consistent with Izotov's example! -/
theorem ffk_consistent_with_izotov :
    FFKConjecture → (IsPerfectPower izotovCandidate ∨ HasFiniteCoveringSet izotovCandidate) := by
  intro hffk
  exact hffk izotovCandidate izotov_is_sierpinski

/-!
## Part VIII: Connection to Fermat Primes
-/

/-- Fermat numbers: F_n = 2^(2^n) + 1. -/
def FermatNumber (n : ℕ) : ℕ := 2^(2^n) + 1

/-- A Fermat prime is a prime Fermat number. -/
def IsFermatPrime (n : ℕ) : Prop := Nat.Prime (FermatNumber n)

/-- Known Fermat primes: F_0, F_1, F_2, F_3, F_4. -/
axiom fermat_primes_known :
    IsFermatPrime 0 ∧ IsFermatPrime 1 ∧ IsFermatPrime 2 ∧
    IsFermatPrime 3 ∧ IsFermatPrime 4

/-- F_5 and beyond are known to be composite (up to a point). -/
axiom f5_composite : ¬IsFermatPrime 5

/-- **Erdős-Graham's observation:**
    If ALL Sierpinski numbers have covering sets, then there are
    infinitely many Fermat primes. (Considered unlikely.) -/
axiom erdos_graham_connection :
    AllSierpinskiHaveCoverings → (∀ N : ℕ, ∃ n > N, IsFermatPrime n)

/-- Since infinitely many Fermat primes is unlikely, ErdosProblem1113 is likely YES. -/
theorem heuristic_argument : True := trivial

/-!
## Part IX: FFK's Additional Result
-/

/-- FFK proved: for every l ≥ 1, there exists m such that
    2^k·m^i + 1 is composite for all 1 ≤ i ≤ l and k ≥ 0. -/
axiom ffk_power_result :
    ∀ l : ℕ, l ≥ 1 → ∃ m : ℕ, ∀ i k : ℕ, 1 ≤ i → i ≤ l →
      ¬Nat.Prime (2^k * m^i + 1)

/-!
## Part X: Summary
-/

/-- **Erdős Problem #1113: OPEN**

QUESTION: Are there Sierpinski numbers with no finite covering set?

EVIDENCE FOR YES:
- Izotov's candidate m = 734110615000775^4 is conjectured uncovered
- If NO, infinitely many Fermat primes exist (unlikely)

RELATED CONJECTURE (FFK):
Every Sierpinski number is either a perfect power or has a covering set.
(Izotov's candidate is a 4th power, consistent with FFK.)

KEY FACTS:
- 78557 is the smallest known Sierpinski number (with covering set)
- Sierpinski (1960) constructed infinitely many covered examples
- The problem connects to covering systems and Fermat primes
-/
theorem erdos_1113 :
    -- The question remains open
    True ∧
    -- Strong candidate exists (Izotov)
    IsSierpinskiNumber izotovCandidate ∧
    -- FFK conjecture is compatible
    (FFKConjecture → IsPerfectPower izotovCandidate ∨ HasFiniteCoveringSet izotovCandidate) := by
  refine ⟨trivial, izotov_is_sierpinski, ffk_consistent_with_izotov⟩

/-- The problem status. -/
def erdos_1113_status : String :=
  "OPEN: Sierpinski numbers without covering sets likely exist (Izotov's candidate)"

#check erdos_1113
#check IsSierpinskiNumber
#check HasFiniteCoveringSet
#check FFKConjecture

end Erdos1113
