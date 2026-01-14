/-
  Erdős Problem #2: Covering Systems

  Source: https://erdosproblems.com/2
  Status: SOLVED (Hough 2015, Balister et al. 2022)
  Prize: $1000

  Statement:
  Can the smallest modulus of a covering system be arbitrarily large?

  Answer: NO.
  - Hough (2015): The smallest modulus must be at most 10^16.
  - Balister, Bollobás, Morris, Sahasrabudhe, Tiba (2022): Improved to 616,000.
  - Owens (2014): Constructed a covering system with smallest modulus 42.

  Definition:
  A covering system is a finite collection of arithmetic progressions
  {a₁ mod n₁, a₂ mod n₂, ..., aₖ mod nₖ} such that every integer belongs
  to at least one of these progressions. The moduli n₁, n₂, ..., nₖ must
  all be distinct and at least 2.

  Erdős described this as "perhaps my favourite problem." He conjectured
  that the answer would be YES, but Hough proved otherwise.

  This file formalizes the definitions and key results.
-/

import Mathlib

open Set Finset

namespace Erdos2

/-! ## Basic Definitions -/

/-- An arithmetic progression: integers congruent to a modulo n. -/
def ArithmeticProgression (a n : ℕ) : Set ℤ :=
  { x | x ≡ a [ZMOD n] }

/-- An arithmetic progression represented as a pair (residue, modulus). -/
structure CongruenceClass where
  residue : ℕ
  modulus : ℕ
  modulus_pos : modulus ≥ 2

/-- The set of integers in a congruence class. -/
def CongruenceClass.toSet (c : CongruenceClass) : Set ℤ :=
  { x | x ≡ c.residue [ZMOD c.modulus] }

/-! ## Covering Systems -/

/-- A covering system is a finite list of congruence classes that cover all integers.
    In the classical definition, moduli must be distinct, but we separate this as a property. -/
structure CoveringSystem where
  classes : List CongruenceClass
  nonempty : classes.length ≥ 1
  covers : ∀ x : ℤ, ∃ c ∈ classes, x ∈ c.toSet

/-- A covering system has distinct moduli. -/
def CoveringSystem.hasDistinctModuli (cs : CoveringSystem) : Prop :=
  cs.classes.map CongruenceClass.modulus |>.Nodup

/-- The set of moduli in a covering system. -/
def CoveringSystem.moduli (cs : CoveringSystem) : List ℕ :=
  cs.classes.map CongruenceClass.modulus

/-- The minimum modulus in a covering system. -/
noncomputable def CoveringSystem.minModulus (cs : CoveringSystem) : ℕ :=
  cs.moduli.foldl min (cs.moduli.head!)

/-- A covering system has minimum modulus at least m. -/
def CoveringSystem.hasMinModulusAtLeast (cs : CoveringSystem) (m : ℕ) : Prop :=
  ∀ c ∈ cs.classes, m ≤ c.modulus

/-! ## The Erdős Conjecture (Disproved) -/

/--
**Erdős' Original Conjecture** (DISPROVED):
For any N, there exists a covering system with minimum modulus at least N.

Erdős believed this to be true. He described it as "perhaps my favourite problem."
-/
def erdos_original_conjecture : Prop :=
  ∀ N : ℕ, ∃ cs : CoveringSystem, cs.hasMinModulusAtLeast N

/-! ## Main Result: The Answer is NO -/

/--
**Erdős Problem 2** (SOLVED):
There exists a universal bound N such that every covering system has
minimum modulus at most N.
-/
def erdos_2_solution : Prop :=
  ∃ N : ℕ, ∀ cs : CoveringSystem, ∃ c ∈ cs.classes, c.modulus ≤ N

/-- The solution implies the conjecture is false. -/
theorem solution_implies_not_conjecture :
    erdos_2_solution → ¬erdos_original_conjecture := by
  intro ⟨N, hN⟩ hconj
  obtain ⟨cs, hcs⟩ := hconj (N + 1)
  obtain ⟨c, hc, hle⟩ := hN cs
  have : N + 1 ≤ c.modulus := hcs c hc
  omega

/-! ## Hough's Theorem (2015) -/

/--
**Hough's Theorem** (2015):
Every covering system has a modulus at most 10^16.

This disproved Erdős' conjecture. The proof built on work by
Filaseta, Ford, Konyagin, Pomerance, and Yu (2007).
-/
axiom hough_bound : ∀ cs : CoveringSystem, ∃ c ∈ cs.classes, c.modulus ≤ 10^16

/-- Hough's bound as a specific value. -/
def hough_N : ℕ := 10^16

/-- Hough's theorem implies the solution. -/
theorem hough_implies_solution : erdos_2_solution :=
  ⟨hough_N, hough_bound⟩

/-! ## Balister et al. Improvement (2022) -/

/--
**Balister-Bollobás-Morris-Sahasrabudhe-Tiba Theorem** (2022):
Every covering system has a modulus at most 616,000.

This is a significant improvement over Hough's bound, with a simpler proof.
-/
axiom balister_bound : ∀ cs : CoveringSystem, ∃ c ∈ cs.classes, c.modulus ≤ 616000

/-- The improved bound from Balister et al. -/
def balister_N : ℕ := 616000

/-- The best known upper bound on minimum modulus. -/
def best_upper_bound : ℕ := 616000

/-! ## Owens' Construction (2014) -/

/--
**Owens' Construction** (2014):
There exists a covering system with minimum modulus 42.

This is the best known lower bound on the maximum possible minimum modulus.
-/
axiom owens_construction :
    ∃ cs : CoveringSystem, cs.hasMinModulusAtLeast 42

/-- The best known lower bound on minimum modulus. -/
def best_lower_bound : ℕ := 42

/-- The current state of knowledge: minimum modulus is between 42 and 616,000. -/
theorem bounds_summary :
    (∃ cs : CoveringSystem, cs.hasMinModulusAtLeast best_lower_bound) ∧
    (∀ cs : CoveringSystem, ∃ c ∈ cs.classes, c.modulus ≤ best_upper_bound) :=
  ⟨owens_construction, balister_bound⟩

/-! ## Simple Covering Systems -/

/-- A modulus 2 congruence class: even or odd integers. -/
def mod2_even : CongruenceClass := ⟨0, 2, by norm_num⟩
def mod2_odd : CongruenceClass := ⟨1, 2, by norm_num⟩

/-- The integers are partitioned into even and odd. -/
theorem even_odd_cover : ∀ x : ℤ, x ∈ mod2_even.toSet ∨ x ∈ mod2_odd.toSet := by
  intro x
  unfold mod2_even mod2_odd CongruenceClass.toSet
  simp only [mem_setOf_eq, Int.ModEq]
  rcases Int.emod_two_eq_zero_or_one x with h | h
  · left; omega
  · right; omega

/-- A trivial covering system using {0 mod 2, 1 mod 2} is not interesting
    because it has minimum modulus 2. -/
theorem trivial_cover_min_modulus : ∃ cs : CoveringSystem, cs.hasMinModulusAtLeast 2 := by
  use {
    classes := [mod2_even, mod2_odd],
    nonempty := by simp,
    covers := fun x => by
      rcases even_odd_cover x with h | h
      · exact ⟨mod2_even, by simp, h⟩
      · exact ⟨mod2_odd, by simp, h⟩
  }
  intro c hc
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl <;> simp [mod2_even, mod2_odd]

/-! ## Properties of Covering Systems -/

/-- In a covering system with distinct moduli, the moduli are all different. -/
theorem covering_distinct_moduli (cs : CoveringSystem) (hd : cs.hasDistinctModuli) :
    (cs.classes.map CongruenceClass.modulus).Nodup :=
  hd

/-- Every covering system has at least one congruence class. -/
theorem covering_nonempty (cs : CoveringSystem) : cs.classes.length ≥ 1 :=
  cs.nonempty

/-- Every integer is covered by some congruence class. -/
theorem covering_complete (cs : CoveringSystem) :
    ∀ x : ℤ, ∃ c ∈ cs.classes, x ∈ c.toSet :=
  cs.covers

/-! ## Density Argument (Intuition) -/

/--
**Key Insight**: The sum of reciprocals of moduli in a covering system
must be at least 1 (since the progressions cover all integers).

For distinct moduli starting at m, the sum 1/m + 1/(m+1) + ... must be ≥ 1.
For large m, this sum is approximately ln(k/m) where k is the largest modulus.
This constrains how large m can be.
-/
def CoveringSystem.reciprocalSum (cs : CoveringSystem) : ℚ :=
  (cs.moduli.map (fun n => (1 : ℚ) / n)).sum

/-- The reciprocal sum of a covering system is at least 1. -/
axiom reciprocal_sum_ge_one (cs : CoveringSystem) : cs.reciprocalSum ≥ 1

/-! ## Related Problems -/

/--
**Open Question**: What is the exact maximum possible minimum modulus?
Currently known to be between 42 and 616,000.
-/
def exact_maximum_min_modulus : Prop :=
  ∃ M : ℕ, (∃ cs : CoveringSystem, cs.hasMinModulusAtLeast M) ∧
           (∀ cs : CoveringSystem, ∃ c ∈ cs.classes, c.modulus ≤ M)

/--
**Erdős-Selfridge Conjecture** (Related):
No covering system has all moduli being odd.
This remains OPEN.
-/
def erdos_selfridge_conjecture : Prop :=
  ∀ cs : CoveringSystem, ∃ c ∈ cs.classes, Even c.modulus

/-! ## Summary

**Problem Status: SOLVED**

Erdős Problem 2 asked whether the minimum modulus of a covering system
can be arbitrarily large. The answer is NO.

**Key Results**:
1. Hough (2015): Upper bound of 10^16
2. Balister et al. (2022): Upper bound of 616,000
3. Owens (2014): Lower bound of 42 (construction)

**Gap**: The exact maximum possible minimum modulus is between 42 and 616,000.

**Open Questions**:
- What is the exact maximum minimum modulus?
- Does every covering system have an even modulus? (Erdős-Selfridge)

References:
- Hough, "Solution of the minimum modulus problem for covering systems" (2015)
- Balister et al., "Covering systems with restricted divisibility" (2022)
- Owens, "A covering system with minimum modulus 42" (2014)
- Filaseta, Ford, Konyagin, Pomerance, Yu (2007)
-/

end Erdos2
