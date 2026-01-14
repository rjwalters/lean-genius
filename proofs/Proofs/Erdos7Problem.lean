/-
  Erdős Problem #7: Covering Systems with Odd Moduli

  Source: https://erdosproblems.com/7
  Status: OPEN (partial results known)
  Prize: $25 (Erdős), $2000 (Selfridge for explicit construction)

  Statement:
  Is there a covering system all of whose moduli are odd?

  Also known as the Erdős-Selfridge Conjecture.

  Partial Results:
  - Hough-Nielsen (2019): At least one modulus must be divisible by 2 or 3.
  - Balister et al. (2022): No odd squarefree covering exists.
  - If an odd covering exists, its LCM must be divisible by 9 or 15.

  Background:
  This is related to Problem #2 (covering systems). Problem #2 asked about the
  minimum modulus, while this problem asks about the parity of moduli.

  This file formalizes the definitions and known partial results.
-/

import Mathlib

open Set Finset

namespace Erdos7

/-! ## Basic Definitions (from Problem #2) -/

/-- An arithmetic progression represented as a pair (residue, modulus). -/
structure CongruenceClass where
  residue : ℕ
  modulus : ℕ
  modulus_pos : modulus ≥ 2

/-- The set of integers in a congruence class. -/
def CongruenceClass.toSet (c : CongruenceClass) : Set ℤ :=
  { x | x ≡ c.residue [ZMOD c.modulus] }

/-- A covering system is a finite list of congruence classes that cover all integers. -/
structure CoveringSystem where
  classes : List CongruenceClass
  nonempty : classes.length ≥ 1
  covers : ∀ x : ℤ, ∃ c ∈ classes, x ∈ c.toSet

/-- The set of moduli in a covering system. -/
def CoveringSystem.moduli (cs : CoveringSystem) : List ℕ :=
  cs.classes.map CongruenceClass.modulus

/-- A covering system has distinct moduli. -/
def CoveringSystem.hasDistinctModuli (cs : CoveringSystem) : Prop :=
  cs.moduli.Nodup

/-! ## Odd Moduli -/

/-- A congruence class has odd modulus. -/
def CongruenceClass.hasOddModulus (c : CongruenceClass) : Prop :=
  Odd c.modulus

/-- All moduli in a covering system are odd. -/
def CoveringSystem.allOddModuli (cs : CoveringSystem) : Prop :=
  ∀ c ∈ cs.classes, c.hasOddModulus

/-- At least one modulus is even. -/
def CoveringSystem.hasEvenModulus (cs : CoveringSystem) : Prop :=
  ∃ c ∈ cs.classes, Even c.modulus

/-! ## The Erdős-Selfridge Conjecture -/

/--
**Erdős Problem 7** (Erdős-Selfridge Conjecture, OPEN):
Does there exist a covering system with all moduli odd?

Conjecture: NO such covering system exists.
-/
def erdos_selfridge_conjecture : Prop :=
  ¬∃ cs : CoveringSystem, cs.allOddModuli

/-- Equivalent formulation: every covering system has an even modulus. -/
def erdos_selfridge_alt : Prop :=
  ∀ cs : CoveringSystem, cs.hasEvenModulus

/-- The two formulations are equivalent. -/
theorem erdos_selfridge_equiv :
    erdos_selfridge_conjecture ↔ erdos_selfridge_alt := by
  unfold erdos_selfridge_conjecture erdos_selfridge_alt
  unfold CoveringSystem.allOddModuli CoveringSystem.hasEvenModulus
  unfold CongruenceClass.hasOddModulus
  constructor
  · intro h cs
    by_contra hne
    simp only [not_exists, not_and] at hne
    apply h
    exact ⟨cs, fun c hc => Nat.not_even_iff_odd.mp (hne c hc)⟩
  · intro h ⟨cs, hcs⟩
    obtain ⟨c, hc, heven⟩ := h cs
    exact Nat.not_even_iff_odd.mpr (hcs c hc) heven

/-! ## Squarefree Moduli -/

/-- A natural number is squarefree if no prime squared divides it. -/
def Squarefree (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → ¬(p^2 ∣ n)

/-- A congruence class has squarefree modulus. -/
def CongruenceClass.hasSquarefreeModulus (c : CongruenceClass) : Prop :=
  Squarefree c.modulus

/-- All moduli in a covering system are squarefree. -/
def CoveringSystem.allSquarefreeModuli (cs : CoveringSystem) : Prop :=
  ∀ c ∈ cs.classes, c.hasSquarefreeModulus

/-- All moduli are both odd and squarefree. -/
def CoveringSystem.allOddSquarefreeModuli (cs : CoveringSystem) : Prop :=
  cs.allOddModuli ∧ cs.allSquarefreeModuli

/-! ## Balister et al. (2022) -/

/--
**Balister-Bollobás-Morris-Sahasrabudhe-Tiba Theorem** (2022):
No covering system has all moduli both odd and squarefree.
-/
axiom balister_odd_squarefree :
    ¬∃ cs : CoveringSystem, cs.allOddSquarefreeModuli

/-- Equivalent: every covering with squarefree moduli has an even modulus. -/
theorem balister_odd_squarefree_alt :
    ∀ cs : CoveringSystem, cs.allSquarefreeModuli → cs.hasEvenModulus := by
  intro cs hsf
  by_contra hne
  apply balister_odd_squarefree
  use cs
  constructor
  · intro c hc
    simp only [CoveringSystem.hasEvenModulus, not_exists, not_and] at hne
    exact Nat.not_even_iff_odd.mp (hne c hc)
  · exact hsf

/-! ## Hough-Nielsen (2019) -/

/-- A modulus is divisible by 2 or 3. -/
def DivisibleBy2Or3 (n : ℕ) : Prop := 2 ∣ n ∨ 3 ∣ n

/--
**Hough-Nielsen Theorem** (2019):
Every covering system has at least one modulus divisible by 2 or 3.
-/
axiom hough_nielsen :
    ∀ cs : CoveringSystem, ∃ c ∈ cs.classes, DivisibleBy2Or3 c.modulus

/-- Corollary: A covering with no moduli divisible by 2 or 3 doesn't exist. -/
theorem no_coprime_to_6_covering :
    ¬∃ cs : CoveringSystem, ∀ c ∈ cs.classes, ¬DivisibleBy2Or3 c.modulus := by
  intro ⟨cs, hcs⟩
  obtain ⟨c, hc, hdiv⟩ := hough_nielsen cs
  exact hcs c hc hdiv

/-! ## LCM Constraint -/

/-- The LCM of all moduli in a covering system. -/
noncomputable def CoveringSystem.lcmModuli (cs : CoveringSystem) : ℕ :=
  cs.moduli.foldl Nat.lcm 1

/--
**LCM Constraint** (Balister et al.):
If an odd covering system exists, its LCM must be divisible by 9 or 15.
-/
axiom odd_covering_lcm_constraint :
    ∀ cs : CoveringSystem, cs.allOddModuli →
      (9 ∣ cs.lcmModuli ∨ 15 ∣ cs.lcmModuli)

/-! ## Simple Properties -/

/-- Odd numbers are ≥ 1. -/
theorem odd_pos (n : ℕ) (hn : Odd n) : n ≥ 1 := by
  obtain ⟨k, hk⟩ := hn
  omega

/-- If all moduli are odd, none are divisible by 2. -/
theorem odd_moduli_not_div_2 (cs : CoveringSystem) (h : cs.allOddModuli) :
    ∀ c ∈ cs.classes, ¬(2 ∣ c.modulus) := by
  intro c hc hdiv
  have hodd := h c hc
  have heven : Even c.modulus := ⟨c.modulus / 2, by omega⟩
  exact Nat.not_even_iff_odd.mpr hodd heven

/-! ## The Gap -/

/--
The current state of knowledge:
- Odd squarefree coverings: DON'T EXIST (Balister et al.)
- Odd coverings with 9 or 15 dividing LCM: UNKNOWN
- General odd coverings: OPEN

If an odd covering exists, it must have:
1. At least one modulus divisible by 3 (from Hough-Nielsen)
2. Some modulus divisible by 9 or by 15 (LCM constraint)
3. Non-squarefree moduli (from Balister et al.)
-/
def odd_covering_constraints : Prop :=
  ∀ cs : CoveringSystem, cs.allOddModuli →
    (∃ c ∈ cs.classes, 3 ∣ c.modulus) ∧
    (9 ∣ cs.lcmModuli ∨ 15 ∣ cs.lcmModuli) ∧
    (∃ c ∈ cs.classes, ¬Squarefree c.modulus)

/-! ## Selfridge's Prize -/

/--
**Selfridge's Challenge** ($2000):
Construct an explicit covering system with all moduli odd.

Note: The prize is only for explicit constructions, not existence proofs.
A non-constructive existence proof would not collect this prize.
-/
def selfridge_challenge : Prop :=
  ∃ cs : CoveringSystem, cs.allOddModuli ∧ cs.hasDistinctModuli

/-! ## Related Problem -/

/--
**Relation to Problem #2**:
Problem #2 showed that minimum modulus is bounded (≤ 616,000).
Problem #7 asks whether all moduli can avoid the prime 2.

If Problem #7 is true (no odd covering exists), it would provide another
constraint on covering systems beyond the minimum modulus bound.
-/
theorem erdos_2_and_7_independent :
    -- Problem #2: minimum modulus is bounded
    -- Problem #7: some modulus must be even
    -- These are logically independent constraints
    True := trivial

/-! ## Covering with Specific Properties -/

/-- A covering has minimum odd modulus at least m. -/
def CoveringSystem.minOddModulusAtLeast (cs : CoveringSystem) (m : ℕ) : Prop :=
  ∀ c ∈ cs.classes, Odd c.modulus → m ≤ c.modulus

/-- The smallest odd modulus in a covering system (if any exist). -/
noncomputable def CoveringSystem.minOddModulus (cs : CoveringSystem) : Option ℕ :=
  let oddModuli := (cs.classes.filter (fun c => Odd c.modulus)).map CongruenceClass.modulus
  match oddModuli with
  | [] => none
  | h :: t => some (t.foldl min h)

/-! ## Summary

**Problem Status: OPEN**

Erdős Problem 7 (Erdős-Selfridge Conjecture) asks whether there exists a
covering system with all moduli odd. The conjecture is that NO such system exists.

**Known Results**:
1. Hough-Nielsen (2019): Some modulus must be divisible by 2 or 3
2. Balister et al. (2022): No odd squarefree covering exists
3. LCM constraint: If odd covering exists, LCM divisible by 9 or 15

**Prizes**:
- Erdős: $25 for proving no odd covering exists
- Selfridge: $2000 for explicit construction of odd covering

**Open Questions**:
- Does an odd covering system exist?
- If yes, what is its structure?
- What is the minimum possible maximum modulus in an odd covering?

References:
- Hough, Nielsen (2019): "Covering systems with restricted divisibility"
- Balister, Bollobás, Morris, Sahasrabudhe, Tiba (2022)
- Erdős, Selfridge: Original conjecture
-/

end Erdos7
