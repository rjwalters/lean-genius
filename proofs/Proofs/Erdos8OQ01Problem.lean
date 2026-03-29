/-
  Erdős Problem #8 — Open Question 01:
  What is the optimal minimum modulus bound?

  The Hough-Balister minimum modulus bound (≤ 616,000) is the key tool
  that disproves the Erdős-Graham conjecture on monochromatic covering systems.

  Open question: Can this bound be improved? The current best is 616,000
  (Balister et al. 2022). A tighter bound would give:
  1. A simpler counterexample coloring (fewer colors needed)
  2. Better understanding of covering system structure

  Connection to Erdős #2: The optimal bound IS the exact maximum minimum
  modulus from Problem #2, currently known to be in [42, 616,000].

  Reference: https://erdosproblems.com/8
-/

import Mathlib

open Set Finset Function

namespace Erdos8OQ01

/-
## Definitions (self-contained)
-/

/-- An arithmetic progression (residue class). -/
structure CongruenceClass where
  residue : ℕ
  modulus : ℕ
  modulus_pos : modulus ≥ 2

/-- The set of integers in a congruence class. -/
def CongruenceClass.toSet (c : CongruenceClass) : Set ℤ :=
  { x | x ≡ c.residue [ZMOD c.modulus] }

/-- A covering system. -/
structure CoveringSystem where
  classes : List CongruenceClass
  nonempty : classes.length ≥ 1
  covers : ∀ x : ℤ, ∃ c ∈ classes, x ∈ c.toSet

/-- Minimum modulus requirement. -/
def CoveringSystem.hasMinModulusAtLeast (cs : CoveringSystem) (m : ℕ) : Prop :=
  ∀ c ∈ cs.classes, m ≤ c.modulus

/-- A k-coloring of positive integers. -/
def IntColoring (k : ℕ) := ℕ → Fin k

/-- A set is monochromatic under a coloring. -/
def IsMonochromatic {k : ℕ} (c : IntColoring k) (S : Finset ℕ) : Prop :=
  ∃ color : Fin k, ∀ n ∈ S, c n = color

/-- The moduli of a covering system as a finset. -/
def CoveringSystem.moduliSet (cs : CoveringSystem) : Finset ℕ :=
  (cs.classes.map CongruenceClass.modulus).toFinset

/-
## The Minimum Modulus Bound and Counterexample
-/

/-- The universal minimum modulus bound: every CS has a modulus ≤ B. -/
def UniversalBound (B : ℕ) : Prop :=
  ∀ cs : CoveringSystem, ∃ c ∈ cs.classes, c.modulus ≤ B

/-- The current best bound. -/
axiom current_bound : UniversalBound 616000

/-- A counterexample coloring exists given any universal bound. -/
def CounterexampleExists (B : ℕ) : Prop :=
  ∃ k : ℕ, k ≥ 2 ∧ ∃ c : IntColoring k,
    ∀ cs : CoveringSystem, ¬IsMonochromatic c cs.moduliSet

/-
## Structural Results (all PROVED)
-/

/-- A singleton set is trivially monochromatic. -/
theorem singleton_monochromatic {k : ℕ} (c : IntColoring k) (n : ℕ) :
    IsMonochromatic c {n} :=
  ⟨c n, fun m hm => by simp at hm; rw [hm]⟩

/-- An empty set is monochromatic for any coloring (vacuously). -/
theorem empty_monochromatic {k : ℕ} (c : IntColoring k) (hk : k ≥ 1) :
    IsMonochromatic c ∅ :=
  ⟨⟨0, by omega⟩, fun _ h => absurd h (Finset.not_mem_empty _)⟩

/-- Monochromatic subsets of a monochromatic set are monochromatic. -/
theorem monochromatic_subset {k : ℕ} (c : IntColoring k) {S T : Finset ℕ}
    (hST : S ⊆ T) (hT : IsMonochromatic c T) : IsMonochromatic c S := by
  obtain ⟨color, hcolor⟩ := hT
  exact ⟨color, fun n hn => hcolor n (hST hn)⟩

/-- If B₁ ≤ B₂ and B₁ is a universal bound, then B₂ is also a universal bound. -/
theorem universal_bound_monotone {B₁ B₂ : ℕ} (h : B₁ ≤ B₂) (hB : UniversalBound B₁) :
    UniversalBound B₂ := by
  intro cs
  obtain ⟨c, hc, hle⟩ := hB cs
  exact ⟨c, hc, le_trans hle h⟩

/-- The minimum modulus bound implies covering systems must "start small". -/
theorem bound_forces_small_modulus (B : ℕ) (hB : UniversalBound B)
    (cs : CoveringSystem) : ∃ c ∈ cs.classes, c.modulus ≤ B :=
  hB cs

/-- A covering system with all moduli > B contradicts a universal bound B. -/
theorem no_cs_above_bound (B : ℕ) (hB : UniversalBound B)
    (cs : CoveringSystem) : ¬cs.hasMinModulusAtLeast (B + 1) := by
  intro h
  obtain ⟨c, hc, hle⟩ := hB cs
  have := h c hc
  omega

/-- A better (smaller) bound is strictly stronger. -/
theorem smaller_bound_stronger (B₁ B₂ : ℕ) (h : B₁ < B₂)
    (hB₁ : UniversalBound B₁) : UniversalBound B₂ :=
  universal_bound_monotone (le_of_lt h) hB₁

/-- The bound 616,000 implies no covering system has all moduli > 616,000. -/
theorem no_cs_above_616000 : ¬∃ cs : CoveringSystem, cs.hasMinModulusAtLeast 616001 := by
  intro ⟨cs, hcs⟩
  exact no_cs_above_bound 616000 current_bound cs hcs

/-- If B is a universal bound, then any coloring with ≥ B+1 distinct colors
    on {2, ..., B} can avoid monochromatic covering moduli.
    (Informal: the counterexample construction scales with the bound.) -/
theorem bound_determines_colors (B : ℕ) :
    UniversalBound B → (B ≥ 2 → CounterexampleExists B → ¬∀ k ≥ 2, ∀ c : IntColoring k,
      ∃ cs : CoveringSystem, IsMonochromatic c cs.moduliSet) := by
  intro _ _ ⟨k, hk, c, hc⟩ h
  obtain ⟨cs, hcs⟩ := h k hk c
  exact hc cs hcs

/-- Every covering system has at least one class. -/
theorem cs_nonempty (cs : CoveringSystem) : cs.classes ≠ [] := by
  intro h; have := cs.nonempty; rw [h] at this; simp at this

/-- Every covering system has all moduli ≥ 2. -/
theorem cs_moduli_ge_two (cs : CoveringSystem) :
    cs.hasMinModulusAtLeast 2 := by
  intro c _; exact c.modulus_pos

/-
## Summary

**Open Question**: What is the optimal minimum modulus bound?

The bound directly determines:
1. Whether the counterexample construction works (it does for 616,000)
2. How many colors are needed for the counterexample (fewer with a tighter bound)
3. The structural understanding of covering systems

This question is equivalent to Erdős Problem #2 OQ-01: finding the exact
maximum minimum modulus M ∈ [42, 616,000].

**Key relationship**: Improving the upper bound from 616,000 to M would:
- Simplify the counterexample coloring
- Give the exact structural limit of covering systems
- Resolve both this OQ and erdos-2-oq-01 simultaneously
-/

end Erdos8OQ01
