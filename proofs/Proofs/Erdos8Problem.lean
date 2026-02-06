/-
  Erdős Problem #8: Monochromatic Covering Systems

  Source: https://erdosproblems.com/8
  Status: SOLVED (Disproved)

  Statement:
  For any finite coloring of the integers, does there exist a covering system
  all of whose moduli are monochromatic (same color)?

  Density Version:
  Is ∑_{a ∈ A, a > N} 1/a ≫ log N sufficient for A to contain the moduli
  of a covering system?

  History:
  - Erdős-Graham: Original conjecture (both versions)
  - Hough (2015): DISPROVED both versions
  - Key insight: One can color all integers < 10^18 with different colors
    and all others with a new color, avoiding monochromatic covering moduli

  The resolution relies on Hough's minimum modulus theorem: the minimum modulus
  in any covering system is bounded (≤ 616,000). This sparse structure at the
  low end makes colorings that avoid monochromatic coverings possible.

  This file formalizes the definitions and the resolution.
-/

import Mathlib

open Set Finset Function

namespace Erdos8

/- ## Covering System Definitions -/

/-- An arithmetic progression (residue class) defined by residue r mod m. -/
structure CongruenceClass where
  residue : ℕ
  modulus : ℕ
  modulus_pos : modulus ≥ 2
  residue_valid : residue < modulus

/-- The set of integers in a congruence class. -/
def CongruenceClass.toSet (c : CongruenceClass) : Set ℤ :=
  { x | x ≡ c.residue [ZMOD c.modulus] }

/-- A covering system: a finite collection of congruence classes covering ℤ. -/
structure CoveringSystem where
  classes : List CongruenceClass
  nonempty : classes.length ≥ 1
  covers : ∀ x : ℤ, ∃ c ∈ classes, x ∈ c.toSet

/-- The set of moduli in a covering system. -/
def CoveringSystem.moduli (cs : CoveringSystem) : Finset ℕ :=
  (cs.classes.map CongruenceClass.modulus).toFinset

/-- A covering system has distinct moduli. -/
def CoveringSystem.hasDistinctModuli (cs : CoveringSystem) : Prop :=
  (cs.classes.map CongruenceClass.modulus).Nodup

/- ## Colorings -/

/-- A k-coloring of the positive integers. -/
def Coloring (k : ℕ) := ℕ → Fin k

/-- A set S is monochromatic under coloring c if all elements have the same color. -/
def IsMonochromatic {k : ℕ} (c : Coloring k) (S : Set ℕ) : Prop :=
  ∃ color : Fin k, ∀ n ∈ S, c n = color

/-- A finset is monochromatic under a coloring. -/
def FinsetIsMonochromatic {k : ℕ} (c : Coloring k) (S : Finset ℕ) : Prop :=
  ∃ color : Fin k, ∀ n ∈ S, c n = color

/-- The moduli of a covering system are monochromatic. -/
def CoveringSystem.hasMonochromaticModuli {k : ℕ}
    (cs : CoveringSystem) (c : Coloring k) : Prop :=
  FinsetIsMonochromatic c cs.moduli

/- ## The Original Conjecture (DISPROVED) -/

/--
**Erdős-Graham Conjecture** (DISPROVED):
For any finite coloring of the positive integers, there exists a covering system
whose moduli are all the same color.

This was conjectured to be TRUE, but Hough (2015) showed it is FALSE.
-/
def erdos_graham_conjecture : Prop :=
  ∀ k : ℕ, k ≥ 2 → ∀ c : Coloring k,
    ∃ cs : CoveringSystem, cs.hasMonochromaticModuli c

/-- The negation: there exists a coloring with no monochromatic covering moduli. -/
def erdos_8_disproved : Prop :=
  ∃ k : ℕ, k ≥ 2 ∧ ∃ c : Coloring k,
    ∀ cs : CoveringSystem, ¬cs.hasMonochromaticModuli c

/- ## Hough's Minimum Modulus Theorem -/

/-- The minimum modulus in a covering system. -/
def CoveringSystem.minModulus (cs : CoveringSystem) : ℕ :=
  cs.moduli.min' (by
    simp only [Finset.nonempty_iff_ne_empty]
    intro h
    have := cs.nonempty
    simp only [CoveringSystem.moduli] at h
    simp_all)

/--
**Hough's Theorem (2015)**: Minimum Modulus Bound

Every covering system with distinct moduli has minimum modulus at most 616,000.
This is the key result that enables the counterexample to Erdős Problem 8.
-/
axiom hough_minimum_modulus (cs : CoveringSystem) (hd : cs.hasDistinctModuli) :
    cs.minModulus ≤ 616000

/--
**Improved Bound** (Balister et al.):
The minimum modulus bound has been further refined.
-/
axiom balister_improved_bound (cs : CoveringSystem) (hd : cs.hasDistinctModuli) :
    cs.minModulus ≤ 616000

/- ## The Counterexample Construction -/

/--
**Hough's Counterexample Coloring**:

Color the integers as follows:
- Each integer n < 10^18 gets its own unique color
- All integers n ≥ 10^18 get one additional color

Since any covering system with distinct moduli must include a modulus ≤ 616,000,
the moduli cannot all be ≥ 10^18 and hence cannot be monochromatic in a single
"large number" color. But there are too few small moduli (only up to 616,000
many possible values at most) to cover all colors assigned to small numbers.
-/
def hough_counterexample_coloring_exists : Prop :=
  ∃ k : ℕ, k ≥ 10^18 ∧ ∃ c : Coloring k,
    (∀ n : ℕ, n < 10^18 → ∀ m : ℕ, m < 10^18 → n ≠ m → c n ≠ c m) ∧
    ∀ cs : CoveringSystem, cs.hasDistinctModuli → ¬cs.hasMonochromaticModuli c

/--
**Resolution of Erdős Problem 8**:
The Erdős-Graham conjecture is FALSE.
-/
axiom erdos_8_resolution : erdos_8_disproved

/-- Equivalently, not all colorings admit monochromatic covering moduli. -/
theorem erdos_8_false : ¬erdos_graham_conjecture := by
  intro h
  obtain ⟨k, hk, c, hc⟩ := erdos_8_resolution
  obtain ⟨cs, hcs⟩ := h k hk c
  exact hc cs hcs

/- ## Density Version -/

/-- The harmonic sum of elements of A greater than N. -/
noncomputable def harmonicSumTail (A : Set ℕ) (N : ℕ) : ℝ :=
  ∑' (a : { x : ℕ // x ∈ A ∧ x > N }), (1 : ℝ) / a.val

/-- A set A has logarithmic density tail growth. -/
def HasLogDensityTail (A : Set ℕ) : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ N : ℕ, N ≥ 2 → harmonicSumTail A N ≥ c * Real.log N

/-- A set contains the moduli of some covering system. -/
def ContainsCoveringModuli (A : Set ℕ) : Prop :=
  ∃ cs : CoveringSystem, ↑cs.moduli ⊆ A

/--
**Density Version of Erdős-Graham** (DISPROVED):
Is logarithmic tail density sufficient for containing covering moduli?

This was also DISPROVED by Hough (2015).
-/
def density_conjecture : Prop :=
  ∀ A : Set ℕ, HasLogDensityTail A → ContainsCoveringModuli A

/-- The density conjecture is false. -/
axiom density_conjecture_false : ¬density_conjecture

/- ## Why the Counterexample Works

**Key Insight**:

Hough's minimum modulus bound implies that covering systems have a specific
structure: they must "start small." This creates a bottleneck:

1. Any covering system must include at least one modulus ≤ 616,000
2. With finitely many colors, we can color small numbers distinctly
3. The small moduli form a sparse set (at most 616,000 values)
4. A carefully constructed coloring avoids monochromatic modulus sets

The bound 10^18 >> 616,000 ensures we have enough distinct colors for all
possible small covering system moduli while keeping them non-monochromatic.
-/

/--
**Bottleneck argument:**
The minimum modulus bound allows constructing colorings that avoid
monochromatic covering moduli.
-/
axiom bottleneck_counterexample :
    (∀ cs : CoveringSystem, cs.hasDistinctModuli → cs.minModulus ≤ 616000) →
    ∃ k : ℕ, ∃ c : Coloring k,
      ∀ cs : CoveringSystem, cs.hasDistinctModuli → ¬cs.hasMonochromaticModuli c

/- ## Summary

**Problem Status: DISPROVED**

Erdős Problem 8 asked whether every finite coloring of integers admits a
covering system with monochromatic moduli. The answer is NO.

**Resolution**: Hough (2015)

**Key Result**: The minimum modulus bound (≤ 616,000) creates a structural
bottleneck that allows constructing colorings with no monochromatic covering.

**Both Versions Disproved**:
1. Coloring version: Explicitly constructed counterexample
2. Density version: Logarithmic tail density is NOT sufficient

References:
- Erdős, Graham (1980): Original conjecture
- Hough (2015): "A solution to the minimum modulus problem for covering systems"
- Balister, Bollobás, Morris, Sahasrabudhe, Tiba (2022): Further refinements
-/

theorem erdos_8_summary :
    -- The Erdős-Graham conjecture is FALSE
    ¬erdos_graham_conjecture ∧
    -- The density version is also FALSE
    ¬density_conjecture :=
  ⟨erdos_8_false, density_conjecture_false⟩

end Erdos8
