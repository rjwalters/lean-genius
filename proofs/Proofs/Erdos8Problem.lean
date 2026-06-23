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
with distinct moduli whose moduli are all the same color.

This was conjectured to be TRUE, but Hough (2015) showed it is FALSE.

Note: Covering systems classically have distinct moduli. Without this condition,
trivial systems like {0 mod 2, 1 mod 2} always have monochromatic moduli ({2}).
-/
def erdos_graham_conjecture : Prop :=
  ∀ k : ℕ, k ≥ 2 → ∀ c : Coloring k,
    ∃ cs : CoveringSystem, cs.hasDistinctModuli ∧ cs.hasMonochromaticModuli c

/-- The negation: there exists a coloring where no covering system with distinct
    moduli has monochromatic moduli. -/
def erdos_8_disproved : Prop :=
  ∃ k : ℕ, k ≥ 2 ∧ ∃ c : Coloring k,
    ∀ cs : CoveringSystem, cs.hasDistinctModuli → ¬cs.hasMonochromaticModuli c

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
(Currently stated with same bound as Hough; derived from `hough_minimum_modulus`.)
-/
theorem balister_improved_bound (cs : CoveringSystem) (hd : cs.hasDistinctModuli) :
    cs.minModulus ≤ 616000 :=
  hough_minimum_modulus cs hd

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
**Resolution of Erdős Problem 8** (PROVED — was axiom):
The Erdős-Graham conjecture is FALSE.

Derived from `bottleneck_counterexample` and `hough_minimum_modulus`:
Hough's bound provides the hypothesis, and the bottleneck construction
produces a coloring that avoids monochromatic covering moduli.
-/
theorem erdos_8_resolution : erdos_8_disproved :=
  bottleneck_counterexample fun cs hd => hough_minimum_modulus cs hd

/-- Equivalently, not all colorings admit monochromatic covering moduli. -/
theorem erdos_8_false : ¬erdos_graham_conjecture := by
  intro h
  obtain ⟨k, hk, c, hc⟩ := erdos_8_resolution
  obtain ⟨cs, hcs_d, hcs_m⟩ := h k hk c
  exact hc cs hcs_d hcs_m

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
A single congruence class with modulus ≥ 2 cannot cover all integers.
The integer `residue + 1` is not congruent to `residue` mod any modulus ≥ 2.
-/
theorem single_class_not_covering (c : CongruenceClass) :
    ∃ x : ℤ, x ∉ c.toSet := by
  use ↑c.residue + 1
  simp only [CongruenceClass.toSet, mem_setOf_eq, Int.ModEq]
  have hm := c.modulus_pos  -- modulus ≥ 2
  have hr := c.residue_valid  -- residue < modulus
  omega

/-- A covering system with distinct moduli has at least 2 congruence classes.
    A single class with modulus ≥ 2 cannot cover all integers. -/
theorem covering_distinct_has_ge_two_classes (cs : CoveringSystem)
    (_ : cs.hasDistinctModuli) : cs.classes.length ≥ 2 := by
  by_contra h
  push_neg at h
  have hlen : cs.classes.length = 1 := by omega
  obtain ⟨c, hc⟩ := List.length_eq_one.mp hlen
  obtain ⟨x, hx⟩ := single_class_not_covering (cs.classes.head (by simp [hc]))
  obtain ⟨c', hc', hcov⟩ := cs.covers x
  rw [hc, List.mem_singleton] at hc'
  subst hc'
  exact hx (by rwa [List.head_cons] at hcov)

/-- A covering system with distinct moduli has at least 2 distinct moduli. -/
theorem covering_distinct_moduli_card_ge_two (cs : CoveringSystem)
    (hd : cs.hasDistinctModuli) : cs.moduli.card ≥ 2 := by
  have hlen := covering_distinct_has_ge_two_classes cs hd
  unfold CoveringSystem.moduli CoveringSystem.hasDistinctModuli at *
  rw [List.toFinset_card_of_nodup hd]
  exact hlen

/-- The minimum modulus is a member of the moduli finset. -/
theorem CoveringSystem.minModulus_mem (cs : CoveringSystem) :
    cs.minModulus ∈ cs.moduli :=
  Finset.min'_mem _ _

/--
**Bottleneck argument (PROVED — was axiom):**
The minimum modulus bound allows constructing colorings that avoid
monochromatic covering moduli.

**Proof**: Color each n ≤ 616000 with its own color (color n),
and all n > 616000 with color 0. Any covering system must include
a modulus m₁ ≤ 616000 (by the bound) and at least one other distinct
modulus m₂. If m₂ ≤ 616000, color(m₂) = m₂ ≠ m₁ = color(m₁).
If m₂ > 616000, color(m₂) = 0 ≠ m₁ (since m₁ ≥ 2).
-/
theorem bottleneck_counterexample :
    (∀ cs : CoveringSystem, cs.hasDistinctModuli → cs.minModulus ≤ 616000) →
    ∃ k : ℕ, k ≥ 2 ∧ ∃ c : Coloring k,
      ∀ cs : CoveringSystem, cs.hasDistinctModuli → ¬cs.hasMonochromaticModuli c := by
  intro hbound
  refine ⟨616001, by omega, fun n => if h : n ≤ 616000 then ⟨n, by omega⟩ else ⟨0, by omega⟩, ?_⟩
  intro cs hd ⟨color, hcolor⟩
  set m₁ := cs.minModulus with hm₁_def
  have hm₁_mem : m₁ ∈ cs.moduli := cs.minModulus_mem
  have hm₁_le : m₁ ≤ 616000 := hbound cs hd
  -- m₁ ≥ 2 (all congruence classes have modulus ≥ 2)
  have hm₁_ge : m₁ ≥ 2 := by
    have hmem := Finset.min'_mem cs.moduli _
    simp only [CoveringSystem.moduli, List.mem_toFinset, List.mem_map] at hmem
    obtain ⟨c, _, hc⟩ := hmem
    rw [← hm₁_def, ← hc]; exact c.modulus_pos
  -- Color of m₁ = ⟨m₁, _⟩
  have hcm₁ : (fun n => if h : n ≤ 616000 then (⟨n, by omega⟩ : Fin 616001)
      else ⟨0, by omega⟩) m₁ = ⟨m₁, by omega⟩ := by simp [hm₁_le]
  have hm₁_color := hcolor m₁ hm₁_mem
  rw [hcm₁] at hm₁_color
  -- There exists another modulus m₂ ≠ m₁ (≥ 2 distinct moduli)
  have hcard := covering_distinct_moduli_card_ge_two cs hd
  obtain ⟨m₂, hm₂_mem, hm₂_ne⟩ : ∃ m₂ ∈ cs.moduli, m₂ ≠ m₁ := by
    by_contra h; push_neg at h
    have : cs.moduli ⊆ {m₁} := fun x hx => Finset.mem_singleton.mpr (h x hx)
    have := Finset.card_le_card this; simp at this; omega
  have hm₂_color := hcolor m₂ hm₂_mem
  by_cases hm₂_le : m₂ ≤ 616000
  · -- m₂ ≤ 616000: color(m₂) = ⟨m₂, _⟩ ≠ ⟨m₁, _⟩
    have hcm₂ : (fun n => if h : n ≤ 616000 then (⟨n, by omega⟩ : Fin 616001)
        else ⟨0, by omega⟩) m₂ = ⟨m₂, by omega⟩ := by simp [hm₂_le]
    rw [hcm₂] at hm₂_color
    have : m₁ = m₂ := Fin.val_eq_of_eq (hm₂_color.symm.trans hm₁_color)
    exact hm₂_ne this.symm
  · -- m₂ > 616000: color(m₂) = ⟨0, _⟩ ≠ ⟨m₁, _⟩ (since m₁ ≥ 2)
    push_neg at hm₂_le
    have hcm₂ : (fun n => if h : n ≤ 616000 then (⟨n, by omega⟩ : Fin 616001)
        else ⟨0, by omega⟩) m₂ = ⟨0, by omega⟩ := by
      simp [show ¬(m₂ ≤ 616000) by omega]
    rw [hcm₂] at hm₂_color
    have : m₁ = 0 := Fin.val_eq_of_eq (hm₂_color.symm.trans hm₁_color)
    omega

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

**Axioms** (2 — reduced from 5):
1. hough_minimum_modulus — every CS has min modulus ≤ 616000 (deep result, 2015)
2. density_conjecture_false — the density version is false (deep result, 2015)

**Proved** (9 theorems):
1. balister_improved_bound — derived from hough
2. erdos_8_resolution — **PROVED (was axiom)**: derived from bottleneck + Hough
3. erdos_8_false — conjecture negation
4. single_class_not_covering — modulus ≥ 2 misses integers
5. covering_distinct_has_ge_two_classes — covering systems need ≥ 2 classes
6. covering_distinct_moduli_card_ge_two — ≥ 2 distinct moduli
7. CoveringSystem.minModulus_mem — min modulus membership
8. bottleneck_counterexample — **PROVED (was axiom)**: pigeonhole coloring
9. erdos_8_summary — both versions false

**Bug Fixed**: erdos_graham_conjecture and erdos_8_disproved now require
hasDistinctModuli. Without this, trivial CS like {0 mod 2, 1 mod 2} always
have monochromatic moduli, making the disproval statement vacuously false.

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
