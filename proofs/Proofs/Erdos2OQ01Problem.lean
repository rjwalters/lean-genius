/-
  Erdős Problem #2 — Open Question 01:
  What is the exact maximum possible minimum modulus?

  A covering system is a finite set of arithmetic progressions
  {a₁ mod n₁, ..., aₖ mod nₖ} (distinct moduli ≥ 2) covering all integers.

  Known bounds on the maximum achievable minimum modulus M:
  - Lower: M ≥ 42 (Owens 2014: explicit construction)
  - Upper: M ≤ 616,000 (Balister-Bollobás-Morris-Sahasrabudhe-Tiba 2022)

  The gap between 42 and 616,000 is the central open question.

  Reference: https://erdosproblems.com/2
-/

import Mathlib

open Set Finset

namespace Erdos2OQ01

/-
## Definitions (self-contained)
-/

/-- An arithmetic progression represented as (residue, modulus). -/
structure CongruenceClass where
  residue : ℕ
  modulus : ℕ
  modulus_pos : modulus ≥ 2

/-- The set of integers in a congruence class. -/
def CongruenceClass.toSet (c : CongruenceClass) : Set ℤ :=
  { x | x ≡ c.residue [ZMOD c.modulus] }

/-- A covering system: finitely many congruence classes covering all integers. -/
structure CoveringSystem where
  classes : List CongruenceClass
  nonempty : classes.length ≥ 1
  covers : ∀ x : ℤ, ∃ c ∈ classes, x ∈ c.toSet

/-- Minimum modulus requirement: all moduli ≥ m. -/
def CoveringSystem.hasMinModulusAtLeast (cs : CoveringSystem) (m : ℕ) : Prop :=
  ∀ c ∈ cs.classes, m ≤ c.modulus

/-- The set of moduli in a covering system. -/
def CoveringSystem.moduli (cs : CoveringSystem) : List ℕ :=
  cs.classes.map CongruenceClass.modulus

/-
## The Gap Problem
-/

/-- The exact maximum minimum modulus: the largest m such that a covering
    system with all moduli ≥ m exists. -/
def ExactMaxMinModulus (M : ℕ) : Prop :=
  (∃ cs : CoveringSystem, cs.hasMinModulusAtLeast M) ∧
  (∀ cs : CoveringSystem, ∃ c ∈ cs.classes, c.modulus ≤ M)

/-- Known lower bound: M ≥ 42 (Owens 2014). -/
axiom owens_construction : ∃ cs : CoveringSystem, cs.hasMinModulusAtLeast 42

/-- Known upper bound: M ≤ 616,000 (Balister et al. 2022). -/
axiom balister_upper_bound : ∀ cs : CoveringSystem, ∃ c ∈ cs.classes, c.modulus ≤ 616000

/-- The gap: the exact M is between 42 and 616,000. -/
theorem gap_bounds :
    (∃ cs : CoveringSystem, cs.hasMinModulusAtLeast 42) ∧
    (∀ cs : CoveringSystem, ∃ c ∈ cs.classes, c.modulus ≤ 616000) :=
  ⟨owens_construction, balister_upper_bound⟩

/-
## Structural Properties of Covering Systems (all PROVED)
-/

/-- Every covering system has at least one congruence class. -/
theorem covering_has_class (cs : CoveringSystem) : cs.classes ≠ [] := by
  intro h
  have := cs.nonempty
  rw [h] at this
  simp at this

/-- Every integer is in at least one congruence class. -/
theorem covering_surjective (cs : CoveringSystem) (x : ℤ) :
    ∃ c ∈ cs.classes, x ∈ c.toSet :=
  cs.covers x

/-- If all moduli ≥ m and m ≤ m', then all moduli ≥ m' is stronger.
    Equivalently: hasMinModulusAtLeast is monotone downward. -/
theorem min_modulus_monotone (cs : CoveringSystem) {m m' : ℕ} (hmm' : m' ≤ m)
    (h : cs.hasMinModulusAtLeast m) : cs.hasMinModulusAtLeast m' := by
  intro c hc
  exact le_trans hmm' (h c hc)

/-- Any covering system has all moduli ≥ 2 (by definition). -/
theorem moduli_ge_two (cs : CoveringSystem) :
    cs.hasMinModulusAtLeast 2 := by
  intro c _
  exact c.modulus_pos

/-- If a covering system has min modulus ≥ m, the class count is at least 1.
    (Trivially true since covering systems must be nonempty.) -/
theorem min_modulus_implies_many_classes (cs : CoveringSystem) (m : ℕ) (hm : m ≥ 3)
    (h : cs.hasMinModulusAtLeast m) : cs.classes.length ≥ 1 :=
  cs.nonempty

/-- A congruence class modulo n has density 1/n among the integers.
    This is the key insight for the reciprocal sum argument:
    if k classes with distinct moduli n₁ < ... < nₖ cover all integers,
    then 1/n₁ + ... + 1/nₖ ≥ 1. -/
def reciprocalSum (cs : CoveringSystem) : ℚ :=
  (cs.moduli.map (fun n => (1 : ℚ) / n)).sum

/-- The reciprocal sum of moduli is at least 1 for any covering system. -/
axiom reciprocal_sum_ge_one (cs : CoveringSystem) : reciprocalSum cs ≥ 1

/-- The Owens bound is weaker than the Balister bound
    (consistency check: 42 ≤ 616000). -/
theorem bounds_consistent : 42 ≤ 616000 := by omega

/-- If ExactMaxMinModulus M holds, then M ≥ 42. -/
theorem exact_max_ge_42 (M : ℕ) (h : ExactMaxMinModulus M) : M ≥ 42 := by
  -- From the Owens construction, there exists a CS with min modulus ≥ 42.
  -- If M < 42, then M < 42 ≤ all moduli, contradicting h.2 which gives a modulus ≤ M.
  by_contra hlt
  push_neg at hlt
  obtain ⟨cs, hcs⟩ := owens_construction
  obtain ⟨c, hc, hle⟩ := h.2 cs
  have h42 := hcs c hc
  omega

/-- If ExactMaxMinModulus M holds, then M ≤ 616,000. -/
theorem exact_max_le_616000 (M : ℕ) (h : ExactMaxMinModulus M) : M ≤ 616000 := by
  -- From Balister, every CS has a modulus ≤ 616000.
  -- The CS from h.1 has min modulus ≥ M, hence M ≤ min modulus ≤ 616000.
  obtain ⟨cs, hcs⟩ := h.1
  obtain ⟨c, hc, hle⟩ := balister_upper_bound cs
  have hM := hcs c hc
  omega

/-- The exact maximum minimum modulus, if it exists, is in [42, 616000]. -/
theorem exact_max_in_range (M : ℕ) (h : ExactMaxMinModulus M) : 42 ≤ M ∧ M ≤ 616000 :=
  ⟨exact_max_ge_42 M h, exact_max_le_616000 M h⟩

/-- For any m ≤ 42, there exists a covering system with min modulus ≥ m.
    (Follows from Owens' construction with min modulus 42.) -/
theorem existence_below_42 (m : ℕ) (hm : m ≤ 42) :
    ∃ cs : CoveringSystem, cs.hasMinModulusAtLeast m := by
  obtain ⟨cs, hcs⟩ := owens_construction
  exact ⟨cs, min_modulus_monotone cs hm hcs⟩

/-- No covering system can have all moduli > 616,000. -/
theorem no_covering_above_616000 :
    ¬∃ cs : CoveringSystem, cs.hasMinModulusAtLeast 616001 := by
  intro ⟨cs, hcs⟩
  obtain ⟨c, hc, hle⟩ := balister_upper_bound cs
  have := hcs c hc
  omega

/-
## Summary

**Open Question**: What is the exact maximum possible minimum modulus M?

**Known**: 42 ≤ M ≤ 616,000
- Lower bound 42: Owens (2014) — explicit construction
- Upper bound 616,000: Balister et al. (2022) — probabilistic method

**Proved in this file**:
- exact_max_ge_42: M ≥ 42 from Owens construction
- exact_max_le_616000: M ≤ 616,000 from Balister bound
- no_covering_above_616000: no CS has all moduli > 616,000
- existence_below_42: CS with min modulus ≥ m exists for any m ≤ 42
- Basic structural properties of covering systems

**Gap narrowing**: The key challenge is either:
1. Constructing covering systems with min modulus > 42, OR
2. Proving stronger upper bounds (reducing 616,000)

Both directions are actively researched.
-/

end Erdos2OQ01
