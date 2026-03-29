/-
  Aristotle targets for Erdős Problem #268
  Routine supporting lemmas for automated proof search.
  See Erdos268Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main interior-nonempty result (axiomatized)
  - Routine analysis/topology facts provable from Mathlib
  - Clean theorem statements with no definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos268Aristotle

open Set Filter Topology

/-- A subset A ⊆ ℕ has a convergent harmonic subseries. -/
def HasConvergentHarmonicSubseries (A : Set ℕ) : Prop :=
  Summable (fun n : A => (1 : ℝ) / n)

/-- The shifted harmonic subseries sum. -/
noncomputable def shiftedHarmonicSum (A : Set ℕ) (k : ℕ) : ℝ :=
  ∑' n : A, (1 : ℝ) / (n + k)

/-- The set of perfect squares. -/
def squaresSet : Set ℕ := {n | ∃ k : ℕ, k ≥ 1 ∧ n = k ^ 2}

/-- The set of powers of 2. -/
def powersOf2Set : Set ℕ := {n | ∃ k : ℕ, n = 2 ^ k}

-- Routine: Finite sets have convergent harmonic subseries
theorem finite_has_convergent (A : Set ℕ) (hA : A.Finite) :
    HasConvergentHarmonicSubseries A := by
  simp only [HasConvergentHarmonicSubseries]
  haveI : Finite ↥A := hA.to_subtype
  haveI := Fintype.ofFinite ↥A
  exact (hasSum_fintype _).summable

-- Routine: If A has convergent harmonic sum, shifted version is also summable
theorem shifted_summable (A : Set ℕ) (k : ℕ)
    (h : HasConvergentHarmonicSubseries A) :
    Summable (fun n : A => (1 : ℝ) / (n + k)) := by
  sorry

-- Routine: The set of perfect squares has convergent harmonic subseries
-- (this is ∑ 1/n² = π²/6, well-known convergence)
theorem squares_convergent : HasConvergentHarmonicSubseries squaresSet := by
  sorry

-- Routine: Powers of 2 have convergent harmonic subseries
-- (geometric series ∑ 1/2^k = 1)
theorem powers_convergent : HasConvergentHarmonicSubseries powersOf2Set := by
  sorry

-- Routine: Shifted harmonic sum is non-negative for non-empty A
theorem shiftedHarmonicSum_nonneg (A : Set ℕ) (k : ℕ)
    (hA : A.Nonempty) (h : Summable (fun n : A => (1 : ℝ) / (n + k))) :
    shiftedHarmonicSum A k ≥ 0 := by
  simp only [shiftedHarmonicSum]
  exact tsum_nonneg (fun n => div_nonneg one_nonneg (by positivity))

-- Routine: Shifted harmonic sum is decreasing in k
-- (1/(n+j) < 1/(n+i) when i < j)
theorem shiftedHarmonicSum_antitone (A : Set ℕ) (hA : A.Infinite)
    (hconv : HasConvergentHarmonicSubseries A)
    (i j : ℕ) (hij : i < j) :
    shiftedHarmonicSum A j < shiftedHarmonicSum A i := by
  sorry

-- Routine: The squares set is infinite
theorem squaresSet_infinite : squaresSet.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro n
  exact ⟨(n + 1) ^ 2, ⟨n + 1, by omega, rfl⟩, by nlinarith⟩

-- Routine: The powers of 2 set is infinite
theorem powersOf2Set_infinite : powersOf2Set.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro n
  obtain ⟨k, hk⟩ := Nat.exists_lt_pow (b := 2) (by omega) n
  exact ⟨2 ^ k, ⟨k, rfl⟩, hk⟩

-- Routine: 1/(n+k) ≤ 1/n for k ≥ 0 and n ≥ 1
theorem inv_shift_le (n : ℕ) (hn : n ≥ 1) (k : ℕ) :
    (1 : ℝ) / (n + k) ≤ 1 / n := by
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact_mod_cast Nat.le_add_right n k

end Erdos268Aristotle
