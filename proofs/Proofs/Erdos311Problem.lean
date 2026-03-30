/-
# Erdős Problem #311: Minimal Deviation of Unit Fraction Sums from 1

Define δ(N) = min { |1 - ∑_{n ∈ A} 1/n| : A ⊆ {1,...,N}, ∑ ≠ 1, ∑ ≤ 1 }
(the minimal nonzero deviation from 1 achievable by unit fraction sums).

Question: Is δ(N) = e^{-(c+o(1))N} for some constant c ∈ (0,1)?

Known:
- Lower bound: δ(N) ≥ 1/lcm(1,...,N) = e^{-(1+o(1))N} (trivial)
- Upper bound: δ(N) ≤ exp(-cN/(log N · log log N)³) for some c > 0 (Tang)
- Kovac showed the subset-sum-to-1 variant is equivalent

Status: OPEN.

Reference: https://erdosproblems.com/311
-/

import Mathlib

open scoped Classical

/- ## Definitions -/

/-- The sum of unit fractions 1/n for n ∈ A. -/
noncomputable def unitFracSum (A : Finset ℕ) : ℝ :=
  A.sum (fun n => (1 : ℝ) / n)

/-- A subset A ⊆ {1,...,N} is a valid candidate if its unit fraction sum is at most 1
    and not equal to 1 (i.e., the deviation from 1 is nonzero). -/
def validCandidate (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧ unitFracSum A ≤ 1 ∧ unitFracSum A ≠ 1

/-- The set of valid candidates for a given N. -/
noncomputable def validCandidates (N : ℕ) : Finset (Finset ℕ) :=
  ((Finset.Icc 1 N).powerset).filter (fun A => unitFracSum A ≤ 1 ∧ unitFracSum A ≠ 1)

/-- The set of deviations |1 - Σ 1/n| over valid candidates. Since unitFracSum A ≤ 1
    and unitFracSum A ≠ 1 for valid candidates, the deviation equals 1 - unitFracSum A > 0. -/
noncomputable def deviations (N : ℕ) : Finset ℝ :=
  (validCandidates N).image (fun A => 1 - unitFracSum A)

private lemma empty_mem_validCandidates (N : ℕ) : ∅ ∈ validCandidates N := by
  simp only [validCandidates, Finset.mem_filter, Finset.mem_powerset]
  refine ⟨Finset.empty_subset _, ?_, ?_⟩
  · simp [unitFracSum]
  · simp [unitFracSum]

private lemma deviations_nonempty (N : ℕ) : (deviations N).Nonempty :=
  ⟨1 - unitFracSum ∅, Finset.mem_image.mpr ⟨∅, empty_mem_validCandidates N, rfl⟩⟩

/-- δ(N): the minimal nonzero value of |1 - Σ_{n∈A} 1/n| over subsets A ⊆ {1,...,N}
    with the sum at most 1 and not equal to 1. Defined as the minimum over all valid
    candidates. -/
noncomputable def delta (N : ℕ) : ℝ :=
  (deviations N).min' (deviations_nonempty N)

/-- Every deviation in the set is positive. -/
private lemma deviations_pos (N : ℕ) : ∀ x ∈ deviations N, 0 < x := by
  intro x hx
  simp only [deviations, Finset.mem_image] at hx
  obtain ⟨A, hA, rfl⟩ := hx
  simp only [validCandidates, Finset.mem_filter, Finset.mem_powerset] at hA
  obtain ⟨_, hle, hne⟩ := hA
  linarith [lt_of_le_of_ne hle hne]

/-- δ(N) is positive for all N. (The original axiom required N ≥ 1 but this holds
    unconditionally from the definition.) -/
theorem delta_pos (N : ℕ) (_hN : 1 ≤ N) : 0 < delta N := by
  exact deviations_pos N _ (Finset.min'_mem _ _)

/- ## Structural Properties -/

/-- δ(N) ≤ 1 for all N: the empty set is always a valid candidate
    with deviation 1 - 0 = 1. -/
theorem delta_le_one (N : ℕ) : delta N ≤ 1 := by
  apply Finset.min'_le
  simp only [deviations, Finset.mem_image]
  exact ⟨∅, empty_mem_validCandidates N, by simp [unitFracSum]⟩

/-- δ is antitone: δ(N+1) ≤ δ(N). More numbers means more candidates,
    so the minimum deviation can only decrease or stay the same. -/
theorem delta_antitone (N : ℕ) : delta (N + 1) ≤ delta N := by
  apply Finset.min'_le
  have hmin := Finset.min'_mem (deviations N) (deviations_nonempty N)
  simp only [deviations, Finset.mem_image] at hmin ⊢
  obtain ⟨A, hA, rfl⟩ := hmin
  refine ⟨A, ?_, rfl⟩
  simp only [validCandidates, Finset.mem_filter, Finset.mem_powerset] at hA ⊢
  exact ⟨hA.1.trans (Finset.Icc_subset_Icc_right (by omega)), hA.2⟩

/- ## Lower Bound -/

/-- δ(N) ≥ e^{-(1+o(1))N}: for every ε > 0, δ(N) ≥ e^{-(1+ε)N} for large N.
    This follows from δ(N) ≥ 1/lcm(1,...,N) and the PNT estimate on lcm. -/
/- ## Upper Bound -/

/-- Tang's upper bound: δ(N) ≤ exp(-cN/(log N · log log N)³) for some c > 0.
    This is far from the conjectured e^{-cN}. -/
/- ## The Conjecture -/

/-- Erdős Problem #311 (Erdős–Graham 1980): δ(N) = e^{-(c+o(1))N}
    for some constant c ∈ (0,1). -/
