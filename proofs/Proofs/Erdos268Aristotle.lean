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
  unfold HasConvergentHarmonicSubseries
  haveI := hA.to_subtype
  exact summable_of_finite _

-- Routine: If A has convergent harmonic sum, shifted version is also summable
theorem shifted_summable (A : Set ℕ) (k : ℕ)
    (h : HasConvergentHarmonicSubseries A) :
    Summable (fun n : A => (1 : ℝ) / (n + k)) := by
  apply Summable.of_nonneg_of_le
  · intro n; exact div_nonneg one_nonneg (by positivity)
  · intro ⟨n, hn⟩
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (by exact_mod_cast Nat.le_add_right n k)
  · exact h

-- Routine: The set of perfect squares has convergent harmonic subseries
-- (this is ∑ 1/n² = π²/6, well-known convergence)
theorem squares_convergent : HasConvergentHarmonicSubseries squaresSet := by
  unfold HasConvergentHarmonicSubseries
  -- Build bijection ℕ ≃ squaresSet via k ↦ (k+1)²
  let e : ℕ → squaresSet := fun k => ⟨(k+1)^2, k+1, by omega, rfl⟩
  have hinj : Function.Injective e := by
    intro a b h; simp only [e, Subtype.ext_iff] at h; omega
  have hsurj : Function.Surjective e := by
    intro ⟨n, k, hk, hkn⟩; exact ⟨k - 1, by simp only [e, Subtype.ext_iff]; omega⟩
  rw [← (Equiv.ofBijective e ⟨hinj, hsurj⟩).summable_iff]
  -- Reindexed series: fun k => 1/((k+1)² : ℝ)
  -- Bounded by p-series ∑ 1/n² (p=2>1, convergent)
  have hpseries : Summable (fun n : ℕ => ((n : ℝ) ^ (2 : ℝ))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)
  apply Summable.of_nonneg_of_le
  · intro k; positivity
  · intro k
    show (1 : ℝ) / ↑((k + 1) ^ 2) ≤ ((↑(k + 1) : ℝ) ^ (2 : ℝ))⁻¹
    rw [Nat.cast_pow, one_div]
    congr 1
    push_cast; ring
  · exact hpseries.comp_injective (fun a b h => by omega : Function.Injective (· + 1))

-- Routine: Powers of 2 have convergent harmonic subseries
-- (geometric series ∑ 1/2^k = 1)
theorem powers_convergent : HasConvergentHarmonicSubseries powersOf2Set := by
  unfold HasConvergentHarmonicSubseries
  -- Build bijection ℕ ≃ powersOf2Set via k ↦ 2^k
  let e : ℕ → powersOf2Set := fun k => ⟨2^k, k, rfl⟩
  have hinj : Function.Injective e := by
    intro a b h
    simp only [e, Subtype.ext_iff] at h
    exact Nat.pow_right_injective (by norm_num) h
  have hsurj : Function.Surjective e := by
    intro ⟨n, k, hk⟩
    exact ⟨k, by simp only [e, Subtype.ext_iff]; exact hk.symm⟩
  rw [← (Equiv.ofBijective e ⟨hinj, hsurj⟩).summable_iff]
  -- Reindexed: fun k => 1/(2^k : ℝ) = (1/2)^k, geometric series
  have : ((fun n : powersOf2Set => (1 : ℝ) / ↑↑n) ∘ (Equiv.ofBijective e ⟨hinj, hsurj⟩)) =
      fun k => ((1 : ℝ) / 2) ^ k := by
    ext k
    simp only [Function.comp, Equiv.ofBijective_apply, e, Subtype.val]
    rw [Nat.cast_pow, Nat.cast_ofNat, div_pow, one_pow]
  rw [this]
  exact summable_geometric_of_lt_one (by positivity) (by norm_num)

-- Routine: Shifted harmonic sum is non-negative for non-empty A
theorem shiftedHarmonicSum_nonneg (A : Set ℕ) (k : ℕ)
    (hA : A.Nonempty) (h : Summable (fun n : A => (1 : ℝ) / (n + k))) :
    shiftedHarmonicSum A k ≥ 0 := by
  unfold shiftedHarmonicSum
  exact tsum_nonneg (fun n => div_nonneg one_nonneg (by positivity))

-- Routine: Shifted harmonic sum is decreasing in k
-- (1/(n+j) < 1/(n+i) when i < j)
theorem shiftedHarmonicSum_antitone (A : Set ℕ) (hA : A.Infinite)
    (hconv : HasConvergentHarmonicSubseries A)
    (i j : ℕ) (hij : i < j) :
    shiftedHarmonicSum A j < shiftedHarmonicSum A i := by
  unfold shiftedHarmonicSum
  -- Each term: 1/(n+j) < 1/(n+i) since j > i
  apply tsum_lt_tsum
  · -- ∀ n, 1/(n+j) ≤ 1/(n+i)
    intro ⟨n, hn⟩
    apply div_le_div_of_nonneg_left (by positivity : (0:ℝ) < 1) (by positivity) (by positivity)
    exact_mod_cast Nat.add_le_add_left (Nat.le_of_lt hij) n
  · -- ∃ n ∈ A, 1/(n+j) < 1/(n+i)
    obtain ⟨n, hn⟩ := hA.nonempty
    exact ⟨⟨n, hn⟩, div_lt_div_of_pos_left (by positivity : (0:ℝ) < 1) (by positivity)
      (by exact_mod_cast Nat.add_lt_add_left hij n)⟩
  · exact shifted_summable A i hconv

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
