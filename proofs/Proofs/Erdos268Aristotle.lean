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
  exact Summable.of_finite

-- Routine: If A has convergent harmonic sum (and A avoids 0, so every denominator is
-- positive), the shifted version is also summable.
-- (The `0 ∉ A` hypothesis is needed: with 0 ∈ A the pointwise bound `1/(n+k) ≤ 1/n`
-- fails at n = 0 for k ≥ 1, since 1/0 = 0 by convention but 1/k > 0.)
theorem shifted_summable (A : Set ℕ) (hA0 : (0 : ℕ) ∉ A) (k : ℕ)
    (h : HasConvergentHarmonicSubseries A) :
    Summable (fun n : A => (1 : ℝ) / (n + k)) := by
  apply Summable.of_nonneg_of_le (fun n => div_nonneg zero_le_one (by positivity)) ?_ h
  rintro ⟨n, hn⟩
  have hnpos : 0 < n := Nat.pos_of_ne_zero (fun heq => hA0 (heq ▸ hn))
  show (1 : ℝ) / (n + k) ≤ (1 : ℝ) / n
  apply one_div_le_one_div_of_le (by exact_mod_cast hnpos)
  exact_mod_cast Nat.le_add_right n k

-- Routine: The set of perfect squares has convergent harmonic subseries
-- (this is ∑ 1/n² = π²/6, well-known convergence)
theorem squares_convergent : HasConvergentHarmonicSubseries squaresSet := by
  unfold HasConvergentHarmonicSubseries
  -- Build bijection ℕ ≃ squaresSet via k ↦ (k+1)²
  let e : ℕ → squaresSet := fun k => ⟨(k+1)^2, k+1, by omega, rfl⟩
  have hinj : Function.Injective e := by
    intro a b h
    simp only [e, Subtype.ext_iff] at h
    have := Nat.pow_left_injective (n := 2) (by norm_num) h
    omega
  have hsurj : Function.Surjective e := by
    intro ⟨n, k, hk, hkn⟩
    refine ⟨k - 1, ?_⟩
    simp only [e, Subtype.ext_iff]
    have hk1 : k - 1 + 1 = k := by omega
    rw [hk1, ← hkn]
  rw [← (Equiv.ofBijective e ⟨hinj, hsurj⟩).summable_iff]
  -- Reindexed series: fun k => 1/((k+1)² : ℝ)
  -- Bounded by p-series ∑ 1/n² (p=2>1, convergent)
  have hpseries : Summable (fun n : ℕ => ((n : ℝ) ^ (2 : ℝ))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)
  apply Summable.of_nonneg_of_le
    (fun k => by
      simp only [Function.comp_apply, Equiv.ofBijective_apply]
      positivity)
    (fun k => by
      simp only [Function.comp_apply, Equiv.ofBijective_apply, e]
      have h2 : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
      rw [h2, Real.rpow_natCast, Nat.cast_pow, one_div])
    (hpseries.comp_injective (fun a b (h : a + 1 = b + 1) => by omega : Function.Injective (· + 1)))

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
    simp only [Function.comp, Equiv.ofBijective_apply, e]
    rw [Nat.cast_pow, Nat.cast_ofNat, div_pow, one_pow]
  rw [this]
  exact summable_geometric_of_lt_one (by positivity) (by norm_num)

-- Routine: Shifted harmonic sum is non-negative for non-empty A
theorem shiftedHarmonicSum_nonneg (A : Set ℕ) (k : ℕ)
    (hA : A.Nonempty) (h : Summable (fun n : A => (1 : ℝ) / (n + k))) :
    shiftedHarmonicSum A k ≥ 0 := by
  unfold shiftedHarmonicSum
  exact tsum_nonneg (fun n => div_nonneg zero_le_one (by positivity))

-- Routine: Shifted harmonic sum is decreasing in k
-- (1/(n+j) < 1/(n+i) when i < j)
-- (Requires `0 ∉ A`, same as `shifted_summable`: with 0 ∈ A and i = 0, the pointwise
-- bound `1/(n+j) ≤ 1/(n+i)` fails at n = 0 since 1/(0+i) = 1/0 = 0 by convention.)
theorem shiftedHarmonicSum_antitone (A : Set ℕ) (hA : A.Infinite) (hA0 : (0 : ℕ) ∉ A)
    (hconv : HasConvergentHarmonicSubseries A)
    (i j : ℕ) (hij : i < j) :
    shiftedHarmonicSum A j < shiftedHarmonicSum A i := by
  unfold shiftedHarmonicSum
  obtain ⟨n0, hn0⟩ := hA.nonempty
  have hn0pos : 0 < n0 := Nat.pos_of_ne_zero (fun heq => hA0 (heq ▸ hn0))
  have hle : (fun n : A => (1 : ℝ) / (n + j)) ≤ (fun n : A => (1 : ℝ) / (n + i)) := by
    rintro ⟨n, hn⟩
    have hnpos : 0 < n := Nat.pos_of_ne_zero (fun heq => hA0 (heq ▸ hn))
    show (1 : ℝ) / (n + j) ≤ (1 : ℝ) / (n + i)
    apply one_div_le_one_div_of_le (by exact_mod_cast Nat.add_pos_left hnpos i)
    exact_mod_cast Nat.add_le_add_left hij.le n
  have hstrict : (fun n : A => (1 : ℝ) / (n + j)) (⟨n0, hn0⟩ : A) <
      (fun n : A => (1 : ℝ) / (n + i)) (⟨n0, hn0⟩ : A) := by
    show (1 : ℝ) / (n0 + j) < (1 : ℝ) / (n0 + i)
    apply one_div_lt_one_div_of_lt (by exact_mod_cast Nat.add_pos_left hn0pos i)
    exact_mod_cast Nat.add_lt_add_left hij n0
  exact (shifted_summable A hA0 j hconv).tsum_lt_tsum hle hstrict
    (shifted_summable A hA0 i hconv)

-- Routine: The squares set is infinite
theorem squaresSet_infinite : squaresSet.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro n
  exact ⟨(n + 1) ^ 2, ⟨n + 1, by omega, rfl⟩, by nlinarith⟩

-- Routine: The powers of 2 set is infinite
theorem powersOf2Set_infinite : powersOf2Set.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro n
  exact ⟨2 ^ n, ⟨n, rfl⟩, Nat.lt_pow_self (by norm_num)⟩

-- Routine: 1/(n+k) ≤ 1/n for k ≥ 0 and n ≥ 1
theorem inv_shift_le (n : ℕ) (hn : n ≥ 1) (k : ℕ) :
    (1 : ℝ) / (n + k) ≤ 1 / n := by
  apply one_div_le_one_div_of_le (by exact_mod_cast hn : (0:ℝ) < n)
  exact_mod_cast Nat.le_add_right n k

end Erdos268Aristotle
