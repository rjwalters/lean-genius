import Proofs.Erdos85PolarityAbsolute
import Proofs.Erdos85IteratedDeletion

/-!
# Deletion bands below finite-field polarity orders

The polarity witness can be deleted repeatedly.  Starting from an absolute
point gives one deletion for free: after deleting that point the certified
minimum degree is still q, and each subsequent arbitrary deletion costs at
most one.
-/

open scoped LinearAlgebra.Projectivization

namespace Erdos85.Polarity

universe u

variable (K : Type u) [Field K] [Finite K] [DecidableEq K]

private noncomputable abbrev q : ℕ := Nat.card K
private noncomputable abbrev M : ℕ := (q K + 1) * q K

/-- The basic polarity graph supplies a deletion band below q²+q+1. -/
theorem c4FreeMinDegreeWitness_projectivePlane_delete_band
    {k : ℕ} (hk : k ≤ q K) :
    C4FreeMinDegreeWitness (M K + 1 - k) (q K - k) := by
  have hq : 2 ≤ q K := by
    exact Finite.one_lt_card (α := K)
  have hM : q K + 4 ≤ M K := by
    dsimp [M]
    nlinarith
  have hw : C4FreeMinDegreeWitness (M K + 1) (q K) := by
    simpa [M, q, TightC4Witness] using tightC4Witness K
  apply hw.delete_vertices_sub
  · dsimp [M]
    nlinarith
  · omega

/-- Deleting an absolute point first gives a one-unit stronger band below
q²+q: the first deletion does not lower the certified minimum degree. -/
theorem c4FreeMinDegreeWitness_projectivePlane_free_delete_band
    {k : ℕ} (hk : k ≤ q K) :
    C4FreeMinDegreeWitness (M K - k) (q K - k) := by
  have hq : 2 ≤ q K := by
    exact Finite.one_lt_card (α := K)
  have hM : q K + 4 ≤ M K := by
    dsimp [M]
    nlinarith
  have hw : C4FreeMinDegreeWitness (M K) (q K) :=
    c4FreeMinDegreeWitness_projectivePlane_pred K
  apply hw.delete_vertices_sub
  · dsimp [M]
    nlinarith
  · omega

/-- Explicit threshold lower bounds throughout the free-deletion band. -/
theorem minDegreeForC4_projectivePlane_free_delete_band_lower
    {k : ℕ} (hk : k ≤ q K) :
    q K - k < minDegreeForC4 (M K - k) := by
  have hq : 2 ≤ q K := by
    exact Finite.one_lt_card (α := K)
  have hM : q K + 4 ≤ M K := by
    dsimp [M]
    nlinarith
  apply (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 ?_).1
    (c4FreeMinDegreeWitness_projectivePlane_free_delete_band K hk)
  omega

/-- Two-sided control throughout the free-deletion band.  The lower endpoint
comes from the deleted polarity witness; the common-neighbor count keeps the
threshold no larger than its value at the projective-plane endpoint. -/
theorem minDegreeForC4_projectivePlane_free_delete_band_bounds
    {k : ℕ} (hk : k ≤ q K) :
    q K - k + 1 ≤ minDegreeForC4 (M K - k) ∧
      minDegreeForC4 (M K - k) ≤ q K + 1 := by
  have hq : 2 ≤ q K := by
    exact Finite.one_lt_card (α := K)
  have hM : q K + 4 ≤ M K := by
    dsimp [M]
    nlinarith
  constructor
  · have hlower := minDegreeForC4_projectivePlane_free_delete_band_lower K hk
    omega
  · apply minDegreeForC4_le_of_le_mul_pred (by omega)
    simp [M]

end Erdos85.Polarity
