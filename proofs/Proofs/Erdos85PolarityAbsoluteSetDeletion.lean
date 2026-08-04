import Proofs.Erdos85ControlledDeletion
import Proofs.Erdos85PolarityAbsolute

/-!
# Deleting sets of absolute polarity points

Absolute points are pairwise nonadjacent.  Consequently they suffer no degree
loss when other absolute points are deleted.  Nonabsolute points have one unit
of degree slack.  Thus an incidence bound of two deleted absolute neighbors per
nonabsolute survivor yields a degree-(q-1) witness, independently of how many
absolute points are removed.
-/

open SimpleGraph
open scoped LinearAlgebra.Projectivization

namespace Erdos85.Polarity

universe u

variable (K : Type u) [Field K] [Finite K] [DecidableEq K]

private noncomputable abbrev P := ℙ K (Fin 3 → K)
private noncomputable abbrev q : ℕ := Nat.card K
private noncomputable abbrev N : ℕ := (q K + 1) * q K + 1

/-- The finite set of all absolute points of the orthogonal polarity. -/
noncomputable def absolutePoints : Finset (P K) := by
  classical
  exact Finset.univ.filter fun x => Projectivization.orthogonal x x

@[simp] theorem mem_absolutePoints (x : P K) :
    x ∈ absolutePoints K ↔ Projectivization.orthogonal x x := by
  classical
  simp [absolutePoints]

/-- The precise finite-geometry input needed for multi-absolute deletion:
every nonabsolute polar line meets the absolute locus in at most two points. -/
def AbsoluteTwoSecant : Prop :=
  ∀ v : P K, ¬ Projectivization.orthogonal v v →
    ((graph K).neighborFinset v ∩ absolutePoints K).card ≤ 2

/-- The two-secant property descends from the full absolute locus to every
chosen subset of absolute points. -/
theorem card_neighborFinset_inter_le_two_of_subset_absolute
    (hsec : AbsoluteTwoSecant K) (D : Finset (P K))
    (hDabs : ∀ y ∈ D, Projectivization.orthogonal y y)
    (v : P K) (hv : ¬ Projectivization.orthogonal v v) :
    ((graph K).neighborFinset v ∩ D).card ≤ 2 := by
  apply (Finset.card_le_card ?_).trans (hsec v hv)
  intro y hy
  rw [Finset.mem_inter] at hy ⊢
  exact ⟨hy.1, (mem_absolutePoints K y).mpr (hDabs y hy.2)⟩

/-- A surviving absolute point has no neighbor in a deleted set consisting
entirely of absolute points. -/
theorem card_neighborFinset_inter_eq_zero_of_absolute_set
    (D : Finset (P K))
    (hDabs : ∀ y ∈ D, Projectivization.orthogonal y y)
    (v : {v : P K // v ∉ D})
    (hvabs : Projectivization.orthogonal v.1 v.1) :
    ((graph K).neighborFinset v ∩ D).card = 0 := by
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro y hy
  rw [Finset.mem_inter] at hy
  have hvy : (graph K).Adj v y := by simpa using hy.1
  exact (not_selfOrthogonal_of_adj_selfOrthogonal hvy hvabs)
    (hDabs y hy.2)

/-- Conditional multi-absolute deletion theorem.  Its only geometric input is
that every surviving nonabsolute point is adjacent to at most two members of
D.  Under that condition, deleting D preserves minimum degree at least q-1. -/
theorem c4FreeMinDegreeWitness_delete_absolute_set_of_incidence_two
    (D : Finset (P K)) {k : ℕ}
    (hDcard : D.card = k)
    (hremain : 1 ≤ N K - k)
    (hDabs : ∀ y ∈ D, Projectivization.orthogonal y y)
    (hinc : ∀ v : {v : P K // v ∉ D},
      ¬ Projectivization.orthogonal v.1 v.1 →
        ((graph K).neighborFinset v ∩ D).card ≤ 2) :
    C4FreeMinDegreeWitness (N K - k) (q K - 1) := by
  apply c4FreeMinDegreeWitness_delete_vertex_set_of_compensated_degrees
    (graph K) D
  · rw [Fintype.card_eq_nat_card, card_points_tight K]
  · exact hDcard
  · exact hremain
  · exact graph_not_containsC4
  · intro v
    by_cases hvabs : Projectivization.orthogonal v.1 v.1
    · rw [card_neighborFinset_inter_eq_zero_of_absolute_set K D hDabs v hvabs,
        Nat.add_zero, degree_eq_card_of_selfOrthogonal hvabs]
      change Nat.card K - 1 ≤ Nat.card K
      omega
    · have hvinc := hinc v hvabs
      have hq : 2 ≤ Nat.card K := Finite.one_lt_card (α := K)
      rw [degree_eq_card_add_one_of_not_selfOrthogonal hvabs]
      change Nat.card K - 1 + ((graph K).neighborFinset v ∩ D).card ≤
        Nat.card K + 1
      omega

/-- Threshold lower bound supplied by a controlled absolute-point deletion. -/
theorem minDegreeForC4_delete_absolute_set_lower
    (D : Finset (P K)) {k : ℕ}
    (hDcard : D.card = k)
    (hremain : 4 ≤ N K - k)
    (hDabs : ∀ y ∈ D, Projectivization.orthogonal y y)
    (hinc : ∀ v : {v : P K // v ∉ D},
      ¬ Projectivization.orthogonal v.1 v.1 →
        ((graph K).neighborFinset v ∩ D).card ≤ 2) :
    q K - 1 < minDegreeForC4 (N K - k) := by
  apply (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 hremain).1
  exact c4FreeMinDegreeWitness_delete_absolute_set_of_incidence_two
    K D hDcard (by omega) hDabs hinc

/-- Under the global two-secant property, every chosen absolute subset gives
the controlled degree-`q-1` witness automatically. -/
theorem c4FreeMinDegreeWitness_delete_absolute_set
    (hsec : AbsoluteTwoSecant K) (D : Finset (P K)) {k : ℕ}
    (hDcard : D.card = k) (hremain : 1 ≤ N K - k)
    (hDabs : ∀ y ∈ D, Projectivization.orthogonal y y) :
    C4FreeMinDegreeWitness (N K - k) (q K - 1) := by
  apply c4FreeMinDegreeWitness_delete_absolute_set_of_incidence_two
    K D hDcard hremain hDabs
  intro v hv
  exact card_neighborFinset_inter_le_two_of_subset_absolute
    K hsec D hDabs v hv

end Erdos85.Polarity
