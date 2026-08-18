import Proofs.Erdos85PolarityDegree

/-!
# The finite-field polarity family for Erdős Problem 85
-/

open SimpleGraph
open scoped LinearAlgebra.Projectivization

namespace Erdos85.Polarity

universe u

variable (K : Type*) [Field K] [Finite K] [DecidableEq K]

private noncomputable abbrev q (K : Type u) : ℕ := Nat.card K
private abbrev P (K : Type u) [Field K] : Type u := ℙ K (Fin 3 → K)

theorem card_points_eq : Nat.card (P K) = (q K) ^ 2 + q K + 1 := by
  rw [Projectivization.card_of_finrank K (Fin 3 → K) (n := 3)]
  · simp [q, Finset.sum_range_succ, pow_two, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc]
  · simp

theorem projectivePlane_order_eq_card :
    Configuration.ProjectivePlane.order (P K) (P K) = q K := by
  have hp := Configuration.ProjectivePlane.card_points (P K) (P K)
  rw [← Nat.card_eq_fintype_card, card_points_eq K] at hp
  have hrq :
      Configuration.ProjectivePlane.order (P K) (P K) ^ 2 +
          Configuration.ProjectivePlane.order (P K) (P K) =
        (q K) ^ 2 + q K := by omega
  nlinarith

theorem card_points_tight : Nat.card (P K) = (q K + 1) * q K + 1 := by
  rw [card_points_eq K]
  ring

noncomputable def pointEquivFin : P K ≃ Fin ((q K + 1) * q K + 1) :=
  Fintype.equivFinOfCardEq (by
    rw [Fintype.card_eq_nat_card, card_points_tight K])

noncomputable def finGraph : SimpleGraph (Fin ((q K + 1) * q K + 1)) :=
  (graph K).comap (pointEquivFin K).symm

noncomputable instance finGraphDecidableAdj : DecidableRel (finGraph K).Adj :=
  Classical.decRel _

theorem finGraph_minDegree : q K ≤ (finGraph K).minDegree := by
  have hi := SimpleGraph.Iso.comap (pointEquivFin K).symm (graph K)
  change q K ≤ ((graph K).comap (pointEquivFin K).symm).minDegree
  rw [hi.minDegree_eq]
  rw [← projectivePlane_order_eq_card K]
  exact order_le_minDegree

theorem finGraph_not_containsC4 :
    ¬ containsC4 _ (finGraph K) := by
  intro h
  rcases h with ⟨f, hf, hadj⟩
  apply graph_not_containsC4 (K := K)
  refine ⟨fun i ↦ (pointEquivFin K).symm (f i), ?_, ?_⟩
  · exact (pointEquivFin K).symm.injective.comp hf
  · intro i j hij
    exact hadj i j hij

theorem tightC4Witness : TightC4Witness (q K + 1) := by
  refine ⟨finGraph K, finGraphDecidableAdj K, ?_, finGraph_not_containsC4 K⟩
  simpa [TightC4Witness] using finGraph_minDegree K

theorem minDegreeForC4_projectivePlane :
    minDegreeForC4 ((q K + 1) * q K + 1) = q K + 1 := by
  apply minDegreeForC4_eq_tight_of_witness
  · have := Finite.one_lt_card (α := K)
    change 3 ≤ Nat.card K + 1
    omega
  · simpa [TightC4Witness] using tightC4Witness K

end Erdos85.Polarity
