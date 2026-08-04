import Proofs.Erdos85PolarityFamily
import Proofs.Erdos85Relabel
import Proofs.Erdos85DeletePair
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# Deleting an absolute point from a polarity graph

Deleting one self-orthogonal point from the orthogonal-polarity graph preserves
minimum degree.  This gives a second consecutive order at each projective-plane
parameter, conditional only on the existence of an absolute point.
-/

open SimpleGraph Finset
open scoped LinearAlgebra.Projectivization

namespace Erdos85.Polarity

universe u

variable {K : Type u} [Field K] [Finite K] [DecidableEq K]

private noncomputable abbrev P (K : Type u) [Field K] := ℙ K (Fin 3 → K)
private noncomputable abbrev q (K : Type u) := Nat.card K

/-- Distinct self-orthogonal projective points cannot be orthogonal. -/
theorem not_selfOrthogonal_of_adj_selfOrthogonal {x y : P K}
    (hxy : (graph K).Adj x y) (hxx : Projectivization.orthogonal x x) :
    ¬ Projectivization.orthogonal y y := by
  intro hyy
  have hne : x ≠ y := (graph_adj_iff x y).mp hxy |>.1
  have hxy' : Projectivization.orthogonal x y := (graph_adj_iff x y).mp hxy |>.2
  have hxxm : x ∈ x := (Configuration.ofField.mem_iff x x).2 hxx
  have hxym : x ∈ y := (Configuration.ofField.mem_iff x y).2 hxy'
  have hyxm : y ∈ x := (Configuration.ofField.mem_iff y x).2
    (Projectivization.orthogonal_comm.mp hxy')
  have hyym : y ∈ y := (Configuration.ofField.mem_iff y y).2 hyy
  exact hne (Configuration.Nondegenerate.eq_or_eq hxxm hyxm hxym hyym |>.resolve_right hne)

/-- A non-absolute point has degree exactly `q+1`. -/
theorem degree_eq_card_add_one_of_not_selfOrthogonal {y : P K}
    (hyy : ¬ Projectivization.orthogonal y y) :
    (graph K).degree y = q K + 1 := by
  classical
  rw [SimpleGraph.degree, neighborFinset_eq_erase_incidentFinset]
  have hy : y ∉ incidentFinset y := by
    simpa [incidentFinset, Configuration.ofField.mem_iff] using hyy
  rw [Finset.erase_eq_self.mpr hy, card_incidentFinset,
    projectivePlane_order_eq_card K]

/-- A self-orthogonal point has degree exactly `q`: its incidence line has
`q+1` points, but the loop at the point itself is removed. -/
theorem degree_eq_card_of_selfOrthogonal {y : P K}
    (hyy : Projectivization.orthogonal y y) :
    (graph K).degree y = q K := by
  classical
  rw [SimpleGraph.degree, neighborFinset_eq_erase_incidentFinset]
  have hy : y ∈ incidentFinset y := by
    simpa [incidentFinset, Configuration.ofField.mem_iff] using hyy
  rw [Finset.card_erase_of_mem hy, card_incidentFinset,
    projectivePlane_order_eq_card K]
  simp [q]

/-- The graph obtained by deleting a projective point. -/
noncomputable def deletePointGraph (x : P K) :
    SimpleGraph {y : P K // y ≠ x} :=
  (graph K).induce {y | y ≠ x}

noncomputable instance deletePointGraphDecidableAdj (x : P K) :
    DecidableRel (deletePointGraph x).Adj := Classical.decRel _

theorem deletePointGraph_degree (x : P K) (y : {y : P K // y ≠ x}) :
    (deletePointGraph x).degree y =
      (((graph K).neighborFinset y.1).erase x).card := by
  classical
  have hdeg : (deletePointGraph x).degree y =
      (graph K).degree y - if (graph K).Adj y x then 1 else 0 := by
    exact degree_induce_delete_eq (graph K) x y
  rw [hdeg]
  by_cases hxy : (graph K).Adj y x
  · rw [if_pos hxy, Finset.card_erase_of_mem (by simpa using hxy)]
    rw [SimpleGraph.card_neighborFinset_eq_degree]
  · rw [if_neg hxy, Nat.sub_zero, Finset.erase_eq_of_notMem (by simpa using hxy)]
    rw [SimpleGraph.card_neighborFinset_eq_degree]

/-- Deleting a self-orthogonal point preserves minimum degree `q`. -/
theorem deletePointGraph_minDegree (x : P K)
    (hxx : Projectivization.orthogonal x x) :
    q K ≤ (deletePointGraph x).minDegree := by
  classical
  obtain ⟨z, hz⟩ := Projectivization.exists_not_self_orthogonal x
  letI : Nonempty {y : P K // y ≠ x} :=
    ⟨⟨z, fun hzx => hz (by simpa [hzx] using hxx)⟩⟩
  apply SimpleGraph.le_minDegree_of_forall_le_degree
  intro y
  rw [deletePointGraph_degree]
  by_cases hxy : (graph K).Adj x y.1
  · have hyx : (graph K).Adj y.1 x := hxy.symm
    have hydeg := degree_eq_card_add_one_of_not_selfOrthogonal
      (not_selfOrthogonal_of_adj_selfOrthogonal hxy hxx)
    have hxmem : x ∈ (graph K).neighborFinset y.1 := by simpa using hyx
    rw [Finset.card_erase_of_mem hxmem,
      SimpleGraph.card_neighborFinset_eq_degree, hydeg]
    omega
  · have hxnot : x ∉ (graph K).neighborFinset y.1 := by
      simpa [adj_comm] using hxy
    rw [Finset.erase_eq_self.mpr hxnot, SimpleGraph.card_neighborFinset_eq_degree]
    exact (order_le_degree y.1).trans' (by rw [projectivePlane_order_eq_card K])

theorem deletePointGraph_not_containsC4 (x : P K) :
    ¬ containsC4 _ (deletePointGraph x) := by
  rintro ⟨f, hf, hadj⟩
  apply graph_not_containsC4 (K := K)
  refine ⟨fun i ↦ (f i).1, Subtype.val_injective.comp hf, ?_⟩
  intro i j hij
  exact hadj i j hij

/-- Conditional consecutive-order polarity witness at `q²+q`. -/
theorem c4FreeMinDegreeWitness_card_mul_add (x : P K)
    (hxx : Projectivization.orthogonal x x) :
    C4FreeMinDegreeWitness ((q K + 1) * q K) (q K) := by
  classical
  apply c4FreeMinDegreeWitness_of_card_eq (deletePointGraph x)
  · change Fintype.card {y : P K // y ≠ x} = (q K + 1) * q K
    have hcard : Fintype.card (P K) = (q K + 1) * q K + 1 := by
      rw [Fintype.card_eq_nat_card]
      exact card_points_tight K
    have hone : Fintype.card {y : P K // y = x} = 1 :=
      Fintype.card_unique
    rw [Fintype.card_subtype_compl]
    rw [hcard, hone]
    omega
  · exact deletePointGraph_minDegree x hxx
  · exact deletePointGraph_not_containsC4 x

/-- An absolute point pins the exact threshold at the order immediately below
the projective-plane order. -/
theorem minDegreeForC4_card_mul_add (x : P K)
    (hxx : Projectivization.orthogonal x x) :
    minDegreeForC4 ((q K + 1) * q K) = q K + 1 := by
  apply le_antisymm
  · apply minDegreeForC4_le_of_le_mul_pred
    · have := Finite.one_lt_card (α := K)
      change 1 < q K at this
      nlinarith
    · simp only [Nat.add_sub_cancel]
      exact le_rfl
  · exact (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 (by
        have := Finite.one_lt_card (α := K)
        nlinarith)).mp
      (c4FreeMinDegreeWitness_card_mul_add x hxx)

end Erdos85.Polarity
