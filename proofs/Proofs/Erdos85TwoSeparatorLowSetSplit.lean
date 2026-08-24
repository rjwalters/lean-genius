import Proofs.Erdos85TwoSeparatorLowSetCoupling
import Proofs.Erdos85ExteriorDefectDecomposition
import Proofs.Erdos85C4FreeCommonNeighborUnique

/-!
# Splitting a coupled low set across two pole neighborhoods

The Boolean coupling identity forces each low set to contain the unique
common pole neighbor and otherwise split between the two punctured pole
neighborhoods.  Each half together with the center is independent in the
second-order defect graph, since all of its vertices share a pole neighbor.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Nonadjacent defect poles have exactly one common ambient neighbor. -/
theorem exists_commonNeighbor_inter_eq_singleton_of_not_secondOrderDefect_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {x y : V} (hxy : x ≠ y)
    (hnotD : ¬ (secondOrderDefectGraph G).Adj x y) :
    ∃ c, G.neighborFinset x ∩ G.neighborFinset y = {c} := by
  have hcard : (G.neighborFinset x ∩ G.neighborFinset y).card ≠ 0 := by
    intro hzero
    exact hnotD ((secondOrderDefectGraph_adj_iff_card_common_eq_zero
      G hfree hxy).mpr hzero)
  obtain ⟨c, hc⟩ := Finset.card_ne_zero.mp hcard
  refine ⟨c, ?_⟩
  ext z
  constructor
  · intro hz
    have hcAdj := Finset.mem_inter.mp hc
    have hzAdj := Finset.mem_inter.mp hz
    have hzc : z = c := commonNeighbor_unique_of_c4Free hfree hxy
      ((SimpleGraph.mem_neighborFinset G x z).mp hzAdj.1)
      ((SimpleGraph.mem_neighborFinset G y z).mp hzAdj.2)
      ((SimpleGraph.mem_neighborFinset G x c).mp hcAdj.1)
      ((SimpleGraph.mem_neighborFinset G y c).mp hcAdj.2)
    simpa [hzc]
  · intro hz
    have hzc : z = c := Finset.mem_singleton.mp hz
    simpa [hzc] using hc

/-- A set participating in a two-set indicator coupling is the disjoint
union of the common center and its two punctured pole-neighborhood parts. -/
theorem indicatorCoupledSet_eq_center_union_puncturedParts
    {V : Type*} [DecidableEq V]
    (Z Z' Nx Ny : Finset V) (c : V)
    (hinter : Nx ∩ Ny = {c})
    (hcoup : ∀ v,
      (if v ∈ Z then 1 else 0) + (if v ∈ Z' then 1 else 0) =
        (if v ∈ Nx then 1 else 0) + (if v ∈ Ny then 1 else 0)) :
    let P := Z ∩ (Nx \ Ny)
    let Q := Z ∩ (Ny \ Nx)
    c ∈ Z ∧ c ∉ P ∧ c ∉ Q ∧ Disjoint P Q ∧
      Z = insert c (P ∪ Q) := by
  have hcInter : c ∈ Nx ∩ Ny := by rw [hinter]; simp
  have hcNx : c ∈ Nx := (Finset.mem_inter.mp hcInter).1
  have hcNy : c ∈ Ny := (Finset.mem_inter.mp hcInter).2
  have hcZ : c ∈ Z := by
    specialize hcoup c
    by_cases hcZ : c ∈ Z <;> by_cases hcZ' : c ∈ Z' <;>
      simp [hcZ, hcZ', hcNx, hcNy] at hcoup ⊢
  let P := Z ∩ (Nx \ Ny)
  let Q := Z ∩ (Ny \ Nx)
  have hcP : c ∉ P := by simp [P, hcNy]
  have hcQ : c ∉ Q := by simp [Q, hcNx]
  have hPQ : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro v hvP hvQ
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hvP).2).2
      (Finset.mem_sdiff.mp (Finset.mem_inter.mp hvQ).2).1
  refine ⟨hcZ, hcP, hcQ, hPQ, ?_⟩
  ext v
  constructor
  · intro hvZ
    by_cases hvc : v = c
    · simp [hvc]
    have hsupp : v ∈ Nx ∨ v ∈ Ny := by
      specialize hcoup v
      by_contra hnone
      push_neg at hnone
      simp [hvZ, hnone.1, hnone.2] at hcoup
    have hnotBoth : ¬ (v ∈ Nx ∧ v ∈ Ny) := by
      rintro ⟨hvNx, hvNy⟩
      have hvInter : v ∈ Nx ∩ Ny := Finset.mem_inter.mpr ⟨hvNx, hvNy⟩
      rw [hinter] at hvInter
      exact hvc (Finset.mem_singleton.mp hvInter)
    simp only [Finset.mem_insert, Finset.mem_union, P, Q,
      Finset.mem_inter, Finset.mem_sdiff]
    rcases hsupp with hvNx | hvNy
    · exact Or.inr (Or.inl ⟨hvZ, hvNx, fun hvNy => hnotBoth ⟨hvNx, hvNy⟩⟩)
    · exact Or.inr (Or.inr ⟨hvZ, hvNy, fun hvNx => hnotBoth ⟨hvNx, hvNy⟩⟩)
  · intro hv
    simp only [Finset.mem_insert, Finset.mem_union, P, Q,
      Finset.mem_inter, Finset.mem_sdiff] at hv
    rcases hv with rfl | ⟨hvZ, _⟩ | ⟨hvZ, _⟩
    · exact hcZ
    · exact hvZ
    · exact hvZ

/-- Cardinality form of the punctured split. -/
theorem indicatorCoupledSet_puncturedParts_card_add
    {V : Type*} [DecidableEq V]
    (Z Z' Nx Ny : Finset V) (c : V) (q : ℕ)
    (hZcard : Z.card = q)
    (hinter : Nx ∩ Ny = {c})
    (hcoup : ∀ v,
      (if v ∈ Z then 1 else 0) + (if v ∈ Z' then 1 else 0) =
        (if v ∈ Nx then 1 else 0) + (if v ∈ Ny then 1 else 0)) :
    (Z ∩ (Nx \ Ny)).card + (Z ∩ (Ny \ Nx)).card = q - 1 := by
  obtain ⟨_, hcP, hcQ, hPQ, hsplit⟩ :=
    indicatorCoupledSet_eq_center_union_puncturedParts
      Z Z' Nx Ny c hinter hcoup
  have hcUnion : c ∉ (Z ∩ (Nx \ Ny)) ∪ (Z ∩ (Ny \ Nx)) := by simp [hcP, hcQ]
  have hcard := congrArg Finset.card hsplit
  rw [Finset.card_insert_of_notMem hcUnion,
    Finset.card_union_of_disjoint hPQ, hZcard] at hcard
  omega

/-- Any collection of vertices sharing an ambient neighbor is independent
in the second-order defect graph. -/
theorem secondOrderDefect_isIndepSet_of_subset_neighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (pole : V) (R : Finset V)
    (hR : R ⊆ G.neighborFinset pole) :
    (secondOrderDefectGraph G).IsIndepSet (R : Set V) := by
  intro u hu v hv huv
  have hup : G.Adj u pole :=
    ((SimpleGraph.mem_neighborFinset G pole u).mp (hR hu)).symm
  have hvp : G.Adj v pole :=
    ((SimpleGraph.mem_neighborFinset G pole v).mp (hR hv)).symm
  intro hD
  have hzero := (secondOrderDefectGraph_adj_iff_card_common_eq_zero
    G hfree huv).mp hD
  have hp : pole ∈ G.neighborFinset u ∩ G.neighborFinset v :=
    Finset.mem_inter.mpr ⟨
      (SimpleGraph.mem_neighborFinset G u pole).mpr hup,
      (SimpleGraph.mem_neighborFinset G v pole).mpr hvp⟩
  rw [Finset.card_eq_zero.mp hzero] at hp
  simp at hp

/-- Graph-facing split package for one of the two coupled low sets. -/
theorem exists_twoPole_puncturedParts_with_defect_independence
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {x y : V} (hxy : x ≠ y)
    (hnotD : ¬ (secondOrderDefectGraph G).Adj x y)
    (Z Z' : Finset V) (q : ℕ) (hZcard : Z.card = q)
    (hcoup : ∀ v,
      (if v ∈ Z then 1 else 0) + (if v ∈ Z' then 1 else 0) =
        (if G.Adj v x then 1 else 0) + (if G.Adj v y then 1 else 0)) :
    ∃ c P Q,
      G.neighborFinset x ∩ G.neighborFinset y = {c} ∧
      c ∈ Z ∧ c ∉ P ∧ c ∉ Q ∧ Disjoint P Q ∧
      Z = insert c (P ∪ Q) ∧ P.card + Q.card = q - 1 ∧
      (secondOrderDefectGraph G).IsIndepSet (↑(insert c P) : Set V) ∧
      (secondOrderDefectGraph G).IsIndepSet (↑(insert c Q) : Set V) := by
  obtain ⟨c, hinter⟩ :=
    exists_commonNeighbor_inter_eq_singleton_of_not_secondOrderDefect_adj
      G hfree hxy hnotD
  let Nx := G.neighborFinset x
  let Ny := G.neighborFinset y
  let P := Z ∩ (Nx \ Ny)
  let Q := Z ∩ (Ny \ Nx)
  have hcoup' : ∀ v,
      (if v ∈ Z then 1 else 0) + (if v ∈ Z' then 1 else 0) =
        (if v ∈ Nx then 1 else 0) + (if v ∈ Ny then 1 else 0) := by
    intro v
    simpa [Nx, Ny, SimpleGraph.mem_neighborFinset, G.adj_comm] using hcoup v
  obtain ⟨hcZ, hcP, hcQ, hPQ, hsplit⟩ :=
    indicatorCoupledSet_eq_center_union_puncturedParts
      Z Z' Nx Ny c hinter hcoup'
  have hcards : P.card + Q.card = q - 1 :=
    indicatorCoupledSet_puncturedParts_card_add
      Z Z' Nx Ny c q hZcard hinter hcoup'
  have hcInter : c ∈ Nx ∩ Ny := by rw [hinter]; simp
  have hsubP : insert c P ⊆ Nx := by
    intro v hv
    simp only [Finset.mem_insert] at hv
    rcases hv with rfl | hv
    · exact (Finset.mem_inter.mp hcInter).1
    · exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hv).2).1
  have hsubQ : insert c Q ⊆ Ny := by
    intro v hv
    simp only [Finset.mem_insert] at hv
    rcases hv with rfl | hv
    · exact (Finset.mem_inter.mp hcInter).2
    · exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hv).2).1
  refine ⟨c, P, Q, hinter, hcZ, hcP, hcQ, hPQ, hsplit, hcards, ?_, ?_⟩
  · exact secondOrderDefect_isIndepSet_of_subset_neighborFinset
      G hfree x (insert c P) hsubP
  · exact secondOrderDefect_isIndepSet_of_subset_neighborFinset
      G hfree y (insert c Q) hsubQ

#print axioms indicatorCoupledSet_eq_center_union_puncturedParts
#print axioms indicatorCoupledSet_puncturedParts_card_add
#print axioms secondOrderDefect_isIndepSet_of_subset_neighborFinset
#print axioms exists_commonNeighbor_inter_eq_singleton_of_not_secondOrderDefect_adj
#print axioms exists_twoPole_puncturedParts_with_defect_independence

end

end Erdos85
