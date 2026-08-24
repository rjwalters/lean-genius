import Proofs.Erdos85FinalDyadicExceptionalProfile
import Proofs.Erdos85CanonicalExceptionalSaturatedDeficit

/-!
# Incidence capacity of an exceptional empty clique

Defect adjacency means zero ambient codegree.  Thus a defect clique of empty
line centers has point replication at most one, and its disjoint `q`-blocks
must fit inside the complementary shore.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A second-order-defect clique has ambient point replication at most one. -/
theorem secondOrderDefectClique_replicationAtMostOne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (E : Finset V)
    (hclique : ∀ ⦃u v⦄, u ∈ E → v ∈ E → u ≠ v →
      (secondOrderDefectGraph G).Adj u v) :
    ∀ x, (G.neighborFinset x ∩ E).card ≤ 1 := by
  intro x
  rw [Finset.card_le_one]
  intro u hu v hv
  have huData := Finset.mem_inter.mp hu
  have hvData := Finset.mem_inter.mp hv
  by_contra huv
  exact (not_secondOrderDefect_adj_of_commonNeighbor
    G hfree huv
      ((G.mem_neighborFinset x u).mp huData.1).symm
      ((G.mem_neighborFinset x v).mp hvData.1).symm)
    (hclique huData.2 hvData.2 huv)

/-- Canonical empty-clique incidence capacity: all its disjoint degree-`q`
blocks lie in the complementary shore. -/
theorem emptyLineCenters_mul_degree_le_complement_card_of_clique
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ v, G.degree v = q) (S : Finset V)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v) :
    q * (emptyLineCenters G S).card ≤ Fintype.card V - S.card := by
  apply regular_emptyLines_mul_card_le_complement_card
    G hreg S (emptyLineCenters G S)
  · exact fun e he => (mem_emptyLineCenters G S e).mp he
  · intro v _hv
    exact secondOrderDefectClique_replicationAtMostOne
      G hfree (emptyLineCenters G S) hemptyClique v

/-- Square-order form of the canonical empty-clique incidence capacity. -/
theorem binarySquare_emptyLineCenters_mul_degree_le_complement_card_of_clique
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v) :
    q * (emptyLineCenters G S).card ≤ q * q - S.card := by
  rw [← hcard]
  exact emptyLineCenters_mul_degree_le_complement_card_of_clique
    G hfree hreg S hemptyClique

/-- At saturated exceptional support, empty-clique incidence capacity forces
the deficit population to be at most half the degree. -/
theorem binarySquare_saturatedDeficit_twice_le_degree_of_emptyClique
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q r : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      2 * (G.neighborFinset v ∩ S).card = q ∨
      (G.neighborFinset v ∩ S).card = q)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v)
    (hsupportCard : (exceptionalSignedSupport G S q).card = q)
    (hdisplacement :
      2 * (S.card : ℤ) - Fintype.card V = (q : ℤ) - 2 * r) :
    2 * r ≤ q := by
  have hsum : (fullLineCenters G S q).card +
      (emptyLineCenters G S).card = q := by
    rw [← exceptionalSignedSupport_card_eq_full_add_empty G S (by omega),
      hsupportCard]
  have hdiff : ((fullLineCenters G S q).card : ℤ) -
      (emptyLineCenters G S).card = (q : ℤ) - 2 * r := by
    rw [fullLineCenters_card_sub_emptyLineCenters_card_eq_cutDisplacement
      G (by omega) hreg S htri, hdisplacement]
  have hemptyCard : (emptyLineCenters G S).card = r :=
    (full_empty_populations_of_saturated_deficit hsum hdiff).1
  have hinc :=
    binarySquare_emptyLineCenters_mul_degree_le_complement_card_of_clique
      G hfree hreg hcard S hemptyClique
  have hScard : S.card ≤ Fintype.card V := by
    simpa only [Finset.card_univ] using
      Finset.card_le_card (show S ⊆ (Finset.univ : Finset V) from Finset.subset_univ S)
  have hincAdd : q * r + S.card ≤ q * q := by
    rw [← hemptyCard]
    omega
  have hincZ : (q : ℤ) * r + S.card ≤ (q : ℤ) * q := by
    exact_mod_cast hincAdd
  rw [hcard] at hdisplacement
  push_cast at hdisplacement
  nlinarith

/-- Final-dyadic specialization: divisibility supplies the occupancy
trichotomy required by the saturated half-degree bound. -/
theorem binarySquare_finalDyadic_saturatedDeficit_twice_le_degree_of_emptyClique
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j r : ℕ} (hq : 3 ≤ q)
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v)
    (hsupportCard : (exceptionalSignedSupport G S q).card = q)
    (hdisplacement :
      2 * (S.card : ℤ) - Fintype.card V = (q : ℤ) - 2 * r) :
    2 * r ≤ q := by
  exact binarySquare_saturatedDeficit_twice_le_degree_of_emptyClique
    G hfree hq hreg hcard S
      (finalDyadic_occupancy_trichotomy G hqa hreg S hdiv)
      hemptyClique hsupportCard hdisplacement

end

end Erdos85

#print axioms Erdos85.secondOrderDefectClique_replicationAtMostOne
#print axioms Erdos85.emptyLineCenters_mul_degree_le_complement_card_of_clique
#print axioms
  Erdos85.binarySquare_emptyLineCenters_mul_degree_le_complement_card_of_clique
#print axioms
  Erdos85.binarySquare_saturatedDeficit_twice_le_degree_of_emptyClique
#print axioms
  Erdos85.binarySquare_finalDyadic_saturatedDeficit_twice_le_degree_of_emptyClique
