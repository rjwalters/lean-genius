import Proofs.Erdos85OddSquareOrderNineOneHighDefectGrid

/-! # Component parity in the q=9 one-high defect graph

Node: B.3 / GAP B-CLASSIFY.  The exact 70/10 decomposition forces every
defect-closed sector to contain an even number of one-incidence vertices.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

private theorem degree_induce_finset_eq_card_inter_local
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V)
    (x : ↥(↑A : Set V)) :
    (G.induce (↑A : Set V)).degree x =
      (G.neighborFinset x.1 ∩ A).card := by
  classical
  rw [← (G.induce (↑A : Set V)).card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun y _ => y.1)
  · intro y hy
    have hxy : G.Adj x.1 y.1 :=
      ((G.induce (↑A : Set V)).mem_neighborFinset x y).mp hy
    exact Finset.mem_inter.mpr ⟨
      (G.mem_neighborFinset x.1 y.1).mpr hxy, Finset.mem_coe.mp y.2⟩
  · intro y₁ _ y₂ _ heq
    exact Subtype.ext heq
  · intro y hy
    have hy' := Finset.mem_inter.mp hy
    refine ⟨⟨y, Finset.mem_coe.mpr hy'.2⟩, ?_, rfl⟩
    exact ((G.induce (↑A : Set V)).mem_neighborFinset _ _).mpr
      ((G.mem_neighborFinset x.1 y).mp hy'.1)

/-- In the one-high q=9 horn, any vertex set closed under defect adjacency
meets the one-incidence bin in even cardinality.  Hence the same holds for
every union of defect components, in particular for each component. -/
theorem squareOrderNine_oneHigh_defectClosed_oneBin_card_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 1)
    (S : Finset V)
    (hclosed : ∀ {x y : V}, x ∈ S →
      (secondOrderDefectGraph G).Adj x y → y ∈ S) :
    Even ((S ∩ squareOrderNineLowIncidenceBin G 1).card) := by
  classical
  let D := secondOrderDefectGraph G
  let B0 := squareOrderNineLowIncidenceBin G 0
  let B1 := squareOrderNineLowIncidenceBin G 1
  let A := S ∩ B0
  let C := S ∩ B1
  have hdec := squareOrderNine_oneHigh_defect_decomposition
    G hfree hmin hcover hcard hp hhigh
  dsimp only at hdec
  have hA0 (x : V) (hx : x ∈ A) :
      (D.neighborFinset x ∩ A).card = 7 := by
    change x ∈ S ∩ B0 at hx
    have hx' := Finset.mem_inter.mp hx
    have heq : D.neighborFinset x ∩ A = D.neighborFinset x ∩ B0 := by
      change D.neighborFinset x ∩ (S ∩ B0) = D.neighborFinset x ∩ B0
      ext y
      simp only [Finset.mem_inter]
      constructor
      · exact fun hy => ⟨hy.1, hy.2.2⟩
      · intro hy
        refine ⟨hy.1, ?_, hy.2⟩
        exact hclosed hx'.1 ((D.mem_neighborFinset x y).mp hy.1)
    rw [heq]
    exact (hdec.2.2.1 x hx'.2).1
  have hA1 (x : V) (hx : x ∈ A) :
      (D.neighborFinset x ∩ C).card = 1 := by
    change x ∈ S ∩ B0 at hx
    have hx' := Finset.mem_inter.mp hx
    have heq : D.neighborFinset x ∩ C = D.neighborFinset x ∩ B1 := by
      change D.neighborFinset x ∩ (S ∩ B1) = D.neighborFinset x ∩ B1
      ext y
      simp only [Finset.mem_inter]
      constructor
      · exact fun hy => ⟨hy.1, hy.2.2⟩
      · intro hy
        refine ⟨hy.1, ?_, hy.2⟩
        exact hclosed hx'.1 ((D.mem_neighborFinset x y).mp hy.1)
    rw [heq]
    exact (hdec.2.2.1 x hx'.2).2
  have hC0 (y : V) (hy : y ∈ C) :
      (D.neighborFinset y ∩ A).card = 7 := by
    change y ∈ S ∩ B1 at hy
    have hy' := Finset.mem_inter.mp hy
    have heq : D.neighborFinset y ∩ A = D.neighborFinset y ∩ B0 := by
      change D.neighborFinset y ∩ (S ∩ B0) = D.neighborFinset y ∩ B0
      ext x
      simp only [Finset.mem_inter]
      constructor
      · exact fun hx => ⟨hx.1, hx.2.2⟩
      · intro hx
        refine ⟨hx.1, ?_, hx.2⟩
        exact hclosed hy'.1 ((D.mem_neighborFinset y x).mp hx.1)
    rw [heq]
    exact (hdec.2.2.2 y hy'.2).1
  have hcross : A.card = 7 * C.card := by
    have hcomm := sum_card_neighborFinset_inter_comm D A C
    calc
      A.card = ∑ x ∈ A, (D.neighborFinset x ∩ C).card := by
        calc
          A.card = ∑ _x ∈ A, 1 := by simp
          _ = _ := by
            apply Finset.sum_congr rfl
            intro x hx
            symm
            exact hA1 x hx
      _ = ∑ y ∈ C, (D.neighborFinset y ∩ A).card := hcomm
      _ = ∑ _y ∈ C, 7 := by
        apply Finset.sum_congr rfl
        intro y hy
        exact hC0 y hy
      _ = 7 * C.card := by simp [Nat.mul_comm]
  have hinternalEven : Even (7 * A.card) := by
    let K := D.induce (↑A : Set V)
    have hsum : (∑ x ∈ A, (D.neighborFinset x ∩ A).card) =
        ∑ x : ↥(↑A : Set V), K.degree x := by
      rw [← Finset.sum_attach]
      apply Finset.sum_congr rfl
      intro x _hx
      exact (degree_induce_finset_eq_card_inter_local D A x).symm
    have hseven : (∑ x ∈ A, (D.neighborFinset x ∩ A).card) =
        7 * A.card := by
      calc
        _ = ∑ _x ∈ A, 7 := by
          apply Finset.sum_congr rfl
          intro x hx
          exact hA0 x hx
        _ = 7 * A.card := by simp [Nat.mul_comm]
    rw [← hseven, hsum, K.sum_degrees_eq_twice_card_edges]
    exact ⟨K.edgeFinset.card, by omega⟩
  change Even C.card
  obtain ⟨w, hw⟩ := hinternalEven
  rw [hcross] at hw
  apply Nat.even_iff.mpr
  have hwmod := congrArg (fun n : ℕ => n % 2) hw
  omega

end

end Erdos85

#print axioms Erdos85.squareOrderNine_oneHigh_defectClosed_oneBin_card_even
