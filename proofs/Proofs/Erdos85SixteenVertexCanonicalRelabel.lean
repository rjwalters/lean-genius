import Proofs.Erdos85BipartiteMissingMatching
import Proofs.Erdos85K88MinusMatchingMatrix

/-! # Canonical relabeling of the sixteen-vertex bipartite component -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- An exhaustive disjoint finset partition identifies the ambient type with
the sum of its two side subtypes. -/
def finsetPartitionEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (L R : Finset V) (hcover : L ∪ R = univ) (hdisj : Disjoint L R) :
    V ≃ (L : Set V) ⊕ (R : Set V) where
  toFun x := if hx : x ∈ L then Sum.inl ⟨x, hx⟩ else
    Sum.inr ⟨x, by
      have hxUnion : x ∈ L ∪ R := by rw [hcover]; simp
      exact (mem_union.mp hxUnion).resolve_left hx⟩
  invFun s := Sum.elim (fun x => x.1) (fun x => x.1) s
  left_inv x := by
    by_cases hx : x ∈ L <;> simp [hx]
  right_inv s := by
    rcases s with x | x
    · simp [x.2]
    · have hxnot : x.1 ∉ L := by
        intro hxL
        exact (Finset.disjoint_left.mp hdisj hxL) x.2
      simp [hxnot]

def sixteenLeftLabel
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ x : V, G.degree x = 7) (u : V)
    (c : (nonneighborResidual G u : Set V)) :
    (sixteenLeftSide G u c : Set V) ≃ Fin 8 :=
  Fintype.equivFinOfCardEq (by
    simpa using card_sixteenLeftSide_eq_eight G hreg u c)

/-- Coherent canonical labels: label the left shore arbitrarily by `Fin 8`;
label a right vertex by the label of its unique missing left partner. -/
def sixteenCanonicalRelabel
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 16)
    (htriangle : G.CliqueFree 3)
    (hreg : ∀ x : V, G.degree x = 7) (u : V)
    (c : (nonneighborResidual G u : Set V))
    (hc : (G.induce (nonneighborResidual G u : Set V)).degree c = 7) :
    V ≃ K88Vertex := by
  let L := sixteenLeftSide G u c
  let R := sixteenRightSide G u c
  let split : V ≃ (L : Set V) ⊕ (R : Set V) :=
    finsetPartitionEquiv L R
      (union_sixteenSides_eq_univ G hcard hreg u c hc)
      (disjoint_sixteenLeftSide_sixteenRightSide G u c)
  let miss : (L : Set V) ≃ (R : Set V) :=
    sixteenMissingEquiv G hcard htriangle hreg u c hc
  let labelL : (L : Set V) ≃ Fin 8 := sixteenLeftLabel G hreg u c
  let labelSides : (L : Set V) ⊕ (R : Set V) ≃ Fin 8 ⊕ Fin 8 :=
    Equiv.sumCongr labelL (miss.symm.trans labelL)
  exact split.trans <| labelSides.trans <|
    (Equiv.boolProdEquivSum (Fin 8)).symm.trans (Equiv.prodComm Bool (Fin 8))

theorem sixteenCanonicalRelabel_symm_false
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 16)
    (htriangle : G.CliqueFree 3)
    (hreg : ∀ x : V, G.degree x = 7) (u : V)
    (c : (nonneighborResidual G u : Set V))
    (hc : (G.induce (nonneighborResidual G u : Set V)).degree c = 7)
    (i : Fin 8) :
    (sixteenCanonicalRelabel G hcard htriangle hreg u c hc).symm (i, false) =
      ((sixteenLeftLabel G hreg u c).symm i).1 := by
  rfl

theorem sixteenCanonicalRelabel_symm_true
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 16)
    (htriangle : G.CliqueFree 3)
    (hreg : ∀ x : V, G.degree x = 7) (u : V)
    (c : (nonneighborResidual G u : Set V))
    (hc : (G.induce (nonneighborResidual G u : Set V)).degree c = 7)
    (i : Fin 8) :
    (sixteenCanonicalRelabel G hcard htriangle hreg u c hc).symm (i, true) =
      (sixteenMissingEquiv G hcard htriangle hreg u c hc
        ((sixteenLeftLabel G hreg u c).symm i)).1 := by
  rfl

/-- In canonical labels, adjacency means opposite sides and unequal matching
indices. -/
theorem sixteenCanonicalRelabel_adj_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 16)
    (htriangle : G.CliqueFree 3)
    (hreg : ∀ x : V, G.degree x = 7) (u : V)
    (c : (nonneighborResidual G u : Set V))
    (hc : (G.induce (nonneighborResidual G u : Set V)).degree c = 7)
    (p q : K88Vertex) :
    G.Adj
      ((sixteenCanonicalRelabel G hcard htriangle hreg u c hc).symm p)
      ((sixteenCanonicalRelabel G hcard htriangle hreg u c hc).symm q) ↔
      p.2 ≠ q.2 ∧ p.1 ≠ q.1 := by
  rcases p with ⟨i, bi⟩
  rcases q with ⟨j, bj⟩
  fin_cases bi <;> fin_cases bj
  · rw [sixteenCanonicalRelabel_symm_true,
      sixteenCanonicalRelabel_symm_true]
    have hnot : ¬ G.Adj
        (sixteenMissingEquiv G hcard htriangle hreg u c hc
          ((sixteenLeftLabel G hreg u c).symm i)).1
        (sixteenMissingEquiv G hcard htriangle hreg u c hc
          ((sixteenLeftLabel G hreg u c).symm j)).1 := by
      by_cases hij :
          (sixteenMissingEquiv G hcard htriangle hreg u c hc
            ((sixteenLeftLabel G hreg u c).symm i)).1 =
          (sixteenMissingEquiv G hcard htriangle hreg u c hc
            ((sixteenLeftLabel G hreg u c).symm j)).1
      · intro hadj
        rw [hij] at hadj
        exact G.loopless.irrefl _ hadj
      · exact sixteenRightSide_not_adj G htriangle u c
          (sixteenMissingEquiv G hcard htriangle hreg u c hc
            ((sixteenLeftLabel G hreg u c).symm i)).2
          (sixteenMissingEquiv G hcard htriangle hreg u c hc
            ((sixteenLeftLabel G hreg u c).symm j)).2 hij
    simp [hnot]

  · rw [sixteenCanonicalRelabel_symm_true,
      sixteenCanonicalRelabel_symm_false, G.adj_comm]
    let L := sixteenLeftSide G u c
    let R := sixteenRightSide G u c
    have h := adj_bipartiteMissingEquiv_apply_iff_ne G L R
      (card_sixteenLeftSide_eq_eight G hreg u c)
      (card_sixteenRightSide_eq_eight G u c hc)
      (fun x hx => left_neighbor_inter_right_card_eq_seven
        G hcard htriangle hreg u c hc hx)
      (fun y hy => right_neighbor_inter_left_card_eq_seven
        G hcard htriangle hreg u c hc hy)
      ((sixteenLeftLabel G hreg u c).symm j)
      ((sixteenLeftLabel G hreg u c).symm i)
    have hindex :
        (sixteenLeftLabel G hreg u c).symm j ≠
          (sixteenLeftLabel G hreg u c).symm i ↔ j ≠ i := by
      exact (sixteenLeftLabel G hreg u c).symm.injective.ne_iff
    simpa [L, R, sixteenMissingEquiv, hindex, ne_comm] using h
  · rw [sixteenCanonicalRelabel_symm_false,
      sixteenCanonicalRelabel_symm_true]
    let L := sixteenLeftSide G u c
    let R := sixteenRightSide G u c
    have h := adj_bipartiteMissingEquiv_apply_iff_ne G L R
      (card_sixteenLeftSide_eq_eight G hreg u c)
      (card_sixteenRightSide_eq_eight G u c hc)
      (fun x hx => left_neighbor_inter_right_card_eq_seven
        G hcard htriangle hreg u c hc hx)
      (fun y hy => right_neighbor_inter_left_card_eq_seven
        G hcard htriangle hreg u c hc hy)
      ((sixteenLeftLabel G hreg u c).symm i)
      ((sixteenLeftLabel G hreg u c).symm j)
    have hindex :
        (sixteenLeftLabel G hreg u c).symm i ≠
          (sixteenLeftLabel G hreg u c).symm j ↔ i ≠ j := by
      exact (sixteenLeftLabel G hreg u c).symm.injective.ne_iff
    simpa [L, R, sixteenMissingEquiv, hindex] using h
  · rw [sixteenCanonicalRelabel_symm_false,
      sixteenCanonicalRelabel_symm_false]
    have hnot : ¬ G.Adj
        ((sixteenLeftLabel G hreg u c).symm i).1
        ((sixteenLeftLabel G hreg u c).symm j).1 := by
      by_cases hij : ((sixteenLeftLabel G hreg u c).symm i).1 =
          ((sixteenLeftLabel G hreg u c).symm j).1
      · intro hadj
        rw [hij] at hadj
        exact G.loopless.irrefl _ hadj
      · exact sixteenLeftSide_not_adj G htriangle hreg u c hc
          ((sixteenLeftLabel G hreg u c).symm i).2
          ((sixteenLeftLabel G hreg u c).symm j).2 hij
    simp [hnot]

/-- The relabelled rational adjacency matrix is exactly the canonical
`K_{8,8}`-minus-matching matrix. -/
theorem reindex_adjMatrix_eq_k88MinusMatching
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 16)
    (htriangle : G.CliqueFree 3)
    (hreg : ∀ x : V, G.degree x = 7) (u : V)
    (c : (nonneighborResidual G u : Set V))
    (hc : (G.induce (nonneighborResidual G u : Set V)).degree c = 7) :
    Matrix.reindex
      (sixteenCanonicalRelabel G hcard htriangle hreg u c hc)
      (sixteenCanonicalRelabel G hcard htriangle hreg u c hc)
      (G.adjMatrix ℚ) = k88MinusMatchingMatrix := by
  ext p q
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    SimpleGraph.adjMatrix_apply, k88MinusMatchingMatrix]
  simp only [sixteenCanonicalRelabel_adj_iff G hcard htriangle hreg u c hc p q]

/-- Capstone: every triangle-free seven-regular graph on sixteen vertices has
the `K_{8,8}`-minus-matching annihilator. -/
theorem triangleFree_sevenRegular_sixteen_aeval_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 16)
    (htriangle : G.CliqueFree 3)
    (hreg : ∀ x : V, G.degree x = 7) (u : V) :
    Polynomial.aeval (Matrix.toLin' (G.adjMatrix ℚ))
      ((Polynomial.X - Polynomial.C (7 : ℚ)) *
       (Polynomial.X - Polynomial.C (1 : ℚ)) *
       (Polynomial.X - Polynomial.C (-1 : ℚ)) *
       (Polynomial.X - Polynomial.C (-7 : ℚ))) = 0 := by
  obtain ⟨c, hc⟩ :=
    exists_degree_seven_in_nonneighborResidual_unconditional
      G hcard htriangle hreg u
  exact aeval_bipartite_defect_polynomial_eq_zero_of_reindex_eq_k88
    (G.adjMatrix ℚ)
    (sixteenCanonicalRelabel G hcard htriangle hreg u c hc)
    (reindex_adjMatrix_eq_k88MinusMatching G hcard htriangle hreg u c hc)

end

end Erdos85
