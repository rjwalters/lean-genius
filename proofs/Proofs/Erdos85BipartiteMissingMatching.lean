import Proofs.Erdos85SixteenVertexBipartition

/-! # The missing perfect matching between two eight-element shores -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

def missingAcross
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset V) (x : V) : Finset V :=
  R \ G.neighborFinset x

theorem card_missingAcross_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset V) (x : V)
    (hR : R.card = 8)
    (hcross : (G.neighborFinset x ∩ R).card = 7) :
    (missingAcross G R x).card = 1 := by
  rw [missingAcross, card_sdiff, hR]
  rw [hcross]

def missingAcrossVertex
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset V) (x : V)
    (hone : (missingAcross G R x).card = 1) : V :=
  Classical.choose (show (missingAcross G R x).Nonempty by
    rw [← card_pos]
    omega)

theorem missingAcrossVertex_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset V) (x : V)
    (hone : (missingAcross G R x).card = 1) :
    missingAcrossVertex G R x hone ∈ missingAcross G R x :=
  Classical.choose_spec (show (missingAcross G R x).Nonempty by
    rw [← card_pos]
    omega)

/-- The unique vertex across the bipartition which is not adjacent to `x`. -/
def bipartiteMiss
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset V) (x : V)
    (hone : (missingAcross G R x).card = 1) : (R : Set V) := by
  exact ⟨missingAcrossVertex G R x hone,
    (mem_sdiff.mp (missingAcrossVertex_mem G R x hone)).1⟩

theorem bipartiteMiss_mem_missingAcross
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset V) (x : V)
    (hone : (missingAcross G R x).card = 1) :
    (bipartiteMiss G R x hone).1 ∈ missingAcross G R x := by
  unfold bipartiteMiss
  dsimp only
  exact missingAcrossVertex_mem G R x hone

theorem eq_bipartiteMiss_of_mem_missingAcross
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset V) (x y : V)
    (hone : (missingAcross G R x).card = 1)
    (hy : y ∈ missingAcross G R x) :
    y = (bipartiteMiss G R x hone).1 := by
  obtain ⟨z, hz⟩ := card_eq_one.mp hone
  have hyz : y = z := by simpa [hz] using hy
  have hm := bipartiteMiss_mem_missingAcross G R x hone
  have hmz : (bipartiteMiss G R x hone).1 = z := by simpa [hz] using hm
  exact hyz.trans hmz.symm

/-- If both shores have size eight and every vertex has seven cross
neighbours, the unique misses form a bijection (a perfect matching in the
cross-complement). -/
def bipartiteMissingEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (L R : Finset V)
    (hLcard : L.card = 8) (hRcard : R.card = 8)
    (hLR : ∀ x ∈ L, (G.neighborFinset x ∩ R).card = 7)
    (hRL : ∀ y ∈ R, (G.neighborFinset y ∩ L).card = 7) :
    (L : Set V) ≃ (R : Set V) where
  toFun x := bipartiteMiss G R x.1
    (card_missingAcross_eq_one G R x.1 hRcard (hLR x.1 x.2))
  invFun y := bipartiteMiss G L y.1
    (card_missingAcross_eq_one G L y.1 hLcard (hRL y.1 y.2))
  left_inv x := by
    apply Subtype.ext
    let hRone := card_missingAcross_eq_one G R x.1 hRcard (hLR x.1 x.2)
    let y := bipartiteMiss G R x.1 hRone
    let hLone := card_missingAcross_eq_one G L y.1 hLcard (hRL y.1 y.2)
    symm
    apply eq_bipartiteMiss_of_mem_missingAcross G L y.1 x.1 hLone
    apply mem_sdiff.mpr
    constructor
    · exact x.2
    · have hymiss := bipartiteMiss_mem_missingAcross G R x.1 hRone
      have hxyNonadj : x.1 ∉ G.neighborFinset y.1 := by
        have hyNonadj : y.1 ∉ G.neighborFinset x.1 := (mem_sdiff.mp hymiss).2
        intro hxy
        exact hyNonadj ((G.mem_neighborFinset x.1 y.1).mpr
          ((G.adj_comm y.1 x.1).mp ((G.mem_neighborFinset y.1 x.1).mp hxy)))
      exact hxyNonadj
  right_inv y := by
    apply Subtype.ext
    let hLone := card_missingAcross_eq_one G L y.1 hLcard (hRL y.1 y.2)
    let x := bipartiteMiss G L y.1 hLone
    let hRone := card_missingAcross_eq_one G R x.1 hRcard (hLR x.1 x.2)
    symm
    apply eq_bipartiteMiss_of_mem_missingAcross G R x.1 y.1 hRone
    apply mem_sdiff.mpr
    constructor
    · exact y.2
    · have hxmiss := bipartiteMiss_mem_missingAcross G L y.1 hLone
      have hyxNonadj : y.1 ∉ G.neighborFinset x.1 := by
        have hxNonadj : x.1 ∉ G.neighborFinset y.1 := (mem_sdiff.mp hxmiss).2
        intro hyx
        exact hxNonadj ((G.mem_neighborFinset y.1 x.1).mpr
          ((G.adj_comm x.1 y.1).mp ((G.mem_neighborFinset x.1 y.1).mp hyx)))
      exact hyxNonadj

/-- The cross-complement of the two sides extracted from a residual star is
therefore a perfect matching. -/
def sixteenMissingEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 16)
    (htriangle : G.CliqueFree 3)
    (hreg : ∀ x : V, G.degree x = 7) (u : V)
    (c : (nonneighborResidual G u : Set V))
    (hc : (G.induce (nonneighborResidual G u : Set V)).degree c = 7) :
    (sixteenLeftSide G u c : Set V) ≃
      (sixteenRightSide G u c : Set V) :=
  bipartiteMissingEquiv G (sixteenLeftSide G u c)
    (sixteenRightSide G u c)
    (card_sixteenLeftSide_eq_eight G hreg u c)
    (card_sixteenRightSide_eq_eight G u c hc)
    (fun x hx => left_neighbor_inter_right_card_eq_seven
      G hcard htriangle hreg u c hc hx)
    (fun y hy => right_neighbor_inter_left_card_eq_seven
      G hcard htriangle hreg u c hc hy)

end

end Erdos85
