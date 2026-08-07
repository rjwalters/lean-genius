import Proofs.Erdos85OrderFortyNineFullCanonicalLabeling
import Proofs.Erdos85OrderFortyNineBooleanTerminal
import Proofs.Erdos85Relabel

/-!
# From exact canonical labels to the order-49 Boolean terminal

The aligned key remembers the literal label of every high vertex.  This file
extracts the two pointwise facts needed for graph relabeling: exact placement
of high vertices and preservation of every high-support bit.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

theorem orderFortyNine_alignedLabeling_high_image
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    (masks : Array Nat) (E : V ≃ Fin 49)
    (hE : ∀ x,
      orderFortyNineMaskAlignedVertexKey masks (E x) =
        orderFortyNineGraphAlignedVertexKey G e x)
    (w : Fin 9) : E (e.symm w).1 = ⟨w.val, by omega⟩ := by
  have hfirst := congrArg Prod.fst (hE (e.symm w).1)
  have hsome :
      (if h : (E (e.symm w).1).val < 9
        then some (⟨(E (e.symm w).1).val, h⟩ : Fin 9)
        else none) = some w := by
    simpa [orderFortyNineMaskAlignedVertexKey,
      orderFortyNineGraphAlignedVertexKey] using hfirst
  by_cases hlt : (E (e.symm w).1).val < 9
  · simp [hlt] at hsome
    apply Fin.ext
    simpa using congrArg Fin.val hsome
  · simp [hlt] at hsome

theorem orderFortyNine_alignedLabeling_support
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    (masks : Array Nat) (E : V ≃ Fin 49)
    (hE : ∀ x,
      orderFortyNineMaskAlignedVertexKey masks (E x) =
        orderFortyNineGraphAlignedVertexKey G e x)
    (x : V) :
    orderFortyNineMaskSupport masks (E x) =
      orderFortyNineLabeledHighSupport G e x := by
  simpa [orderFortyNineMaskAlignedVertexKey,
    orderFortyNineGraphAlignedVertexKey] using congrArg Prod.snd (hE x)

/-- Relabel `G` by an exact canonical vertex equivalence. -/
def orderFortyNineRelabeledGraph
    {V : Type*} (G : SimpleGraph V) (E : V ≃ Fin 49) :
    SimpleGraph (Fin 49) :=
  SimpleGraph.comap E.symm G

instance orderFortyNineRelabeledGraph_decidableAdj
    {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (E : V ≃ Fin 49) : DecidableRel (orderFortyNineRelabeledGraph G E).Adj :=
  fun i j => inferInstanceAs (Decidable (G.Adj (E.symm i) (E.symm j)))

theorem orderFortyNineRelabeledGraph_adj
    {V : Type*} (G : SimpleGraph V) (E : V ≃ Fin 49)
    (i j : Fin 49) :
    (orderFortyNineRelabeledGraph G E).Adj i j ↔
      G.Adj (E.symm i) (E.symm j) := by
  rfl

theorem orderFortyNineRelabeledGraph_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (E : V ≃ Fin 49) (i : Fin 49) :
    (orderFortyNineRelabeledGraph G E).degree i = G.degree (E.symm i) := by
  classical
  exact (SimpleGraph.Iso.comap E.symm G).degree_eq i |>.symm

theorem orderFortyNineRelabeledGraph_not_containsC4
    {V : Type*} (G : SimpleGraph V) (E : V ≃ Fin 49)
    (hfree : ¬ containsC4 V G) :
    ¬ containsC4 (Fin 49) (orderFortyNineRelabeledGraph G E) := by
  exact fun h => hfree ((containsC4_iff_of_iso
    (SimpleGraph.Iso.comap E.symm G)).mp h)

/-- Exact high-label alignment turns support preservation into the fixed-edge
condition expected by the Boolean terminal. -/
theorem orderFortyNineRelabeledGraph_highAdj_eq_supportBit
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    (masks : Array Nat) (E : V ≃ Fin 49)
    (hE : ∀ x,
      orderFortyNineMaskAlignedVertexKey masks (E x) =
        orderFortyNineGraphAlignedVertexKey G e x)
    (i : Fin 49) (w : Fin 9) :
    decide ((orderFortyNineRelabeledGraph G E).Adj
      i ⟨w.val, by omega⟩) =
      (orderFortyNineSupportMask masks i).getLsbD w.val := by
  let wi : Fin 49 := ⟨w.val, by omega⟩
  have hhigh : E (e.symm w).1 = wi :=
    orderFortyNine_alignedLabeling_high_image G e masks E hE w
  have hhighSymm : E.symm wi = (e.symm w).1 := by
    apply E.injective
    simp [hhigh]
  have hs := orderFortyNine_alignedLabeling_support
    G e masks E hE (E.symm i)
  have hs' : orderFortyNineMaskSupport masks i =
      orderFortyNineLabeledHighSupport G e (E.symm i) := by
    simpa using hs
  have hadjmem : G.Adj (E.symm i) (e.symm w).1 ↔
      w ∈ orderFortyNineMaskSupport masks i := by
    rw [hs']
    exact (mem_orderFortyNineLabeledHighSupport_iff
      G e (E.symm i) w).symm
  rw [Bool.eq_iff_iff]
  simpa [wi, orderFortyNineRelabeledGraph_adj,
    hhighSymm, orderFortyNineMaskSupport] using hadjmem

end

end Erdos85
