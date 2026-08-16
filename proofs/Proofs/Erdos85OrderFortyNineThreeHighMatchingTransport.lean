import Proofs.Erdos85OrderFortyNineThreeRootedWedgeGluing
import Proofs.Erdos85OrderFortyNineThreeHighScoutGraphBridge

/-! # Transporting local standard mates to the three-high scout -/

namespace Erdos85

open SimpleGraph

def OrderFortyNineStandardMatchingTarget
    (target : Fin 8 → Fin 49) (vertices : List (Fin 49))
    (matching : List (Fin 49 × Fin 49)) : Prop :=
  ∀ ab ∈ orderFortyNineStrictPairs vertices,
    ∃ i j : Fin 8,
      target i = ab.1 ∧ target j = ab.2 ∧
      (ab ∈ matching ↔ j = oneHighStandardMate i)

theorem orderFortyNineDistTwoFirstTarget_standard :
    OrderFortyNineStandardMatchingTarget
      orderFortyNineDistTwoFirstTarget
      [3, 4, 5, 6, 7, 8, 9, 10]
      [(3, 4), (5, 6), (7, 8), (9, 10)] := by
  unfold OrderFortyNineStandardMatchingTarget
  native_decide

theorem orderFortyNineDistTwoSecondTarget_standard :
    OrderFortyNineStandardMatchingTarget
      orderFortyNineDistTwoSecondTarget
      [3, 11, 14, 15, 16, 17, 18, 19]
      [(3, 11), (14, 15), (16, 17), (18, 19)] := by
  unfold OrderFortyNineStandardMatchingTarget
  native_decide

theorem orderFortyNineDistTwoThirdTarget_standard :
    OrderFortyNineStandardMatchingTarget
      orderFortyNineDistTwoThirdTarget
      [3, 12, 20, 21, 22, 23, 24, 25]
      [(3, 12), (20, 21), (22, 23), (24, 25)] := by
  unfold OrderFortyNineStandardMatchingTarget
  native_decide

theorem orderFortyNineGraphPinnedMatchingRealized_of_localNormalization
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {v : V} (e : {x : V // x ∈ G.neighborSet v} ≃ Fin 8)
    (E : V ≃ Fin 49) (target : Fin 8 → Fin 49)
    (vertices : List (Fin 49)) (matching : List (Fin 49 × Fin 49))
    (hcanonical : ∀ x y,
      decide ((G.induce (G.neighborSet v)).Adj x y) =
        decide (e y = oneHighStandardMate (e x)))
    (hmap : ∀ i, E (e.symm i).1 = target i)
    (htarget : OrderFortyNineStandardMatchingTarget
      target vertices matching) :
    OrderFortyNineGraphPinnedMatchingRealized
      (orderFortyNineRelabeledGraph G E) vertices matching := by
  intro ab hab
  obtain ⟨i, j, hi, hj, hm⟩ := htarget ab hab
  have hEi : E (e.symm i).1 = ab.1 := (hmap i).trans hi
  have hEj : E (e.symm j).1 = ab.2 := (hmap j).trans hj
  have hsymi : E.symm ab.1 = (e.symm i).1 := by
    apply E.injective
    simp [hEi]
  have hsymj : E.symm ab.2 = (e.symm j).1 := by
    apply E.injective
    simp [hEj]
  rw [orderFortyNineRelabeledGraph_adj, hsymi, hsymj]
  have hc := hcanonical (e.symm i) (e.symm j)
  simp only [SimpleGraph.induce_adj, e.apply_symm_apply] at hc
  have hiff : G.Adj (e.symm i).1 (e.symm j).1 ↔
      j = oneHighStandardMate i := by
    constructor
    · intro h
      have ht : decide (G.Adj (e.symm i).1 (e.symm j).1) = true := by
        simp [h]
      rw [hc] at ht
      simpa using ht
    · intro h
      have ht : decide (j = oneHighStandardMate i) = true := by simp [h]
      rw [← hc] at ht
      simpa using ht
  exact hiff.trans hm.symm

end Erdos85
