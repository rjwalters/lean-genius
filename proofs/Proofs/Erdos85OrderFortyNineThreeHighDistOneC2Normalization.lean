import Proofs.Erdos85OrderFortyNineHighNeighborhoodNormalization
import Proofs.Erdos85OrderFortyNineThreeHighMatchingTransport

/-! # Normalization infrastructure for the three-high `dist1_c2` scout -/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- A degree-eight neighborhood may be normalized while sending two
nonadjacent distinguished neighbors to the two prescribed scout branches. -/
theorem exists_orderFortyNine_highNeighborhood_two_rooted_matching
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v root other : V} (hv : G.degree v = 8)
    (hroot : G.Adj root v) (hother : G.Adj other v)
    (hne : root ≠ other) (hnotAdj : ¬ G.Adj root other) :
    ∃ e : {x : V // x ∈ G.neighborSet v} ≃ Fin 8,
      e ⟨root, by simpa using hroot.symm⟩ = 0 ∧
      e ⟨other, by simpa using hother.symm⟩ = 2 ∧
      ∀ x y,
        decide ((G.induce (G.neighborSet v)).Adj x y) =
          decide (e y = oneHighStandardMate (e x)) := by
  let P := {x : V // x ∈ G.neighborSet v}
  let H := G.induce (G.neighborSet v)
  have hPcard : Fintype.card P = 8 := by
    rw [Fintype.card_subtype]
    have hfilter : Finset.univ.filter (fun z : V => z ∈ G.neighborSet v) =
        G.neighborFinset v := by
      ext z
      simp
    rw [hfilter, G.card_neighborFinset_eq_degree, hv]
  have hlocal : ∀ x : P, H.degree x = 1 :=
    orderFortyNine_localNeighborhood_degree_eq_one_of_degreeEight
      G hfree hmin hcard hv
  have hunique : ∀ x : P, ∃! y : P, decide (H.Adj x y) = true := by
    intro x
    have hx := hlocal x
    rw [← H.card_neighborFinset_eq_degree, Finset.card_eq_one] at hx
    obtain ⟨y, hy⟩ := hx
    refine ⟨y, ?_, ?_⟩
    · simp only [decide_eq_true_eq]
      rw [← H.mem_neighborFinset, hy]
      simp
    · intro z hz
      have hzmem : z ∈ H.neighborFinset x := by
        rw [H.mem_neighborFinset]
        simpa using hz
      simpa [hy] using hzmem
  let rootLocal : P := ⟨root, by simpa using hroot.symm⟩
  let otherLocal : P := ⟨other, by simpa using hother.symm⟩
  apply exists_equiv_finEight_canonical_matching_of_unique_two_rooted
    (root := rootLocal) (other := otherLocal)
    hPcard (fun x y : P => decide (H.Adj x y))
  · intro x y
    apply Bool.decide_congr
    exact H.adj_comm x y
  · intro x
    simp
  · exact hunique
  · simp [H, rootLocal, otherLocal, hnotAdj]
  · intro h
    exact hne (congrArg Subtype.val h)

def orderFortyNineDistOneC2FirstTarget : Fin 8 → Fin 49 :=
  ![3, 4, 5, 6, 7, 8, 9, 10]

def orderFortyNineDistOneC2SecondTarget : Fin 8 → Fin 49 :=
  ![3, 25, 12, 13, 14, 15, 16, 17]

def orderFortyNineDistOneC2ThirdTarget : Fin 8 → Fin 49 :=
  ![5, 18, 19, 25, 20, 21, 22, 23]

theorem orderFortyNineDistOneC2FirstTarget_standard :
    OrderFortyNineStandardMatchingTarget
      orderFortyNineDistOneC2FirstTarget
      [3, 4, 5, 6, 7, 8, 9, 10]
      [(3, 4), (5, 6), (7, 8), (9, 10)] := by
  unfold OrderFortyNineStandardMatchingTarget
  native_decide

theorem orderFortyNineDistOneC2SecondTarget_standard :
    OrderFortyNineStandardMatchingTarget
      orderFortyNineDistOneC2SecondTarget
      [3, 12, 13, 14, 15, 16, 17, 25]
      [(3, 25), (12, 13), (14, 15), (16, 17)] := by
  unfold OrderFortyNineStandardMatchingTarget
  native_decide

theorem orderFortyNineDistOneC2ThirdTarget_standard :
    OrderFortyNineStandardMatchingTarget
      orderFortyNineDistOneC2ThirdTarget
      [5, 18, 19, 20, 21, 22, 23, 25]
      [(5, 18), (19, 25), (20, 21), (22, 23)] := by
  unfold OrderFortyNineStandardMatchingTarget
  native_decide

end

end Erdos85
