import Proofs.Erdos85LocalCycleSAT

/-!
# A six-cycle in every K₄-free `(16,6,2,2)` neighborhood
-/

namespace Erdos85

open SimpleGraph

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

/-- The local labeling needed before extending to the normalized global
`Fin 16` labeling. -/
def HasSixCycleNeighborhood {V : Type*} (H : SimpleGraph V) : Prop :=
  ∃ x : V, ∃ u : Fin 6 → V,
    Function.Injective u ∧
    (∀ i, H.Adj x (u i)) ∧
    H.Adj (u 0) (u 1) ∧ H.Adj (u 1) (u 2) ∧
    H.Adj (u 2) (u 3) ∧ H.Adj (u 3) (u 4) ∧
    H.Adj (u 4) (u 5) ∧ H.Adj (u 5) (u 0)

theorem hasSixCycleNeighborhood_of_srg1622_of_not_hasK4
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : Fintype.card V = 16)
    (hreg : ∀ x : V, H.degree x = 6)
    (hcommon : ∀ x y : V, x ≠ y →
      (H.neighborFinset x ∩ H.neighborFinset y).card = 2)
    (hnok4 : ¬ HasK4 H) :
    HasSixCycleNeighborhood H := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let x : V := Classical.choice inferInstance
  let N := H.neighborFinset x
  have hNcard : N.card = 6 := hreg x
  let e : Fin 6 ≃ ↑N :=
    (Fintype.equivFinOfCardEq (by simpa using hNcard)).symm
  have eAdj (i : Fin 6) : H.Adj x (e i : V) := by
    have hp := (e i).property
    change (e i : V) ∈ H.neighborFinset x at hp
    simpa using hp
  let r : Fin 6 → Fin 6 → Bool := fun i j => decide (H.Adj (e i) (e j))
  have hr : BoolLocalTwoRegularTriangleFree r := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      simp [r]
    · intro i j
      simp only [r, decide_eq_decide]
      exact H.adj_comm _ _
    · intro i
      have hxi : x ≠ (e i : V) := by
        intro h
        have hadj : H.Adj x (e i : V) := eAdj i
        exact H.loopless.irrefl x (h ▸ hadj)
      calc
        (Finset.univ.filter fun j => r i j).card =
            (H.neighborFinset x ∩ H.neighborFinset (e i : V)).card := by
          apply Finset.card_bij (fun j _ => (e j : V))
          · intro j hj
            rw [Finset.mem_filter] at hj
            have hjadj : H.Adj (e i : V) (e j : V) := by
              simpa [r] using hj.2
            exact Finset.mem_inter.mpr ⟨by simpa using eAdj j, by simpa using hjadj⟩
          · intro a ha b hb hab
            exact e.injective (Subtype.ext hab)
          · intro z hz
            have hz' := Finset.mem_inter.mp hz
            let zn : ↑N := ⟨z, hz'.1⟩
            refine ⟨e.symm zn, ?_, ?_⟩
            · rw [Finset.mem_filter]
              refine ⟨by simp, ?_⟩
              simpa [r, zn] using hz'.2
            · simp [zn]
        _ = 2 := hcommon x (e i : V) hxi
    · intro i j k hij hik hjk htri
      rcases htri with ⟨hijA, hikA, hjkA⟩
      apply hnok4
      have hxi : x ≠ (e i : V) := by
        intro h
        exact H.loopless.irrefl x (h ▸ eAdj i)
      have hxj : x ≠ (e j : V) := by
        intro h
        exact H.loopless.irrefl x (h ▸ eAdj j)
      have hxk : x ≠ (e k : V) := by
        intro h
        exact H.loopless.irrefl x (h ▸ eAdj k)
      have eij : (e i : V) ≠ (e j : V) := fun h => hij (e.injective (Subtype.ext h))
      have eik : (e i : V) ≠ (e k : V) := fun h => hik (e.injective (Subtype.ext h))
      have ejk : (e j : V) ≠ (e k : V) := fun h => hjk (e.injective (Subtype.ext h))
      have Aij : H.Adj (e i : V) (e j : V) := by simpa [r] using hijA
      have Aik : H.Adj (e i : V) (e k : V) := by simpa [r] using hikA
      have Ajk : H.Adj (e j : V) (e k : V) := by simpa [r] using hjkA
      exact ⟨x, (e i : V), (e j : V), (e k : V),
        hxi, hxj, hxk, eij, eik, ejk,
        eAdj i, eAdj j, eAdj k, Aij, Aik, Ajk⟩
  have hcycle := boolLocalTwoRegularTriangleFree_hasCycleOrder6 hr
  rcases hcycle with ⟨p1, p2, p3, p4, p5,
    h01, h02, h03, h04, h05, h12, h13, h14, h15,
    h23, h24, h25, h34, h35, h45,
    A01, A12, A23, A34, A45, A50⟩
  let o : Fin 6 → Fin 6 := ![0, p1, p2, p3, p4, p5]
  have ho : Function.Injective o := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [o] at * <;> aesop
  let u : Fin 6 → V := fun i => (e (o i) : V)
  refine ⟨x, u, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Subtype.val_injective.comp e.injective).comp ho
  · intro i
    exact eAdj (o i)
  · simpa [u, o, r] using A01
  · simpa [u, o, r] using A12
  · simpa [u, o, r] using A23
  · simpa [u, o, r] using A34
  · simpa [u, o, r] using A45
  · simpa [u, o, r] using A50

end Erdos85
