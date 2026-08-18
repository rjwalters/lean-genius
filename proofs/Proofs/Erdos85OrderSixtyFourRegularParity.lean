import Proofs.Erdos85OrderSixtyFourRegularKernel
import Proofs.Erdos85EvenExcessOneDefectKernel

/-! # Mod-two parity in the order-64 regular kernel -/

open SimpleGraph

namespace Erdos85

/-- The even-order alternating adjacency matrix has a kernel vector other
than zero and the all-ones vector.  Through the defect square identity this
is a nontrivial kernel vector of `I + J + D`. -/
theorem orderSixtyFour_exists_nontrivial_defect_kernel_vector
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8) :
    ∃ w : Fin 64 → ZMod 2, w ≠ 0 ∧ w ≠ (fun _ => 1) ∧
      ((1 : Matrix (Fin 64) (Fin 64) (ZMod 2)) +
        Matrix.of (fun _ _ => (1 : ZMod 2)) +
        (secondOrderDefectGraph G).adjMatrix (ZMod 2)).mulVec w = 0 := by
  have hreg := orderSixtyFour_regular_of_tightCover G hfree hmin hcover
  have hones := adjMatrix_zmodTwo_mulVec_ones_eq_zero
    G (show Even 8 by norm_num) hreg
  have hsymm : ∀ x y : Fin 64,
      G.adjMatrix (ZMod 2) x y = G.adjMatrix (ZMod 2) y x := by
    intro x y
    simp only [SimpleGraph.adjMatrix_apply]
    by_cases h : G.Adj x y
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun h' => h h'.symm)]
  have hdiag : ∀ x : Fin 64, G.adjMatrix (ZMod 2) x x = 0 := by
    intro x
    rw [SimpleGraph.adjMatrix_apply, if_neg (G.loopless.irrefl x)]
  obtain ⟨w, hker, hw0, hw1⟩ := exists_kernel_vector_ne_zero_ne_ones
    (show Even (Fintype.card (Fin 64)) by norm_num)
    (G.adjMatrix (ZMod 2)) hsymm hdiag hones
  refine ⟨w, hw0, hw1, ?_⟩
  rw [← adjMatrix_sq_eq_defect_mod_two_of_even_regular
      G hfree (show Even 8 by norm_num) hreg,
    ← Matrix.mulVec_mulVec, hker, Matrix.mulVec_zero]

/-- Set form of the endpoint parity obstruction.  The support is proper and
nonempty, and every vertex sees the prescribed parity in the 7-regular
second-order defect graph. -/
theorem orderSixtyFour_exists_proper_defect_parity_set
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8) :
    ∃ W : Finset (Fin 64), W ≠ ∅ ∧ W ≠ Finset.univ ∧ ∀ v : Fin 64,
      (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
        ((((secondOrderDefectGraph G).neighborFinset v ∩ W).card : ZMod 2))
          = 0 := by
  obtain ⟨w, hw0, hw1, hker⟩ :=
    orderSixtyFour_exists_nontrivial_defect_kernel_vector
      G hfree hmin hcover
  set W : Finset (Fin 64) := Finset.univ.filter (fun v => w v = 1) with hWdef
  have hmem : ∀ v, v ∈ W ↔ w v = 1 := by
    intro v
    simp [hWdef]
  have hval : ∀ v, w v = if v ∈ W then (1 : ZMod 2) else 0 := by
    intro v
    by_cases h : v ∈ W
    · rw [if_pos h]
      exact (hmem v).mp h
    · rw [if_neg h]
      have hne : w v ≠ 1 := fun hc => h ((hmem v).mpr hc)
      have hcases : ∀ x : ZMod 2, x ≠ 1 → x = 0 := by decide
      exact hcases _ hne
  refine ⟨W, ?_, ?_, ?_⟩
  · intro hW
    apply hw0
    funext v
    rw [Pi.zero_apply, hval v, hW]
    simp
  · intro hW
    apply hw1
    funext v
    rw [hval v, hW]
    simp
  · intro v
    have hcomp := congrFun hker v
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec] at hcomp
    simp only [Pi.add_apply, Pi.zero_apply] at hcomp
    have hJ : ((Matrix.of (fun _ _ => (1 : ZMod 2))).mulVec w) v =
        (W.card : ZMod 2) := by
      rw [Matrix.mulVec, dotProduct]
      simp only [Matrix.of_apply, one_mul]
      calc
        ∑ u, w u = ∑ u, (if u ∈ W then (1 : ZMod 2) else 0) :=
          Finset.sum_congr rfl fun u _ => hval u
        _ = ((Finset.univ.filter (· ∈ W)).card : ZMod 2) := by
          rw [Finset.sum_boole]
        _ = (W.card : ZMod 2) := by rw [Finset.filter_univ_mem]
    have hD :
        (((secondOrderDefectGraph G).adjMatrix (ZMod 2)).mulVec w) v =
          ((((secondOrderDefectGraph G).neighborFinset v ∩ W).card :
            ZMod 2)) := by
      rw [Matrix.mulVec, dotProduct]
      simp only [SimpleGraph.adjMatrix_apply, ite_mul, one_mul, zero_mul]
      rw [← Finset.sum_filter]
      have hfilt : Finset.univ.filter
          (fun u => (secondOrderDefectGraph G).Adj v u) =
          (secondOrderDefectGraph G).neighborFinset v := by
        ext u
        simp [SimpleGraph.mem_neighborFinset]
      rw [hfilt]
      calc
        ∑ u ∈ (secondOrderDefectGraph G).neighborFinset v, w u =
            ∑ u ∈ (secondOrderDefectGraph G).neighborFinset v,
              (if u ∈ W then (1 : ZMod 2) else 0) :=
          Finset.sum_congr rfl fun u _ => hval u
        _ = ((((secondOrderDefectGraph G).neighborFinset v).filter
            (· ∈ W)).card : ZMod 2) := by
          rw [Finset.sum_boole]
        _ = ((((secondOrderDefectGraph G).neighborFinset v ∩ W).card :
            ZMod 2)) := by
          rw [Finset.filter_mem_eq_inter]
    rw [hJ, hD] at hcomp
    rw [← hval v]
    exact hcomp

end Erdos85
