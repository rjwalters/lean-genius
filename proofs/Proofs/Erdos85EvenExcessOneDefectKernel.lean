import Proofs.Erdos85AlternatingParity
import Proofs.Erdos85ExcessDefectRegular

/-!
# The `𝔽₂` defect kernel at even-degree excess one

At even regular degree the defect matrix equation `A² = (d-1)I + J - D`
reduces mod two to `A² = I + J + D`.  The adjacency matrix is alternating
over `𝔽₂` and kills the all-ones vector (the degree is even), so by the
alternating-parity engine its kernel contains a vector `w ∉ {0, 𝟙}`.
Since `ker A ⊆ ker A²`, the matrix `I + J + D` kills `w` as well.

Translated to sets, the support `W` of `w` is an **odd defect set**: it is
neither empty nor the full vertex set, and for every vertex `v` the count
`[v ∈ W] + |W| + |N_D(v) ∩ W|` is even.  This is a structural constraint
that any putative even-degree excess-one graph must satisfy; it pins the
mod-two combinatorics of the three-regular defect graph `D` against the
canonical `(0,3)/(2,1)` color regime.
-/

open SimpleGraph

namespace Erdos85

/-- Doubling kills every element of `ZMod 2`. -/
theorem zmodTwo_add_self : ∀ x : ZMod 2, x + x = 0 := by decide

/-- Mod-two version of the common-neighbor square formula. -/
theorem adjMatrix_sq_apply_eq_card_common_zmodTwo
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) :
    (G.adjMatrix (ZMod 2) * G.adjMatrix (ZMod 2)) x y =
      ((G.neighborFinset x ∩ G.neighborFinset y).card : ZMod 2) := by
  rw [G.adjMatrix_mul_apply]
  simp only [SimpleGraph.adjMatrix_apply]
  rw [Finset.sum_boole]
  have hfilt : (G.neighborFinset x).filter (fun z => G.Adj z y) =
      G.neighborFinset x ∩ G.neighborFinset y := by
    ext z
    simp [SimpleGraph.mem_neighborFinset, G.adj_comm]
  rw [hfilt]

/-- **Mod-two defect matrix equation.**  At even regular degree,
`A² = I + J + D` over `𝔽₂`. -/
theorem adjMatrix_sq_eq_defect_mod_two_of_even_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (heven : Even d)
    (hreg : ∀ x, G.degree x = d) :
    G.adjMatrix (ZMod 2) * G.adjMatrix (ZMod 2) =
      (1 : Matrix V V (ZMod 2)) + Matrix.of (fun _ _ => (1 : ZMod 2)) +
        (secondOrderDefectGraph G).adjMatrix (ZMod 2) := by
  ext x y
  simp only [Matrix.add_apply, Matrix.of_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [SimpleGraph.adjMatrix_mul_self_apply_self, hreg x,
      Matrix.one_apply_eq, SimpleGraph.adjMatrix_apply,
      if_neg ((secondOrderDefectGraph G).loopless.irrefl x)]
    obtain ⟨k, hk⟩ := heven
    subst hk
    have hcast : ((k + k : ℕ) : ZMod 2) = 0 := by
      push_cast
      exact zmodTwo_add_self _
    rw [hcast, add_zero]
    decide +kernel
  · rw [adjMatrix_sq_apply_eq_card_common_zmodTwo,
      Matrix.one_apply_ne hxy,
      card_common_eq_if_secondOrderDefect G hfree x y hxy]
    by_cases hdef : y ∈ (secondOrderDefectGraph G).neighborFinset x
    · rw [if_pos hdef, SimpleGraph.adjMatrix_apply,
        if_pos (((secondOrderDefectGraph G).mem_neighborFinset x y).mp hdef)]
      decide +kernel
    · rw [if_neg hdef, SimpleGraph.adjMatrix_apply,
        if_neg (fun hadj => hdef
          (((secondOrderDefectGraph G).mem_neighborFinset x y).mpr hadj))]
      decide +kernel

/-- At even regular degree the mod-two adjacency matrix kills the all-ones
vector. -/
theorem adjMatrix_zmodTwo_mulVec_ones_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (heven : Even d) (hreg : ∀ x, G.degree x = d) :
    (G.adjMatrix (ZMod 2)).mulVec (fun _ => 1) = 0 := by
  funext x
  rw [Pi.zero_apply, Matrix.mulVec, dotProduct]
  simp only [mul_one, SimpleGraph.adjMatrix_apply]
  rw [Finset.sum_boole]
  have hfilt : Finset.univ.filter (fun y => G.Adj x y) =
      G.neighborFinset x := by
    ext y
    simp [SimpleGraph.mem_neighborFinset]
  rw [hfilt, G.card_neighborFinset_eq_degree, hreg x]
  obtain ⟨k, hk⟩ := heven
  subst hk
  push_cast
  exact zmodTwo_add_self _

/-- **The `𝔽₂` defect kernel.**  Every even-degree excess-one graph admits
a mod-two kernel vector of `I + J + D` distinct from `0` and the all-ones
vector. -/
theorem excessOne_even_exists_defect_kernel_vector
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (heven : Even d)
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) :
    ∃ w : V → ZMod 2, w ≠ 0 ∧ w ≠ (fun _ => 1) ∧
      ((1 : Matrix V V (ZMod 2)) + Matrix.of (fun _ _ => (1 : ZMod 2)) +
        (secondOrderDefectGraph G).adjMatrix (ZMod 2)).mulVec w = 0 := by
  haveI : Nonempty V := by
    rw [← Fintype.card_pos_iff, hcard]
    omega
  have hnEven : Even (Fintype.card V) := by
    obtain ⟨k, hk⟩ := heven
    exact ⟨k * (d - 1) + 2, by rw [hcard, hk]; ring⟩
  have hsymm : ∀ x y : V,
      G.adjMatrix (ZMod 2) x y = G.adjMatrix (ZMod 2) y x := by
    intro x y
    simp only [SimpleGraph.adjMatrix_apply]
    by_cases h : G.Adj x y
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun h' => h h'.symm)]
  have hdiag : ∀ x : V, G.adjMatrix (ZMod 2) x x = 0 := by
    intro x
    rw [SimpleGraph.adjMatrix_apply, if_neg (G.loopless.irrefl x)]
  have hones := adjMatrix_zmodTwo_mulVec_ones_eq_zero G heven hreg
  obtain ⟨w, hker, hw0, hw1⟩ := exists_kernel_vector_ne_zero_ne_ones
    hnEven (G.adjMatrix (ZMod 2)) hsymm hdiag hones
  refine ⟨w, hw0, hw1, ?_⟩
  rw [← adjMatrix_sq_eq_defect_mod_two_of_even_regular G hfree heven hreg,
    ← Matrix.mulVec_mulVec, hker, Matrix.mulVec_zero]

/-- **Odd defect set.**  At even degree and excess one there is a vertex
set `W`, neither empty nor the full set, such that for every vertex `v`
the quantity `[v ∈ W] + |W| + |N_D(v) ∩ W|` vanishes mod two.  In
particular if `|W|` is even, every vertex of `W` has an odd number of
`D`-neighbors inside `W` while every outside vertex has an even number;
for odd `|W|` the two parities are exchanged. -/
theorem excessOne_even_exists_odd_defect_set
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (heven : Even d)
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) :
    ∃ W : Finset V, W ≠ ∅ ∧ W ≠ Finset.univ ∧ ∀ v : V,
      (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
        ((((secondOrderDefectGraph G).neighborFinset v ∩ W).card : ZMod 2))
          = 0 := by
  obtain ⟨w, hw0, hw1, hker⟩ :=
    excessOne_even_exists_defect_kernel_vector G hfree heven hreg hcard
  set W : Finset V := Finset.univ.filter (fun v => w v = 1) with hWdef
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
    have hD : (((secondOrderDefectGraph G).adjMatrix (ZMod 2)).mulVec w) v =
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
        ∑ u ∈ (secondOrderDefectGraph G).neighborFinset v, w u
            = ∑ u ∈ (secondOrderDefectGraph G).neighborFinset v,
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
