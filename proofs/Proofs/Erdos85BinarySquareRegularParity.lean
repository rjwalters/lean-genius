import Proofs.Erdos85EvenExcessOneDefectKernel
import Proofs.Erdos85AdjacencyCharpolySquareModTwo

/-!
# Characteristic-two parity for regular square-order cores

The mod-two defect-kernel argument is not peculiar to the order-64 endpoint
or to the excess-one order.  On any even square order, an even-regular
`C₄`-free graph has a second adjacency-kernel vector, hence the same
nonconstant vector lies in the kernel of `I + J + D`.  This is the uniform parity input for the
regular binary square-order branch.
-/

open SimpleGraph

namespace Erdos85

/-- **Uniform binary-square defect kernel.**  Let `G` be an even-regular
`C₄`-free graph on `q²` vertices, with `q > 0`.  Over `𝔽₂`, the matrix
`A` has a kernel vector distinct from both zero and the all-ones vector, and
that same vector is killed by `I + J + D`.

The proof uses only that `q²` is even.  Thus every hypothetical regular core
in the characteristic-two square-order branch carries this extra parity
structure, independently of any finite component census. -/
theorem binarySquare_regular_exists_nontrivial_defect_kernel_vector
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 0 < q) (heven : Even q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) :
    ∃ w : V → ZMod 2, w ≠ 0 ∧ w ≠ (fun _ => 1) ∧
      (G.adjMatrix (ZMod 2)).mulVec w = 0 ∧
      ((1 : Matrix V V (ZMod 2)) + Matrix.of (fun _ _ => (1 : ZMod 2)) +
        (secondOrderDefectGraph G).adjMatrix (ZMod 2)).mulVec w = 0 := by
  haveI : Nonempty V := by
    rw [← Fintype.card_pos_iff, hcard]
    positivity
  have hnEven : Even (Fintype.card V) := by
    obtain ⟨k, hk⟩ := heven
    refine ⟨k * q, ?_⟩
    rw [hcard, hk]
    ring
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
  refine ⟨w, hw0, hw1, hker, ?_⟩
  rw [← adjMatrix_sq_eq_defect_mod_two_of_even_regular G hfree heven hreg,
    ← Matrix.mulVec_mulVec, hker, Matrix.mulVec_zero]

/-- **Coupled parity-set form.**  Under the same binary square-order
hypotheses, there is a proper nonempty vertex set `W` such that every vertex
has an even number of `G`-neighbors in `W`, while its defect neighborhood
satisfies the parity forced by membership in `W` and by `|W|`.

This is the combinatorial interface intended for component and Gram arguments:
it remembers both halves of the coupled kernel statement without mentioning
matrix-vector multiplication. -/
theorem binarySquare_regular_exists_coupled_parity_set
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 0 < q) (heven : Even q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) :
    ∃ W : Finset V, W ≠ ∅ ∧ W ≠ Finset.univ ∧
      (∀ v : V, (((G.neighborFinset v ∩ W).card : ZMod 2)) = 0) ∧
      (∀ v : V,
        (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
          ((((secondOrderDefectGraph G).neighborFinset v ∩ W).card : ZMod 2))
            = 0) := by
  obtain ⟨w, hw0, hw1, hA, hDker⟩ :=
    binarySquare_regular_exists_nontrivial_defect_kernel_vector
      G hfree hq heven hreg hcard
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
  refine ⟨W, ?_, ?_, ?_, ?_⟩
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
    have hcomp := congrFun hA v
    rw [Matrix.mulVec, dotProduct] at hcomp
    simp only [SimpleGraph.adjMatrix_apply, ite_mul, one_mul, zero_mul] at hcomp
    rw [← Finset.sum_filter] at hcomp
    have hfilt : Finset.univ.filter (fun u => G.Adj v u) =
        G.neighborFinset v := by
      ext u
      simp [SimpleGraph.mem_neighborFinset]
    rw [hfilt] at hcomp
    calc
      (((G.neighborFinset v ∩ W).card : ZMod 2)) =
          ∑ u ∈ G.neighborFinset v,
            (if u ∈ W then (1 : ZMod 2) else 0) := by
        symm
        rw [Finset.sum_boole, Finset.filter_mem_eq_inter]
      _ = ∑ u ∈ G.neighborFinset v, w u :=
        Finset.sum_congr rfl fun u _ => (hval u).symm
      _ = 0 := by simpa using hcomp
  · intro v
    have hcomp := congrFun hDker v
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

/-- On an even square order, the mod-two characteristic polynomial of the
second-order defect graph is a square.  No transfer through the adjacency
square identity is needed: the defect graph is itself a simple graph on the
same even vertex type. -/
theorem binarySquare_defect_charpoly_isSquare_zmodTwo
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (secondOrderDefectGraph G).Adj]
    {q : ℕ} (heven : Even q) (hcard : Fintype.card V = q * q) :
    ∃ p : Polynomial (ZMod 2),
      ((secondOrderDefectGraph G).adjMatrix (ZMod 2)).charpoly = p ^ 2 := by
  apply adjMatrix_charpoly_isSquare_zmodTwo
  obtain ⟨k, hk⟩ := heven
  refine ⟨k * q, ?_⟩
  rw [hcard, hk]
  ring

end Erdos85
